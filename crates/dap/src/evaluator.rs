//! 在目标 JVM 的一个栈帧上求值 Java 表达式：`evaluate`、条件断点和日志断点共用。
//!
//! 表达式用仓库自己的语法分析器解析，按语法树求值：
//! - 名字依次在局部变量、`this`（和外层实例）的字段、当前类的静态字段里找，找不到时当作类型名
//!   （当前类和外层类的成员类、源文件的 import、同一个包、`java.lang`）；
//! - 字段访问、数组下标和 `length`、`.class`；
//! - 方法调用：实例方法按运行时类型分派，静态方法、`super.m()`；按实参的运行时类型选重载
//!   （先不装箱、再装箱拆箱、最后变长参数），实参按形参类型拓宽、装箱拆箱、打包成变长数组；
//! - `new` 对象和数组（含初始化器）；
//! - 算术、位运算、移位、比较、字符串连接（对象调 `toString()`）、`&& || !` 短路、三元、
//!   `instanceof`、强制转换。字符串之间的 `==` 比较内容。
//!
//! 方法调用用 `INVOKE_SINGLE_THREADED` 在当前挂起的线程上执行：期间这个线程碰到的断点、单步和
//! 异常事件不停下；别的线程的事件留到调用结束后处理。超时后用 `ThreadReference.Stop` 让被调用的
//! 方法抛出异常退出，会话不会卡住。线程恢复过之后帧 ID 失效，按位置重新取。

use std::{
    collections::HashSet,
    rc::Rc,
    time::{Duration, Instant},
};

use anyhow::{bail, Context};
use base_db::{tr, trs};
use syntax::{
    ast::{self, AstNode},
    SyntaxKind,
};

use crate::{
    eval::{self, Lit},
    jdwp::{
        self, reply_result, signature_to_type_name, tag, FieldInfo, Invoke, JdwpEvent, MethodInfo,
        Value, Vm,
    },
    session::{FrameRef, Session, VarRef},
    sources::{relative_source_path, FoundSource},
    variables::find_field,
};

/// 一次方法调用最多等这么久，超时后打断它
const INVOKE_TIMEOUT: Duration = Duration::from_secs(5);
/// 打断之后再等多久
const ABORT_TIMEOUT: Duration = Duration::from_secs(3);

pub(crate) const OBJECT: &str = "Ljava/lang/Object;";
pub(crate) const STRING: &str = "Ljava/lang/String;";
const CLASS: &str = "Ljava/lang/Class;";

/// 求值的中间结果。
#[derive(Debug, Clone)]
pub(crate) enum Val {
    /// 目标 JVM 里的值，带静态类型的签名（知道时）
    Jdwp(Value, Option<String>),
    /// 求值过程中得到、还没放进目标 JVM 的字符串（字面量、字符串连接的结果）
    Str(String),
    /// 类型名：静态成员的接收者
    Type { class: u64, signature: String },
    /// 还没认出来的限定名前缀（可能是包名）
    Package(String),
}

fn null() -> Value {
    Value::Object {
        tag: tag::OBJECT,
        id: 0,
    }
}

/// 一次求值的上下文。
pub(crate) struct Cx {
    pub vm: Rc<Vm>,
    pub frame: FrameRef,
    /// 能不能调用方法、新建对象。悬停求值不能：鼠标划过不该改变程序状态
    pub allow_invoke: bool,
    imports: Option<Rc<Imports>>,
}

impl Cx {
    pub fn new(vm: Rc<Vm>, frame: FrameRef, allow_invoke: bool) -> Cx {
        Cx {
            vm,
            frame,
            allow_invoke,
            imports: None,
        }
    }
}

/// 当前栈帧所在源文件的 import。
#[derive(Default)]
pub(crate) struct Imports {
    pub single: Vec<String>,
    pub on_demand: Vec<String>,
    pub static_single: Vec<(String, String)>,
    pub static_on_demand: Vec<String>,
}

/// 实参的类型，选重载用。
#[derive(Debug, Clone)]
enum ArgType {
    Primitive(u8),
    Null,
    Ref { class: u64, signature: String },
}

impl ArgType {
    fn describe(&self) -> String {
        match self {
            ArgType::Primitive(tag) => signature_to_type_name(&(*tag as char).to_string()),
            ArgType::Null => "null".to_owned(),
            ArgType::Ref { signature, .. } => signature_to_type_name(signature),
        }
    }
}

fn is_primitive_signature(signature: &str) -> bool {
    signature.len() == 1 && signature != "V"
}

fn operand(expr: Option<ast::Expr>) -> anyhow::Result<ast::Expr> {
    expr.context(incomplete())
}

/// 语法树缺了一部分（表达式没写完）。
fn incomplete() -> &'static str {
    trs!("表达式不完整", "The expression is incomplete")
}

fn unknown_name(name: &str) -> String {
    tr!("找不到名字 `{name}`", "Cannot find name `{name}`")
}

fn type_not_value(signature: &str) -> String {
    tr!(
        "`{}` 是类型，不是值",
        "`{}` is a type, not a value",
        signature_to_type_name(signature)
    )
}

fn no_field_value() -> &'static str {
    trs!("JVM 没有返回字段值", "The JVM returned no field value")
}

/// 字段的值：静态字段读 `declaring` 类，实例字段读 `object`。
fn field_value(vm: &Vm, declaring: u64, field: FieldInfo, object: u64) -> anyhow::Result<Val> {
    let values = if field.is_static() {
        vm.static_values(declaring, &[field.id])?
    } else {
        vm.object_values(object, &[field.id])?
    };
    let value = *values.first().context(no_field_value())?;
    Ok(Val::Jdwp(value, Some(field.signature)))
}

fn null_pointer(expr: impl std::fmt::Display) -> String {
    tr!(
        "java.lang.NullPointerException: `{expr}` 是 null",
        "java.lang.NullPointerException: `{expr}` is null"
    )
}

/// 方法调用的接收者。
enum Target {
    /// 静态方法（类型名、静态上下文）
    Static,
    /// 实例方法：对象；`nonvirtual` 时不按运行时类型分派
    Object { id: u64, nonvirtual: bool },
}

impl Session {
    /// 解析并求值。结果不会是类型名或包名。
    pub(crate) fn eval_text(&mut self, cx: &mut Cx, text: &str) -> anyhow::Result<Val> {
        let expr = eval::parse(text).map_err(anyhow::Error::msg)?;
        match self.eval(cx, &expr)? {
            Val::Type { signature, .. } => {
                bail!(type_not_value(&signature))
            }
            Val::Package(name) => bail!(unknown_name(&name)),
            val => Ok(val),
        }
    }

    /// 把结果放进目标 JVM（字符串要先创建）。
    pub(crate) fn materialize(
        &mut self,
        cx: &Cx,
        val: Val,
    ) -> anyhow::Result<(Value, Option<String>)> {
        match val {
            Val::Jdwp(value, signature) => Ok((value, signature)),
            Val::Str(text) => Ok((self.new_string(cx, &text)?, Some(STRING.to_owned()))),
            Val::Type { signature, .. } => {
                bail!(type_not_value(&signature))
            }
            Val::Package(name) => bail!(unknown_name(&name)),
        }
    }

    /// 求值并转换成要赋给 `signature` 类型变量的值：基本类型只做拓宽，引用类型按需装箱。
    pub(crate) fn eval_for_assignment(
        &mut self,
        cx: &mut Cx,
        text: &str,
        signature: &str,
    ) -> anyhow::Result<Value> {
        let val = self.eval_text(cx, text)?;
        if is_primitive_signature(signature) {
            let to = signature.as_bytes()[0];
            let fits = self
                .primitive(cx, &val)?
                .and_then(|value| eval::primitive_tag(&value))
                .is_some_and(|from| from == to || eval::widens_to(from, to));
            anyhow::ensure!(
                fits,
                tr!(
                    "`{text}` 不是 {} 类型的值",
                    "`{text}` is not a value of type {}",
                    signature_to_type_name(signature)
                )
            );
        }
        self.convert_arg(cx, val, signature)
    }

    pub(crate) fn truthy(&mut self, cx: &Cx, val: &Val) -> anyhow::Result<bool> {
        match self.primitive(cx, val)? {
            Some(Value::Boolean(b)) => Ok(b),
            _ => bail!(trs!("结果不是 boolean", "The result is not a boolean")),
        }
    }

    pub(crate) fn eval(&mut self, cx: &mut Cx, expr: &ast::Expr) -> anyhow::Result<Val> {
        use ast::Expr as E;
        match expr {
            E::Literal(literal) => {
                let token = literal
                    .token()
                    .context(trs!("字面量不完整", "The literal is incomplete"))?;
                Ok(match eval::literal(&token).map_err(anyhow::Error::msg)? {
                    Lit::Value(value) => Val::Jdwp(value, None),
                    Lit::Str(text) => Val::Str(text),
                    Lit::Null => Val::Jdwp(null(), None),
                })
            }
            E::ParenExpr(paren) => self.eval(cx, &operand(paren.expr())?),
            E::NameExpr(name) => {
                let name = name.name_ref().context(incomplete())?.text();
                self.eval_name(cx, &name)
            }
            E::ThisExpr(this) => self.eval_this(cx, this.qualifier()),
            E::FieldAccess(access) => self.eval_field_access(cx, access),
            E::MethodCall(call) => self.eval_call(cx, call),
            E::NewExpr(new) => self.eval_new(cx, new),
            E::ArrayCreationExpr(creation) => self.eval_new_array(cx, creation),
            E::ArrayAccess(access) => self.eval_array_access(cx, access),
            E::UnaryExpr(unary) => {
                let op = unary.op_token().map(|t| t.kind()).context(incomplete())?;
                if matches!(op, SyntaxKind::PLUS_PLUS | SyntaxKind::MINUS_MINUS) {
                    bail!(trs!(
                        "不支持自增自减",
                        "Increment and decrement are not supported"
                    ));
                }
                let value = self.eval(cx, &operand(unary.operand())?)?;
                let value = self.primitive(cx, &value)?.with_context(|| {
                    tr!(
                        "运算符 `{}` 只能用在基本类型上",
                        "Operator `{}` can only be applied to primitive types",
                        eval::op_text(op)
                    )
                })?;
                Ok(Val::Jdwp(
                    eval::unary(op, value).map_err(anyhow::Error::msg)?,
                    None,
                ))
            }
            E::BinaryExpr(binary) => self.eval_binary(cx, binary),
            E::ConditionalExpr(conditional) => {
                let condition = self.eval(cx, &operand(conditional.condition())?)?;
                if self.truthy(cx, &condition)? {
                    self.eval(cx, &operand(conditional.then_expr())?)
                } else {
                    self.eval(cx, &operand(conditional.else_expr())?)
                }
            }
            E::InstanceofExpr(instanceof) => self.eval_instanceof(cx, instanceof),
            E::CastExpr(cast) => self.eval_cast(cx, cast),
            E::ClassLiteral(literal) => self.eval_class_literal(cx, literal),
            E::PostfixExpr(_) => bail!(trs!(
                "不支持自增自减",
                "Increment and decrement are not supported"
            )),
            E::AssignExpr(_) => bail!(trs!(
                "不支持赋值（修改变量请在变量视图里改）",
                "Assignment is not supported (change variables in the Variables view)"
            )),
            E::LambdaExpr(_) | E::MethodRef(_) => bail!(trs!(
                "不支持 lambda 和方法引用",
                "Lambdas and method references are not supported"
            )),
            E::SwitchExpr(_) => bail!(trs!(
                "不支持 switch 表达式",
                "Switch expressions are not supported"
            )),
            other => bail!(tr!(
                "不支持的表达式 `{}`",
                "Unsupported expression `{}`",
                other.syntax().text()
            )),
        }
    }

    // ---------------------------------------------------------------
    // 名字、字段、数组
    // ---------------------------------------------------------------

    /// 名字依次在局部变量、`this` 和外层实例的字段、当前类的静态字段里找，然后当作类型名。
    fn eval_name(&mut self, cx: &mut Cx, name: &str) -> anyhow::Result<Val> {
        let vm = cx.vm.clone();
        let frame = cx.frame;
        if let Some(vars) = self.visible_locals(&vm, &frame)? {
            if let Some(var) = vars.iter().rev().find(|v| v.name == name) {
                let values = vm.frame_values(
                    frame.thread,
                    frame.frame,
                    &[(var.slot, var.signature.as_bytes()[0])],
                )?;
                let value = *values.first().context(trs!(
                    "JVM 没有返回变量值",
                    "The JVM returned no variable value"
                ))?;
                return Ok(Val::Jdwp(value, Some(var.signature.clone())));
            }
        }
        let this = vm.this_object(frame.thread, frame.frame)?;
        let mut objects = Vec::new();
        if let Some(this) = this.object_id() {
            objects.push(this);
            objects.extend(outer_instances(&vm, this));
        }
        let lexical = enclosing_classes(&vm, frame.location.class);
        // 先按词法作用域找：从包着当前代码的那个类开始，字段不按运行时类型分派
        for &object in &objects {
            let chain = vm.class_chain(vm.object_type(object)?)?;
            if let Some(&class) = lexical.iter().find(|c| chain.contains(c)) {
                if let Some((declaring, field)) = find_field(&vm, class, name)? {
                    return field_value(&vm, declaring, field, object);
                }
            }
        }
        for &class in &lexical {
            if let Some((declaring, field)) = find_field(&vm, class, name)? {
                if field.is_static() {
                    return field_value(&vm, declaring, field, 0);
                }
            }
        }
        // 词法上都找不到，才退回对象的运行时类型：子类才有的字段在监视里仍然读得到
        for &object in &objects {
            if let Some((declaring, field)) = find_field(&vm, vm.object_type(object)?, name)? {
                return field_value(&vm, declaring, field, object);
            }
        }
        match self.resolve_simple_type(cx, name)? {
            Some((class, signature)) => Ok(Val::Type { class, signature }),
            None => Ok(Val::Package(name.to_owned())),
        }
    }

    /// `this` 或 `Outer.this`。
    fn eval_this(&mut self, cx: &mut Cx, qualifier: Option<ast::Expr>) -> anyhow::Result<Val> {
        let vm = cx.vm.clone();
        let this = vm.this_object(cx.frame.thread, cx.frame.frame)?;
        let this = this.object_id().context(trs!(
            "静态方法里没有 this",
            "There is no `this` in a static method"
        ))?;
        let Some(qualifier) = qualifier else {
            // `this` 的静态类型是当前方法所在的类，不是对象的运行时类型
            return Ok(Val::Jdwp(
                Value::Object {
                    tag: tag::OBJECT,
                    id: this,
                },
                Some(vm.class_signature(cx.frame.location.class)?),
            ));
        };
        let Val::Type { signature, .. } = self.eval(cx, &qualifier)? else {
            bail!(tr!(
                "`{}.this` 里的限定符不是类型",
                "The qualifier of `{}.this` is not a type",
                qualifier.syntax().text()
            ));
        };
        let mut objects = vec![this];
        objects.extend(outer_instances(&vm, this));
        for object in objects {
            let class = vm.object_type(object)?;
            if vm.class_signature(class)? == signature {
                return Ok(Val::Jdwp(
                    Value::Object {
                        tag: tag::OBJECT,
                        id: object,
                    },
                    Some(signature),
                ));
            }
        }
        bail!(tr!(
            "找不到外层实例 `{}.this`",
            "Cannot find the enclosing instance `{}.this`",
            signature_to_type_name(&signature)
        ))
    }

    /// 表达式的静态类型（签名）对应的类。同名的类可以由不同的 ClassLoader 各载入一份，只按签名
    /// 找会选错：对象不是 null 时从对象自己的类层次（含接口）里找；是 null 时只在这个类已经载入、
    /// 同名的类又只有一份时才认。
    fn declared_class(
        &mut self,
        cx: &mut Cx,
        object: u64,
        signature: &str,
    ) -> anyhow::Result<Option<u64>> {
        let vm = cx.vm.clone();
        if object != 0 {
            let mut types = vm.class_chain(vm.object_type(object)?)?;
            let mut i = 0;
            while i < types.len() {
                if vm.class_signature(types[i])? == signature {
                    return Ok(Some(types[i]));
                }
                for &interface in vm.interfaces(types[i])?.iter() {
                    if !types.contains(&interface) {
                        types.push(interface);
                    }
                }
                i += 1;
            }
        }
        // 接收者是 null：只能按签名找。没载入过（不为了读字段去载入、初始化它，Java 里 `f.x` 不会）
        // 或者同名的类不止一份时认不出是哪一份，不猜（按报错处理）
        match vm.classes_by_signature(signature)?.as_slice() {
            [(_, class, _)] => Ok(Some(*class)),
            _ => Ok(None),
        }
    }

    fn eval_field_access(&mut self, cx: &mut Cx, access: &ast::FieldAccess) -> anyhow::Result<Val> {
        let name = access.name_ref().context(incomplete())?.text();
        let receiver_expr = operand(access.receiver())?;
        let receiver = self.eval(cx, &receiver_expr)?;
        let vm = cx.vm.clone();
        match receiver {
            Val::Package(prefix) => {
                let qualified = format!("{prefix}.{name}");
                Ok(match self.class_by_name(cx, &qualified)? {
                    Some((class, signature)) => Val::Type { class, signature },
                    None => Val::Package(qualified),
                })
            }
            Val::Type { class, signature } => {
                if let Some((declaring, field)) = find_field(&vm, class, &name)? {
                    anyhow::ensure!(
                        field.is_static(),
                        tr!("`{name}` 不是静态字段", "`{name}` is not a static field")
                    );
                    return field_value(&vm, declaring, field, 0);
                }
                let nested = format!("{}${name}", signature_to_type_name(&signature));
                match self.class_by_name(cx, &nested)? {
                    Some((class, signature)) => Ok(Val::Type { class, signature }),
                    None => bail!(tr!(
                        "类型 `{}` 没有静态字段 `{name}`",
                        "Type `{}` has no static field `{name}`",
                        signature_to_type_name(&signature)
                    )),
                }
            }
            Val::Str(_) => bail!(tr!(
                "String 没有可访问的字段 `{name}`",
                "String has no accessible field `{name}`"
            )),
            Val::Jdwp(value, declared) => {
                let Value::Object { id, .. } = value else {
                    bail!(tr!(
                        "`{}` 是基本类型，没有字段 `{name}`",
                        "`{}` is a primitive and has no field `{name}`",
                        receiver_expr.syntax().text()
                    ));
                };
                if id != 0
                    && name == "length"
                    && vm.class_signature(vm.object_type(id)?)?.starts_with('[')
                {
                    return Ok(Val::Jdwp(
                        Value::Int(vm.array_length(id)?),
                        Some("I".to_owned()),
                    ));
                }
                // 字段不按运行时类型分派：先在表达式的静态类型里找，找不到才退回运行时类型
                let mut found = None;
                if let Some(signature) = declared.as_deref().filter(|s| s.starts_with('L')) {
                    if let Some(class) = self.declared_class(cx, id, signature)? {
                        found = find_field(&vm, class, &name)?;
                    }
                }
                if found.is_none() && id != 0 {
                    found = find_field(&vm, vm.object_type(id)?, &name)?;
                }
                let Some((declaring, field)) = found else {
                    if id == 0 {
                        bail!(null_pointer(receiver_expr.syntax().text()));
                    }
                    bail!(tr!(
                        "`{}` 没有字段 `{name}`",
                        "`{}` has no field `{name}`",
                        receiver_expr.syntax().text()
                    ));
                };
                // 静态字段不读接收者，接收者是 null 也合法
                if id == 0 && !field.is_static() {
                    bail!(null_pointer(receiver_expr.syntax().text()));
                }
                field_value(&vm, declaring, field, id)
            }
        }
    }

    fn eval_array_access(&mut self, cx: &mut Cx, access: &ast::ArrayAccess) -> anyhow::Result<Val> {
        let array_expr = operand(access.array())?;
        let array = self.eval(cx, &array_expr)?;
        let index = self.eval(cx, &operand(access.index())?)?;
        let index = match self.primitive(cx, &index)? {
            Some(v @ (Value::Byte(_) | Value::Short(_) | Value::Char(_) | Value::Int(_))) => {
                match eval::convert_primitive(v, b'I') {
                    Ok(Value::Int(i)) => i,
                    _ => bail!(trs!("数组下标不是 int", "The array index is not an int")),
                }
            }
            _ => bail!(trs!("数组下标不是 int", "The array index is not an int")),
        };
        let vm = cx.vm.clone();
        let (id, declared) = match array {
            Val::Jdwp(Value::Object { id: 0, .. }, _) => {
                bail!(null_pointer(array_expr.syntax().text()))
            }
            Val::Jdwp(Value::Object { id, .. }, signature) => (id, signature),
            _ => bail!(tr!(
                "`{}` 不是数组",
                "`{}` is not an array",
                array_expr.syntax().text()
            )),
        };
        let runtime = vm.class_signature(vm.object_type(id)?)?;
        anyhow::ensure!(
            runtime.starts_with('['),
            tr!(
                "`{}` 不是数组",
                "`{}` is not an array",
                array_expr.syntax().text()
            )
        );
        let len = vm.array_length(id)?;
        anyhow::ensure!(
            (0..len).contains(&index),
            "java.lang.ArrayIndexOutOfBoundsException: Index {index} out of bounds for length {len}"
        );
        let value = *vm.array_values(id, index, 1)?.first().context(trs!(
            "JVM 没有返回数组元素",
            "The JVM returned no array element"
        ))?;
        let element = declared
            .as_deref()
            .and_then(|s| s.strip_prefix('['))
            .unwrap_or(&runtime[1..])
            .to_owned();
        Ok(Val::Jdwp(value, Some(element)))
    }

    fn eval_class_literal(
        &mut self,
        cx: &mut Cx,
        literal: &ast::ClassLiteral,
    ) -> anyhow::Result<Val> {
        let signature = match (literal.ty(), literal.expr()) {
            (Some(ty), _) => self.resolve_type(cx, &ty)?,
            (None, Some(expr)) => match self.eval(cx, &expr)? {
                Val::Type { signature, .. } => signature,
                _ => bail!(tr!(
                    "`{}` 不是类型",
                    "`{}` is not a type",
                    expr.syntax().text()
                )),
            },
            (None, None) => bail!(incomplete()),
        };
        let id = self.class_object_of(cx, &signature)?;
        Ok(Val::Jdwp(
            Value::Object {
                tag: tag::CLASS_OBJECT,
                id,
            },
            Some(CLASS.to_owned()),
        ))
    }

    /// 签名对应的 `java.lang.Class` 对象；基本类型取包装类的 `TYPE` 字段。
    fn class_object_of(&mut self, cx: &mut Cx, signature: &str) -> anyhow::Result<u64> {
        let vm = cx.vm.clone();
        if is_primitive_signature(signature) || signature == "V" {
            let box_signature = if signature == "V" {
                "Ljava/lang/Void;"
            } else {
                eval::box_signature(signature.as_bytes()[0])
                    .context(trs!("未知的基本类型", "Unknown primitive type"))?
            };
            let class = self.class_by_signature(cx, box_signature)?.context(trs!(
                "包装类型还没有加载",
                "The wrapper class is not loaded yet"
            ))?;
            let (declaring, field) = find_field(&vm, class, "TYPE")?.context(trs!(
                "包装类型没有 TYPE 字段",
                "The wrapper class has no TYPE field"
            ))?;
            let value = *vm
                .static_values(declaring, &[field.id])?
                .first()
                .context(no_field_value())?;
            return value
                .object_id()
                .context(trs!("TYPE 字段是 null", "The TYPE field is null"));
        }
        let class = self.class_by_signature(cx, signature)?.with_context(|| {
            tr!(
                "类型 `{}` 还没有加载",
                "Type `{}` is not loaded yet",
                signature_to_type_name(signature)
            )
        })?;
        vm.class_object(class)
    }

    // ---------------------------------------------------------------
    // 运算符
    // ---------------------------------------------------------------

    /// 基本类型的值；包装类型拆箱；别的返回 `None`。
    fn primitive(&mut self, cx: &Cx, val: &Val) -> anyhow::Result<Option<Value>> {
        match val {
            Val::Jdwp(value, _) if eval::primitive_tag(value).is_some() => Ok(Some(*value)),
            Val::Jdwp(Value::Object { id, .. }, _) if *id != 0 => unbox(&cx.vm, *id),
            _ => Ok(None),
        }
    }

    fn is_string(&self, val: &Val) -> bool {
        match val {
            Val::Str(_) => true,
            Val::Jdwp(Value::Object { tag: t, id }, signature) => {
                *t == tag::STRING || (*id == 0 && signature.as_deref() == Some(STRING))
            }
            _ => false,
        }
    }

    fn eval_binary(&mut self, cx: &mut Cx, binary: &ast::BinaryExpr) -> anyhow::Result<Val> {
        let op = binary.op_kind().context(incomplete())?;
        let lhs = operand(binary.lhs())?;
        let rhs = operand(binary.rhs())?;
        if matches!(op, SyntaxKind::AMP_AMP | SyntaxKind::PIPE_PIPE) {
            let left = self.eval(cx, &lhs)?;
            let left = self.truthy(cx, &left)?;
            let result = if (op == SyntaxKind::AMP_AMP) == left {
                let right = self.eval(cx, &rhs)?;
                self.truthy(cx, &right)?
            } else {
                left
            };
            return Ok(Val::Jdwp(Value::Boolean(result), None));
        }
        let left = self.eval(cx, &lhs)?;
        let right = self.eval(cx, &rhs)?;
        if op == SyntaxKind::PLUS && (self.is_string(&left) || self.is_string(&right)) {
            let text = self.string_of(cx, &left)? + &self.string_of(cx, &right)?;
            return Ok(Val::Str(text));
        }
        if matches!(op, SyntaxKind::EQ_EQ | SyntaxKind::NEQ) {
            if let Some(equal) = self.reference_equality(cx, &left, &right)? {
                return Ok(Val::Jdwp(
                    Value::Boolean(equal == (op == SyntaxKind::EQ_EQ)),
                    None,
                ));
            }
        }
        let bad = || {
            anyhow::anyhow!(tr!(
                "运算符 `{}` 不能用在 `{}` 和 `{}` 上",
                "Operator `{}` cannot be applied to `{}` and `{}`",
                eval::op_text(op),
                lhs.syntax().text(),
                rhs.syntax().text()
            ))
        };
        let left = self.primitive(cx, &left)?.ok_or_else(bad)?;
        let right = self.primitive(cx, &right)?.ok_or_else(bad)?;
        Ok(Val::Jdwp(
            eval::binary(op, left, right).map_err(anyhow::Error::msg)?,
            None,
        ))
    }

    /// `==` / `!=` 两边不都是数值时：字符串比较内容，别的比较引用。两边有一个是基本类型时返回 `None`
    /// （按数值比较，包装类型拆箱）。
    fn reference_equality(
        &mut self,
        cx: &mut Cx,
        left: &Val,
        right: &Val,
    ) -> anyhow::Result<Option<bool>> {
        let is_primitive =
            |val: &Val| matches!(val, Val::Jdwp(value, _) if eval::primitive_tag(value).is_some());
        if is_primitive(left) || is_primitive(right) {
            return Ok(None);
        }
        let is_null = |val: &Val| matches!(val, Val::Jdwp(value, _) if value.is_null());
        if is_null(left) || is_null(right) {
            return Ok(Some(is_null(left) && is_null(right)));
        }
        if self.is_string(left) && self.is_string(right) {
            let a = self.string_of(cx, left)?;
            let b = self.string_of(cx, right)?;
            return Ok(Some(a == b));
        }
        match (left, right) {
            (Val::Jdwp(a, _), Val::Jdwp(b, _)) => Ok(Some(a.object_id() == b.object_id())),
            _ => Ok(Some(false)),
        }
    }

    /// `String.valueOf(x)`：对象调用 `toString()`（悬停求值时不调用，显示摘要）。
    fn string_of(&mut self, cx: &mut Cx, val: &Val) -> anyhow::Result<String> {
        let vm = cx.vm.clone();
        match val {
            Val::Str(text) => Ok(text.clone()),
            Val::Jdwp(value, _) if eval::primitive_tag(value).is_some() => {
                Ok(eval::primitive_to_string(value))
            }
            Val::Jdwp(Value::Object { id: 0, .. }, _) => Ok("null".to_owned()),
            Val::Jdwp(
                Value::Object {
                    tag: tag::STRING,
                    id,
                },
                _,
            ) => vm.string_value(*id),
            Val::Jdwp(value @ Value::Object { id, .. }, signature) => {
                if !cx.allow_invoke {
                    return Ok(self.describe_value(&vm, value, signature.as_deref()));
                }
                let class = vm.object_type(*id)?;
                let methods = self.methods_named(&vm, class, "toString")?;
                let (declaring, method) = methods
                    .into_iter()
                    .find(|(_, m)| m.signature == "()Ljava/lang/String;" && !m.is_static())
                    .context(trs!("找不到 toString()", "Cannot find toString()"))?;
                let result = self.invoke(
                    cx,
                    Invoke::Instance {
                        object: *id,
                        class: declaring,
                        thread: cx.frame.thread,
                        method: method.id,
                        args: Vec::new(),
                        nonvirtual: false,
                    },
                )?;
                match result.object_id() {
                    Some(text) => vm.string_value(text),
                    None => Ok("null".to_owned()),
                }
            }
            Val::Jdwp(..) => bail!(trs!(
                "void 方法没有返回值",
                "A void method has no return value"
            )),
            Val::Type { signature, .. } => {
                bail!(type_not_value(signature))
            }
            Val::Package(name) => bail!(unknown_name(name)),
        }
    }

    fn eval_instanceof(
        &mut self,
        cx: &mut Cx,
        instanceof: &ast::InstanceofExpr,
    ) -> anyhow::Result<Val> {
        let value = self.eval(cx, &operand(instanceof.expr())?)?;
        let ty = match (instanceof.ty(), instanceof.pattern()) {
            (Some(ty), _) => ty,
            (None, Some(ast::Pattern::TypePattern(pattern))) => {
                pattern.ty().context(incomplete())?
            }
            _ => bail!(trs!("不支持记录模式", "Record patterns are not supported")),
        };
        let signature = self.resolve_type(cx, &ty)?;
        let vm = cx.vm.clone();
        let result = match value {
            Val::Str(_) => self.signature_is_subtype(cx, STRING, &signature)?,
            Val::Jdwp(Value::Object { id: 0, .. }, _) => false,
            Val::Jdwp(Value::Object { id, .. }, _) => {
                let class = vm.object_type(id)?;
                let runtime = vm.class_signature(class)?;
                is_subtype(&vm, class, &runtime, &signature)?
            }
            _ => bail!(trs!(
                "instanceof 的左边不是对象",
                "The left side of instanceof is not an object"
            )),
        };
        Ok(Val::Jdwp(Value::Boolean(result), None))
    }

    fn eval_cast(&mut self, cx: &mut Cx, cast: &ast::CastExpr) -> anyhow::Result<Val> {
        let ty = cast.ty().context(incomplete())?;
        let signature = self.resolve_type(cx, &ty)?;
        let value = self.eval(cx, &operand(cast.expr())?)?;
        if is_primitive_signature(&signature) {
            let primitive = self.primitive(cx, &value)?.with_context(|| {
                tr!(
                    "不能转换成 {}",
                    "Cannot be converted to {}",
                    signature_to_type_name(&signature)
                )
            })?;
            let converted = eval::convert_primitive(primitive, signature.as_bytes()[0])
                .map_err(anyhow::Error::msg)?;
            return Ok(Val::Jdwp(converted, Some(signature)));
        }
        let vm = cx.vm.clone();
        match value {
            Val::Str(text) => {
                anyhow::ensure!(
                    self.signature_is_subtype(cx, STRING, &signature)?,
                    tr!(
                        "java.lang.ClassCastException: String 不能转换成 {}",
                        "java.lang.ClassCastException: String cannot be cast to {}",
                        signature_to_type_name(&signature)
                    )
                );
                Ok(Val::Str(text))
            }
            Val::Jdwp(value, _) if eval::primitive_tag(&value).is_some() => {
                let boxed = self.box_value(cx, value)?;
                Ok(Val::Jdwp(boxed, Some(signature)))
            }
            Val::Jdwp(value @ Value::Object { id: 0, .. }, _) => {
                Ok(Val::Jdwp(value, Some(signature)))
            }
            Val::Jdwp(value @ Value::Object { id, .. }, _) => {
                let class = vm.object_type(id)?;
                let runtime = vm.class_signature(class)?;
                anyhow::ensure!(
                    is_subtype(&vm, class, &runtime, &signature)?,
                    tr!(
                        "java.lang.ClassCastException: {} 不能转换成 {}",
                        "java.lang.ClassCastException: {} cannot be cast to {}",
                        signature_to_type_name(&runtime),
                        signature_to_type_name(&signature)
                    )
                );
                Ok(Val::Jdwp(value, Some(signature)))
            }
            _ => bail!(tr!(
                "`{}` 不是值",
                "`{}` is not a value",
                cast.syntax().text()
            )),
        }
    }

    // ---------------------------------------------------------------
    // 类型
    // ---------------------------------------------------------------

    /// 语法里的类型 → 签名。
    pub(crate) fn resolve_type(&mut self, cx: &mut Cx, ty: &ast::Type) -> anyhow::Result<String> {
        match ty {
            ast::Type::PrimitiveType(primitive) => {
                let keyword = primitive.keyword().context(incomplete())?;
                Ok(eval::type_name_to_signature(keyword.text()))
            }
            ast::Type::ArrayType(array) => {
                let element = array.element().context(incomplete())?;
                Ok(format!("[{}", self.resolve_type(cx, &element)?))
            }
            ast::Type::ClassType(class) => {
                let segments: Vec<String> =
                    class.segments().iter().map(|s| s.to_string()).collect();
                let (first, rest) = segments.split_first().context(incomplete())?;
                let found = match self.resolve_simple_type(cx, first)? {
                    Some((_, signature)) if rest.is_empty() => Some(signature),
                    Some((_, signature)) => {
                        let nested =
                            format!("{}${}", signature_to_type_name(&signature), rest.join("$"));
                        self.class_by_name(cx, &nested)?.map(|(_, s)| s)
                    }
                    None => self.class_by_name(cx, &segments.join("."))?.map(|(_, s)| s),
                };
                found.with_context(|| {
                    tr!(
                        "找不到类型 `{}`",
                        "Cannot find type `{}`",
                        segments.join(".")
                    )
                })
            }
            other => bail!(tr!(
                "不支持的类型 `{}`",
                "Unsupported type `{}`",
                other.syntax().text()
            )),
        }
    }

    /// 简单类型名：当前类和外层类（及它们的成员类）、单类型 import、同一个包、按需 import、
    /// `java.lang`；都没有加载时让目标 JVM 按这个顺序加载，最后在已加载的类里按简单名找。
    fn resolve_simple_type(
        &mut self,
        cx: &mut Cx,
        name: &str,
    ) -> anyhow::Result<Option<(u64, String)>> {
        let vm = cx.vm.clone();
        let current = vm.class_name(cx.frame.location.class)?;
        let (package, binary) = match current.rfind('.') {
            Some(i) => (&current[..i], &current[i + 1..]),
            None => ("", current.as_str()),
        };
        let qualify = |simple: &str| {
            if package.is_empty() {
                simple.to_owned()
            } else {
                format!("{package}.{simple}")
            }
        };
        let mut candidates: Vec<String> = Vec::new();
        let mut nest = binary;
        loop {
            if nest.rsplit('$').next() == Some(name) {
                candidates.push(qualify(nest));
            }
            candidates.push(qualify(&format!("{nest}${name}")));
            match nest.rfind('$') {
                Some(i) => nest = &nest[..i],
                None => break,
            }
        }
        let imports = self.imports(cx);
        candidates.extend(
            imports
                .single
                .iter()
                .filter(|single| single.rsplit('.').next() == Some(name))
                .cloned(),
        );
        candidates.push(qualify(name));
        candidates.extend(imports.on_demand.iter().map(|p| format!("{p}.{name}")));
        candidates.push(format!("java.lang.{name}"));

        for candidate in &candidates {
            if let Some(found) = self.loaded_class_by_name(&vm, candidate)? {
                return Ok(Some(found));
            }
        }
        // 只在像类名（首字母大写）时才让 JVM 加载，免得把包名逐个试一遍
        if cx.allow_invoke && name.starts_with(char::is_uppercase) {
            for candidate in &candidates {
                if let Some(found) = self.load_class(cx, candidate)? {
                    return Ok(Some(found));
                }
            }
        }
        // 最后在所有已加载的类里按简单名找（要列出全部类，只对像类名的名字做）
        if !name.starts_with(char::is_uppercase) {
            return Ok(None);
        }
        let suffixes = [format!("/{name};"), format!("${name};")];
        let found = vm
            .all_classes()?
            .into_iter()
            .find(|(_, signature, status)| {
                status & jdwp::CLASS_STATUS_PREPARED != 0
                    && (suffixes.iter().any(|s| signature.ends_with(s.as_str()))
                        || *signature == format!("L{name};"))
            });
        Ok(found.map(|(id, signature, _)| (id, signature)))
    }

    /// 限定名（成员类可以用 `.` 也可以用 `$` 分隔）对应的类，没有加载时让 JVM 加载。
    pub(crate) fn class_by_name(
        &mut self,
        cx: &mut Cx,
        name: &str,
    ) -> anyhow::Result<Option<(u64, String)>> {
        let vm = cx.vm.clone();
        if let Some(found) = self.loaded_class_by_name(&vm, name)? {
            return Ok(Some(found));
        }
        let last = name.rsplit(['.', '$']).next().unwrap_or(name);
        if cx.allow_invoke && last.starts_with(char::is_uppercase) {
            return self.load_class(cx, name);
        }
        Ok(None)
    }

    /// 已加载的类：限定名里的点从右往左依次当作成员类的 `$` 试。
    fn loaded_class_by_name(&self, vm: &Vm, name: &str) -> anyhow::Result<Option<(u64, String)>> {
        for binary in binary_name_variants(name) {
            let signature = format!("L{};", binary.replace('.', "/"));
            if let Some(class) = loaded_class(vm, &signature)? {
                return Ok(Some((class, signature)));
            }
        }
        Ok(None)
    }

    /// 用当前类的类加载器 `Class.forName` 加载。
    fn load_class(&mut self, cx: &mut Cx, name: &str) -> anyhow::Result<Option<(u64, String)>> {
        self.ensure_abort_exception(cx);
        let vm = cx.vm.clone();
        let Some(class_class) = loaded_class(&vm, CLASS)? else {
            return Ok(None);
        };
        let Some(for_name) = vm
            .methods(class_class)?
            .iter()
            .find(|m| {
                m.name == "forName"
                    && m.signature
                        == "(Ljava/lang/String;ZLjava/lang/ClassLoader;)Ljava/lang/Class;"
            })
            .cloned()
        else {
            return Ok(None);
        };
        let loader = vm.class_loader(cx.frame.location.class)?;
        for binary in binary_name_variants(name) {
            let text = self.new_string(cx, &binary)?;
            let result = self.raw_invoke(
                cx,
                &Invoke::Static {
                    class: class_class,
                    interface: false,
                    thread: cx.frame.thread,
                    method: for_name.id,
                    args: vec![
                        text,
                        Value::Boolean(true),
                        Value::Object {
                            tag: tag::CLASS_LOADER,
                            id: loader,
                        },
                    ],
                },
            )?;
            if let (Value::Object { id, .. }, 0) = result {
                if id != 0 {
                    let class = vm.reflected_type(id)?;
                    let signature = vm.class_signature(class)?;
                    return Ok(Some((class, signature)));
                }
            }
        }
        Ok(None)
    }

    /// 签名对应的已加载类；数组和包装类型这类签名直接查，类名不需要解析。
    fn class_by_signature(&mut self, cx: &mut Cx, signature: &str) -> anyhow::Result<Option<u64>> {
        if let Some(class) = loaded_class(&cx.vm, signature)? {
            return Ok(Some(class));
        }
        if let Some(name) = signature
            .strip_prefix('L')
            .and_then(|s| s.strip_suffix(';'))
        {
            let name = name.replace('/', ".");
            return Ok(self.class_by_name(cx, &name)?.map(|(class, _)| class));
        }
        Ok(None)
    }

    fn signature_is_subtype(
        &mut self,
        cx: &mut Cx,
        signature: &str,
        target: &str,
    ) -> anyhow::Result<bool> {
        if signature == target || target == OBJECT {
            return Ok(true);
        }
        match self.class_by_signature(cx, signature)? {
            Some(class) => is_subtype(&cx.vm, class, signature, target),
            None => Ok(false),
        }
    }

    pub(crate) fn imports(&mut self, cx: &mut Cx) -> Rc<Imports> {
        if let Some(imports) = &cx.imports {
            return imports.clone();
        }
        let imports = Rc::new(
            self.read_imports(&cx.vm, cx.frame.location.class)
                .unwrap_or_default(),
        );
        cx.imports = Some(imports.clone());
        imports
    }

    fn read_imports(&mut self, vm: &Vm, class: u64) -> Option<Imports> {
        let class_name = vm.class_name(class).ok()?;
        let source_file = vm.source_file(class).ok().flatten();
        let relative = relative_source_path(&class_name, source_file.as_deref());
        let text = match self.sources.find(&relative)? {
            FoundSource::File(path) => crate::sources::read_lossy(&path)?,
            FoundSource::Archive { reference, .. } => {
                self.sources.read_reference(reference).ok()?
            }
        };
        let unit = ast::CompilationUnit::parse(&text).tree();
        let mut imports = Imports::default();
        for import in unit.imports() {
            if import.is_module() {
                continue;
            }
            let Some(name) = import.name() else { continue };
            let name = name
                .segments()
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(".");
            match (import.is_static(), import.is_on_demand()) {
                (false, false) => imports.single.push(name),
                (false, true) => imports.on_demand.push(name),
                (true, false) => {
                    if let Some((ty, member)) = name.rsplit_once('.') {
                        imports
                            .static_single
                            .push((ty.to_owned(), member.to_owned()));
                    }
                }
                (true, true) => imports.static_on_demand.push(name),
            }
        }
        Some(imports)
    }

    // ---------------------------------------------------------------
    // 方法调用和新建对象
    // ---------------------------------------------------------------

    fn eval_call(&mut self, cx: &mut Cx, call: &ast::MethodCall) -> anyhow::Result<Val> {
        let name = call.name_ref().context(incomplete())?.text().to_string();
        anyhow::ensure!(
            cx.allow_invoke,
            trs!("悬停时不调用方法", "Methods are not called while hovering")
        );
        let vm = cx.vm.clone();
        // 先求接收者，再求实参（和 Java 的求值顺序一致）
        let receiver = match call.receiver() {
            None => None,
            Some(ast::Expr::SuperExpr(_)) => {
                let this = vm.this_object(cx.frame.thread, cx.frame.frame)?;
                let this = this.object_id().context(trs!(
                    "静态方法里没有 super",
                    "There is no `super` in a static method"
                ))?;
                let superclass = vm.superclass(cx.frame.location.class)?.context(trs!(
                    "当前类没有父类",
                    "The current class has no superclass"
                ))?;
                Some((
                    Target::Object {
                        id: this,
                        nonvirtual: true,
                    },
                    superclass,
                ))
            }
            Some(expr) => {
                let receiver = self.eval(cx, &expr)?;
                Some(match receiver {
                    Val::Type { class, .. } => (Target::Static, class),
                    Val::Package(name) => {
                        bail!(unknown_name(&name))
                    }
                    Val::Str(text) => {
                        let value = self.new_string(cx, &text)?;
                        let id = value
                            .object_id()
                            .context(trs!("创建字符串失败", "Failed to create the string"))?;
                        (
                            Target::Object {
                                id,
                                nonvirtual: false,
                            },
                            vm.object_type(id)?,
                        )
                    }
                    Val::Jdwp(Value::Object { id: 0, .. }, _) => {
                        bail!(null_pointer(expr.syntax().text()))
                    }
                    Val::Jdwp(Value::Object { id, .. }, _) => (
                        Target::Object {
                            id,
                            nonvirtual: false,
                        },
                        vm.object_type(id)?,
                    ),
                    Val::Jdwp(..) => bail!(tr!(
                        "`{}` 是基本类型，没有方法",
                        "`{}` is a primitive and has no methods",
                        expr.syntax().text()
                    )),
                })
            }
        };
        let mut args = Vec::new();
        if let Some(list) = call.arg_list() {
            for arg in list.args() {
                args.push(self.eval(cx, &arg)?);
            }
        }

        let (target, candidates) = match receiver {
            Some((target, class)) => {
                let mut candidates = self.methods_named(&vm, class, &name)?;
                if matches!(target, Target::Static) {
                    candidates.retain(|(_, m)| m.is_static());
                }
                (target, candidates)
            }
            None => self.unqualified_candidates(cx, &name)?,
        };
        anyhow::ensure!(
            !candidates.is_empty(),
            tr!("找不到方法 `{name}`", "Cannot find method `{name}`")
        );
        self.call_method(cx, target, &name, &candidates, args)
    }

    /// 不带接收者的方法调用：`this`、外层实例、当前类和外层类的静态方法、静态 import。
    /// 找到同名方法的第一层就停（和 Java 的作用域规则一致）。
    fn unqualified_candidates(
        &mut self,
        cx: &mut Cx,
        name: &str,
    ) -> anyhow::Result<(Target, Vec<(u64, MethodInfo)>)> {
        let vm = cx.vm.clone();
        let this = vm.this_object(cx.frame.thread, cx.frame.frame)?;
        if let Some(this) = this.object_id() {
            let mut objects = vec![this];
            objects.extend(outer_instances(&vm, this));
            for object in objects {
                let candidates = self.methods_named(&vm, vm.object_type(object)?, name)?;
                if !candidates.is_empty() {
                    return Ok((
                        Target::Object {
                            id: object,
                            nonvirtual: false,
                        },
                        candidates,
                    ));
                }
            }
        }
        for class in enclosing_classes(&vm, cx.frame.location.class) {
            let mut candidates = self.methods_named(&vm, class, name)?;
            candidates.retain(|(_, m)| m.is_static());
            if !candidates.is_empty() {
                return Ok((Target::Static, candidates));
            }
        }
        let imports = self.imports(cx);
        let types: Vec<String> = imports
            .static_single
            .iter()
            .filter(|(_, member)| member == name)
            .map(|(ty, _)| ty.clone())
            .chain(imports.static_on_demand.iter().cloned())
            .collect();
        for ty in types {
            if let Some((class, _)) = self.class_by_name(cx, &ty)? {
                let mut candidates = self.methods_named(&vm, class, name)?;
                candidates.retain(|(_, m)| m.is_static());
                if !candidates.is_empty() {
                    return Ok((Target::Static, candidates));
                }
            }
        }
        bail!(tr!("找不到方法 `{name}`", "Cannot find method `{name}`"))
    }

    /// 类型（含父类和接口）里叫 `name` 的方法：`(声明它的类型, 方法)`，同一个签名只取最下层的。
    /// 接口的静态方法只在接口自己身上。数组按 `Object` 处理。
    pub(crate) fn methods_named(
        &self,
        vm: &Vm,
        class: u64,
        name: &str,
    ) -> anyhow::Result<Vec<(u64, MethodInfo)>> {
        let class = if vm.class_signature(class)?.starts_with('[') {
            loaded_class(vm, OBJECT)?.context(trs!(
                "找不到 java.lang.Object",
                "Cannot find java.lang.Object"
            ))?
        } else {
            class
        };
        let mut types = vm.class_chain(class)?;
        let mut seen: HashSet<u64> = types.iter().copied().collect();
        let mut i = 0;
        while i < types.len() {
            for &interface in vm.interfaces(types[i])?.iter() {
                if seen.insert(interface) {
                    types.push(interface);
                }
            }
            i += 1;
        }
        let mut signatures = HashSet::new();
        let mut out = Vec::new();
        for ty in types {
            for method in vm.methods(ty)?.iter() {
                if method.name != name {
                    continue;
                }
                if method.is_static() && ty != class && vm.is_interface(ty)? {
                    continue;
                }
                if signatures.insert(method.signature.clone()) {
                    out.push((ty, method.clone()));
                }
            }
        }
        Ok(out)
    }

    fn eval_new(&mut self, cx: &mut Cx, new: &ast::NewExpr) -> anyhow::Result<Val> {
        anyhow::ensure!(
            cx.allow_invoke,
            trs!("悬停时不新建对象", "Objects are not created while hovering")
        );
        anyhow::ensure!(
            new.body().is_none(),
            trs!("不支持匿名类", "Anonymous classes are not supported")
        );
        anyhow::ensure!(
            new.qualifier().is_none(),
            trs!(
                "不支持 `outer.new Inner()`",
                "`outer.new Inner()` is not supported"
            )
        );
        let ty = new.ty().context(incomplete())?;
        let signature = self.resolve_type(cx, &ty)?;
        let class = self.class_by_signature(cx, &signature)?.with_context(|| {
            tr!(
                "找不到类型 `{}`",
                "Cannot find type `{}`",
                signature_to_type_name(&signature)
            )
        })?;
        let vm = cx.vm.clone();
        anyhow::ensure!(
            !vm.is_interface(class)?,
            tr!(
                "`{}` 是接口，不能 new",
                "`{}` is an interface and cannot be instantiated",
                signature_to_type_name(&signature)
            )
        );
        let mut args = Vec::new();
        if let Some(list) = new.arg_list() {
            for arg in list.args() {
                args.push(self.eval(cx, &arg)?);
            }
        }
        let constructors: Vec<(u64, MethodInfo)> = vm
            .methods(class)?
            .iter()
            .filter(|m| m.name == "<init>")
            .map(|m| (class, m.clone()))
            .collect();
        let (method, values) =
            self.prepare_call(cx, &signature_to_type_name(&signature), &constructors, args)?;
        let value = self.invoke(
            cx,
            Invoke::New {
                class,
                thread: cx.frame.thread,
                method: method.id,
                args: values,
            },
        )?;
        Ok(Val::Jdwp(value, Some(signature)))
    }

    fn eval_new_array(
        &mut self,
        cx: &mut Cx,
        creation: &ast::ArrayCreationExpr,
    ) -> anyhow::Result<Val> {
        anyhow::ensure!(
            cx.allow_invoke,
            trs!("悬停时不新建数组", "Arrays are not created while hovering")
        );
        let element = creation.element_type().context(incomplete())?;
        let element = self.resolve_type(cx, &element)?;
        let sized: Vec<ast::DimExpr> = creation.dims().collect();
        let empty = creation
            .syntax()
            .children_with_tokens()
            .filter(|it| it.kind() == SyntaxKind::L_BRACK)
            .count();
        let signature = format!("{}{element}", "[".repeat(sized.len() + empty));
        let value = match creation.initializer() {
            Some(initializer) => self.array_from_initializer(cx, &signature, &initializer)?,
            None => {
                let mut lengths = Vec::new();
                for dim in sized {
                    let length = self.eval(cx, &operand(dim.expr())?)?;
                    let length = match self.primitive(cx, &length)? {
                        Some(v) => match eval::convert_primitive(v, b'I') {
                            Ok(Value::Int(n))
                                if !matches!(
                                    v,
                                    Value::Long(_)
                                        | Value::Float(_)
                                        | Value::Double(_)
                                        | Value::Boolean(_)
                                ) =>
                            {
                                n
                            }
                            _ => bail!(trs!("数组长度不是 int", "The array length is not an int")),
                        },
                        None => bail!(trs!("数组长度不是 int", "The array length is not an int")),
                    };
                    anyhow::ensure!(
                        length >= 0,
                        "java.lang.NegativeArraySizeException: {length}"
                    );
                    lengths.push(length);
                }
                self.array_with_lengths(cx, &signature, &lengths)?
            }
        };
        Ok(Val::Jdwp(value, Some(signature)))
    }

    fn array_from_initializer(
        &mut self,
        cx: &mut Cx,
        signature: &str,
        initializer: &ast::ArrayInitializer,
    ) -> anyhow::Result<Value> {
        let component = signature
            .strip_prefix('[')
            .context(trs!("不是数组类型", "Not an array type"))?
            .to_owned();
        let exprs: Vec<ast::Expr> = initializer.exprs().collect();
        let mut values = Vec::with_capacity(exprs.len());
        for expr in &exprs {
            let value = match expr {
                ast::Expr::ArrayInitializer(inner) if component.starts_with('[') => {
                    self.array_from_initializer(cx, &component, inner)?
                }
                other => {
                    let val = self.eval(cx, other)?;
                    self.convert_arg(cx, val, &component)?
                }
            };
            values.push(value);
        }
        let array = self.new_array(cx, signature, values.len() as i32)?;
        if let (Some(id), false) = (array.object_id(), values.is_empty()) {
            cx.vm.set_array_values(id, 0, &values)?;
        }
        Ok(array)
    }

    fn array_with_lengths(
        &mut self,
        cx: &mut Cx,
        signature: &str,
        lengths: &[i32],
    ) -> anyhow::Result<Value> {
        let array = self.new_array(cx, signature, lengths[0])?;
        if lengths.len() > 1 {
            let id = array
                .object_id()
                .context(trs!("创建数组失败", "Failed to create the array"))?;
            for i in 0..lengths[0] {
                let inner = self.array_with_lengths(cx, &signature[1..], &lengths[1..])?;
                cx.vm.set_array_value(id, i, &inner)?;
            }
        }
        Ok(array)
    }

    /// 新建数组：数组类型已经加载时直接创建，否则用 `java.lang.reflect.Array.newInstance`。
    fn new_array(&mut self, cx: &mut Cx, signature: &str, length: i32) -> anyhow::Result<Value> {
        let vm = cx.vm.clone();
        if let Some(class) = loaded_class(&vm, signature)? {
            let array = vm.new_array(class, length)?;
            if let Some(id) = array.object_id() {
                self.pin(&vm, id);
            }
            return Ok(array);
        }
        let component = self.class_object_of(cx, &signature[1..])?;
        let array_class = self
            .class_by_name(cx, "java.lang.reflect.Array")?
            .context(trs!(
                "找不到 java.lang.reflect.Array",
                "Cannot find java.lang.reflect.Array"
            ))?
            .0;
        let new_instance = vm
            .methods(array_class)?
            .iter()
            .find(|m| {
                m.name == "newInstance" && m.signature == "(Ljava/lang/Class;I)Ljava/lang/Object;"
            })
            .cloned()
            .context(trs!(
                "找不到 Array.newInstance",
                "Cannot find Array.newInstance"
            ))?;
        self.invoke(
            cx,
            Invoke::Static {
                class: array_class,
                interface: false,
                thread: cx.frame.thread,
                method: new_instance.id,
                args: vec![
                    Value::Object {
                        tag: tag::CLASS_OBJECT,
                        id: component,
                    },
                    Value::Int(length),
                ],
            },
        )
    }

    fn call_method(
        &mut self,
        cx: &mut Cx,
        target: Target,
        name: &str,
        candidates: &[(u64, MethodInfo)],
        args: Vec<Val>,
    ) -> anyhow::Result<Val> {
        let (method, values) = self.prepare_call(cx, name, candidates, args)?;
        let declaring = candidates
            .iter()
            .find(|(_, m)| m.id == method.id && m.signature == method.signature)
            .map(|(class, _)| *class)
            .context(trs!(
                "方法不在候选里",
                "The method is not among the candidates"
            ))?;
        let thread = cx.frame.thread;
        let invoke = match target {
            Target::Object { id, nonvirtual } if !method.is_static() => Invoke::Instance {
                object: id,
                class: declaring,
                thread,
                method: method.id,
                args: values,
                nonvirtual,
            },
            _ => {
                anyhow::ensure!(
                    method.is_static(),
                    tr!("`{name}` 不是静态方法", "`{name}` is not a static method")
                );
                Invoke::Static {
                    class: declaring,
                    interface: cx.vm.is_interface(declaring)?,
                    thread,
                    method: method.id,
                    args: values,
                }
            }
        };
        let value = self.invoke(cx, invoke)?;
        let (_, returns) = eval::split_method_signature(&method.signature)
            .context(trs!("方法签名格式不对", "Malformed method signature"))?;
        Ok(Val::Jdwp(value, Some(returns)))
    }

    /// 选重载并把实参转换成形参类型：先不装箱、再装箱拆箱、最后变长参数，同一阶段里取最具体的。
    fn prepare_call(
        &mut self,
        cx: &mut Cx,
        name: &str,
        candidates: &[(u64, MethodInfo)],
        args: Vec<Val>,
    ) -> anyhow::Result<(MethodInfo, Vec<Value>)> {
        let mut types = Vec::with_capacity(args.len());
        for arg in &args {
            types.push(self.arg_type(cx, arg)?);
        }
        let parsed: Vec<(MethodInfo, Vec<String>)> = candidates
            .iter()
            .filter_map(|(_, m)| {
                let (params, _) = eval::split_method_signature(&m.signature)?;
                Some((m.clone(), params))
            })
            .collect();
        for phase in 1..=3u8 {
            let mut applicable = Vec::new();
            for (i, (method, params)) in parsed.iter().enumerate() {
                if self.applicable(cx, method, params, &types, phase)? {
                    applicable.push(i);
                }
            }
            if applicable.is_empty() {
                continue;
            }
            // 有普通方法可选时不用编译器生成的桥接方法
            if applicable.iter().any(|&i| !parsed[i].0.is_bridge()) {
                applicable.retain(|&i| !parsed[i].0.is_bridge());
            }
            let mut chosen = applicable[0];
            'outer: for &i in &applicable {
                for &j in &applicable {
                    if i != j && !self.more_specific(cx, &parsed[i].1, &parsed[j].1)? {
                        continue 'outer;
                    }
                }
                chosen = i;
                break;
            }
            let (method, params) = parsed[chosen].clone();
            let values = self.convert_args(cx, args, &params, phase == 3)?;
            return Ok((method, values));
        }
        let given: Vec<String> = types.iter().map(ArgType::describe).collect();
        let declared: Vec<String> = parsed
            .iter()
            .map(|(_, params)| {
                let params: Vec<String> =
                    params.iter().map(|p| signature_to_type_name(p)).collect();
                format!("{name}({})", params.join(", "))
            })
            .collect();
        bail!(tr!(
            "没有适用于参数 ({}) 的 `{name}`；可选的有：{}",
            "No `{name}` is applicable to the arguments ({}); candidates: {}",
            given.join(", "),
            declared.join("; ")
        ))
    }

    fn arg_type(&mut self, cx: &mut Cx, arg: &Val) -> anyhow::Result<ArgType> {
        let vm = cx.vm.clone();
        Ok(match arg {
            Val::Jdwp(value, _) => match eval::primitive_tag(value) {
                Some(tag) => ArgType::Primitive(tag),
                None => match value.object_id() {
                    None => ArgType::Null,
                    Some(id) => {
                        let class = vm.object_type(id)?;
                        ArgType::Ref {
                            class,
                            signature: vm.class_signature(class)?,
                        }
                    }
                },
            },
            Val::Str(_) => ArgType::Ref {
                class: loaded_class(&vm, STRING)?.context(trs!(
                    "找不到 java.lang.String",
                    "Cannot find java.lang.String"
                ))?,
                signature: STRING.to_owned(),
            },
            Val::Type { signature, .. } => {
                bail!(type_not_value(signature))
            }
            Val::Package(name) => bail!(unknown_name(name)),
        })
    }

    /// 一个实参能否在 `phase`（1 不装箱、2 装箱拆箱）下传给形参。
    fn arg_fits(
        &mut self,
        cx: &mut Cx,
        param: &str,
        arg: &ArgType,
        phase: u8,
    ) -> anyhow::Result<bool> {
        let vm = cx.vm.clone();
        if is_primitive_signature(param) {
            let to = param.as_bytes()[0];
            return Ok(match arg {
                ArgType::Primitive(from) => eval::widens_to(*from, to),
                ArgType::Ref { signature, .. } if phase >= 2 => {
                    eval::unboxed_tag(signature).is_some_and(|from| eval::widens_to(from, to))
                }
                _ => false,
            });
        }
        match arg {
            ArgType::Null => Ok(true),
            ArgType::Primitive(tag) if phase >= 2 => {
                let boxed = eval::box_signature(*tag)
                    .context(trs!("未知的基本类型", "Unknown primitive type"))?;
                self.signature_is_subtype(cx, boxed, param)
            }
            ArgType::Primitive(_) => Ok(false),
            ArgType::Ref { class, signature } => is_subtype(&vm, *class, signature, param),
        }
    }

    fn applicable(
        &mut self,
        cx: &mut Cx,
        method: &MethodInfo,
        params: &[String],
        args: &[ArgType],
        phase: u8,
    ) -> anyhow::Result<bool> {
        if phase < 3 {
            if params.len() != args.len() {
                return Ok(false);
            }
            for (param, arg) in params.iter().zip(args) {
                if !self.arg_fits(cx, param, arg, phase)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        if !method.is_varargs() || args.len() + 1 < params.len() {
            return Ok(false);
        }
        let (last, fixed) = params.split_last().context(trs!(
            "变长参数方法没有形参",
            "The varargs method has no parameters"
        ))?;
        let component = last.strip_prefix('[').context(trs!(
            "变长参数不是数组",
            "The varargs parameter is not an array"
        ))?;
        for (i, arg) in args.iter().enumerate() {
            let param = fixed.get(i).map_or(component, String::as_str);
            if !self.arg_fits(cx, param, arg, 2)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// 形参列表 `a` 是否比 `b` 更具体（逐个形参都能传给对方）。
    fn more_specific(&mut self, cx: &mut Cx, a: &[String], b: &[String]) -> anyhow::Result<bool> {
        for (x, y) in a.iter().zip(b) {
            if x == y {
                continue;
            }
            let fits = match (is_primitive_signature(x), is_primitive_signature(y)) {
                (true, true) => eval::widens_to(x.as_bytes()[0], y.as_bytes()[0]),
                (false, false) => self.signature_is_subtype(cx, x, y)?,
                _ => false,
            };
            if !fits {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn convert_args(
        &mut self,
        cx: &mut Cx,
        args: Vec<Val>,
        params: &[String],
        varargs: bool,
    ) -> anyhow::Result<Vec<Value>> {
        let mut values = Vec::with_capacity(params.len());
        let mut args = args.into_iter();
        let fixed = if varargs {
            params.len() - 1
        } else {
            params.len()
        };
        for param in &params[..fixed] {
            let arg = args
                .next()
                .context(trs!("实参不够", "Not enough arguments"))?;
            values.push(self.convert_arg(cx, arg, param)?);
        }
        if varargs {
            let array_signature = &params[fixed];
            let component = &array_signature[1..];
            let mut elements = Vec::new();
            for arg in args {
                elements.push(self.convert_arg(cx, arg, component)?);
            }
            let array = self.new_array(cx, array_signature, elements.len() as i32)?;
            if let (Some(id), false) = (array.object_id(), elements.is_empty()) {
                cx.vm.set_array_values(id, 0, &elements)?;
            }
            values.push(array);
        }
        Ok(values)
    }

    /// 实参转换成形参类型的值：拓宽、拆箱、装箱，字符串放进 JVM。
    fn convert_arg(&mut self, cx: &mut Cx, arg: Val, param: &str) -> anyhow::Result<Value> {
        if is_primitive_signature(param) {
            let value = self.primitive(cx, &arg)?.with_context(|| {
                tr!(
                    "实参不能转换成 {}",
                    "The argument cannot be converted to {}",
                    signature_to_type_name(param)
                )
            })?;
            return eval::convert_primitive(value, param.as_bytes()[0]).map_err(anyhow::Error::msg);
        }
        match arg {
            Val::Jdwp(value, _) if eval::primitive_tag(&value).is_some() => {
                self.box_value(cx, value)
            }
            Val::Jdwp(value, _) => Ok(value),
            Val::Str(text) => self.new_string(cx, &text),
            other => Ok(self.materialize(cx, other)?.0),
        }
    }

    /// 装箱：调用包装类的 `valueOf`。
    fn box_value(&mut self, cx: &mut Cx, value: Value) -> anyhow::Result<Value> {
        let tag =
            eval::primitive_tag(&value).context(trs!("不是基本类型", "Not a primitive type"))?;
        let signature =
            eval::box_signature(tag).context(trs!("未知的基本类型", "Unknown primitive type"))?;
        let class = self.class_by_signature(cx, signature)?.with_context(|| {
            tr!(
                "找不到 {}",
                "Cannot find {}",
                signature_to_type_name(signature)
            )
        })?;
        let value_of = format!("({}){signature}", tag as char);
        let method = cx
            .vm
            .methods(class)?
            .iter()
            .find(|m| m.name == "valueOf" && m.signature == value_of)
            .cloned()
            .context(trs!("找不到 valueOf", "Cannot find valueOf"))?;
        self.invoke(
            cx,
            Invoke::Static {
                class,
                interface: false,
                thread: cx.frame.thread,
                method: method.id,
                args: vec![value],
            },
        )
    }

    fn new_string(&mut self, cx: &Cx, text: &str) -> anyhow::Result<Value> {
        let id = cx.vm.create_string(text)?;
        self.pin(&cx.vm, id);
        Ok(Value::Object {
            tag: tag::STRING,
            id,
        })
    }

    /// 禁止回收求值时新建的对象，程序继续运行时再放开。
    fn pin(&mut self, vm: &Vm, id: u64) {
        if id != 0 && vm.disable_collection(id).is_ok() {
            self.pinned.push(id);
        }
    }

    // ---------------------------------------------------------------
    // 在目标 JVM 里执行
    // ---------------------------------------------------------------

    /// 执行调用；抛出异常时报错（带异常类型和消息），返回的对象禁止回收。
    fn invoke(&mut self, cx: &mut Cx, invoke: Invoke) -> anyhow::Result<Value> {
        anyhow::ensure!(
            cx.allow_invoke,
            trs!("悬停时不调用方法", "Methods are not called while hovering")
        );
        self.ensure_abort_exception(cx);
        let (value, exception) = self.raw_invoke(cx, &invoke)?;
        if exception != 0 {
            if Some(exception) == self.abort_exception {
                bail!(tr!(
                    "方法调用超时（{} 秒内没有返回），已经中止",
                    "The method call timed out (no return within {} seconds) and was aborted",
                    INVOKE_TIMEOUT.as_secs()
                ));
            }
            let vm = cx.vm.clone();
            let type_name = vm
                .object_type(exception)
                .and_then(|class| vm.class_name(class))
                .unwrap_or_else(|_| "java.lang.Throwable".to_owned());
            match self.throwable_message(exception) {
                Some(message) => bail!(tr!(
                    "抛出了异常 {type_name}: {message}",
                    "Threw exception {type_name}: {message}"
                )),
                None => bail!(tr!("抛出了异常 {type_name}", "Threw exception {type_name}")),
            }
        }
        if let Some(id) = value.object_id() {
            self.pin(&cx.vm, id);
        }
        Ok(value)
    }

    /// 打断超时调用用的异常对象：第一次调用方法前在同一个线程上创建，之后一直复用。
    fn ensure_abort_exception(&mut self, cx: &mut Cx) {
        if self.abort_exception.is_some() {
            return;
        }
        let created = (|| -> anyhow::Result<Option<u64>> {
            let vm = cx.vm.clone();
            let Some(class) = loaded_class(&vm, "Ljava/lang/RuntimeException;")? else {
                return Ok(None);
            };
            let Some(constructor) = vm
                .methods(class)?
                .iter()
                .find(|m| m.name == "<init>" && m.signature == "(Ljava/lang/String;)V")
                .cloned()
            else {
                return Ok(None);
            };
            let message = vm.create_string("evaluation timed out (java-analyzer)")?;
            let (value, exception) = self.raw_invoke(
                cx,
                &Invoke::New {
                    class,
                    thread: cx.frame.thread,
                    method: constructor.id,
                    args: vec![Value::Object {
                        tag: tag::STRING,
                        id: message,
                    }],
                },
            )?;
            match (value.object_id(), exception) {
                (Some(id), 0) => {
                    vm.disable_collection(id)?;
                    Ok(Some(id))
                }
                _ => Ok(None),
            }
        })();
        match created {
            Ok(id) => self.abort_exception = id,
            Err(err) => tracing::debug!("创建中止求值用的异常对象失败: {err:#}"),
        }
    }

    /// 发出调用并等结果：`(返回值, 抛出的异常（没有时为 0）)`。线程恢复过，调用结束后重新取帧 ID。
    fn raw_invoke(&mut self, cx: &mut Cx, invoke: &Invoke) -> anyhow::Result<(Value, u64)> {
        let vm = cx.vm.clone();
        let thread = cx.frame.thread;
        let depth_before = vm.frames(thread, 0, -1)?.len();
        let pending = vm.start_invoke(invoke)?;
        self.invoking = Some(thread);
        let result = self.wait_invoke(&vm, pending, thread, depth_before);
        self.invoking = None;
        self.refresh_frames(&vm, thread, cx);
        let data = result.map_err(|err| {
            if jdwp::is_error(&err, jdwp::error_code::INVALID_THREAD)
                || jdwp::is_error(&err, jdwp::error_code::THREAD_NOT_SUSPENDED)
            {
                anyhow::anyhow!(trs!("只能在因为断点、单步或异常停下的线程上调用方法（暂停的线程不行）", "Methods can only be called on a thread stopped by a breakpoint, a step or an exception (not on a paused thread)"))
            } else {
                err
            }
        })?;
        vm.invoke_result(&data)
    }

    /// 等调用的回复。期间被调用线程的事件就地处理（不停下，接着执行），别的事件留到之后处理；
    /// 超时后打断被调用的方法。
    fn wait_invoke(
        &mut self,
        vm: &Rc<Vm>,
        pending: jdwp::PendingReply,
        thread: u64,
        depth_before: usize,
    ) -> anyhow::Result<Vec<u8>> {
        let events = self.events_rx.clone();
        let mut deadline = Instant::now() + INVOKE_TIMEOUT;
        let mut aborted = false;
        loop {
            let left = deadline.saturating_duration_since(Instant::now());
            crossbeam_channel::select! {
                recv(pending.rx) -> reply => {
                    return match reply {
                        Ok(reply) => reply_result(reply),
                        Err(_) => bail!(jdwp::disconnected()),
                    };
                }
                recv(events) -> event => match event {
                    Ok(JdwpEvent::Composite(data)) => match vm.parse_events(&data) {
                        Ok(set) if set.events.iter().any(|e| e.thread() == Some(thread)) => {
                            self.handle_event_set(vm, set);
                        }
                        _ => self.deferred.push_back(JdwpEvent::Composite(data)),
                    },
                    Ok(JdwpEvent::Closed) | Err(_) => {
                        self.deferred.push_back(JdwpEvent::Closed);
                        vm.connection().forget(pending.id);
                        bail!(jdwp::disconnected());
                    }
                },
                default(left) => {
                    if aborted {
                        vm.connection().forget(pending.id);
                        bail!(
                            tr!("方法调用超时（{} 秒内没有返回），也没能中止：线程还在执行被调用的方法", "The method call timed out (no return within {} seconds) and could not be aborted: the thread is still running the called method",
                            INVOKE_TIMEOUT.as_secs()));
                    }
                    aborted = true;
                    self.abort_invoke(vm, thread, depth_before);
                    deadline = Instant::now() + ABORT_TIMEOUT;
                }
            }
        }
    }

    /// 让还在执行的被调用方法抛出异常退出。先挂起线程确认调用还没返回（栈比调用前深），
    /// 免得把异常抛进程序自己的代码里。
    fn abort_invoke(&mut self, vm: &Vm, thread: u64, depth_before: usize) {
        let Some(throwable) = self.abort_exception else {
            return;
        };
        if vm.thread_suspend(thread).is_err() {
            return;
        }
        let running = vm
            .frames(thread, 0, -1)
            .is_ok_and(|frames| frames.len() > depth_before);
        if running {
            if let Err(err) = vm.thread_stop(thread, throwable) {
                tracing::debug!("中止求值调用失败: {err:#}");
            }
        }
        let _ = vm.thread_resume(thread);
    }

    /// 线程恢复过：按调用栈位置重新取这个线程的帧 ID（会话里记着的栈帧和当前求值的栈帧）。
    fn refresh_frames(&mut self, vm: &Vm, thread: u64, cx: &mut Cx) {
        let Ok(frames) = vm.frames(thread, 0, -1) else {
            return;
        };
        let update = |frame: &mut FrameRef| {
            if frame.thread == thread {
                if let Some((id, location)) = frames.get(frame.depth as usize) {
                    frame.frame = *id;
                    frame.location = *location;
                }
            }
        };
        for frame in self.frames.values_mut() {
            update(frame);
        }
        for var in self.vars.values_mut() {
            if let VarRef::Locals(frame) = var {
                update(frame);
            }
        }
        update(&mut cx.frame);
    }

    /// 摘要显示（悬停求值里的字符串连接用）。
    fn describe_value(&self, vm: &Vm, value: &Value, declared: Option<&str>) -> String {
        self.describe(vm, value, declared).value
    }
}

/// 拆箱：包装类型对象的 `value` 字段；不是包装类型时返回 `None`。
fn unbox(vm: &Vm, id: u64) -> anyhow::Result<Option<Value>> {
    let class = vm.object_type(id)?;
    let signature = vm.class_signature(class)?;
    if eval::unboxed_tag(&signature).is_none() {
        return Ok(None);
    }
    let Some((_, field)) = find_field(vm, class, "value")? else {
        return Ok(None);
    };
    Ok(vm.object_values(id, &[field.id])?.first().copied())
}

/// 已加载（且已准备好）的类。
pub(crate) fn loaded_class(vm: &Vm, signature: &str) -> anyhow::Result<Option<u64>> {
    let classes = vm.classes_by_signature(signature)?;
    Ok(classes
        .iter()
        .find(|(_, _, status)| status & jdwp::CLASS_STATUS_PREPARED != 0)
        .or(classes.first())
        .map(|(_, id, _)| *id))
}

/// 限定名的各种二进制名写法：原样，然后从右往左把点换成 `$`（`java.util.Map.Entry` →
/// `java.util.Map$Entry`）。
fn binary_name_variants(name: &str) -> Vec<String> {
    let mut variants = vec![name.to_owned()];
    let mut current = name.to_owned();
    while let Some(i) = current.rfind('.') {
        current.replace_range(i..=i, "$");
        variants.push(current.clone());
    }
    variants
}

/// 类型是否是 `target` 的子类型（`class` 和 `signature` 是同一个类型）。
fn is_subtype(vm: &Vm, class: u64, signature: &str, target: &str) -> anyhow::Result<bool> {
    if signature == target || target == OBJECT {
        return Ok(true);
    }
    if let Some(component) = signature.strip_prefix('[') {
        if matches!(target, "Ljava/lang/Cloneable;" | "Ljava/io/Serializable;") {
            return Ok(true);
        }
        let Some(target_component) = target.strip_prefix('[') else {
            return Ok(false);
        };
        if is_primitive_signature(component) || is_primitive_signature(target_component) {
            return Ok(false);
        }
        return match loaded_class(vm, component)? {
            Some(component_class) => is_subtype(vm, component_class, component, target_component),
            None => Ok(false),
        };
    }
    let mut types = vm.class_chain(class)?;
    let mut seen: HashSet<u64> = types.iter().copied().collect();
    let mut i = 0;
    while i < types.len() {
        if vm.class_signature(types[i])? == target {
            return Ok(true);
        }
        for &interface in vm.interfaces(types[i])?.iter() {
            if seen.insert(interface) {
                types.push(interface);
            }
        }
        i += 1;
    }
    Ok(false)
}

/// 内部类实例的外层实例链（`this$0` 字段）。
pub(crate) fn outer_instances(vm: &Vm, object: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut current = object;
    while out.len() < 16 {
        let Ok(class) = vm.object_type(current) else {
            break;
        };
        let Ok(fields) = vm.fields(class) else { break };
        let Some(field) = fields
            .iter()
            .find(|f| f.name.starts_with("this$") && !f.is_static())
        else {
            break;
        };
        match vm
            .object_values(current, &[field.id])
            .ok()
            .and_then(|values| values.first().and_then(Value::object_id))
        {
            Some(outer) => {
                out.push(outer);
                current = outer;
            }
            None => break,
        }
    }
    out
}

/// 当前类和它的外层类（按 `$` 拆二进制名，已加载的）。
pub(crate) fn enclosing_classes(vm: &Vm, class: u64) -> Vec<u64> {
    let mut out = vec![class];
    let Ok(signature) = vm.class_signature(class) else {
        return out;
    };
    let mut name = signature.trim_end_matches(';').to_owned();
    while let Some(i) = name.rfind('$') {
        name.truncate(i);
        if let Ok(Some(outer)) = loaded_class(vm, &format!("{name};")) {
            out.push(outer);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binary_names() {
        assert_eq!(
            binary_name_variants("java.util.Map.Entry"),
            vec![
                "java.util.Map.Entry",
                "java.util.Map$Entry",
                "java.util$Map$Entry",
                "java$util$Map$Entry"
            ]
        );
        assert_eq!(binary_name_variants("Foo"), vec!["Foo"]);
    }
}
