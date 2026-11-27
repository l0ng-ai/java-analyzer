//! 方法体级别的推断：名字解析 + 表达式类型。
//!
//! 推断直接在语法树上进行，结果按节点的文本范围索引。一个"体"（[`BodyId`]）是一个方法、
//! 构造器、字段初始化式或初始化块；匿名类和局部类的成员在所属的体里就地推断。
//!
//! 每个体是一个独立的惰性查询：只有被请求到的体才会计算；别的文件的体只依赖签名级查询，
//! 所以在某个方法体里编辑不会让其它文件的推断结果失效。
//!
//! 同一个文件里也一样：推断在从体的语法子树单独取出来的树上进行（[`BodySource`]），结果按
//! 相对于子树起点的范围存放，只依赖这棵子树和签名。别的体里的编辑、让这个体挪动位置的编辑
//! 都不会让它重新推断；对外的 [`InferenceResult`] 在查询时把范围换算到文件里的当前位置。

mod expr;
mod pattern_scope;

use std::sync::Arc;

use base_db::{Db, SourceFile};
use hir_def::{
    class_data, class_decl_file, class_header, file_scope, lower_type, source_map, ClassId,
    DeclIdx, FieldId, FileScope, MethodId, Name, TypeParamId, TypeScope,
};
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;
use syntax::{
    ast::{self, AstNode},
    GreenNode, SyntaxKind, SyntaxNode, TextRange, TextSize,
};

use crate::{
    lower::{class_supertypes, field_ty, lower_type_ref, method_sig, this_ty},
    members::MethodCandidate,
    subtype::{find_super, is_assignable, lub},
    ty::Ty,
};

/// int 字面量（可以带一元负号）的值。
fn int_literal_value(expr: &ast::Expr) -> Option<i64> {
    match expr {
        ast::Expr::ParenExpr(it) => int_literal_value(&it.expr()?),
        ast::Expr::UnaryExpr(it) => {
            let op = it.op_token()?;
            match op.kind() {
                syntax::SyntaxKind::MINUS => int_literal_value(&it.operand()?).map(|v| -v),
                syntax::SyntaxKind::PLUS => int_literal_value(&it.operand()?),
                _ => None,
            }
        }
        ast::Expr::Literal(lit) => {
            let token = lit.token()?;
            if token.kind() != syntax::SyntaxKind::INT_LITERAL {
                return None;
            }
            let text: String = token.text().chars().filter(|c| *c != '_').collect();
            let lower = text.to_ascii_lowercase();
            // 十六进制 / 八进制 / 二进制字面量是 32 位的位模式（`0xFFFFFFFF` 是 -1）
            let radix_value = |digits: &str, radix: u32| {
                u32::from_str_radix(digits, radix)
                    .ok()
                    .map(|v| i64::from(v as i32))
            };
            if let Some(hex) = lower.strip_prefix("0x") {
                radix_value(hex, 16)
            } else if let Some(bin) = lower.strip_prefix("0b") {
                radix_value(bin, 2)
            } else if lower.len() > 1 && lower.starts_with('0') {
                radix_value(&lower[1..], 8)
            } else {
                lower.parse::<i64>().ok()
            }
        }
        _ => None,
    }
}

/// 常量值能否不丢失地收窄成 byte / short / char。
fn int_fits(value: i64, target: hir_def::PrimitiveType) -> bool {
    use hir_def::PrimitiveType as P;
    match target {
        P::Byte => (-128..=127).contains(&value),
        P::Short => (-32768..=32767).contains(&value),
        P::Char => (0..=65535).contains(&value),
        _ => true,
    }
}

/// `new Foo<A>(..)`：写明了类型实参，既不是菱形 `new Foo<>()`，也不是匿名类。
fn has_explicit_type_args(new: &ast::NewExpr) -> bool {
    new.body().is_none()
        && new.ty().is_some_and(|ty| {
            let text: String = ty.syntax().text().to_string().split_whitespace().collect();
            text.ends_with('>') && !text.ends_with("<>")
        })
}

/// 一段可以独立推断的代码。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BodyId {
    Method(MethodId),
    /// 字段初始化式，或枚举常量的实参与类体
    Field(FieldId),
    /// 类里第 `idx` 个初始化块
    Initializer {
        class: ClassId,
        idx: u32,
    },
}

impl BodyId {
    pub fn class(self) -> ClassId {
        match self {
            BodyId::Method(m) => m.class,
            BodyId::Field(f) => f.class,
            BodyId::Initializer { class, .. } => class,
        }
    }
}

pub type LocalId = u32;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum LocalKind {
    Param,
    Local,
    LambdaParam,
    CatchParam,
    Pattern,
    Resource,
    ForeachVar,
    /// 匿名类 / 局部类里声明的字段
    LocalClassField,
    /// 匿名类 / 局部类里声明的方法；`ty` 是它的返回类型
    LocalClassMethod,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct LocalData {
    pub name: Name,
    pub ty: Ty,
    /// 声明处名字节点的范围
    pub decl_range: TextRange,
    pub kind: LocalKind,
}

/// 一个名字引用解析到了什么。
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Resolution {
    Local(LocalId),
    Field(FieldId),
    Method(MethodId),
    Class(ClassId),
    TypeParam(TypeParamId),
    Package(SmolStr),
    /// 数组的 `length`
    ArrayLength,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum InferDiagnosticKind {
    UnresolvedName {
        name: Name,
    },
    UnresolvedField {
        name: Name,
        receiver: String,
    },
    UnresolvedMethod {
        name: Name,
        receiver: Option<String>,
    },
    TypeMismatch {
        expected: String,
        actual: String,
    },
    /// 没有一个重载能接受这组实参
    ArgumentMismatch {
        name: Name,
        args: String,
    },
    /// 运算符不能用在这样的操作数上
    BadOperand {
        op: String,
        operands: String,
    },
    /// 同一个方法体里已经有同名的局部变量 / 形参
    DuplicateLocal {
        name: Name,
    },
    /// 有不止一个重载同样适用，谁也不比谁更具体
    AmbiguousCall {
        name: Name,
        /// 两个候选，形如 `Math.abs(int)`
        first: String,
        second: String,
    },
    /// lambda 的形参个数和目标函数式接口的方法对不上
    LambdaArity {
        target: String,
        expected: usize,
        found: usize,
    },
    /// 目标函数式接口的方法返回 void，lambda 体却是一个值（不是语句表达式，或 `return 值;`）
    LambdaReturnsValue {
        target: String,
    },
    /// 目标函数式接口的方法要返回值，lambda 的块体却没有 `return 值;`
    LambdaMissingValue {
        target: String,
        expected: String,
    },
    /// 在基本类型或 void 的值上访问成员（`x.foo()`、`voidCall().toString()`）
    PrimitiveDereference {
        ty: String,
        method: bool,
    },
    /// 对不是数组的值用下标（`s[0]`）
    NotAnArray {
        ty: String,
    },
    /// `var` 声明推不出类型（`var x;`、`var x = null;`）。`reason` 已经本地化
    CannotInferVar {
        name: Name,
        reason: String,
    },
    /// 增强 for 遍历的值既不是数组也不是 `Iterable`
    NotIterable {
        ty: String,
    },
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct InferDiagnostic {
    pub range: TextRange,
    pub kind: InferDiagnosticKind,
}

/// 一次调用的重载信息，供签名帮助使用。
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CallInfo {
    pub candidates: Vec<MethodCandidate>,
    pub chosen: Option<MethodId>,
}

/// 一个体的推断结果，范围都相对于推断时用的子树（见 [`BodySource`]）：体之外的编辑
/// （包括让体整体挪动位置的编辑）不会改变它。
#[derive(Default, PartialEq, Eq, Debug)]
pub(crate) struct BodyInference {
    /// 表达式节点范围 → 类型
    expr_types: FxHashMap<TextRange, Ty>,
    /// 名字引用（`NAME_REF`）范围 → 解析结果。
    /// 显式构造器调用 `this(...)` / `super(...)` 以 `this` / `super` 表达式的范围为键。
    resolutions: FxHashMap<TextRange, Resolution>,
    locals: Vec<LocalData>,
    /// 声明处名字节点范围 → 局部变量
    local_decls: FxHashMap<TextRange, LocalId>,
    /// 实参列表（`ARG_LIST`）范围 → 调用信息
    calls: FxHashMap<TextRange, CallInfo>,
    diagnostics: Vec<InferDiagnostic>,
}

impl BodyInference {
    pub(crate) fn type_of(&self, expr_range: TextRange) -> Option<&Ty> {
        self.expr_types.get(&expr_range)
    }

    pub(crate) fn resolution(&self, name_range: TextRange) -> Option<&Resolution> {
        self.resolutions.get(&name_range)
    }
}

/// 一个体的推断结果，范围是文件里的绝对位置。
///
/// 内部共享按相对位置存放的 [`BodyInference`]，查询时再换算：体前面的编辑只让偏移变化，
/// 不需要重新推断。
#[derive(Default, PartialEq, Eq, Debug)]
pub struct InferenceResult {
    /// 推断用的子树在文件里的起点
    offset: TextSize,
    data: Arc<BodyInference>,
    /// 换算成绝对位置的局部变量和诊断
    locals: Vec<LocalData>,
    diagnostics: Vec<InferDiagnostic>,
}

impl InferenceResult {
    pub(crate) fn new(data: Arc<BodyInference>, offset: TextSize) -> InferenceResult {
        let locals = data
            .locals
            .iter()
            .map(|local| LocalData {
                decl_range: local.decl_range + offset,
                ..local.clone()
            })
            .collect();
        let diagnostics = data
            .diagnostics
            .iter()
            .map(|diag| InferDiagnostic {
                range: diag.range + offset,
                kind: diag.kind.clone(),
            })
            .collect();
        InferenceResult {
            offset,
            data,
            locals,
            diagnostics,
        }
    }

    /// 文件里的范围 → 推断时的相对范围。
    fn relative(&self, range: TextRange) -> Option<TextRange> {
        range.checked_sub(self.offset)
    }

    pub fn type_of(&self, expr_range: TextRange) -> Option<&Ty> {
        self.data.expr_types.get(&self.relative(expr_range)?)
    }

    pub fn resolution(&self, name_range: TextRange) -> Option<&Resolution> {
        self.data.resolutions.get(&self.relative(name_range)?)
    }

    pub fn local(&self, id: LocalId) -> &LocalData {
        &self.locals[id as usize]
    }

    pub fn locals(&self) -> &[LocalData] {
        &self.locals
    }

    pub fn local_at_decl(&self, name_range: TextRange) -> Option<LocalId> {
        self.data
            .local_decls
            .get(&self.relative(name_range)?)
            .copied()
    }

    pub fn call_info(&self, arg_list_range: TextRange) -> Option<&CallInfo> {
        self.data.calls.get(&self.relative(arg_list_range)?)
    }

    pub fn diagnostics(&self) -> &[InferDiagnostic] {
        &self.diagnostics
    }

    pub fn expr_types(&self) -> impl Iterator<Item = (TextRange, &Ty)> {
        let offset = self.offset;
        self.data
            .expr_types
            .iter()
            .map(move |(range, ty)| (*range + offset, ty))
    }

    pub fn resolutions(&self) -> impl Iterator<Item = (TextRange, &Resolution)> {
        let offset = self.offset;
        self.data
            .resolutions
            .iter()
            .map(move |(range, res)| (*range + offset, res))
    }
}

/// 体对应的语法节点（方法 / 构造器声明、变量声明符、枚举常量或初始化块）。
pub fn body_syntax(db: &dyn Db, body: BodyId) -> Option<(SourceFile, SyntaxNode)> {
    let class = body.class();
    // 工作区源码，或者依赖库的类对应的、已经打开的库源码文件
    let file = class_decl_file(db, class)?;
    let data = class_data(db, class)?;
    let root = base_db::parse(db, file).syntax_node();
    let map = source_map(db, file);
    let node = match body {
        BodyId::Method(m) => map.to_node(data.methods.get(m.idx as usize)?.decl?, &root)?,
        BodyId::Field(f) => map.to_node(data.fields.get(f.idx as usize)?.decl?, &root)?,
        BodyId::Initializer { idx, .. } => {
            let class_node = map.to_node(data.decl?, &root)?;
            let decl = ast::TypeDecl::cast(class_node)?;
            decl.body()?
                .members()
                .filter_map(|m| match m {
                    ast::Member::InitializerBlock(it) => Some(it),
                    _ => None,
                })
                .nth(idx as usize)?
                .syntax()
                .clone()
        }
    };
    Some((file, node))
}

/// 推断一个体时用的子树的根：一般就是体自己的节点。记录的紧凑构造器的形参是记录的组件，
/// 写在构造器之外，用整个记录声明。
pub(crate) fn body_anchor(node: &SyntaxNode) -> SyntaxNode {
    let compact_ctor =
        ast::ConstructorDecl::cast(node.clone()).is_some_and(|ctor| ctor.param_list().is_none());
    if compact_ctor {
        if let Some(record) = node.ancestors().skip(1).find_map(ast::TypeDecl::cast) {
            return record.syntax().clone();
        }
    }
    node.clone()
}

/// 推断一个体所需的全部语法，和体在文件里的位置无关。
///
/// 每次编辑所在文件后都会重新计算（很便宜），但只要体自己的文本没变，结果就和上次相等，
/// salsa 因此不会重新执行依赖它的推断。
#[derive(Eq, Debug)]
struct BodySource {
    file: SourceFile,
    /// 推断用的子树（见 [`body_anchor`]），位置从 0 开始
    green: GreenNode,
    /// 体的节点在子树里的种类和范围
    body: (SyntaxKind, TextRange),
    /// 子树里的声明（局部类、匿名类体和它们的成员）：（种类，相对范围，声明下标）
    decls: Vec<(SyntaxKind, TextRange, DeclIdx)>,
}

impl PartialEq for BodySource {
    fn eq(&self, other: &Self) -> bool {
        self.file == other.file
            && self.body == other.body
            && self.decls == other.decls
            && syntax::green_eq(&self.green, &other.green)
    }
}

impl BodySource {
    fn root(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }

    fn body_node(&self, root: &SyntaxNode) -> Option<SyntaxNode> {
        let (kind, range) = self.body;
        if root.kind() == kind && root.text_range() == range {
            return Some(root.clone());
        }
        root.descendants()
            .find(|n| n.kind() == kind && n.text_range() == range)
    }

    /// 子树里某个声明节点的声明下标。
    fn decl_idx(&self, node: &SyntaxNode) -> Option<DeclIdx> {
        let (kind, range) = (node.kind(), node.text_range());
        self.decls
            .iter()
            .find(|(k, r, _)| *k == kind && *r == range)
            .map(|(_, _, idx)| *idx)
    }
}

#[salsa::tracked]
fn body_source(db: &dyn Db, _ws: base_db::Workspace, body: BodyId) -> Option<Arc<BodySource>> {
    let (file, node) = body_syntax(db, body)?;
    let anchor = body_anchor(&node);
    let offset = anchor.text_range().start();
    let decls = source_map(db, file)
        .decls_in(anchor.text_range())
        .map(|(idx, ptr)| (ptr.kind(), ptr.text_range() - offset, idx))
        .collect();
    Some(Arc::new(BodySource {
        file,
        green: anchor.green().into_owned(),
        body: (node.kind(), node.text_range() - offset),
        decls,
    }))
}

/// 体的推断结果。
pub fn infer(db: &dyn Db, body: BodyId) -> Arc<InferenceResult> {
    infer_located(db, base_db::workspace(db), body)
}

/// 把按相对位置存放的推断结果放到体在文件里的当前位置上。文件每次编辑后都会重新执行，
/// 但只是换算位置，不重新推断。
#[salsa::tracked]
fn infer_located(db: &dyn Db, ws: base_db::Workspace, body: BodyId) -> Arc<InferenceResult> {
    let data = infer_tracked(db, ws, body);
    let offset = body_syntax(db, body)
        .map(|(_, node)| body_anchor(&node).text_range().start())
        .unwrap_or_default();
    Arc::new(InferenceResult::new(data, offset))
}

// salsa 的追踪函数要求第一个参数是 salsa 结构体；键是普通值时借工作区单例占位，
// 多参数的追踪函数会自动把参数驻留。
//
// 只依赖体自己的语法（[`body_source`]）和签名级的查询：别的体、别的文件里的编辑，
// 以及让这个体挪动位置的编辑，都不会让它重新执行。
#[salsa::tracked]
pub(crate) fn infer_tracked(
    db: &dyn Db,
    ws: base_db::Workspace,
    body: BodyId,
) -> Arc<BodyInference> {
    let Some(source) = body_source(db, ws, body) else {
        return Arc::default();
    };
    let root = source.root();
    let Some(node) = source.body_node(&root) else {
        return Arc::default();
    };
    let mut cx = InferCtx::new(db, &source, body);
    cx.infer_body(body, &node);
    Arc::new(cx.result)
}

/// 一层"当前类"。最外层是体所属的具名类，匿名类 / 局部类的类体各压一层。
struct Frame {
    /// 有 `ClassId` 的类（具名类、局部类、登记过的匿名类）是它自己的类型；
    /// 没有登记成类的匿名类（菱形、`outer.new Inner() { ... }`）是它的父类型
    this_ty: Ty,
    /// 没有登记成类的匿名类：它自己声明的成员登记为局部符号
    anonymous: bool,
    /// 进入这一层之前的类型作用域
    saved_scope: TypeScope,
}

pub(crate) struct InferCtx<'a> {
    db: &'a dyn Db,
    /// 体的语法（相对位置）和其中的声明
    source: &'a BodySource,
    /// 文件的 import 等
    file_scope: FileScope,
    scope: TypeScope,
    class: ClassId,
    frames: Vec<Frame>,
    scopes: Vec<FxHashMap<Name, LocalId>>,
    /// 每一层帧开始时 `scopes` 的深度：匿名类 / 局部类的类体可以重新声明外层的局部变量
    frame_scope_base: Vec<usize>,
    /// 下一次重载决议失败时可以报"实参不匹配"的方法名（由调用方在确认候选完整之后设置）
    pub(crate) report_inapplicable: Option<Name>,
    /// 当前函数体（方法或 lambda）里各 `return` 的类型
    return_tys: Vec<Vec<Ty>>,
    /// 当前函数体期望的返回类型
    ret_expected: Vec<Option<Ty>>,
    /// 当前 switch 表达式各分支的结果类型
    yield_tys: Vec<Vec<Ty>>,
    /// 是否抑制"无法解析"类诊断（没有 JDK、文件用了 Lombok 等会凭空生成成员的工具）
    suppress_unresolved: bool,
    /// 体里声明的局部类 / 记录 / 接口 / 枚举的名字
    local_type_names: FxHashSet<Name>,
    /// `instanceof` 模式变量的作用域
    pattern_scopes: pattern_scope::PatternScopes,
    /// 类型来自推断、可能不准的局部变量（`var`、隐式类型的 lambda 形参、`var` 模式等），
    /// 不拿它们的类型对参数化类型下结论
    uncertain_locals: FxHashSet<LocalId>,
    /// 当前检查的目标类型本身可能不准（比如赋值的左边是 `var` 变量）
    pub(crate) target_uncertain: bool,
    /// 下一次 `finish_call` 的接收者（由调用方在推断实参之前设置）
    pub(crate) call_receiver: CallReceiver,
    /// 下一个推断的 lambda 的隐式形参类型可靠（目标函数式接口的形参类型确定）
    pub(crate) lambda_params_certain: bool,
    /// 下一个推断的表达式的期望类型是声明出来的目标类型（见 `infer_method_call`）
    pub(crate) declared_target: bool,
    /// 没有目标类型的表达式（`var` 的初始值）：泛型调用里只能由目标确定的类型参数取上界
    pub(crate) no_target_expr: Option<TextRange>,
    /// 下一个菱形构造没有目标类型（见 `without_target`）
    pub(crate) standalone_new: bool,
    /// 当前嵌套在几层"带 lambda 的实参按目标类型重新推断"里
    pub(crate) retarget_depth: u32,
    result: BodyInference,
}

/// 一次调用的接收者，用来判断按接收者代换出来的形参类型是否可靠。
#[derive(Clone, Default)]
pub(crate) enum CallReceiver {
    /// 接收者的类型不确定
    #[default]
    Uncertain,
    /// 类型确定的接收者（或者构造器调用里写明的类型）
    Certain(Ty),
    /// 不带限定符的调用：接收者是某一层的 `this`
    Implicit,
}

impl<'a> InferCtx<'a> {
    fn new(db: &'a dyn Db, source: &'a BodySource, body: BodyId) -> InferCtx<'a> {
        let class = body.class();
        let scope = match body {
            BodyId::Method(m) => TypeScope::method(db, m),
            _ => TypeScope::class(db, class),
        };
        let no_jdk = Ty::object(db).is_unknown();
        let file_scope = file_scope(db, source.file);
        let generated_members = file_scope.imports_lombok();
        InferCtx {
            db,
            source,
            file_scope,
            scope,
            class,
            frames: vec![Frame {
                this_ty: this_ty(db, class),
                anonymous: false,
                saved_scope: scope,
            }],
            scopes: vec![FxHashMap::default()],
            frame_scope_base: vec![0],
            report_inapplicable: None,
            return_tys: Vec::new(),
            ret_expected: Vec::new(),
            yield_tys: Vec::new(),
            suppress_unresolved: no_jdk || generated_members,
            local_type_names: FxHashSet::default(),
            pattern_scopes: pattern_scope::PatternScopes::default(),
            uncertain_locals: FxHashSet::default(),
            target_uncertain: false,
            call_receiver: CallReceiver::Uncertain,
            lambda_params_certain: false,
            declared_target: false,
            no_target_expr: None,
            standalone_new: false,
            retarget_depth: 0,
            result: BodyInference::default(),
        }
    }

    fn infer_body(&mut self, body: BodyId, node: &SyntaxNode) {
        self.local_type_names = node
            .descendants()
            .filter(|n| *n != *node)
            .filter_map(ast::TypeDecl::cast)
            .filter_map(|decl| decl.name())
            .map(|name| name.text())
            .collect();
        self.pattern_scopes = pattern_scope::pattern_scopes(node);
        match body {
            BodyId::Method(method) => {
                let sig = method_sig(self.db, method);
                if let Some(decl) = ast::MethodDecl::cast(node.clone()) {
                    self.declare_params(decl.param_list(), &sig.params);
                    self.ret_expected.push(Some(sig.ret.clone()));
                    if let Some(block) = decl.body() {
                        self.infer_block(&block);
                    }
                    if let Some(default) = decl.default_value().and_then(|d| d.expr()) {
                        self.infer_expr(&default, Some(&sig.ret));
                    }
                    self.ret_expected.pop();
                } else if let Some(decl) = ast::ConstructorDecl::cast(node.clone()) {
                    match decl.param_list() {
                        Some(list) => self.declare_params(Some(list), &sig.params),
                        // 记录的紧凑构造器：形参是记录的全部组件
                        None => {
                            let components = decl
                                .syntax()
                                .ancestors()
                                .find_map(ast::TypeDecl::cast)
                                .and_then(|class| class.record_components());
                            self.declare_params(components, &sig.params);
                        }
                    }
                    self.ret_expected.push(Some(Ty::Void));
                    if let Some(block) = decl.body() {
                        self.infer_block(&block);
                    }
                    self.ret_expected.pop();
                }
            }
            BodyId::Field(field) => {
                let ty = field_ty(self.db, field);
                if let Some(declarator) = ast::VariableDeclarator::cast(node.clone()) {
                    if let Some(init) = declarator.initializer() {
                        self.declared_target = true;
                        let actual = self.infer_expr(&init, Some(&ty));
                        self.check_assignable(init.syntax().text_range(), &actual, &ty, &init);
                    }
                } else if let Some(constant) = ast::EnumConstant::cast(node.clone()) {
                    let class_ty = Ty::class(field.class);
                    if let Some(args) = constant.arg_list() {
                        let key = constant.name().map(|n| n.syntax().text_range());
                        self.infer_constructor_call(
                            field.class,
                            &class_ty,
                            false,
                            &args,
                            None,
                            key,
                        );
                    }
                    if let Some(body) = constant.body() {
                        self.infer_class_body(&body, class_ty);
                    }
                }
            }
            BodyId::Initializer { .. } => {
                if let Some(block) =
                    ast::InitializerBlock::cast(node.clone()).and_then(|b| b.body())
                {
                    self.ret_expected.push(None);
                    self.infer_block(&block);
                    self.ret_expected.pop();
                }
            }
        }
    }

    // ---- 作用域与局部变量 ----

    fn push_scope(&mut self) {
        self.scopes.push(FxHashMap::default());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn declare(&mut self, name: &ast::Name, ty: Ty, kind: LocalKind) -> LocalId {
        let id = self.result.locals.len() as LocalId;
        let text = name.text();
        let decl_range = name.syntax().text_range();
        // 局部变量不能遮蔽同一个方法体里的另一个局部变量或形参（JLS §6.4）。
        // 模式变量的作用域取决于控制流，这里不建模，不参与判断。
        let declares_variable = matches!(
            kind,
            LocalKind::Local
                | LocalKind::LambdaParam
                | LocalKind::CatchParam
                | LocalKind::ForeachVar
                | LocalKind::Resource
        );
        if declares_variable && text != "_" {
            let base = self.frame_scope_base.last().copied().unwrap_or(0);
            let clash = self.scopes[base.min(self.scopes.len())..]
                .iter()
                .rev()
                .find_map(|scope| scope.get(text.as_str()).copied())
                .is_some_and(|existing| {
                    matches!(
                        self.result.locals[existing as usize].kind,
                        LocalKind::Param
                            | LocalKind::Local
                            | LocalKind::LambdaParam
                            | LocalKind::CatchParam
                            | LocalKind::ForeachVar
                            | LocalKind::Resource
                    )
                });
            if clash {
                self.diagnostic(
                    decl_range,
                    InferDiagnosticKind::DuplicateLocal { name: text.clone() },
                );
            }
        }
        self.result.locals.push(LocalData {
            name: text.clone(),
            ty,
            decl_range,
            kind,
        });
        self.result.local_decls.insert(decl_range, id);
        // 方法和变量是两个名字空间：方法以 `名字()` 为键，
        // 这样同名的字段和方法（`boolean hasNext; boolean hasNext()`）互不覆盖
        let key = if kind == LocalKind::LocalClassMethod {
            Name::from(format!("{text}()"))
        } else {
            text
        };
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(key, id);
        }
        id
    }

    /// 匿名类 / 局部类自己声明的方法。
    fn lookup_local_method(&self, name: &str) -> Option<LocalId> {
        self.lookup_local(&format!("{name}()"))
    }

    /// 偏移 `offset` 处的引用在 `scopes[lo..hi]` 里看得到的局部符号：跳过作用域不覆盖这里的
    /// 模式变量。
    fn lookup_local_in(
        &self,
        lo: usize,
        hi: usize,
        name: &str,
        offset: TextSize,
    ) -> Option<LocalId> {
        let hi = hi.min(self.scopes.len());
        self.scopes[lo.min(hi)..hi]
            .iter()
            .rev()
            .filter_map(|scope| scope.get(name).copied())
            .find(|&local| {
                let data = &self.result.locals[local as usize];
                data.kind != LocalKind::Pattern
                    || pattern_scope::in_scope(&self.pattern_scopes, data.decl_range, offset)
            })
    }

    fn lookup_local(&self, name: &str) -> Option<LocalId> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }

    fn declare_params(&mut self, list: Option<ast::ParamList>, tys: &[Ty]) {
        let Some(list) = list else { return };
        let named = list.params().filter_map(|p| p.name());
        for (i, name) in named.enumerate() {
            let ty = tys.get(i).cloned().unwrap_or(Ty::Unknown);
            self.declare(&name, ty, LocalKind::Param);
        }
    }

    // ---- 类型 ----

    fn lower_ty(&self, ty: &ast::Type) -> Ty {
        self.lower_ref(&lower_type(ty))
    }

    /// 局部变量的类型要从初值推断：`var`，或者 Lombok 的 `val` / `var`（`lombok.val` 相当于 `final var`）。
    fn is_inferred_local_type(&self, ty: &ast::Type) -> bool {
        let type_ref = lower_type(ty);
        if type_ref.is_var() {
            return true;
        }
        let hir_def::TypeRef::Path(segments) = &type_ref else {
            return false;
        };
        if !matches!(
            segments.last().map(|s| s.name.as_str()),
            Some("val" | "var")
        ) {
            return false;
        }
        matches!(self.lower_ref(&type_ref), Ty::Class(class, _)
            if matches!(class.binary_name(self.db).as_str(), "lombok/val" | "lombok/var"))
    }

    fn lower_ref(&self, type_ref: &hir_def::TypeRef) -> Ty {
        // 匿名类 / 局部类的类体里，简单名可以指向从父类型继承来的成员类型
        if self.frames.len() > 1 {
            if let hir_def::TypeRef::Path(segments) = type_ref {
                if let [segment] = segments.as_slice() {
                    let inherited = self
                        .frames
                        .iter()
                        .skip(1)
                        .rev()
                        .find_map(|frame| match &frame.this_ty {
                            Ty::Class(class, _) => {
                                hir_def::member_type(self.db, *class, &segment.name)
                            }
                            _ => None,
                        });
                    if let (Some(class), true) = (inherited, segment.args.is_empty()) {
                        return Ty::class(class);
                    }
                }
            }
        }
        lower_type_ref(self.db, &self.scope, type_ref)
    }

    fn this_ty(&self) -> Ty {
        self.frames
            .last()
            .map_or(Ty::Unknown, |f| f.this_ty.clone())
    }

    fn super_ty(&self) -> Ty {
        // 匿名类 / 枚举常量的类体：这一层记录的 `this` 类型就是它的父类型
        if self.frames.last().is_some_and(|f| f.anonymous) {
            return self.this_ty();
        }
        match self.this_ty() {
            Ty::Class(class, args) => {
                let subst = crate::ty::Subst::for_class(self.db, class, &args);
                let first = class_supertypes(self.db, class).first().cloned();
                let is_superclass = |ty: &Ty| {
                    ty.as_class()
                        .and_then(|c| hir_def::class_header(self.db, c))
                        .is_some_and(|data| !data.is_interface())
                };
                match first {
                    Some(sup) if is_superclass(&sup) => sup.subst(&subst),
                    // 写了 `extends X` 但 X 解析不了（类路径缺了它）：父类不知道，不能当成 `Object`
                    _ if hir_def::class_header(self.db, class)
                        .is_some_and(|data| data.superclass.is_some() && !data.is_interface()) =>
                    {
                        Ty::Unknown
                    }
                    Some(sup) => sup.subst(&subst),
                    None => Ty::object(self.db),
                }
            }
            _ => Ty::Unknown,
        }
    }

    /// `for (T x : iterable)` 里元素的类型。
    fn iterable_element(&self, iterable: &Ty) -> Ty {
        match iterable {
            Ty::Array(element) => (**element).clone(),
            Ty::Unknown => Ty::Unknown,
            _ => {
                let Some(iterable_class) = hir_def::lookup_class(self.db, "java/lang/Iterable")
                else {
                    return Ty::Unknown;
                };
                // 先做近似捕获：`ParameterList<?>`（`T extends Description`）的元素是 `Description`
                let captured = crate::ty::Subst::capture_receiver(self.db, iterable);
                match find_super(self.db, &captured, iterable_class) {
                    Some(found) => match found.type_args().first() {
                        Some(arg) => arg.upper_bound(self.db),
                        // 原始类型的 Iterable：元素是 Object
                        None => Ty::object(self.db),
                    },
                    None => Ty::Unknown,
                }
            }
        }
    }

    // ---- 诊断 ----

    fn diagnostic(&mut self, range: TextRange, kind: InferDiagnosticKind) {
        self.result
            .diagnostics
            .push(InferDiagnostic { range, kind });
    }

    /// "简单"类型：基本类型或非泛型类。类型检查只对两边都简单的情形下结论。
    pub(crate) fn is_simple_ty(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Primitive(_) => true,
            Ty::Class(class, args) => {
                args.is_empty()
                    && class_header(self.db, *class).is_some_and(|d| d.type_params.is_empty())
            }
            _ => false,
        }
    }

    /// 推断条件表达式，类型确定不是 boolean 时报错。
    pub(crate) fn infer_condition(&mut self, cond: &ast::Expr) {
        let ty = self.infer_expr(cond, Some(&Ty::BOOLEAN));
        let definite = matches!(
            cond,
            ast::Expr::Literal(_)
                | ast::Expr::NameExpr(_)
                | ast::Expr::FieldAccess(_)
                | ast::Expr::MethodCall(_)
                | ast::Expr::NewExpr(_)
                | ast::Expr::BinaryExpr(_)
        );
        if definite
            && self.is_simple_ty(&ty)
            && ty.unboxed(self.db) != Some(hir_def::PrimitiveType::Boolean)
        {
            self.diagnostic(
                cond.syntax().text_range(),
                InferDiagnosticKind::TypeMismatch {
                    expected: Ty::BOOLEAN.display(self.db),
                    actual: ty.display(self.db),
                },
            );
        }
    }

    /// 只在两边类型都完全确定、且都是"简单"类型（基本类型或非泛型类）时才报类型不匹配。
    #[inline(never)]
    fn check_assignable(&mut self, range: TextRange, from: &Ty, to: &Ty, expr: &ast::Expr) {
        // lambda 的"类型"就是目标类型，要检查的是它和目标函数式接口的形状、返回类型
        if let ast::Expr::LambdaExpr(lambda) = expr {
            self.check_lambda(lambda, to);
            return;
        }
        let mut inner = expr.clone();
        while let ast::Expr::ParenExpr(paren) = &inner {
            match paren.expr() {
                Some(e) => inner = e,
                None => return,
            }
        }
        if let ast::Expr::ConditionalExpr(cond) = &inner {
            self.check_conditional_assignable(range, cond, from, to);
            return;
        }
        // `int x = voidMethod();`
        if matches!(from, Ty::Void)
            && matches!(expr, ast::Expr::MethodCall(_))
            && !to.contains_unknown()
            && !matches!(to, Ty::Void)
        {
            self.diagnostic(
                range,
                InferDiagnosticKind::TypeMismatch {
                    expected: to.display(self.db),
                    actual: from.display(self.db),
                },
            );
            return;
        }
        // `T t = 1;`、`return "x";`（返回类型是 `T`）：具体类型的值不是任何类型变量的子类型
        if let Ty::TypeParam(param) = to {
            let concrete = from.is_primitive()
                || self.is_simple_ty(from)
                    && from
                        .as_class()
                        .is_some_and(|class| class.binary_name(self.db) != "java/lang/Object");
            let certain = concrete
                && !self.suppress_unresolved
                && self.type_param_in_scope(*param)
                && self.has_target_free_type(expr);
            if certain || self.generic_mismatch(from, to, expr) {
                self.diagnostic(
                    range,
                    InferDiagnosticKind::TypeMismatch {
                        expected: to.display(self.db),
                        actual: from.display(self.db),
                    },
                );
            }
            return;
        }
        if !self.is_simple_ty(from) || !self.is_simple_ty(to) {
            // 带类型实参的类型只在 `new Foo<A>(..)`（写明了类型实参，不是菱形、不是匿名类）
            // 赋给已知的参数化类型时检查：这时两边都不依赖推断
            let explicit_new =
                matches!(expr, ast::Expr::NewExpr(new) if has_explicit_type_args(new));
            let known = |ty: &Ty| {
                matches!(ty, Ty::Class(..))
                    && !ty.contains_unknown()
                    && !crate::method_resolution::mentions_type_param(ty)
            };
            // 一边是非泛型类型（或基本类型）、另一边是已知的类类型时，能不能赋值只看擦除后的类
            // （非泛型类的超类型都是确定的）：`String s = names;`、`List<String> l = "x";`。
            // 值的类型必须是声明出来的，不能来自可能依赖目标类型的推断
            let declared = expr::has_declared_type(expr)
                || matches!(expr, ast::Expr::Literal(_) | ast::Expr::BinaryExpr(_))
                || self.is_non_generic_call(expr);
            let one_side_simple =
                (self.is_simple_ty(from) && known(to)) || (self.is_simple_ty(to) && known(from));
            let certain = explicit_new && known(from) && known(to) || declared && one_side_simple;
            if certain && !is_assignable(self.db, from, to) || self.generic_mismatch(from, to, expr)
            {
                self.diagnostic(
                    range,
                    InferDiagnosticKind::TypeMismatch {
                        expected: to.display(self.db),
                        actual: from.display(self.db),
                    },
                );
            }
            return;
        }
        if is_assignable(self.db, from, to) {
            return;
        }
        // 整型常量表达式可以隐式收窄到 byte / short / char（及其包装类），这里不做常量求值，直接放过
        let from_small_int = matches!(
            from.as_primitive(),
            Some(
                hir_def::PrimitiveType::Int
                    | hir_def::PrimitiveType::Short
                    | hir_def::PrimitiveType::Char
                    | hir_def::PrimitiveType::Byte
            )
        );
        let to_small_int = matches!(
            to.unboxed(self.db),
            Some(
                hir_def::PrimitiveType::Byte
                    | hir_def::PrimitiveType::Short
                    | hir_def::PrimitiveType::Char
            )
        );
        if from_small_int && to_small_int {
            // 只有常量表达式的值在范围内时才能这样收窄：字面量看值，其它表达式确定不是常量才报
            let lossy = !self.suppress_unresolved
                && match (int_literal_value(expr), to.unboxed(self.db)) {
                    (Some(value), Some(target)) => !int_fits(value, target),
                    // 方法调用的类型要确定（重载决议不影响返回类型）
                    _ => {
                        self.certainly_not_constant(expr)
                            && (!matches!(expr, ast::Expr::MethodCall(_))
                                || self.is_certain_call(expr))
                    }
                };
            if lossy {
                self.diagnostic(
                    range,
                    InferDiagnosticKind::TypeMismatch {
                        expected: to.display(self.db),
                        actual: from.display(self.db),
                    },
                );
            }
            return;
        }
        // lambda、方法引用、switch、条件表达式等的类型取决于上下文，不在这里判断
        if !matches!(
            expr,
            ast::Expr::Literal(_)
                | ast::Expr::NameExpr(_)
                | ast::Expr::FieldAccess(_)
                | ast::Expr::MethodCall(_)
                | ast::Expr::NewExpr(_)
                | ast::Expr::BinaryExpr(_)
                | ast::Expr::CastExpr(_)
                | ast::Expr::ArrayAccess(_)
        ) {
            return;
        }
        self.diagnostic(
            range,
            InferDiagnosticKind::TypeMismatch {
                expected: to.display(self.db),
                actual: from.display(self.db),
            },
        );
    }

    /// 涉及参数化类型、类型变量或数组的赋值确定不兼容（`List<Object> xs = strings;`、
    /// `List<? extends Number> ns = strings;`、`String s = t;`）：值的类型不依赖推断，
    /// 两边都没有原始类型，按子类型和类型实参的包含关系判断。
    pub(crate) fn generic_mismatch(&self, from: &Ty, to: &Ty, expr: &ast::Expr) -> bool {
        if self.suppress_unresolved || self.target_uncertain || !self.type_is_certain(expr) {
            return false;
        }
        self.certainly_incompatible(from, to)
    }

    /// `from` 确定不能赋给 `to`（见 [`crate::subtype::Incompatibility`]）。类型变量只认当前
    /// 作用域里的，类的层次结构要可靠。
    pub(crate) fn certainly_incompatible(&self, from: &Ty, to: &Ty) -> bool {
        let reliable = |class: ClassId| self.hierarchy_is_reliable(class);
        let in_scope = |param: TypeParamId| self.type_param_in_scope(param);
        crate::subtype::Incompatibility::new(self.db, &reliable, &in_scope).not_assignable(from, to)
    }

    /// 类型变量属于当前方法，或者当前类及其外层类（不是某个函数式接口等别处的类型参数）。
    fn type_param_in_scope(&self, param: TypeParamId) -> bool {
        match param.owner {
            hir_def::GenericOwner::Method(method) => self.scope.method == Some(method),
            hir_def::GenericOwner::Class(owner) => {
                // 局部类 / 匿名类的类体里从它自己开始往外找
                let mut class = self.scope.class.or(Some(self.class));
                while let Some(current) = class {
                    if current == owner {
                        return true;
                    }
                    class = self.outer_class(current);
                }
                false
            }
        }
    }

    /// 条件表达式赋给 `to`（JLS §15.25）：数值 / boolean 条件表达式是独立表达式，按合并后的
    /// 类型检查；引用条件表达式的两个分支各自要能赋给目标类型。
    fn check_conditional_assignable(
        &mut self,
        range: TextRange,
        cond: &ast::ConditionalExpr,
        merged: &Ty,
        to: &Ty,
    ) {
        use hir_def::PrimitiveType as P;
        let db = self.db;
        let (Some(then), Some(otherwise)) = (cond.then_expr(), cond.else_expr()) else {
            return;
        };
        let ty_of =
            |this: &Self, e: &ast::Expr| this.result.type_of(e.syntax().text_range()).cloned();
        let (Some(a), Some(b)) = (ty_of(self, &then), ty_of(self, &otherwise)) else {
            return;
        };
        let numeric = |ty: &Ty| ty.unboxed(db).is_some_and(|p| p.is_numeric());
        let boolean = |ty: &Ty| ty.unboxed(db) == Some(P::Boolean);
        let both_numeric = numeric(&a) && numeric(&b);
        if both_numeric || (boolean(&a) && boolean(&b)) {
            if !self.is_simple_ty(merged) || !self.is_simple_ty(to) || is_assignable(db, merged, to)
            {
                return;
            }
            // 整型常量可以收窄（`char c = f ? 'a' : 0` 的类型是 char），只对确定的情形下结论：
            // 目标类型不是数值，或者是基本类型而值是 long / float / double
            let report = match to.unboxed(db) {
                None | Some(P::Boolean) => true,
                Some(_) => {
                    !both_numeric
                        || to.is_primitive()
                            && matches!(merged.as_primitive(), Some(P::Long | P::Float | P::Double))
                }
            };
            if report {
                self.diagnostic(
                    range,
                    InferDiagnosticKind::TypeMismatch {
                        expected: to.display(db),
                        actual: merged.display(db),
                    },
                );
            }
            return;
        }
        for (branch, ty) in [(then, a), (otherwise, b)] {
            self.check_assignable(branch.syntax().text_range(), &ty, to, &branch);
        }
    }

    /// 表达式确定不是编译期常量（JLS §15.29）：含方法调用、数组访问、自增自减、赋值，或者
    /// 引用了形参、没有 `final` 的局部变量、非 final 字段。
    fn certainly_not_constant(&self, expr: &ast::Expr) -> bool {
        let any = |exprs: Vec<ast::Expr>| exprs.iter().any(|e| self.certainly_not_constant(e));
        match expr {
            ast::Expr::MethodCall(_)
            | ast::Expr::ArrayAccess(_)
            | ast::Expr::AssignExpr(_)
            | ast::Expr::PostfixExpr(_) => true,
            ast::Expr::ParenExpr(it) => any(it.expr().into_iter().collect()),
            ast::Expr::CastExpr(it) => any(it.expr().into_iter().collect()),
            ast::Expr::UnaryExpr(it) => {
                it.op_token().is_some_and(|op| {
                    matches!(
                        op.kind(),
                        syntax::SyntaxKind::PLUS_PLUS | syntax::SyntaxKind::MINUS_MINUS
                    )
                }) || any(it.operand().into_iter().collect())
            }
            ast::Expr::BinaryExpr(it) => any(it.lhs().into_iter().chain(it.rhs()).collect()),
            ast::Expr::ConditionalExpr(it) => any(it
                .condition()
                .into_iter()
                .chain(it.then_expr())
                .chain(it.else_expr())
                .collect()),
            ast::Expr::NameExpr(it) => it
                .name_ref()
                .is_some_and(|name| self.names_non_constant(name.syntax().text_range(), expr)),
            ast::Expr::FieldAccess(it) => it
                .name_ref()
                .is_some_and(|name| self.names_non_constant(name.syntax().text_range(), expr)),
            _ => false,
        }
    }

    /// 名字引用指向的变量确定不是常量变量。
    fn names_non_constant(&self, name_range: TextRange, expr: &ast::Expr) -> bool {
        match self.result.resolution(name_range) {
            Some(Resolution::ArrayLength) => true,
            Some(Resolution::Field(field)) => {
                crate::lower::field_flags(self.db, *field).is_some_and(|flags| !flags.is_final())
            }
            Some(Resolution::Local(local)) => {
                let data = &self.result.locals[*local as usize];
                match data.kind {
                    LocalKind::Local => {
                        // 声明处的修饰符里没有 `final`
                        let root = expr.syntax().ancestors().last();
                        let decl = root.and_then(|root| {
                            root.covering_element(data.decl_range)
                                .ancestors()
                                .find(|n| n.kind() == syntax::SyntaxKind::LOCAL_VAR_DECL)
                        });
                        decl.is_some_and(|decl| {
                            !decl
                                .children()
                                .find_map(ast::ModifierList::cast)
                                .is_some_and(|list| list.has(syntax::SyntaxKind::FINAL_KW))
                        })
                    }
                    LocalKind::Param
                    | LocalKind::LambdaParam
                    | LocalKind::CatchParam
                    | LocalKind::Pattern
                    | LocalKind::Resource
                    | LocalKind::ForeachVar => true,
                    LocalKind::LocalClassField | LocalKind::LocalClassMethod => false,
                }
            }
            _ => false,
        }
    }

    /// 调用的是没有自己类型参数的方法：返回类型只由接收者决定，不依赖目标类型。
    fn is_non_generic_call(&self, expr: &ast::Expr) -> bool {
        let ast::Expr::MethodCall(call) = expr else {
            return false;
        };
        let Some(name) = call.name_ref() else {
            return false;
        };
        match self.result.resolution(name.syntax().text_range()) {
            Some(Resolution::Method(method)) => method_sig(self.db, *method).n_type_params == 0,
            _ => false,
        }
    }

    /// `throw` 的值确定不是 `Throwable`（`throw "x"`、`throw new Object()`）。
    fn check_throwable(&mut self, expr: &ast::Expr, ty: &Ty) {
        if self.suppress_unresolved || !self.has_target_free_type(expr) {
            return;
        }
        let Some(throwable) = hir_def::lookup_class(self.db, "java/lang/Throwable") else {
            return;
        };
        let wrong = match ty {
            Ty::Primitive(_) => true,
            Ty::Class(..) => self.reliable_class(ty).is_some_and(|class| {
                !is_assignable(self.db, &Ty::class(class), &Ty::class(throwable))
            }),
            _ => false,
        };
        if wrong {
            self.diagnostic(
                expr.syntax().text_range(),
                InferDiagnosticKind::TypeMismatch {
                    expected: Ty::class(throwable).display(self.db),
                    actual: ty.display(self.db),
                },
            );
        }
    }

    /// 增强 for 遍历的值确定既不是数组也不是 `Iterable`（`for (String s : "abc")`）。
    fn check_iterable(&mut self, expr: &ast::Expr, ty: &Ty) {
        if self.suppress_unresolved || !self.has_target_free_type(expr) {
            return;
        }
        let Some(iterable) = hir_def::lookup_class(self.db, "java/lang/Iterable") else {
            return;
        };
        let wrong = match ty {
            Ty::Primitive(_) => true,
            Ty::Class(..) => self.reliable_class(ty).is_some_and(|class| {
                !is_assignable(self.db, &Ty::class(class), &Ty::class(iterable))
            }),
            _ => false,
        };
        if wrong {
            self.diagnostic(
                expr.syntax().text_range(),
                InferDiagnosticKind::NotIterable {
                    ty: ty.display(self.db),
                },
            );
        }
    }

    /// `for (int s : names)`：元素类型确定不能赋给循环变量时报错（被遍历的表达式的类型要是
    /// 声明出来的，判断方式和 `check_assignable` 里一边是非泛型类型的情形一样）。
    fn check_element_type(&mut self, iter_expr: &ast::Expr, iterable: &Ty, declared: &Ty) {
        let element = self.iterable_element(iterable);
        let known = |ty: &Ty| {
            matches!(ty, Ty::Class(..))
                && !ty.contains_unknown()
                && !crate::method_resolution::mentions_type_param(ty)
        };
        let simple = |this: &Self, ty: &Ty| this.is_simple_ty(ty);
        let certain = expr::has_declared_type(iter_expr)
            && (simple(self, &element) || known(&element))
            && (simple(self, declared) || known(declared))
            && (simple(self, &element) || simple(self, declared));
        // 元素类型是参数化类型或类型变量（`for (List<Integer> l : listsOfStrings)`）：被遍历的
        // 表达式的类型要完全确定，不是原始类型
        let generic = !self.suppress_unresolved
            && self.type_is_certain(iter_expr)
            && !self.mentions_raw(iterable)
            && self.certainly_incompatible(&element, declared);
        if certain && !is_assignable(self.db, &element, declared) || generic {
            self.diagnostic(
                iter_expr.syntax().text_range(),
                InferDiagnosticKind::TypeMismatch {
                    expected: declared.display(self.db),
                    actual: element.display(self.db),
                },
            );
        }
    }

    // ---- 语句 ----

    fn infer_block(&mut self, block: &ast::Block) {
        self.push_scope();
        for stmt in block.statements() {
            self.infer_stmt(&stmt);
        }
        self.pop_scope();
    }

    fn infer_local_var_decl(&mut self, decl: &ast::LocalVarDecl, kind: LocalKind) {
        let ty_node = decl.ty();
        let is_var = ty_node
            .as_ref()
            .is_some_and(|t| self.is_inferred_local_type(t));
        let base = match &ty_node {
            Some(t) if !is_var => self.lower_ty(t),
            _ => Ty::Unknown,
        };
        // 真正的 `var`（不是 Lombok 的 `val` / `var`）
        let java_var = ty_node.as_ref().is_some_and(|t| lower_type(t).is_var());
        let n_declarators = decl.declarators().count();
        for declarator in decl.declarators() {
            if java_var {
                self.check_var_declarator(&declarator, n_declarators);
            }
            let mut declared = base.clone();
            for _ in 0..declarator.extra_dims() {
                declared = Ty::array(declared);
            }
            let mut ty = declared.clone();
            let mut init_certain = false;
            if let Some(init) = declarator.initializer() {
                let expected = if is_var { None } else { Some(&declared) };
                self.declared_target = !is_var;
                if is_var {
                    self.no_target_expr = Some(init.syntax().text_range());
                }
                let actual = self.infer_expr(&init, expected);
                if is_var {
                    init_certain = self.type_is_certain(&init);
                    // `var x = new T() { ... }`：变量的类型是匿名类本身；没有登记成类的匿名类
                    // 表示不出来，按未知处理，避免把 `x.ownMember` 报成找不到
                    let anonymous = match &init {
                        ast::Expr::NewExpr(new) => new.body().map(|body| self.class_of_body(&body)),
                        _ => None,
                    };
                    if java_var
                        && actual == Ty::Void
                        && matches!(init, ast::Expr::MethodCall(_))
                        && n_declarators == 1
                    {
                        if let Some(name) = declarator.name() {
                            self.diagnostic(
                                name.syntax().text_range(),
                                InferDiagnosticKind::CannotInferVar {
                                    name: name.text(),
                                    reason: base_db::tr!(
                                        "初始值是 void",
                                        "variable initializer is 'void'"
                                    ),
                                },
                            );
                        }
                    }
                    ty = match (actual, anonymous) {
                        (Ty::Null | Ty::Void, _) => Ty::Unknown,
                        (_, Some(Some(class))) => this_ty(self.db, class),
                        (_, Some(None)) => Ty::Unknown,
                        (other, None) => other,
                    };
                } else {
                    self.check_assignable(init.syntax().text_range(), &actual, &declared, &init);
                }
            }
            if let Some(name) = declarator.name() {
                let id = self.declare(&name, ty, kind);
                if is_var && !init_certain {
                    self.uncertain_locals.insert(id);
                }
            }
        }
    }

    /// `var` 声明的局部变量推不出类型的写法（JLS §14.4.1）。
    fn check_var_declarator(&mut self, declarator: &ast::VariableDeclarator, n_declarators: usize) {
        let Some(name) = declarator.name() else {
            return;
        };
        let init = declarator.initializer();
        let reason = if n_declarators > 1 {
            base_db::tr!(
                "`var` 不能用在声明多个变量的语句里",
                "'var' is not allowed in a compound declaration"
            )
        } else if declarator.extra_dims() > 0 {
            base_db::tr!(
                "`var` 声明的变量不能带数组维度",
                "'var' is not allowed as an element type of an array"
            )
        } else {
            match &init {
                None => base_db::tr!("没有初始值", "variable has no initializer"),
                Some(ast::Expr::Literal(lit))
                    if lit.kind() == Some(syntax::SyntaxKind::NULL_KW) =>
                {
                    base_db::tr!("初始值是 null", "variable initializer is 'null'")
                }
                Some(ast::Expr::ArrayInitializer(_)) => base_db::tr!(
                    "数组初始化器需要明确的目标类型",
                    "array initializer needs an explicit target type"
                ),
                Some(ast::Expr::LambdaExpr(_)) => base_db::tr!(
                    "lambda 表达式需要明确的目标类型",
                    "lambda expression needs an explicit target type"
                ),
                Some(ast::Expr::MethodRef(_)) => base_db::tr!(
                    "方法引用需要明确的目标类型",
                    "method reference needs an explicit target type"
                ),
                _ => return,
            }
        };
        self.diagnostic(
            name.syntax().text_range(),
            InferDiagnosticKind::CannotInferVar {
                name: name.text(),
                reason,
            },
        );
    }

    fn infer_stmt(&mut self, stmt: &ast::Stmt) {
        match stmt {
            ast::Stmt::Block(block) => self.infer_block(block),
            ast::Stmt::LocalVarDecl(decl) => self.infer_local_var_decl(decl, LocalKind::Local),
            ast::Stmt::ExprStmt(it) => {
                if let Some(expr) = it.expr() {
                    self.infer_expr(&expr, None);
                }
            }
            ast::Stmt::IfStmt(it) => {
                if let Some(cond) = it.condition() {
                    self.infer_condition(&cond);
                }
                if let Some(then) = it.then_branch() {
                    self.infer_stmt(&then);
                }
                if let Some(otherwise) = it.else_branch() {
                    self.infer_stmt(&otherwise);
                }
            }
            ast::Stmt::WhileStmt(it) => {
                if let Some(cond) = it.condition() {
                    self.infer_condition(&cond);
                }
                if let Some(body) = it.body() {
                    self.infer_stmt(&body);
                }
            }
            ast::Stmt::DoWhileStmt(it) => {
                if let Some(body) = it.body() {
                    self.infer_stmt(&body);
                }
                if let Some(cond) = it.condition() {
                    self.infer_condition(&cond);
                }
            }
            ast::Stmt::ForStmt(it) => {
                self.push_scope();
                if let Some(init) = it.init() {
                    if let Some(decl) = init.local_var_decl() {
                        self.infer_local_var_decl(&decl, LocalKind::Local);
                    } else {
                        for expr in init.exprs() {
                            self.infer_expr(&expr, None);
                        }
                    }
                }
                if let Some(cond) = it.condition() {
                    self.infer_condition(&cond);
                }
                if let Some(update) = it.update() {
                    for expr in update.exprs() {
                        self.infer_expr(&expr, None);
                    }
                }
                if let Some(body) = it.body() {
                    self.infer_stmt(&body);
                }
                self.pop_scope();
            }
            ast::Stmt::ForeachStmt(it) => {
                self.push_scope();
                let iterable = it
                    .iterable()
                    .map_or(Ty::Unknown, |e| self.infer_expr(&e, None));
                if let Some(iter_expr) = it.iterable() {
                    self.check_iterable(&iter_expr, &iterable);
                }
                if let Some(param) = it.param() {
                    let ty = match param.ty() {
                        Some(t) if !self.is_inferred_local_type(&t) => {
                            let declared = self.lower_ty(&t);
                            if let Some(iter_expr) = it.iterable() {
                                self.check_element_type(&iter_expr, &iterable, &declared);
                            }
                            declared
                        }
                        _ => self.iterable_element(&iterable),
                    };
                    let inferred = param.ty().is_none_or(|t| self.is_inferred_local_type(&t));
                    if let Some(name) = param.name() {
                        let id = self.declare(&name, ty, LocalKind::ForeachVar);
                        if inferred {
                            self.uncertain_locals.insert(id);
                        }
                    }
                }
                if let Some(body) = it.body() {
                    self.infer_stmt(&body);
                }
                self.pop_scope();
            }
            ast::Stmt::ReturnStmt(it) => {
                if let Some(expr) = it.expr() {
                    let expected = self.ret_expected.last().cloned().flatten();
                    // 方法体（不是 lambda）里的 return：期望类型是声明的返回类型
                    self.declared_target = self.return_tys.is_empty();
                    let ty = self.infer_expr(&expr, expected.as_ref());
                    if let Some(returns) = self.return_tys.last_mut() {
                        returns.push(ty);
                    } else if let Some(expected) = &expected {
                        self.check_assignable(expr.syntax().text_range(), &ty, expected, &expr);
                    }
                }
            }
            ast::Stmt::ThrowStmt(it) => {
                if let Some(expr) = it.expr() {
                    let ty = self.infer_expr(&expr, None);
                    self.check_throwable(&expr, &ty);
                }
            }
            ast::Stmt::YieldStmt(it) => {
                if let Some(expr) = it.expr() {
                    let ty = self.infer_expr(&expr, None);
                    if let Some(yields) = self.yield_tys.last_mut() {
                        yields.push(ty);
                    }
                }
            }
            ast::Stmt::AssertStmt(it) => {
                if let Some(cond) = it.condition() {
                    self.infer_condition(&cond);
                }
                if let Some(message) = it.message() {
                    self.infer_expr(&message, None);
                }
            }
            ast::Stmt::SynchronizedStmt(it) => {
                if let Some(lock) = it.lock() {
                    self.infer_expr(&lock, None);
                }
                if let Some(body) = it.body() {
                    self.infer_block(&body);
                }
            }
            ast::Stmt::TryStmt(it) => {
                self.push_scope();
                if let Some(resources) = it.resource_list() {
                    for resource in resources.resources() {
                        self.infer_resource(&resource);
                    }
                }
                if let Some(body) = it.body() {
                    self.infer_block(&body);
                }
                self.pop_scope();
                for catch in it.catch_clauses() {
                    self.push_scope();
                    if let Some(param) = catch.param() {
                        let ty = match param.ty() {
                            // 多重 catch 的形参按各备选的最小上界算（成员、可赋值性都由它决定）；
                            // 算不出单个类型（交集）时照旧用第一个备选，它的成员和重载多半也对
                            Some(ast::Type::UnionType(union)) => {
                                let alternatives: Vec<Ty> =
                                    union.types().map(|t| self.lower_ty(&t)).collect();
                                let lub = lub(self.db, &alternatives);
                                if lub.is_unknown() || matches!(lub, Ty::Intersection(_)) {
                                    alternatives.into_iter().next().unwrap_or(Ty::Unknown)
                                } else {
                                    lub
                                }
                            }
                            Some(t) => self.lower_ty(&t),
                            None => Ty::Unknown,
                        };
                        if let Some(name) = param.name() {
                            let id = self.declare(&name, ty, LocalKind::CatchParam);
                            self.uncertain_locals.insert(id);
                        }
                    }
                    if let Some(body) = catch.body() {
                        self.infer_block(&body);
                    }
                    self.pop_scope();
                }
                if let Some(body) = it.finally_clause().and_then(|f| f.body()) {
                    self.infer_block(&body);
                }
            }
            ast::Stmt::SwitchStmt(it) => {
                let scrutinee = it
                    .scrutinee()
                    .map_or(Ty::Unknown, |e| self.infer_expr(&e, None));
                if let Some(block) = it.block() {
                    self.infer_switch_block(&block, &scrutinee, false);
                }
            }
            ast::Stmt::LabeledStmt(it) => {
                if let Some(body) = it.body() {
                    self.infer_stmt(&body);
                }
            }
            ast::Stmt::BreakStmt(_) | ast::Stmt::ContinueStmt(_) | ast::Stmt::EmptyStmt(_) => {}
            // 局部类：它是一个真正的类（有 `ClassId`），成员仍在所属的体里就地推断，
            // 这样能看到外层的局部变量
            ast::Stmt::ClassDecl(_)
            | ast::Stmt::InterfaceDecl(_)
            | ast::Stmt::EnumDecl(_)
            | ast::Stmt::RecordDecl(_) => {
                if let Some(body) =
                    ast::TypeDecl::cast(stmt.syntax().clone()).and_then(|decl| decl.body())
                {
                    self.infer_class_body(&body, Ty::Unknown);
                }
            }
        }
    }

    fn infer_resource(&mut self, resource: &ast::Resource) {
        if let Some(declarator) = resource.declarator() {
            let ty_node = resource.ty();
            let is_var = ty_node
                .as_ref()
                .is_some_and(|t| self.is_inferred_local_type(t));
            let declared = match &ty_node {
                Some(t) if !is_var => self.lower_ty(t),
                _ => Ty::Unknown,
            };
            let mut ty = declared.clone();
            if let Some(init) = declarator.initializer() {
                let actual = self.infer_expr(&init, if is_var { None } else { Some(&declared) });
                if is_var {
                    ty = actual;
                }
            }
            if let Some(name) = declarator.name() {
                let id = self.declare(&name, ty, LocalKind::Resource);
                if is_var {
                    self.uncertain_locals.insert(id);
                }
            }
        } else if let Some(expr) = resource.expr() {
            self.infer_expr(&expr, None);
        }
    }

    /// `is_expr` 为真时收集各分支的结果类型（压在 `yield_tys` 栈顶）。
    fn infer_switch_block(&mut self, block: &ast::SwitchBlock, scrutinee: &Ty, is_expr: bool) {
        // 旧式 `case X:` 的各组语句同属一个块：前面分支里声明的变量后面还能用
        let shared_scope = block.cases().any(|case| !case.is_arrow());
        if shared_scope {
            self.push_scope();
        }
        for case in block.cases() {
            if !shared_scope {
                self.push_scope();
            }
            if let Some(label) = case.label() {
                for expr in label.exprs() {
                    self.infer_case_constant(&expr, scrutinee);
                }
                for pattern in label.patterns() {
                    self.bind_pattern(&pattern, scrutinee);
                }
                if let Some(guard) = label.guard().and_then(|g| g.expr()) {
                    self.infer_expr(&guard, Some(&Ty::BOOLEAN));
                }
            }
            let is_arrow = case.is_arrow();
            for stmt in case.statements() {
                match &stmt {
                    // `case X -> expr;`：表达式的值就是该分支的结果
                    ast::Stmt::ExprStmt(it) if is_arrow && is_expr => {
                        if let Some(expr) = it.expr() {
                            let ty = self.infer_expr(&expr, None);
                            if let Some(yields) = self.yield_tys.last_mut() {
                                yields.push(ty);
                            }
                        }
                    }
                    _ => self.infer_stmt(&stmt),
                }
            }
            if !shared_scope {
                self.pop_scope();
            }
        }
        if shared_scope {
            self.pop_scope();
        }
    }

    /// `case RED:` 里的枚举常量按被匹配表达式的类型解析，不需要限定。
    fn infer_case_constant(&mut self, expr: &ast::Expr, scrutinee: &Ty) {
        if let (ast::Expr::NameExpr(name_expr), Ty::Class(class, _)) = (expr, scrutinee) {
            let is_enum =
                class_header(self.db, *class).is_some_and(|d| d.kind == hir_def::ClassKind::Enum);
            if let (true, Some(name_ref)) = (is_enum, name_expr.name_ref()) {
                if let Some(field) =
                    crate::members::lookup_field(self.db, scrutinee, &name_ref.text())
                {
                    let range = name_ref.syntax().text_range();
                    self.result
                        .resolutions
                        .insert(range, Resolution::Field(field.id));
                    self.result
                        .expr_types
                        .insert(expr.syntax().text_range(), field.ty);
                    return;
                }
            }
        }
        let actual = self.infer_expr(expr, Some(scrutinee));
        // `case "a":` 用在 int 的 switch 上
        let constant_switch = scrutinee
            .unboxed(self.db)
            .is_some_and(|p| p != hir_def::PrimitiveType::Boolean)
            || matches!(scrutinee, Ty::Class(class, _)
                if class.binary_name(self.db) == "java/lang/String");
        if constant_switch {
            self.check_assignable(expr.syntax().text_range(), &actual, scrutinee, expr);
        }
    }

    /// 给模式里的绑定变量定型。`matched` 是被匹配值的类型。
    fn bind_pattern(&mut self, pattern: &ast::Pattern, matched: &Ty) {
        match pattern {
            ast::Pattern::TypePattern(it) => {
                let (ty, inferred) = match it.ty() {
                    Some(t) if !lower_type(&t).is_var() => (self.lower_ty(&t), false),
                    _ => (matched.clone(), true),
                };
                if let Some(name) = it.name() {
                    if name.text() != "_" {
                        let id = self.declare(&name, ty, LocalKind::Pattern);
                        if inferred {
                            self.uncertain_locals.insert(id);
                        }
                    }
                }
            }
            ast::Pattern::RecordPattern(it) => {
                let record_ty = it.ty().map_or(Ty::Unknown, |t| self.lower_ty(&t));
                // 记录组件 = 该类按声明顺序的实例字段
                let components: Vec<Ty> = match &record_ty {
                    Ty::Class(class, args) => {
                        let subst = crate::ty::Subst::for_class(self.db, *class, args);
                        class_data(self.db, *class)
                            .map(|data| {
                                data.fields
                                    .iter()
                                    .enumerate()
                                    .filter(|(_, f)| !f.flags.is_static())
                                    .map(|(idx, _)| {
                                        field_ty(
                                            self.db,
                                            FieldId {
                                                class: *class,
                                                idx: idx as u32,
                                            },
                                        )
                                        .subst(&subst)
                                    })
                                    .collect()
                            })
                            .unwrap_or_default()
                    }
                    _ => Vec::new(),
                };
                for (i, sub) in it.patterns().enumerate() {
                    let component = components.get(i).cloned().unwrap_or(Ty::Unknown);
                    self.bind_pattern(&sub, &component);
                }
            }
            ast::Pattern::UnnamedPattern(_) => {}
        }
    }

    /// 体里的类（局部类、它的成员类和匿名类）的声明节点对应的类。
    fn declared_class(&self, decl: &SyntaxNode) -> Option<ClassId> {
        let file = self.scope.file?;
        let idx = self.source.decl_idx(decl)?;
        let binary_name = hir_def::class_at_decl(self.db, self.source.file, idx)?;
        Some(hir_def::class_in_file(self.db, file, &binary_name))
    }

    /// 类体所属的类：类型声明的类体，或者登记成类的匿名类的类体。
    pub(crate) fn class_of_body(&self, body: &ast::ClassBody) -> Option<ClassId> {
        let parent = body.syntax().parent()?;
        if ast::TypeDecl::can_cast(parent.kind()) {
            self.declared_class(&parent)
        } else {
            self.declared_class(body.syntax())
        }
    }

    /// 局部类 / 匿名类里声明的方法或构造器。
    fn declared_method(&self, class: ClassId, decl: &SyntaxNode) -> Option<MethodId> {
        let idx = self.source.decl_idx(decl)?;
        let data = class_data(self.db, class)?;
        let pos = data.methods.iter().position(|m| m.decl == Some(idx))?;
        Some(MethodId {
            class,
            idx: pos as u32,
        })
    }

    /// 匿名类 / 局部类的类体，成员在这里就地推断（能看到外层的局部变量）。
    ///
    /// 有 `ClassId` 的类：`this` 是它自己，成员按类查找，类型名按它的作用域解析。
    /// 没有登记成类的匿名类：`this` 记成父类型 `fallback_ty`，它自己声明的字段和方法登记为
    /// 局部符号，这样类体内部对它们的引用可以解析和跳转。
    fn infer_class_body(&mut self, body: &ast::ClassBody, fallback_ty: Ty) {
        let class = self.class_of_body(body);
        let (this, anonymous) = match class {
            Some(class) => (this_ty(self.db, class), false),
            None => (fallback_ty, true),
        };
        let saved_scope = self.scope;
        if let Some(class) = class {
            self.scope = TypeScope {
                file: self.scope.file,
                class: Some(class),
                method: None,
                in_class_header: false,
            };
        }
        self.frames.push(Frame {
            this_ty: this,
            anonymous,
            saved_scope,
        });
        self.frame_scope_base.push(self.scopes.len());
        self.push_scope();

        if anonymous {
            for member in body.members() {
                match &member {
                    ast::Member::FieldDecl(field) => {
                        let base = field.ty().map_or(Ty::Unknown, |t| self.lower_ty(&t));
                        for declarator in field.declarators() {
                            let mut ty = base.clone();
                            for _ in 0..declarator.extra_dims() {
                                ty = Ty::array(ty);
                            }
                            if let Some(name) = declarator.name() {
                                self.declare(&name, ty, LocalKind::LocalClassField);
                            }
                        }
                    }
                    ast::Member::MethodDecl(method) => {
                        let ret = method
                            .return_type()
                            .map_or(Ty::Unknown, |t| self.lower_ty(&t));
                        if let Some(name) = method.name() {
                            self.declare(&name, ret, LocalKind::LocalClassMethod);
                        }
                    }
                    _ => {}
                }
            }
        }

        for constant in body.enum_constants() {
            if let Some(args) = constant.arg_list() {
                for arg in args.args() {
                    self.infer_expr(&arg, None);
                }
            }
            if let Some(constant_body) = constant.body() {
                let enum_ty = class.map_or(Ty::Unknown, Ty::class);
                self.infer_class_body(&constant_body, enum_ty);
            }
        }

        for member in body.members() {
            match &member {
                ast::Member::FieldDecl(field) => {
                    let base = field.ty().map_or(Ty::Unknown, |t| self.lower_ty(&t));
                    for declarator in field.declarators() {
                        if let Some(init) = declarator.initializer() {
                            self.infer_expr(&init, Some(&base));
                        }
                    }
                }
                ast::Member::MethodDecl(method) => {
                    let id = class.and_then(|class| self.declared_method(class, method.syntax()));
                    let ret = match id {
                        Some(id) => method_sig(self.db, id).ret.clone(),
                        None => method
                            .return_type()
                            .map_or(Ty::Unknown, |t| self.lower_ty(&t)),
                    };
                    self.infer_local_function(method.param_list(), method.body(), Some(ret), id);
                }
                ast::Member::ConstructorDecl(ctor) => {
                    let id = class.and_then(|class| self.declared_method(class, ctor.syntax()));
                    self.infer_local_function(ctor.param_list(), ctor.body(), Some(Ty::Void), id);
                }
                ast::Member::InitializerBlock(init) => {
                    if let Some(block) = init.body() {
                        self.infer_block(&block);
                    }
                }
                ast::Member::ClassDecl(_)
                | ast::Member::InterfaceDecl(_)
                | ast::Member::EnumDecl(_)
                | ast::Member::RecordDecl(_)
                | ast::Member::AnnotationTypeDecl(_) => {
                    if let Some(nested) =
                        ast::TypeDecl::cast(member.syntax().clone()).and_then(|d| d.body())
                    {
                        self.infer_class_body(&nested, Ty::Unknown);
                    }
                }
            }
        }

        self.pop_scope();
        self.frame_scope_base.pop();
        if let Some(frame) = self.frames.pop() {
            self.scope = frame.saved_scope;
        }
    }

    /// 匿名类 / 局部类里的方法或构造器。`method` 是它登记在类里的方法：找得到时形参类型
    /// 取自签名，体里的类型名按这个方法的作用域解析。
    fn infer_local_function(
        &mut self,
        params: Option<ast::ParamList>,
        body: Option<ast::Block>,
        ret: Option<Ty>,
        method: Option<MethodId>,
    ) {
        let saved_scope = self.scope;
        let sig = method.map(|method| {
            self.scope.method = Some(method);
            method_sig(self.db, method)
        });
        self.push_scope();
        if let Some(params) = params {
            for (i, param) in params.params().enumerate() {
                let ty = match sig.as_ref().and_then(|sig| sig.params.get(i)) {
                    Some(ty) => ty.clone(),
                    None => self.lower_ref(&hir_def::lower_param_type(&param)),
                };
                if let Some(name) = param.name() {
                    self.declare(&name, ty, LocalKind::Param);
                }
            }
        }
        // 嵌套函数体里的 return 不属于外层 lambda
        let outer_returns = std::mem::take(&mut self.return_tys);
        self.ret_expected.push(ret);
        if let Some(body) = body {
            self.infer_block(&body);
        }
        self.ret_expected.pop();
        self.return_tys = outer_returns;
        self.pop_scope();
        self.scope = saved_scope;
    }
}
