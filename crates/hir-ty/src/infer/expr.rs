//! 表达式的推断。

use hir_def::{
    all_supers, class_header, class_source_file, lookup_class, lower_type, member_type,
    package_exists, resolve_qualified_class_from, resolve_simple_type, ClassId, GenericOwner,
    MethodId, Modifiers, PrimitiveType, TypeNs,
};
use syntax::{
    ast::{self, AstNode},
    SyntaxKind, SyntaxNode, TextRange,
};

use super::{CallInfo, InferCtx, InferDiagnosticKind, LocalKind, Resolution};
use crate::{
    lower::{class_supertypes, method_sig, this_ty},
    members::{
        constructors, functional_method, lookup_field, lookup_methods, FieldCandidate,
        MethodCandidate,
    },
    method_resolution::{certainly_violates_bounds, mentions_type_param, resolve_call, Arg, Call},
    subtype::{binary_numeric_promotion, is_subtype},
    ty::{Subst, Ty},
};

/// 表达式位置上的一个名字可能是值，也可能只是类型名或包名（作为限定符）。
pub(super) enum Value {
    Ty(Ty),
    Type(ClassId),
    /// 斜杠形式的包名
    Package(String),
}

/// `new Foo<>() { ... }`：带类体的菱形构造。
fn is_diamond_anonymous(arg: &ast::Expr) -> bool {
    let ast::Expr::NewExpr(new) = arg else {
        return false;
    };
    new.body().is_some()
        && new
            .ty()
            .is_some_and(|ty| ty.syntax().text().to_string().ends_with("<>"))
}

/// 方法引用（`Foo::bar`、`Foo::new`）在同名候选里选中的那一个：函数类型的形参个数对得上、
/// 各形参都能传进去的候选里最具体的；没有时退到形参个数对得上的，最后是第一个。
/// 函数类型未知时取第一个。`takes_receiver`：候选把函数类型的第一个形参当接收者
/// （`Type::instanceMethod`）。
fn method_ref_target<'a>(
    db: &dyn base_db::Db,
    candidates: &'a [MethodCandidate],
    fn_params: Option<&[Ty]>,
    takes_receiver: &dyn Fn(&MethodCandidate) -> bool,
) -> Option<&'a MethodCandidate> {
    let Some(params) = fn_params else {
        return candidates.first();
    };
    let shaped: Vec<(&MethodCandidate, Vec<Ty>)> = candidates
        .iter()
        .filter_map(|c| {
            let formals = c.param_tys(db);
            (formals.len() + usize::from(takes_receiver(c)) == params.len()).then_some((c, formals))
        })
        .collect();
    let applicable: Vec<&(&MethodCandidate, Vec<Ty>)> = shaped
        .iter()
        .filter(|(_, formals)| {
            params[params.len() - formals.len()..]
                .iter()
                .zip(formals)
                .all(|(actual, formal)| crate::subtype::is_assignable(db, actual, formal))
        })
        .collect();
    let more_specific = |a: &[Ty], b: &[Ty]| {
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| is_subtype(db, x, y))
    };
    applicable
        .iter()
        .find(|(_, formals)| {
            applicable
                .iter()
                .all(|(_, other)| more_specific(formals, other))
        })
        .or(applicable.first())
        .map(|(c, _)| *c)
        .or(shaped.first().map(|(c, _)| *c))
        .or(candidates.first())
}

/// 调用的结果直接作为另一次成员访问的接收者（`a.f().g()`、`a.f().x`），或者单独成句、
/// 结果不被使用（`spec.value(...);`）。
fn used_as_receiver(call: &ast::MethodCall) -> bool {
    let Some(parent) = call.syntax().parent() else {
        return false;
    };
    if parent.kind() == SyntaxKind::EXPR_STMT {
        return true;
    }
    let receiver = if let Some(outer) = ast::MethodCall::cast(parent.clone()) {
        outer.receiver()
    } else if let Some(access) = ast::FieldAccess::cast(parent) {
        access.receiver()
    } else {
        None
    };
    receiver.is_some_and(|r| r.syntax() == call.syntax())
}

/// 可以带着目标类型安全地重新推断一遍的实参：方法调用或对象创建，里面没有类体、switch 表达式
/// 和模式。lambda 可以有（形参在新的作用域里重新声明，结果覆盖第一遍的）。
fn is_retargetable(arg: &ast::Expr) -> bool {
    matches!(arg, ast::Expr::MethodCall(_) | ast::Expr::NewExpr(_))
        && !arg.syntax().descendants().any(|n| {
            matches!(
                n.kind(),
                SyntaxKind::CLASS_BODY
                    | SyntaxKind::SWITCH_EXPR
                    | SyntaxKind::TYPE_PATTERN
                    | SyntaxKind::RECORD_PATTERN
            )
        })
}

/// 实参里有 lambda：重新推断的代价随嵌套层数成倍增长，要限制层数。
fn contains_lambda(arg: &ast::Expr) -> bool {
    arg.syntax()
        .descendants()
        .any(|n| n.kind() == SyntaxKind::LAMBDA_EXPR)
}

/// 把类型实参里只给出上界的通配符（`?`、`? extends X`）换成未知，`? super X` 和具体的类型保留。
fn lower_bounds_only(ty: &Ty) -> Ty {
    match ty {
        Ty::Class(class, args) if !args.is_empty() => Ty::Class(
            *class,
            args.iter()
                .map(|arg| match arg {
                    Ty::Wildcard(crate::ty::Wildcard::Super(_)) => arg.clone(),
                    Ty::Wildcard(_) => Ty::Unknown,
                    other => lower_bounds_only(other),
                })
                .collect(),
        ),
        other => other.clone(),
    }
}

/// 带 lambda 的实参最多嵌套重新推断几层。
const MAX_LAMBDA_RETARGET_DEPTH: u32 = 3;

/// 诊断里展示的方法：`Math.abs(int)`。
fn describe_method(db: &dyn base_db::Db, method: MethodId) -> String {
    let class_name = hir_def::class_header(db, method.class)
        .map(|d| d.name.to_string())
        .unwrap_or_default();
    let name = crate::lower::method_data(db, method)
        .map(|m| m.name.to_string())
        .unwrap_or_default();
    let params: Vec<String> = method_sig(db, method)
        .params
        .iter()
        .map(|p| p.display(db))
        .collect();
    format!("{class_name}.{name}({})", params.join(", "))
}

/// 类型参数约束的种类：`T = X`、`X <: T`、`T <: X`。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Bound {
    Eq,
    Lower,
    Upper,
}

/// 形参类型 `formal` 和实参（或其一部分）`actual` 之间按 `kind` 的关系
/// （`Lower`：`actual` 可以赋给 `formal`；`Eq`：两者相同；`Upper`：`formal` 是 `actual` 的子类型）
/// 推出的、方法 `owner` 的类型参数的约束。拿不准的部分直接跳过。
fn collect_constraints(
    db: &dyn base_db::Db,
    owner: GenericOwner,
    formal: &Ty,
    actual: &Ty,
    kind: Bound,
    out: &mut Vec<(u32, Ty, Bound)>,
) {
    match formal {
        Ty::TypeParam(param) if param.owner == owner => {
            if actual.is_wildcard() || matches!(actual, Ty::Null | Ty::Unknown) {
                return;
            }
            let actual = if kind == Bound::Lower {
                actual.boxed(db)
            } else {
                actual.clone()
            };
            if actual.is_primitive() {
                return;
            }
            out.push((param.idx, actual, kind));
        }
        Ty::Class(class, formal_args) if !formal_args.is_empty() => {
            let lifted = match kind {
                Bound::Lower => crate::subtype::find_super(db, &actual.boxed(db), *class),
                Bound::Eq if actual.as_class() == Some(*class) => Some(actual.clone()),
                _ => None,
            };
            let Some(lifted) = lifted else {
                return;
            };
            if lifted.type_args().len() != formal_args.len() {
                return;
            }
            for (formal_arg, actual_arg) in formal_args.iter().zip(lifted.type_args()) {
                use crate::ty::Wildcard;
                match (formal_arg, actual_arg) {
                    (Ty::Wildcard(Wildcard::Unbounded), _) => {}
                    (
                        Ty::Wildcard(Wildcard::Extends(bound)),
                        Ty::Wildcard(Wildcard::Extends(actual_bound)),
                    ) => collect_constraints(db, owner, bound, actual_bound, Bound::Lower, out),
                    (
                        Ty::Wildcard(Wildcard::Super(bound)),
                        Ty::Wildcard(Wildcard::Super(actual_bound)),
                    ) => collect_constraints(db, owner, bound, actual_bound, Bound::Upper, out),
                    (Ty::Wildcard(_), Ty::Wildcard(_)) => {}
                    (Ty::Wildcard(Wildcard::Extends(bound)), actual_arg) => {
                        collect_constraints(db, owner, bound, actual_arg, Bound::Lower, out)
                    }
                    (Ty::Wildcard(Wildcard::Super(bound)), actual_arg) => {
                        collect_constraints(db, owner, bound, actual_arg, Bound::Upper, out)
                    }
                    // 实参是通配符：捕获出来的是新的类型变量，不和别的约束比较
                    (_, Ty::Wildcard(_)) => {}
                    (formal_arg, actual_arg) => {
                        collect_constraints(db, owner, formal_arg, actual_arg, Bound::Eq, out)
                    }
                }
            }
        }
        Ty::Array(formal_element) => {
            if let Ty::Array(actual_element) = actual {
                if !actual_element.is_primitive() {
                    collect_constraints(db, owner, formal_element, actual_element, kind, out);
                }
            }
        }
        _ => {}
    }
}

/// lambda 的体是否可能与返回 `void`（`returns_value` 为假）或返回值的函数类型兼容
/// （JLS 15.12.2.1 的"潜在兼容"）。拿不准时返回 `None`。
fn lambda_shape_fits(lambda: &ast::LambdaExpr, returns_value: bool) -> Option<bool> {
    if let Some(body) = lambda.body_expr() {
        let statement_expr = matches!(
            body,
            ast::Expr::MethodCall(_) | ast::Expr::NewExpr(_) | ast::Expr::AssignExpr(_)
        ) || matches!(&body, ast::Expr::PostfixExpr(_))
            || matches!(&body, ast::Expr::UnaryExpr(u) if u.syntax().children_with_tokens().any(|t| matches!(t.kind(), SyntaxKind::PLUS_PLUS | SyntaxKind::MINUS_MINUS)));
        return Some(returns_value || statement_expr);
    }
    let block = lambda.body_block()?;
    // 只看最外层这个 lambda 自己的 return（嵌套的 lambda、类体里的不算）
    let mut with_value = false;
    let mut without_value = false;
    let mut walk = block.syntax().preorder();
    while let Some(event) = walk.next() {
        let syntax::WalkEvent::Enter(node) = event else {
            continue;
        };
        match node.kind() {
            SyntaxKind::LAMBDA_EXPR | SyntaxKind::CLASS_BODY => walk.skip_subtree(),
            SyntaxKind::RETURN_STMT => {
                if node.children().any(|c| ast::Expr::can_cast(c.kind())) {
                    with_value = true;
                } else {
                    without_value = true;
                }
            }
            // 可能不能正常结束的块对两种函数类型都兼容，判断起来太细，放弃
            SyntaxKind::THROW_STMT
            | SyntaxKind::WHILE_STMT
            | SyntaxKind::FOR_STMT
            | SyntaxKind::DO_WHILE_STMT => return None,
            _ => {}
        }
    }
    match (with_value, without_value) {
        (true, false) => Some(returns_value),
        (false, _) => Some(!returns_value),
        (true, true) => None,
    }
}

/// 块体 lambda 自己的 `return 值;` 里的值（嵌套的 lambda、类体里的不算）。
fn own_return_values(block: &ast::Block) -> Vec<ast::Expr> {
    let mut values = Vec::new();
    let mut walk = block.syntax().preorder();
    while let Some(event) = walk.next() {
        let syntax::WalkEvent::Enter(node) = event else {
            continue;
        };
        match node.kind() {
            SyntaxKind::LAMBDA_EXPR | SyntaxKind::CLASS_BODY => walk.skip_subtree(),
            SyntaxKind::RETURN_STMT => {
                values.extend(ast::ReturnStmt::cast(node).and_then(|r| r.expr()));
            }
            _ => {}
        }
    }
    values
}

fn method_flags(cx: &InferCtx<'_>, method: MethodId) -> Modifiers {
    crate::lower::method_flags(cx.db, method).unwrap_or_default()
}

impl InferCtx<'_> {
    pub(super) fn infer_expr(&mut self, expr: &ast::Expr, expected: Option<&Ty>) -> Ty {
        match self.infer_value(expr, expected) {
            Value::Ty(ty) => ty,
            Value::Type(_) | Value::Package(_) => Ty::Unknown,
        }
    }

    fn infer_value(&mut self, expr: &ast::Expr, expected: Option<&Ty>) -> Value {
        let value = self.infer_value_inner(expr, expected);
        if let Value::Ty(ty) = &value {
            self.result
                .expr_types
                .insert(expr.syntax().text_range(), ty.clone());
        }
        value
    }

    fn infer_value_inner(&mut self, expr: &ast::Expr, expected: Option<&Ty>) -> Value {
        let db = self.db;
        // 期望类型是声明出来的目标类型：只传给方法调用本身和括号、条件表达式的分支
        let declared_target = std::mem::take(&mut self.declared_target);
        let ty = match expr {
            ast::Expr::Literal(it) => match it.kind() {
                Some(SyntaxKind::INT_LITERAL) => Ty::INT,
                Some(SyntaxKind::LONG_LITERAL) => Ty::Primitive(PrimitiveType::Long),
                Some(SyntaxKind::FLOAT_LITERAL) => Ty::Primitive(PrimitiveType::Float),
                Some(SyntaxKind::DOUBLE_LITERAL) => Ty::Primitive(PrimitiveType::Double),
                Some(SyntaxKind::CHAR_LITERAL) => Ty::Primitive(PrimitiveType::Char),
                Some(SyntaxKind::STRING_LITERAL | SyntaxKind::TEXT_BLOCK) => Ty::string(db),
                Some(SyntaxKind::TRUE_KW | SyntaxKind::FALSE_KW) => Ty::BOOLEAN,
                Some(SyntaxKind::NULL_KW) => Ty::Null,
                _ => Ty::Unknown,
            },
            ast::Expr::NameExpr(it) => {
                return match it.name_ref() {
                    Some(name_ref) => self.resolve_simple_name(&name_ref),
                    None => Value::Ty(Ty::Unknown),
                };
            }
            ast::Expr::ThisExpr(it) => match it.qualifier() {
                Some(qualifier) => match self.infer_value(&qualifier, None) {
                    Value::Type(class) => this_ty(db, class),
                    _ => Ty::Unknown,
                },
                None => self.this_ty(),
            },
            ast::Expr::SuperExpr(it) => match it.qualifier() {
                // `Iface.super.method()`
                Some(qualifier) => match self.infer_value(&qualifier, None) {
                    Value::Type(class) => this_ty(db, class),
                    _ => Ty::Unknown,
                },
                None => self.super_ty(),
            },
            ast::Expr::ParenExpr(it) => it.expr().map_or(Ty::Unknown, |e| {
                self.declared_target = declared_target;
                self.infer_expr(&e, expected)
            }),
            ast::Expr::FieldAccess(it) => {
                let Some(receiver) = it.receiver() else {
                    return Value::Ty(Ty::Unknown);
                };
                let receiver = self.infer_value(&receiver, None);
                let Some(name_ref) = it.name_ref() else {
                    return Value::Ty(Ty::Unknown);
                };
                return self.resolve_member(receiver, &name_ref);
            }
            ast::Expr::MethodCall(it) => self.infer_method_call(it, expected, declared_target),
            ast::Expr::ExplicitConstructorCall(it) => {
                let key = it.target().map(|t| t.syntax().text_range());
                let ty = if it.is_super() {
                    self.super_ty()
                } else {
                    self.this_ty()
                };
                if let Some(args) = it.arg_list() {
                    match &ty {
                        Ty::Class(class, _) => {
                            self.infer_constructor_call(*class, &ty, false, &args, None, key);
                        }
                        _ => self.infer_args_untargeted(&args),
                    }
                }
                Ty::Void
            }
            ast::Expr::NewExpr(it) => {
                let qualifier_ty = it
                    .qualifier()
                    .map(|qualifier| self.infer_expr(&qualifier, None));
                let Some(ty_node) = it.ty() else {
                    if let Some(args) = it.arg_list() {
                        self.infer_args_untargeted(&args);
                    }
                    return Value::Ty(Ty::Unknown);
                };
                // `outer.new Inner()`：`Inner` 是 `outer` 的类型的成员类，不按词法作用域解析
                let inner_of_qualifier = match (&qualifier_ty, &ty_node) {
                    (Some(Ty::Class(outer, _)), ast::Type::ClassType(class_ty)) => class_ty
                        .name_ref()
                        .and_then(|name| member_type(db, *outer, &name.text()))
                        .map(Ty::class),
                    (Some(_), _) => Some(Ty::Unknown),
                    _ => None,
                };
                let ty = inner_of_qualifier.unwrap_or_else(|| self.lower_ty(&ty_node));
                let (diamond, key) = match &ty_node {
                    ast::Type::ClassType(class_ty) => (
                        class_ty
                            .type_arg_list()
                            .is_some_and(|list| list.args().next().is_none()),
                        class_ty.name_ref().map(|n| n.syntax().text_range()),
                    ),
                    _ => (false, None),
                };
                let result = match (&ty, it.arg_list()) {
                    (Ty::Class(class, _), Some(args)) => {
                        self.declared_target = declared_target && it.body().is_none();
                        self.standalone_new = diamond
                            && expected.is_none()
                            && it.body().is_none()
                            && self.without_target(it.syntax());
                        self.infer_constructor_call(*class, &ty, diamond, &args, expected, key)
                    }
                    (_, Some(args)) => {
                        self.infer_args_untargeted(&args);
                        ty.clone()
                    }
                    _ => ty.clone(),
                };
                let Some(body) = it.body() else {
                    return Value::Ty(result);
                };
                self.infer_class_body(&body, result.clone());
                // `new T() { ... }.member`：直接访问匿名类自己声明的成员时按匿名类本身的类型；
                // 别处仍按父类型（避免泛型推断把匿名类型传播出去）
                let mut outer = it.syntax().clone();
                while let Some(parent) = outer
                    .parent()
                    .filter(|p| p.kind() == SyntaxKind::PAREN_EXPR)
                {
                    outer = parent;
                }
                let is_receiver = outer.parent().is_some_and(|p| {
                    matches!(p.kind(), SyntaxKind::FIELD_ACCESS | SyntaxKind::METHOD_CALL)
                        && p.first_child().is_some_and(|first| first == outer)
                });
                match self.class_of_body(&body) {
                    Some(class) if is_receiver => this_ty(db, class),
                    _ => result,
                }
            }
            ast::Expr::ArrayCreationExpr(it) => {
                let mut ty = it.element_type().map_or(Ty::Unknown, |t| self.lower_ty(&t));
                for dim in it.dims() {
                    if let Some(size) = dim.expr() {
                        let size_ty = self.infer_expr(&size, Some(&Ty::INT));
                        self.check_index(&size, &size_ty);
                    }
                    ty = Ty::array(ty);
                }
                if let Some(init) = it.initializer() {
                    self.infer_array_initializer(&init, &ty);
                }
                ty
            }
            ast::Expr::ArrayInitializer(it) => {
                let ty = expected.cloned().unwrap_or(Ty::Unknown);
                self.infer_array_initializer(it, &ty);
                ty
            }
            ast::Expr::ArrayAccess(it) => self.infer_array_access(it),
            ast::Expr::UnaryExpr(it) => {
                let operand = it
                    .operand()
                    .map_or(Ty::Unknown, |e| self.infer_expr(&e, None));
                let op = it.op_token();
                if let Some(op) = &op {
                    let ok = match op.kind() {
                        SyntaxKind::BANG => {
                            operand.unboxed(self.db) == Some(PrimitiveType::Boolean)
                        }
                        _ => operand.unboxed(self.db).is_some_and(|p| p.is_numeric()),
                    };
                    if !ok && self.is_simple_ty(&operand) {
                        self.diagnostic(
                            it.syntax().text_range(),
                            InferDiagnosticKind::BadOperand {
                                op: op.text().to_string(),
                                operands: operand.display(self.db),
                            },
                        );
                    }
                }
                match op.map(|t| t.kind()) {
                    Some(SyntaxKind::BANG) => Ty::BOOLEAN,
                    Some(SyntaxKind::PLUS_PLUS | SyntaxKind::MINUS_MINUS) => operand,
                    _ => self.unary_promote(&operand),
                }
            }
            ast::Expr::PostfixExpr(it) => {
                let operand = it
                    .operand()
                    .map_or(Ty::Unknown, |e| self.infer_expr(&e, None));
                // `s++`：只能用于数值类型
                let op = it.syntax().children_with_tokens().find_map(|e| {
                    e.into_token().filter(|t| {
                        matches!(t.kind(), SyntaxKind::PLUS_PLUS | SyntaxKind::MINUS_MINUS)
                    })
                });
                if let Some(op) = op {
                    let numeric = operand.unboxed(self.db).is_some_and(|p| p.is_numeric());
                    if !numeric && self.is_simple_ty(&operand) {
                        self.diagnostic(
                            it.syntax().text_range(),
                            InferDiagnosticKind::BadOperand {
                                op: op.text().to_string(),
                                operands: operand.display(self.db),
                            },
                        );
                    }
                }
                operand
            }
            ast::Expr::BinaryExpr(it) => {
                let lhs = it.lhs().map_or(Ty::Unknown, |e| self.infer_expr(&e, None));
                let rhs = it.rhs().map_or(Ty::Unknown, |e| self.infer_expr(&e, None));
                self.check_operands(it, &lhs, &rhs);
                self.binary_result(it.op_kind(), &lhs, &rhs)
            }
            ast::Expr::AssignExpr(it) => {
                let lhs = it.lhs().map_or(Ty::Unknown, |e| self.infer_expr(&e, None));
                if let Some(rhs) = it.rhs() {
                    // 复合赋值（`+=` 等）带隐式的强制转换，只检查简单赋值
                    let op = it.op_token();
                    let simple = op.as_ref().is_some_and(|op| op.kind() == SyntaxKind::EQ);
                    // 左边的类型可能来自推断（`var` 变量）时，不拿它当确定的目标类型
                    let lhs_certain = it.lhs().is_some_and(|e| self.type_is_certain(&e));
                    self.declared_target = simple && lhs_certain;
                    let actual = self.infer_expr(&rhs, Some(&lhs));
                    if simple && !lhs.is_unknown() {
                        let saved = self.target_uncertain;
                        self.target_uncertain = saved || !lhs_certain;
                        self.check_assignable(rhs.syntax().text_range(), &actual, &lhs, &rhs);
                        self.target_uncertain = saved;
                    } else if let Some(op) = op.filter(|_| !simple) {
                        if self.has_target_free_type(&rhs) {
                            self.check_compound_assign(it, &op, &lhs, &actual);
                        }
                    }
                }
                lhs
            }
            ast::Expr::ConditionalExpr(it) => {
                if let Some(cond) = it.condition() {
                    self.infer_condition(&cond);
                }
                let then_expr = it.then_expr();
                let else_expr = it.else_expr();
                let then = then_expr.as_ref().map_or(Ty::Unknown, |e| {
                    self.declared_target = declared_target;
                    self.infer_expr(e, expected)
                });
                let otherwise = else_expr.as_ref().map_or(Ty::Unknown, |e| {
                    self.declared_target = declared_target;
                    self.infer_expr(e, expected)
                });
                // `flag ? b : 0`：一边是 byte / short / char（或它的包装类），另一边是能用它表示的
                // int 常量时，结果是这个窄类型（JLS §15.25）
                let narrowed = |ty: &Ty, other: Option<&ast::Expr>| {
                    let narrow = ty.unboxed(db).filter(|p| {
                        matches!(
                            p,
                            PrimitiveType::Byte | PrimitiveType::Short | PrimitiveType::Char
                        )
                    })?;
                    let value = super::int_literal_value(other?)?;
                    super::int_fits(value, narrow).then_some(Ty::Primitive(narrow))
                };
                narrowed(&then, else_expr.as_ref())
                    .or_else(|| narrowed(&otherwise, then_expr.as_ref()))
                    .unwrap_or_else(|| self.merge_branches(&then, &otherwise))
            }
            ast::Expr::InstanceofExpr(it) => self.infer_instanceof(it),
            ast::Expr::CastExpr(it) => self.infer_cast(it),
            ast::Expr::LambdaExpr(it) => {
                self.infer_lambda(it, expected);
                expected.cloned().unwrap_or(Ty::Unknown)
            }
            ast::Expr::MethodRef(it) => {
                self.infer_method_ref(it, expected);
                expected.cloned().unwrap_or(Ty::Unknown)
            }
            ast::Expr::ClassLiteral(it) => {
                let inner = if let Some(t) = it.ty() {
                    self.lower_ty(&t)
                } else if let Some(e) = it.expr() {
                    match self.infer_value(&e, None) {
                        Value::Type(class) => Ty::class(class),
                        _ => Ty::Unknown,
                    }
                } else {
                    Ty::Unknown
                };
                match lookup_class(db, "java/lang/Class") {
                    Some(class) => Ty::class_with_args(class, vec![inner.boxed(db)]),
                    None => Ty::Unknown,
                }
            }
            ast::Expr::SwitchExpr(it) => {
                let scrutinee = it
                    .scrutinee()
                    .map_or(Ty::Unknown, |e| self.infer_expr(&e, None));
                self.yield_tys.push(Vec::new());
                if let Some(block) = it.block() {
                    self.infer_switch_block(&block, &scrutinee, true);
                }
                let results = self.yield_tys.pop().unwrap_or_default();
                // 各分支结果按条件表达式的规则合并（`1` 和 `2L` 得到 long）
                results
                    .into_iter()
                    .filter(|ty| !matches!(ty, Ty::Unknown | Ty::Null))
                    .reduce(|a, b| self.merge_branches(&a, &b))
                    .or_else(|| expected.cloned())
                    .unwrap_or(Ty::Unknown)
            }
        };
        Value::Ty(ty)
    }

    // 下面几种表达式单独成函数（不内联）：`infer_value_inner` 随表达式的嵌套层层递归，
    // 它的栈帧要尽量小

    #[inline(never)]
    fn infer_array_access(&mut self, it: &ast::ArrayAccess) -> Ty {
        let db = self.db;
        let array_expr = it.array();
        let array = array_expr
            .as_ref()
            .map_or(Ty::Unknown, |e| self.infer_expr(e, None));
        if let Some(index) = it.index() {
            let index_ty = self.infer_expr(&index, Some(&Ty::INT));
            self.check_index(&index, &index_ty);
        }
        // `s[0]`（`String s`）
        if let Some(array_expr) = &array_expr {
            let known_class = matches!(array, Ty::Class(..))
                && !array.contains_unknown()
                && !mentions_type_param(&array);
            if (array.is_primitive() || known_class)
                && !self.suppress_unresolved
                && self.has_target_free_type(array_expr)
            {
                self.diagnostic(
                    array_expr.syntax().text_range(),
                    InferDiagnosticKind::NotAnArray {
                        ty: array.display(db),
                    },
                );
            }
        }
        match array {
            Ty::Array(element) => (*element).clone(),
            _ => Ty::Unknown,
        }
    }

    #[inline(never)]
    fn infer_instanceof(&mut self, it: &ast::InstanceofExpr) -> Ty {
        let operand = it.expr();
        let matched = operand
            .as_ref()
            .map_or(Ty::Unknown, |e| self.infer_expr(e, None));
        let tested = match (it.ty(), it.pattern()) {
            (Some(t), _) => Some(self.lower_ty(&t)),
            (None, Some(ast::Pattern::TypePattern(p))) => p
                .ty()
                .filter(|t| !lower_type(t).is_var())
                .map(|t| self.lower_ty(&t)),
            _ => None,
        };
        if let (Some(operand), Some(tested)) = (&operand, &tested) {
            // 基本类型的 instanceof 是较新的语言特性，只看引用类型
            if matched.is_reference() && tested.is_reference() {
                self.check_castable(operand, &matched, tested);
            }
        }
        if let Some(pattern) = it.pattern() {
            self.bind_pattern(&pattern, &matched);
        }
        Ty::BOOLEAN
    }

    #[inline(never)]
    fn infer_cast(&mut self, it: &ast::CastExpr) -> Ty {
        let ty = it.ty().map_or(Ty::Unknown, |t| self.lower_ty(&t));
        if let Some(operand) = it.expr() {
            let actual = self.infer_expr(&operand, Some(&ty));
            self.check_castable(&operand, &actual, &ty);
        }
        ty
    }

    // ---- 名字 ----

    pub(super) fn outer_class(&self, class: ClassId) -> Option<ClassId> {
        hir_def::outer_class(self.db, class)
    }

    /// 可能通过 static import 提供名为 `name` 的静态成员的类。
    /// 单个成员的 static import 遮蔽按需的（JLS §6.4.1），所以排在前面。
    fn static_import_classes(&self, name: &str) -> Vec<ClassId> {
        self.static_import_classes_with_kind(name)
            .into_iter()
            .map(|(class, _)| class)
            .collect()
    }

    /// 可能带进静态成员 `name` 的类，以及是否来自按需导入（单个导入在前）。
    fn static_import_classes_with_kind(&self, name: &str) -> Vec<(ClassId, bool)> {
        let mut imports: Vec<_> = self.file_scope.static_imports().collect();
        imports.sort_by_key(|import| import.is_on_demand);
        imports
            .into_iter()
            .filter_map(|import| {
                let class = if import.is_on_demand {
                    resolve_qualified_class_from(self.db, self.scope.file, &import.segments)
                } else {
                    let (last, prefix) = import.segments.split_last()?;
                    (last == name)
                        .then(|| resolve_qualified_class_from(self.db, self.scope.file, prefix))
                        .flatten()
                }?;
                Some((class, import.is_on_demand))
            })
            .collect()
    }

    /// 简单名能看到的 `receiver` 的字段 `name`：别的顶层类的私有字段不被继承，看不到；
    /// `strict` 时别的包里的包私有字段也看不到。
    fn visible_field(&self, receiver: &Ty, name: &str, strict: bool) -> Option<FieldCandidate> {
        let db = self.db;
        lookup_field(db, receiver, name).filter(|field| {
            crate::lower::field_flags(db, field.id).is_none_or(|flags| {
                let checked = match flags.visibility() {
                    hir_def::Visibility::Private => true,
                    hir_def::Visibility::Package => strict,
                    _ => false,
                };
                !checked
                    || crate::members::is_accessible(db, flags, field.id.class, Some(self.class))
            })
        })
    }

    fn resolve_simple_name(&mut self, name_ref: &ast::NameRef) -> Value {
        let db = self.db;
        let name = name_ref.text();
        let range = name_ref.syntax().text_range();

        // 由内到外逐层：这一层类体里的局部符号，然后是这一层类的字段（含继承来的）。
        // 局部类 / 匿名类的成员遮蔽外层方法的同名局部变量（JLS §6.4.1）
        for depth in (0..self.frames.len()).rev() {
            let lo = self.frame_scope_base.get(depth).copied().unwrap_or(0);
            let hi = self
                .frame_scope_base
                .get(depth + 1)
                .copied()
                .unwrap_or(self.scopes.len());
            if let Some(local) = self.lookup_local_in(lo, hi, &name, range.start()) {
                self.result
                    .resolutions
                    .insert(range, Resolution::Local(local));
                return Value::Ty(self.result.locals[local as usize].ty.clone());
            }
            let receiver = self.frames[depth].this_ty.clone();
            // 内层类继承不到的字段（别的包里包私有的）不遮蔽外层的局部变量
            if let Some(field) = self.visible_field(&receiver, &name, depth > 0) {
                self.result
                    .resolutions
                    .insert(range, Resolution::Field(field.id));
                return Value::Ty(field.ty);
            }
        }

        // 外层具名类的字段，然后是静态导入的
        let mut receivers: Vec<Ty> = Vec::new();
        let mut outer = self.outer_class(self.class);
        while let Some(class) = outer {
            receivers.push(this_ty(db, class));
            outer = self.outer_class(class);
        }
        receivers.extend(self.static_import_classes(&name).into_iter().map(Ty::class));
        for receiver in &receivers {
            if let Some(field) = self.visible_field(receiver, &name, false) {
                self.result
                    .resolutions
                    .insert(range, Resolution::Field(field.id));
                return Value::Ty(field.ty);
            }
        }

        match resolve_simple_type(db, &self.scope, &name) {
            Some(TypeNs::Class(class)) => {
                self.result
                    .resolutions
                    .insert(range, Resolution::Class(class));
                return Value::Type(class);
            }
            // 类型变量作限定符（`T.valueOf(..)`）：静态成员在它的擦除（第一个上界）里找
            Some(TypeNs::TypeParam(param)) => {
                if let Ty::Class(class, _) = Ty::TypeParam(param).erasure(db) {
                    self.result
                        .resolutions
                        .insert(range, Resolution::TypeParam(param));
                    return Value::Type(class);
                }
            }
            None => {}
        }
        if package_exists(db, &name) {
            self.result
                .resolutions
                .insert(range, Resolution::Package(name.clone()));
            return Value::Package(name.to_string());
        }

        // 匿名类 / 局部类从父类型继承来的成员类型
        let inherited = self
            .frames
            .iter()
            .skip(1)
            .rev()
            .find_map(|frame| match &frame.this_ty {
                Ty::Class(class, _) => member_type(db, *class, &name),
                _ => None,
            });
        if let Some(class) = inherited {
            self.result
                .resolutions
                .insert(range, Resolution::Class(class));
            return Value::Type(class);
        }
        // 方法体里声明的局部类 / 记录 / 接口：在当前作用域里没找到对应的类，只知道名字存在
        if self.local_type_names.contains(&name) {
            return Value::Ty(Ty::Unknown);
        }
        if self.can_report_unqualified() {
            self.diagnostic(range, InferDiagnosticKind::UnresolvedName { name });
        }
        Value::Ty(Ty::Unknown)
    }

    fn resolve_member(&mut self, receiver: Value, name_ref: &ast::NameRef) -> Value {
        let db = self.db;
        let name = name_ref.text();
        let range = name_ref.syntax().text_range();
        match receiver {
            Value::Ty(ty) => {
                if name == "length" && matches!(ty, Ty::Array(_)) {
                    self.result
                        .resolutions
                        .insert(range, Resolution::ArrayLength);
                    return Value::Ty(Ty::INT);
                }
                if matches!(ty, Ty::Primitive(_)) {
                    if !self.suppress_unresolved {
                        self.diagnostic(
                            range,
                            InferDiagnosticKind::PrimitiveDereference {
                                ty: ty.display(db),
                                method: false,
                            },
                        );
                    }
                    return Value::Ty(Ty::Unknown);
                }
                if let Some(field) = lookup_field(db, &ty, &name) {
                    self.result
                        .resolutions
                        .insert(range, Resolution::Field(field.id));
                    return Value::Ty(field.ty);
                }
                // 匿名类 / 局部类里的 `this.x`：`this` 的类型记成了父类型，
                // 类体自己声明的字段登记在局部符号里
                if self.in_local_class_with_this(&ty) {
                    if let Some(local) = self.lookup_local(&name) {
                        if self.result.locals[local as usize].kind == LocalKind::LocalClassField {
                            self.result
                                .resolutions
                                .insert(range, Resolution::Local(local));
                            return Value::Ty(self.result.locals[local as usize].ty.clone());
                        }
                    }
                    return Value::Ty(Ty::Unknown);
                }
                if self.can_report_missing_member(&ty) {
                    let receiver = ty.display(db);
                    self.diagnostic(
                        range,
                        InferDiagnosticKind::UnresolvedField { name, receiver },
                    );
                }
                Value::Ty(Ty::Unknown)
            }
            Value::Type(class) => {
                let ty = Ty::class(class);
                // 字段和成员类型同名时字段优先；但字段在这里不可访问的话，
                // 名字指的是同名的成员类型（javac 的行为）
                let field = lookup_field(db, &ty, &name).filter(|field| {
                    member_type(db, class, &name).is_none()
                        || crate::lower::field_flags(db, field.id).is_none_or(|flags| {
                            crate::members::is_accessible(
                                db,
                                flags,
                                field.id.class,
                                Some(self.class),
                            )
                        })
                });
                if let Some(field) = field {
                    self.result
                        .resolutions
                        .insert(range, Resolution::Field(field.id));
                    return Value::Ty(field.ty);
                }
                if let Some(nested) = member_type(db, class, &name) {
                    self.result
                        .resolutions
                        .insert(range, Resolution::Class(nested));
                    return Value::Type(nested);
                }
                if self.can_report_missing_member(&ty) {
                    let receiver = ty.display(db);
                    self.diagnostic(
                        range,
                        InferDiagnosticKind::UnresolvedField { name, receiver },
                    );
                }
                Value::Ty(Ty::Unknown)
            }
            Value::Package(package) => {
                let qualified = format!("{package}/{name}");
                let class = hir_def::lookup_class_from(db, self.scope.file, &qualified);
                if let Some(class) = class {
                    self.result
                        .resolutions
                        .insert(range, Resolution::Class(class));
                    Value::Type(class)
                } else if package_exists(db, &qualified) {
                    self.result
                        .resolutions
                        .insert(range, Resolution::Package(qualified.as_str().into()));
                    Value::Package(qualified)
                } else {
                    // 包存在、里面却没有这个类或子包：`java.util.Objects` 在 JDK 6 上就是这样
                    if !self.suppress_unresolved {
                        let name = format!("{}.{name}", package.replace('/', ".")).into();
                        self.diagnostic(range, InferDiagnosticKind::UnresolvedName { name });
                    }
                    Value::Ty(Ty::Unknown)
                }
            }
        }
    }

    // ---- 诊断的前提条件 ----

    /// 类及其所有祖先是否都解析成功，并且都不依赖会凭空生成成员的工具。
    /// 只有这样，"找不到成员"才是确定的。
    pub(super) fn hierarchy_is_reliable(&self, class: ClassId) -> bool {
        let db = self.db;
        std::iter::once(class)
            .chain(all_supers(db, class))
            .all(|c| {
                let Some(data) = class_header(db, c) else {
                    return false;
                };
                let declared = data.superclass.iter().count() + data.interfaces.len();
                if class_supertypes(db, c).len() != declared {
                    return false;
                }
                if data.annotations.iter().any(|a| a.contains("lombok")) {
                    return false;
                }
                match class_source_file(db, c) {
                    Some(file) => !hir_def::file_scope(db, file).imports_lombok(),
                    None => true,
                }
            })
    }

    /// 当前在匿名类 / 局部类的类体里，并且 `ty` 就是这一层 `this` 的类型。
    /// 这种类自己声明的成员不在父类型上，按类型查不到是正常的。
    fn in_local_class_with_this(&self, ty: &Ty) -> bool {
        self.frames.len() > 1
            && self
                .frames
                .last()
                .is_some_and(|frame| frame.anonymous && frame.this_ty == *ty)
    }

    fn can_report_missing_member(&self, receiver: &Ty) -> bool {
        if self.suppress_unresolved || receiver.contains_unknown() {
            return false;
        }
        match receiver {
            Ty::Class(class, _) => self.hierarchy_is_reliable(*class),
            // 数组的成员是确定的：`length`、`clone()` 和 `Object` 的方法
            Ty::Array(_) => true,
            _ => false,
        }
    }

    /// 不带限定符的名字找不到时能否报错：所有可能提供它的地方都必须是确定的。
    fn can_report_unqualified(&self) -> bool {
        if self.suppress_unresolved {
            return false;
        }
        let frames_ok = self.frames.iter().all(|frame| match &frame.this_ty {
            Ty::Class(class, _) => self.hierarchy_is_reliable(*class),
            _ => false,
        });
        if !frames_ok {
            return false;
        }
        let mut outer = self.outer_class(self.class);
        while let Some(class) = outer {
            if !self.hierarchy_is_reliable(class) {
                return false;
            }
            outer = self.outer_class(class);
        }
        // 有解析不了的 static import 时，名字可能就来自它
        self.file_scope.static_imports().all(|import| {
            let class_path = if import.is_on_demand {
                &import.segments[..]
            } else {
                &import.segments[..import.segments.len().saturating_sub(1)]
            };
            resolve_qualified_class_from(self.db, self.scope.file, class_path).is_some()
        })
    }

    // ---- 调用 ----

    fn infer_args_untargeted(&mut self, args: &ast::ArgList) {
        for arg in args.args() {
            self.infer_expr(&arg, None);
        }
    }

    /// 去掉从这里访问不到的私有方法（别的顶层类的私有方法不被继承，也不参与重载决议）。
    fn without_inaccessible_private(&self, found: Vec<MethodCandidate>) -> Vec<MethodCandidate> {
        found
            .into_iter()
            .filter(|candidate| {
                let flags = method_flags(self, candidate.id);
                flags.visibility() != hir_def::Visibility::Private
                    || crate::members::is_accessible(
                        self.db,
                        flags,
                        candidate.id.class,
                        Some(self.class),
                    )
            })
            .collect()
    }

    /// 去掉经由类型为 `receiver` 的表达式访问不到的方法。`receiver` 为 `None`（`super.m()`）时
    /// 不看 protected 对接收者类型的要求。访问发生在体内的局部类、匿名类里时，从这些类访问
    /// 得到也算。
    fn without_inaccessible(
        &self,
        found: Vec<MethodCandidate>,
        receiver: Option<&Ty>,
    ) -> Vec<MethodCandidate> {
        let from_classes: Vec<ClassId> = std::iter::once(self.class)
            .chain(self.frames.iter().filter_map(|frame| match &frame.this_ty {
                Ty::Class(class, _) => Some(*class),
                _ => None,
            }))
            .collect();
        found
            .into_iter()
            .filter(|candidate| {
                let flags = method_flags(self, candidate.id);
                let class = candidate.id.class;
                from_classes.iter().any(|from| match receiver {
                    Some(receiver) => crate::members::is_accessible_via(
                        self.db,
                        flags,
                        class,
                        Some(*from),
                        receiver,
                    ),
                    None => crate::members::is_accessible(self.db, flags, class, Some(*from)),
                })
            })
            .collect()
    }

    fn unqualified_methods(&self, name: &str) -> Vec<MethodCandidate> {
        let db = self.db;
        for frame in self.frames.iter().rev() {
            let found = self.without_inaccessible_private(lookup_methods(db, &frame.this_ty, name));
            if !found.is_empty() {
                return found;
            }
        }
        let mut outer = self.outer_class(self.class);
        while let Some(class) = outer {
            let found =
                self.without_inaccessible_private(lookup_methods(db, &this_ty(db, class), name));
            if !found.is_empty() {
                return found;
            }
            outer = self.outer_class(class);
        }
        // 单个静态导入带进来的同名方法合在一起参与重载决议（来自不同的类也一样）；
        // 都没有时才看按需导入
        let imported = self.static_import_classes_with_kind(name);
        for on_demand in [false, true] {
            let mut found: Vec<MethodCandidate> = Vec::new();
            for (class, _) in imported.iter().filter(|(_, kind)| *kind == on_demand) {
                for candidate in lookup_methods(db, &Ty::class(*class), name) {
                    if method_flags(self, candidate.id).is_static()
                        && !found.iter().any(|c| c.id == candidate.id)
                    {
                        found.push(candidate);
                    }
                }
            }
            if !found.is_empty() {
                return found;
            }
        }
        Vec::new()
    }

    /// `declared_target`：期望类型是声明出来的目标类型（变量、字段、方法返回类型），
    /// 不是由别处的推断得来的，可以拿它检查泛型方法的类型参数。
    fn infer_method_call(
        &mut self,
        call: &ast::MethodCall,
        expected: Option<&Ty>,
        declared_target: bool,
    ) -> Ty {
        let db = self.db;
        let receiver_expr = call.receiver();
        let receiver = receiver_expr.as_ref().map(|r| self.infer_value(r, None));
        let Some(name_ref) = call.name_ref() else {
            if let Some(args) = call.arg_list() {
                self.infer_args_untargeted(&args);
            }
            return Ty::Unknown;
        };
        let name = name_ref.text();
        let name_range = name_ref.syntax().text_range();
        // `x.foo()`（`int x`）、`voidCall().toString()`
        if let Some(Value::Ty(ty)) = &receiver {
            if self.check_primitive_receiver(ty, receiver_expr.as_ref(), name_range) {
                if let Some(args) = call.arg_list() {
                    self.infer_args_untargeted(&args);
                }
                return Ty::Unknown;
            }
        }
        let explicit: Vec<Ty> = call
            .type_arg_list()
            .map(|list| list.args().map(|t| self.lower_ty(&t)).collect())
            .unwrap_or_default();

        // (候选, 用于诊断的接收者类型)
        let (candidates, receiver_ty) = match receiver {
            Some(Value::Ty(ty)) => (lookup_methods(db, &ty, &name), Some(ty)),
            Some(Value::Type(class)) => {
                let ty = Ty::class(class);
                (lookup_methods(db, &ty, &name), Some(ty))
            }
            Some(Value::Package(_)) => {
                if let Some(args) = call.arg_list() {
                    self.infer_args_untargeted(&args);
                }
                return Ty::Unknown;
            }
            None => {
                // 匿名类 / 局部类自己声明的方法
                if let Some(local) = self.lookup_local_method(&name) {
                    let data = &self.result.locals[local as usize];
                    if data.kind == LocalKind::LocalClassMethod {
                        let ty = data.ty.clone();
                        self.result
                            .resolutions
                            .insert(name_range, Resolution::Local(local));
                        if let Some(args) = call.arg_list() {
                            self.infer_args_untargeted(&args);
                        }
                        return ty;
                    }
                }
                (self.unqualified_methods(&name), None)
            }
        };

        // 带限定符的调用：有访问得到的重载时，访问不到的重载（私有的、别的包里包私有的、不能经由
        // 这个接收者访问的 protected）不参与决议（JLS 15.12.2.1）
        let candidates = if let Some(receiver) = &receiver_ty {
            let via_super = matches!(receiver_expr, Some(ast::Expr::SuperExpr(_)));
            let accessible =
                self.without_inaccessible(candidates.clone(), (!via_super).then_some(receiver));
            if accessible.is_empty() {
                candidates
            } else {
                accessible
            }
        } else {
            candidates
        };

        let Some(args) = call.arg_list() else {
            return Ty::Unknown;
        };
        // 数组的 `clone()` 返回数组本身的类型，也不抛受检异常（JLS §10.7）
        if name == "clone" && args.args().next().is_none() {
            if let Some(array @ Ty::Array(_)) = &receiver_ty {
                return array.clone();
            }
        }
        if candidates.is_empty() {
            self.infer_args_untargeted(&args);
            let can_report = match &receiver_ty {
                Some(ty) if self.in_local_class_with_this(ty) => false,
                Some(ty) => self.can_report_missing_member(ty),
                None => self.can_report_unqualified(),
            };
            if can_report {
                let receiver = receiver_ty.map(|ty| ty.display(db));
                self.diagnostic(
                    name_range,
                    InferDiagnosticKind::UnresolvedMethod { name, receiver },
                );
            }
            return Ty::Unknown;
        }

        let candidates_complete = match &receiver_ty {
            Some(ty) if self.in_local_class_with_this(ty) => false,
            Some(ty) => self.can_report_missing_member(ty),
            None => self.can_report_unqualified(),
        };
        self.report_inapplicable = candidates_complete.then(|| name.clone());
        let call_receiver = match (&receiver_expr, &receiver_ty) {
            (None, _) => super::CallReceiver::Implicit,
            (Some(expr), Some(ty)) if self.type_is_certain(expr) => {
                super::CallReceiver::Certain(ty.clone())
            }
            _ => super::CallReceiver::Uncertain,
        };
        self.call_receiver = call_receiver.clone();
        match self.finish_call(
            candidates,
            &args,
            &explicit,
            &[],
            Some(name_range),
            expected,
        ) {
            Some(mut resolved) => {
                if let Some(expected) = expected.filter(|_| declared_target) {
                    self.check_target_typed_call(
                        &resolved,
                        &args,
                        expected,
                        call.syntax().text_range(),
                        &call_receiver,
                        None,
                    );
                }
                // `getClass()` 的类型是 `Class<? extends |T|>`，`T` 是接收者的静态类型（JLS §4.3.2）
                let get_class = name == "getClass"
                    && resolved.sig.params.is_empty()
                    && resolved.method.class.binary_name(db) == "java/lang/Object";
                if get_class {
                    let receiver = receiver_ty.clone().unwrap_or_else(|| self.this_ty());
                    let erased = receiver.erasure(db);
                    let reference = matches!(erased, Ty::Class(..) | Ty::Array(_));
                    if let (true, false, Some(class)) = (
                        reference,
                        erased.contains_unknown(),
                        lookup_class(db, "java/lang/Class"),
                    ) {
                        return Ty::class_with_args(
                            class,
                            vec![Ty::Wildcard(crate::ty::Wildcard::Extends(
                                std::sync::Arc::new(erased),
                            ))],
                        );
                    }
                }
                // 返回类型是代换进来的 `? extends X`（`List<? extends Number>` 上的 `get`）：
                // 捕获出来的类型变量用作值时就是它的上界
                let ty = match resolved.return_ty(db, expected) {
                    Ty::Wildcard(crate::ty::Wildcard::Extends(bound)) => (*bound).clone(),
                    ty => ty,
                };
                // 实参里的菱形匿名类（`body(new ParameterizedTypeReference<>() {})`）：类型实参
                // 要等返回类型按目标定下来才知道，这里按代入后的形参类型补上
                if let Some(args) = call.arg_list() {
                    for (idx, arg) in args.args().enumerate() {
                        if !is_diamond_anonymous(&arg) {
                            continue;
                        }
                        let range = arg.syntax().text_range();
                        let known =
                            self.result.expr_types.get(&range).is_some_and(|t| {
                                !t.contains_unknown() && !t.type_args().is_empty()
                            });
                        if known {
                            continue;
                        }
                        let param = resolved.param_ty(idx);
                        let arg_ty = resolved.finish_ty(db, &param, None);
                        if !arg_ty.contains_unknown() && !arg_ty.type_args().is_empty() {
                            self.result.expr_types.insert(range, arg_ty);
                        }
                    }
                }
                // 没有目标类型（结果只是接着调用成员、不被使用或者是 `var` 的初始值）：只能由目标
                // 确定的类型参数和 javac 一样取上界（`List.of().get(0)` 是 `Object`）；接收者位置上
                // 其余推不出来的类型参数也按上界算（`spec.value(...).returnResult()`），让后面的成员
                // 能解析
                if expected.is_none() && ty.contains_unknown() {
                    let receiver = used_as_receiver(call);
                    if receiver || self.without_target(call.syntax()) {
                        let n_args = call.arg_list().map_or(0, |list| list.args().count());
                        let standalone =
                            match resolved.finish_standalone(db, &resolved.sig.ret, n_args) {
                                Ty::Wildcard(crate::ty::Wildcard::Extends(bound)) => {
                                    (*bound).clone()
                                }
                                ty => ty,
                            };
                        if receiver && standalone.contains_unknown() {
                            if let Some(by_bounds) = resolved.return_ty_by_bounds(db) {
                                return by_bounds;
                            }
                        }
                        return standalone;
                    }
                }
                ty
            }
            None => Ty::Unknown,
        }
    }

    /// 表达式没有目标类型：它（可以隔着括号）是成员访问的接收者、表达式语句或者 `var` 的初始值。
    fn without_target(&self, node: &SyntaxNode) -> bool {
        let mut current = node.clone();
        loop {
            if self.no_target_expr == Some(current.text_range()) {
                return true;
            }
            let Some(parent) = current.parent() else {
                return false;
            };
            match parent.kind() {
                SyntaxKind::PAREN_EXPR => current = parent,
                SyntaxKind::EXPR_STMT => return true,
                _ => {
                    let receiver = if let Some(call) = ast::MethodCall::cast(parent.clone()) {
                        call.receiver()
                    } else if let Some(access) = ast::FieldAccess::cast(parent) {
                        access.receiver()
                    } else {
                        None
                    };
                    return receiver.is_some_and(|r| *r.syntax() == current);
                }
            }
        }
    }

    /// 方法调用的接收者是基本类型或 void 值时报错，返回是否是这种情形。
    #[inline(never)]
    fn check_primitive_receiver(
        &mut self,
        ty: &Ty,
        receiver_expr: Option<&ast::Expr>,
        name_range: TextRange,
    ) -> bool {
        let void_call = *ty == Ty::Void && matches!(receiver_expr, Some(ast::Expr::MethodCall(_)));
        if !matches!(ty, Ty::Primitive(_)) && !void_call {
            return false;
        }
        if !self.suppress_unresolved {
            self.diagnostic(
                name_range,
                InferDiagnosticKind::PrimitiveDereference {
                    ty: ty.display(self.db),
                    method: true,
                },
            );
        }
        true
    }

    /// 泛型方法调用的结果交给一个带类型实参的目标类型（`List<String> xs = List.of(1);`）：
    /// 目标类型把返回类型里的类型参数固定成某个类型，形参类型里的类型参数都被固定下来时，
    /// 对应的实参必须能赋给代换后的形参类型。只检查完全确定的情形：目标类型和实参类型都已知、
    /// 都不含类型变量；有原始类型的实参时（需要未经检查的转换，返回类型会被擦除）不检查。
    fn check_target_typed_call(
        &mut self,
        call: &Call,
        arg_list: &ast::ArgList,
        expected: &Ty,
        range: TextRange,
        receiver: &super::CallReceiver,
        diamond: Option<ClassId>,
    ) {
        let db = self.db;
        // 菱形构造时待推断的是被构造类的类型参数，"返回类型"是这个类本身
        let (owner, ret) = match diamond {
            Some(class) => (GenericOwner::Class(class), this_ty(db, class)),
            None => (
                GenericOwner::Method(call.method),
                call.sig.ret.subst(&call.receiver_subst),
            ),
        };
        if !call.applicable
            || diamond.is_none() && call.sig.n_type_params == 0
            || self.inference_overlaps_scope(&[owner])
        {
            return;
        }
        let Ty::Class(expected_class, expected_args) = expected else {
            return;
        };
        let in_scope = |param| self.type_param_in_scope(param);
        if expected_args.is_empty()
            || expected.contains_unknown()
            || expected.mentions_params_where(&|param| !in_scope(param))
        {
            return;
        }
        let lifted = match &ret {
            Ty::Class(class, _) if class == expected_class => Some(ret.clone()),
            Ty::Class(..) => crate::subtype::find_super_keeping_raw(db, &ret, *expected_class),
            _ => None,
        };
        let Some(lifted) = lifted else {
            return;
        };
        // 方法类型参数 → 目标类型要求它等于的类型
        let mut target = Subst::empty();
        for (arg, expected_arg) in lifted.type_args().iter().zip(expected_args.iter()) {
            if let Ty::TypeParam(param) = arg {
                if param.owner == owner
                    && matches!(
                        expected_arg,
                        Ty::Class(..) | Ty::Array(_) | Ty::TypeParam(_)
                    )
                {
                    target.insert(*param, expected_arg.clone());
                }
            }
        }
        if target.is_empty() {
            return;
        }
        let arg_exprs: Vec<ast::Expr> = arg_list.args().collect();
        let arg_ty = |this: &Self, arg: &ast::Expr| {
            this.result
                .expr_types
                .get(&arg.syntax().text_range())
                .cloned()
        };
        // 推断不出来的实参也可能是原始类型
        let unchecked = arg_exprs.iter().any(|arg| {
            !matches!(arg, ast::Expr::LambdaExpr(_) | ast::Expr::MethodRef(_))
                && arg_ty(self, arg)
                    .is_none_or(|ty| ty.contains_unknown() || self.mentions_raw(&ty))
        });
        if unchecked {
            return;
        }
        for (idx, arg) in arg_exprs.iter().enumerate() {
            if matches!(arg, ast::Expr::LambdaExpr(_) | ast::Expr::MethodRef(_)) {
                continue;
            }
            let formal = call.formal_param_ty(idx);
            if !formal.mentions_params_of(owner) {
                continue;
            }
            let required = formal.subst(&target);
            if required.mentions_params_of(owner) {
                continue;
            }
            let Some(actual) = arg_ty(self, arg) else {
                continue;
            };
            let simple_mismatch = matches!(formal, Ty::TypeParam(_))
                && self.is_simple_ty(&actual)
                && self.is_simple_ty(&required)
                && !crate::subtype::is_assignable(db, &actual, &required);
            // 参数化类型的实参（`List<List<String>> x = List.of(ints);`）或形参
            // （`Optional<List<String>> o = maybe.map(wrap);`）：实参的类型要完全确定，
            // 形参类型里按接收者代换的部分也要可靠
            let generic_mismatch = !simple_mismatch
                && !self.suppress_unresolved
                && self.choice_is_certain(call.method, arg_list, receiver)
                && (matches!(formal, Ty::TypeParam(_))
                    || self.candidate_subst_certain(receiver, call.method))
                && self.type_is_certain(arg)
                && self.certainly_incompatible(&actual, &required);
            if !simple_mismatch && !generic_mismatch {
                continue;
            }
            let found = match formal {
                Ty::TypeParam(param) => {
                    let mut with_actual = Subst::empty();
                    with_actual.insert(param, actual.boxed(db));
                    ret.subst(&with_actual)
                }
                _ => ret.clone(),
            }
            .subst(&call.inference.bindings)
            .erase_params_of(owner);
            self.diagnostic(
                range,
                InferDiagnosticKind::TypeMismatch {
                    expected: expected.display(db),
                    actual: found.display(db),
                },
            );
            return;
        }
        // lambda 实参的函数类型返回的正是被目标类型固定下来的类型参数
        // （`Stream<String> s = ints.stream().map(i -> i + 1);` 里的 `R`）：
        // lambda 的结果必须能赋给它。结果的类型要完全确定（形参的类型来自可靠的接收者）
        if self.suppress_unresolved || !self.choice_is_certain(call.method, arg_list, receiver) {
            return;
        }
        for (idx, arg) in arg_list.args().enumerate() {
            let ast::Expr::LambdaExpr(lambda) = &arg else {
                continue;
            };
            let Some((_, Ty::TypeParam(param))) = self.functional_sig(&call.formal_param_ty(idx))
            else {
                continue;
            };
            let Some(required) = target.get(param).cloned() else {
                continue;
            };
            let values = match lambda.body_expr() {
                Some(body) => vec![body],
                None => lambda
                    .body_block()
                    .map(|block| own_return_values(&block))
                    .unwrap_or_default(),
            };
            let n_diagnostics = self.result.diagnostics.len();
            for value in values {
                let Some(ty) = self.result.type_of(value.syntax().text_range()).cloned() else {
                    continue;
                };
                if self.type_is_certain(&value) && !matches!(value, ast::Expr::LambdaExpr(_)) {
                    self.check_assignable(value.syntax().text_range(), &ty, &required, &value);
                }
            }
            if self.result.diagnostics.len() > n_diagnostics {
                return;
            }
        }
    }

    /// 构造器调用（`new`、`this(...)`、`super(...)`、枚举常量）。返回被构造对象的类型。
    pub(super) fn infer_constructor_call(
        &mut self,
        class: ClassId,
        class_ty: &Ty,
        diamond: bool,
        args: &ast::ArgList,
        expected: Option<&Ty>,
        key: Option<TextRange>,
    ) -> Ty {
        let db = self.db;
        // 期望类型是声明出来的目标类型（由调用方设置，见 `infer_method_call`）
        let declared_target = std::mem::take(&mut self.declared_target);
        // 菱形构造没有目标类型（由调用方设置）
        let standalone = std::mem::take(&mut self.standalone_new);
        // 菱形推断不出来时：期望类型正好是同一个类就用它，否则退回原始类型
        let diamond_fallback = || match expected {
            Some(expected) if expected.as_class() == Some(class) => expected.clone(),
            _ => Ty::class(class),
        };

        let is_interface = class_header(db, class).is_some_and(|d| d.is_interface());
        let subst = if diamond {
            Subst::empty()
        } else {
            Subst::for_receiver(db, class_ty)
        };
        let candidates = if is_interface {
            Vec::new()
        } else {
            constructors(db, class, &subst)
        };
        if candidates.is_empty() {
            self.infer_args_untargeted(args);
            return if diamond {
                diamond_fallback()
            } else {
                class_ty.clone()
            };
        }

        // 菱形构造时，被构造类的类型参数也是待推断的
        let class_owner = [GenericOwner::Class(class)];
        let owners: &[GenericOwner] = if diamond { &class_owner } else { &[] };
        // class 文件里内部类的构造器带着合成的外层实例形参，只对源码里的类下结论
        let candidates_complete = !self.suppress_unresolved
            && class_source_file(db, class).is_some()
            && self.hierarchy_is_reliable(class);
        self.report_inapplicable = candidates_complete
            .then(|| class_header(db, class).map(|d| d.name.clone()))
            .flatten();
        self.call_receiver = if diamond {
            super::CallReceiver::Uncertain
        } else {
            super::CallReceiver::Certain(class_ty.clone())
        };
        match self.finish_call(candidates, args, &[], owners, key, None) {
            Some(mut resolved) if diamond => {
                if let Some(expected) = expected.filter(|_| declared_target) {
                    let generic = this_ty(db, class);
                    self.check_target_typed_call(
                        &resolved,
                        args,
                        expected,
                        args.syntax().text_range(),
                        &super::CallReceiver::Certain(generic),
                        Some(class),
                    );
                }
                if standalone && expected.is_none() {
                    let n_args = args.args().count();
                    return resolved.finish_standalone(db, &this_ty(db, class), n_args);
                }
                resolved.finish_ty(db, &this_ty(db, class), expected)
            }
            Some(_) => class_ty.clone(),
            None if diamond => diamond_fallback(),
            None => class_ty.clone(),
        }
    }

    /// 重载决议 + 实参推断。lambda 和方法引用延后到选定方法之后，以形参类型为目标类型来推断。
    fn finish_call(
        &mut self,
        candidates: Vec<MethodCandidate>,
        arg_list: &ast::ArgList,
        explicit_type_args: &[Ty],
        extra_owners: &[GenericOwner],
        key: Option<TextRange>,
        expected: Option<&Ty>,
    ) -> Option<Call> {
        let db = self.db;
        // 先取走：推断实参时里面嵌套的调用会改写这两个字段
        let report_inapplicable = self.report_inapplicable.take();
        let call_receiver = std::mem::take(&mut self.call_receiver);
        let arg_exprs: Vec<ast::Expr> = arg_list.args().collect();
        let args: Vec<Arg> = arg_exprs
            .iter()
            .map(|arg| match arg {
                ast::Expr::LambdaExpr(lambda) => Arg::Lambda {
                    arity: lambda.param_list().map_or(0, |p| p.params().count()),
                    implicit: lambda.param_list().is_some_and(|p| {
                        p.params().next().is_some() && p.params().all(|param| param.ty().is_none())
                    }),
                    // 判断不了（体里有 throw、循环）时两种都算兼容
                    void_compatible: lambda_shape_fits(lambda, false) != Some(false),
                    value_compatible: lambda_shape_fits(lambda, true) != Some(false),
                },
                ast::Expr::MethodRef(method_ref) => Arg::MethodRef {
                    arities: self.method_ref_arities(method_ref),
                },
                other => Arg::Ty(self.infer_expr(other, None)),
            })
            .collect();

        let resolved = resolve_call(db, &candidates, &args, explicit_type_args, extra_owners);
        // 候选完整、参数个数合得上的只有选中的这一个（选择不可能取决于 lambda 的形状）：
        // 实参 lambda 的函数式接口是确定的
        let lambda_shapes_certain = report_inapplicable.is_some()
            && extra_owners.is_empty()
            && resolved.as_ref().is_some_and(|call| {
                let mut fitting = candidates.iter().filter(|candidate| {
                    let sig = method_sig(db, candidate.id);
                    if sig.varargs {
                        args.len() + 1 >= sig.params.len()
                    } else {
                        sig.params.len() == args.len()
                    }
                });
                fitting.next().is_some_and(|c| c.id == call.method) && fitting.next().is_none()
            });
        // lambda 实参的目标类型也确定：此外选中的方法不是泛型方法，形参类型不涉及要推断的类型参数
        let lambda_targets_certain = lambda_shapes_certain
            && resolved
                .as_ref()
                .is_some_and(|call| call.sig.n_type_params == 0);
        // 选中哪个方法是确定的：候选完整、参数个数合得上的只有它一个，并且它适用
        let choice_certain =
            lambda_shapes_certain && resolved.as_ref().is_some_and(|call| call.applicable);
        if let (Some(name), Some(call)) = (&report_inapplicable, &resolved) {
            let lambdas_fit = |method: MethodId| {
                let sig = method_sig(db, method);
                arg_exprs.iter().enumerate().all(|(idx, arg)| {
                    let ast::Expr::LambdaExpr(lambda) = arg else {
                        return true;
                    };
                    let Some(functional) =
                        sig.params.get(idx).and_then(|p| functional_method(db, p))
                    else {
                        return false;
                    };
                    let returns_value = method_sig(db, functional.id).ret != Ty::Void;
                    lambda_shape_fits(lambda, returns_value) == Some(true)
                })
            };
            if let Some(other) = call
                .ambiguous
                .filter(|other| lambdas_fit(call.method) && lambdas_fit(*other))
            {
                self.diagnostic(
                    key.unwrap_or_else(|| arg_list.syntax().text_range()),
                    InferDiagnosticKind::AmbiguousCall {
                        name: name.clone(),
                        first: describe_method(db, call.method),
                        second: describe_method(db, other),
                    },
                );
            }
        }
        if let Some(name) = report_inapplicable {
            if resolved.as_ref().is_some_and(|call| !call.applicable)
                && self.inapplicable_is_certain(&candidates, &args, &arg_exprs, &call_receiver)
            {
                let shown: Vec<String> = args
                    .iter()
                    .map(|arg| match arg {
                        Arg::Ty(ty) => ty.display(db),
                        Arg::Lambda { .. } => "lambda".to_owned(),
                        Arg::MethodRef { .. } => base_db::tr!("方法引用", "method reference"),
                    })
                    .collect();
                self.diagnostic(
                    key.unwrap_or_else(|| arg_list.syntax().text_range()),
                    InferDiagnosticKind::ArgumentMismatch {
                        name,
                        args: shown.join(", "),
                    },
                );
            }
        }
        self.result.calls.insert(
            arg_list.syntax().text_range(),
            CallInfo {
                chosen: resolved.as_ref().map(|c| c.method),
                candidates,
            },
        );

        let Some(mut call) = resolved else {
            for arg in &arg_exprs {
                if matches!(arg, ast::Expr::LambdaExpr(_) | ast::Expr::MethodRef(_)) {
                    self.infer_expr(arg, None);
                }
            }
            return None;
        };
        if let Some(key) = key {
            self.result
                .resolutions
                .insert(key, Resolution::Method(call.method));
        }

        // 实参本身是泛型调用、且它的类型参数只能由目标类型确定时（`collect(Collectors.toList())`、
        // `add(new ArrayList<>())`），带着形参类型再推一遍，然后用更精确的结果重新约束本次调用。
        let mut arg_tys: Vec<Option<Ty>> = args
            .iter()
            .map(|arg| match arg {
                Arg::Ty(ty) => Some(ty.clone()),
                _ => None,
            })
            .collect();
        self.retarget_args(&mut call, &arg_exprs, &mut arg_tys);

        // 期望类型先确定 lambda / 方法引用的形参类型里还没推出来的类型参数
        // （`collect(Collectors.toMap(s -> s, ...))` 里 `toMap` 的 `T`），显式写出的 lambda
        // 形参类型也一样（`comparing((Person p) -> p.age)`），方法引用 `Type::method`
        // 的接收者类型给出第一个形参（`comparing(Person::getName)`）
        self.bind_functional_inputs(&mut call, &arg_exprs, expected);

        let mut functional_args = false;
        for (idx, arg) in arg_exprs.iter().enumerate() {
            functional_args |= matches!(arg, ast::Expr::LambdaExpr(_) | ast::Expr::MethodRef(_));
            let produced = match arg {
                ast::Expr::LambdaExpr(lambda) => {
                    let target = call.param_ty(idx);
                    self.lambda_params_certain = choice_certain
                        && self.candidate_subst_certain(&call_receiver, call.method)
                        && self.functional_sig(&call.formal_param_ty(idx)).is_some_and(
                            |(params, _)| {
                                params.iter().all(|p| {
                                    // 通配符形参来自被捕获的接收者（`List<?>`），不深究
                                    !p.contains_unknown()
                                        && !p.is_wildcard()
                                        && !p.mentions_params_of(GenericOwner::Method(call.method))
                                })
                            },
                        );
                    let produced = self.infer_lambda(lambda, Some(&target));
                    if lambda_targets_certain && !mentions_type_param(&target) {
                        let saved = self.target_uncertain;
                        self.target_uncertain =
                            saved || !self.candidate_subst_certain(&call_receiver, call.method);
                        self.check_lambda(lambda, &target);
                        self.target_uncertain = saved;
                    } else if lambda_shapes_certain && !call.varargs_expanded {
                        // 声明的形参类型本身就是函数式接口（不是类型变量）
                        if let Some(Ty::Class(..)) = call.sig.params.get(idx) {
                            self.check_lambda_shape(lambda, &call.formal_param_ty(idx));
                        }
                    }
                    Some((produced, target))
                }
                ast::Expr::MethodRef(method_ref) => {
                    let target = call.param_ty(idx);
                    let mut produced = self.infer_method_ref(method_ref, Some(&target));
                    if method_ref.is_constructor() {
                        produced =
                            self.parameterize_constructor_ref(&call, idx, produced, method_ref);
                        // 构造器引用的函数类型形参也被选定构造器的形参约束：
                        // `Func<X, Scalar<Y>>` 收 `IsBlank::new`（唯一构造器 `IsBlank(Textish)`）
                        // 时 `X := Textish`——javac 由方法引用的编译期声明得出同样的约束。
                        // 缺了它，菱形构造的类型参数停在 `?` 上，外层重载决议就分不清谁适用
                        if let Some(Resolution::Method(chosen)) = self
                            .result
                            .resolutions
                            .get(&method_ref.syntax().text_range())
                        {
                            let chosen_params = method_sig(db, *chosen).params.clone();
                            if let Some((inputs, _)) = self.functional_sig(&target) {
                                if inputs.len() == chosen_params.len() {
                                    // 泛型类的构造器形参（`Box(T v)`）里的 `T` 属于被引用的类，
                                    // 不能拿来绑定这次调用的类型参数
                                    for (input, param) in inputs.iter().zip(chosen_params.iter()) {
                                        if !mentions_type_param(param) {
                                            call.inference.unify(db, input, param);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    Some((produced, target))
                }
                _ => None,
            };
            if let Some((produced_ty, target)) = produced {
                // 函数体的结果类型反过来约束方法的类型参数（`map(x -> x.length())` 推出 R）
                if !matches!(produced_ty, Ty::Void | Ty::Unknown) {
                    if let Some((_, functional_ret)) = self.functional_sig(&target) {
                        call.inference.unify(db, &functional_ret, &produced_ty);
                    }
                }
                let arg_ty = call.finish_ty(db, &target, None);
                self.result
                    .expr_types
                    .insert(arg.syntax().text_range(), arg_ty);
            }
        }
        // lambda / 方法引用推出了新的类型参数之后，还没定下来的泛型调用实参再按形参类型推一遍
        // （`mapping(Person::getName, Collectors.toSet())` 里的 `toSet()` 要等 `U` 推出来）
        if functional_args {
            self.retarget_args(&mut call, &arg_exprs, &mut arg_tys);
            // 构造器引用的类型实参可能要等上面的实参定下来（`groupingBy(f, TreeMap::new, toList())`）
            for (idx, arg) in arg_exprs.iter().enumerate() {
                let ast::Expr::MethodRef(method_ref) = arg else {
                    continue;
                };
                if !method_ref.is_constructor() {
                    continue;
                }
                let class = match (method_ref.receiver_type(), method_ref.receiver_expr()) {
                    (Some(t), _) => self.lower_ty(&t).as_class(),
                    (None, Some(e)) => match self.infer_value(&e, None) {
                        Value::Type(class) => Some(class),
                        _ => None,
                    },
                    _ => None,
                };
                let Some(class) = class else {
                    continue;
                };
                let produced =
                    self.parameterize_constructor_ref(&call, idx, Ty::class(class), method_ref);
                if produced.type_args().is_empty() || produced.contains_unknown() {
                    continue;
                }
                match self.functional_sig(&call.formal_param_ty(idx)) {
                    // 第一遍只能绑定成原始类型或者不完整的类型，这里直接改写
                    Some((_, Ty::TypeParam(param)))
                        if call.inference.owners.contains(&param.owner) =>
                    {
                        call.inference.bindings.set(param, produced);
                    }
                    Some((_, functional_ret)) => {
                        call.inference.unify(db, &functional_ret, &produced)
                    }
                    None => {}
                }
                let target = call.param_ty(idx);
                let arg_ty = call.finish_ty(db, &target, None);
                self.result
                    .expr_types
                    .insert(arg.syntax().text_range(), arg_ty);
            }
        }
        Some(call)
    }

    /// 类型里还有推断不出来的部分的泛型调用实参，按（目前推断出来的）形参类型重新推断一遍，
    /// 用更精确的结果重新约束本次调用。
    fn retarget_args(
        &mut self,
        call: &mut Call,
        arg_exprs: &[ast::Expr],
        arg_tys: &mut [Option<Ty>],
    ) {
        let db = self.db;
        for (idx, arg) in arg_exprs.iter().enumerate() {
            let Some(first) = &arg_tys[idx] else {
                continue;
            };
            if !first.contains_unknown() || !is_retargetable(arg) {
                continue;
            }
            let with_lambda = contains_lambda(arg);
            if with_lambda && self.retarget_depth >= MAX_LAMBDA_RETARGET_DEPTH {
                continue;
            }
            let target = call.finish_ty(db, &call.param_ty(idx), None);
            if target.is_unknown() {
                continue;
            }
            let n_diagnostics = self.result.diagnostics.len();
            self.retarget_depth += u32::from(with_lambda);
            let refined = self.infer_expr(arg, Some(&target));
            self.retarget_depth -= u32::from(with_lambda);
            self.result.diagnostics.truncate(n_diagnostics);
            if !refined.is_unknown() {
                call.refine_arg(db, idx, &refined);
                arg_tys[idx] = Some(refined);
            }
        }
    }

    /// 在推断 lambda / 方法引用之前，先确定它们的函数类型的形参里还没推出来的类型参数。
    fn bind_functional_inputs(
        &mut self,
        call: &mut Call,
        arg_exprs: &[ast::Expr],
        expected: Option<&Ty>,
    ) {
        let db = self.db;
        let owner = GenericOwner::Method(call.method);
        let unbound_inputs = |this: &Self, call: &Call| -> Vec<hir_def::TypeParamId> {
            (0..call.sig.n_type_params)
                .map(|idx| hir_def::TypeParamId { owner, idx })
                .filter(|param| !call.inference.bindings.contains(*param))
                .filter(|param| {
                    arg_exprs.iter().enumerate().any(|(idx, arg)| {
                        matches!(arg, ast::Expr::LambdaExpr(_) | ast::Expr::MethodRef(_))
                            && this.functional_sig(&call.formal_param_ty(idx)).is_some_and(
                                |(params, _)| {
                                    params
                                        .iter()
                                        .any(|p| p.mentions_params_where(&|q| q == *param))
                                },
                            )
                    })
                })
                .collect()
        };
        // 期望类型
        if let Some(expected) = expected {
            let inputs = unbound_inputs(self, call);
            if !inputs.is_empty() {
                let mut probe = call.inference.clone();
                let ret = call
                    .sig
                    .ret
                    .subst(&call.receiver_subst)
                    .subst(&probe.bindings);
                // `?`、`? extends X` 只给出上界，形参类型应当由别的实参确定
                // （`Collector<T, ?, R>` 里的 `?` 不能把累加器类型定成 `Object`）
                probe.unify_with_expected(db, &ret, &lower_bounds_only(expected));
                for param in inputs {
                    if let Some(ty) = probe.bindings.get(param).filter(|t| !t.contains_unknown()) {
                        call.inference.bindings.insert(param, ty.clone());
                    }
                }
            }
        }
        for (idx, arg) in arg_exprs.iter().enumerate() {
            let Some((params, _)) = self.functional_sig(&call.formal_param_ty(idx)) else {
                continue;
            };
            match arg {
                // 显式写出的 lambda 形参类型和函数类型的形参类型相等
                ast::Expr::LambdaExpr(lambda) => {
                    let Some(list) = lambda.param_list() else {
                        continue;
                    };
                    let declared: Vec<Option<Ty>> = list
                        .params()
                        .map(|param| {
                            param
                                .ty()
                                .filter(|t| !lower_type(t).is_var())
                                .map(|t| self.lower_ty(&t))
                        })
                        .collect();
                    if declared.len() != params.len() {
                        continue;
                    }
                    for (formal, declared) in params.iter().zip(declared) {
                        if let Some(declared) = declared.filter(|t| !t.contains_unknown()) {
                            call.inference.unify(db, formal, &declared);
                        }
                    }
                }
                // `Type::instanceMethod`：函数类型的第一个形参就是接收者
                ast::Expr::MethodRef(method_ref) => {
                    let Some(Ty::TypeParam(first)) = params.first() else {
                        continue;
                    };
                    if first.owner != owner || call.inference.bindings.contains(*first) {
                        continue;
                    }
                    if let Some(receiver) = self.exact_method_ref_receiver(method_ref, params.len())
                    {
                        call.inference.bindings.insert(*first, receiver);
                    }
                }
                _ => {}
            }
        }
    }

    /// 方法引用 `Type::method` 引用的是 `Type` 唯一的、非泛型、非可变参数的实例方法，并且
    /// 函数类型有 `arity` 个形参（第一个是接收者）时，返回 `Type`。`Type` 要写全类型实参
    /// （或者不是泛型类）。
    fn exact_method_ref_receiver(
        &mut self,
        method_ref: &ast::MethodRef,
        arity: usize,
    ) -> Option<Ty> {
        let db = self.db;
        if method_ref.is_constructor() {
            return None;
        }
        let receiver = if let Some(t) = method_ref.receiver_type() {
            self.lower_ty(&t)
        } else {
            match method_ref.receiver_expr()? {
                e @ (ast::Expr::NameExpr(_) | ast::Expr::FieldAccess(_)) => {
                    match self.infer_value(&e, None) {
                        Value::Type(class) => Ty::class(class),
                        _ => return None,
                    }
                }
                _ => return None,
            }
        };
        let Ty::Class(class, args) = &receiver else {
            return None;
        };
        if args.is_empty() && class_header(db, *class).is_none_or(|d| !d.type_params.is_empty()) {
            return None;
        }
        if receiver.contains_unknown() {
            return None;
        }
        let name = method_ref.name_ref()?.text();
        let candidates = lookup_methods(db, &receiver, &name);
        let [candidate] = candidates.as_slice() else {
            return None;
        };
        let sig = method_sig(db, candidate.id);
        let exact = !sig.varargs
            && sig.n_type_params == 0
            && !method_flags(self, candidate.id).is_static()
            && sig.params.len() + 1 == arity;
        exact.then_some(receiver)
    }

    /// 泛型类的构造器引用（`TreeMap::new`）没写类型实参：按函数类型的返回类型（或者它是待推断的
    /// 类型参数时按它的上界）推出被构造类的类型实参，像菱形一样。
    fn parameterize_constructor_ref(
        &self,
        call: &Call,
        idx: usize,
        produced: Ty,
        method_ref: &ast::MethodRef,
    ) -> Ty {
        let db = self.db;
        let Ty::Class(class, args) = &produced else {
            return produced;
        };
        if !args.is_empty() || class_header(db, *class).is_none_or(|d| d.type_params.is_empty()) {
            return produced;
        }
        // 用声明的形参类型（方法的类型参数还没代换），这样能看到函数类型返回的是哪个类型参数
        let Some((_, ret)) = self.functional_sig(&call.formal_param_ty(idx)) else {
            return produced;
        };
        let ret = match &ret {
            Ty::TypeParam(param) if !call.inference.bindings.contains(*param) => ret.clone(),
            Ty::TypeParam(param)
                if call
                    .inference
                    .bindings
                    .get(*param)
                    .is_some_and(|b| b.contains_unknown() || b.type_args().is_empty()) =>
            {
                ret.clone()
            }
            other => other.subst(&call.inference.bindings),
        };
        // 返回类型是这次调用还没定的类型参数时只能拿它的上界来约束；没有上界就不约束
        let wanted = match &ret {
            Ty::TypeParam(param) if call.inference.owners.contains(&param.owner) => {
                crate::lower::type_param_bounds(db, *param)
                    .first()
                    .map(|bound| {
                        bound
                            .subst(&call.receiver_subst)
                            .subst(&call.inference.bindings)
                    })
            }
            other => Some(other.clone()),
        };
        let class_owner = GenericOwner::Class(*class);
        let generic = this_ty(db, *class);
        let mut inference = crate::method_resolution::Inference::new(vec![class_owner]);
        if let Some(wanted) = &wanted {
            inference.unify_with_expected(db, &generic, wanted);
        }
        // 函数类型的形参也约束类的类型参数：`apply(Box::new, "x")` 里 `Function<String, B>`
        // 收 `Box(T v)` 得出 `T := String`。返回类型还是没定的 `B` 时，只看它推不出来
        if let Some(Resolution::Method(chosen)) = self
            .result
            .resolutions
            .get(&method_ref.syntax().text_range())
        {
            let params = &method_sig(db, *chosen).params;
            if let Some((inputs, _)) = self.functional_sig(&call.param_ty(idx)) {
                if inputs.len() == params.len() {
                    for (param, input) in params.iter().zip(&inputs) {
                        if !input.contains_unknown() && !mentions_type_param(input) {
                            inference.unify(db, param, input);
                        }
                    }
                }
            }
        }
        // 推不出来的类型实参留作未知（之后还可以改写），一个都推不出来时保持原样
        let res = generic
            .subst(&inference.bindings)
            .erase_params_of(class_owner);
        if mentions_type_param(&res) || res.type_args().iter().all(Ty::is_unknown) {
            return produced;
        }
        res
    }

    /// 重载决议失败是不是确定的：要么所有候选的参数个数都对不上，
    /// 要么实参和所有候选的形参都是简单类型（不涉及泛型推断、lambda）。
    fn inapplicable_is_certain(
        &self,
        candidates: &[MethodCandidate],
        args: &[Arg],
        arg_exprs: &[ast::Expr],
        call_receiver: &super::CallReceiver,
    ) -> bool {
        let db = self.db;
        let sigs: Vec<_> = candidates
            .iter()
            .map(|candidate| (candidate, method_sig(db, candidate.id)))
            .collect();
        let arity_never_matches = sigs
            .iter()
            .all(|(_, sig)| !sig.varargs && sig.params.len() != args.len());
        if arity_never_matches {
            return true;
        }
        // 每个候选要么参数个数对不上，要么按实参推出的类型参数确定违反了上界
        let violates_bounds = sigs.iter().all(|(candidate, sig)| {
            (!sig.varargs && sig.params.len() != args.len())
                || certainly_violates_bounds(db, candidate, args)
        });
        if violates_bounds {
            return true;
        }
        // 每个候选都有一个实参确定传不进对应的形参
        if sigs.iter().all(|(candidate, sig)| {
            self.candidate_rejects(candidate, sig, args, arg_exprs, call_receiver)
        }) {
            return true;
        }
        // 形参都是非泛型类型时，能不能赋值只取决于实参类型擦除后的类：实参可以是
        // 参数化类型（`List<String>` 传给 `String`）或原始类型。但这类实参的类型必须是
        // 声明出来的（变量、字段、强制转换、显式写出类型的 `new`），泛型方法调用推出的
        // 类型可能依赖目标类型，不可靠
        let args_simple = args.iter().zip(arg_exprs).all(|(arg, expr)| match arg {
            Arg::Ty(ty) => {
                self.is_simple_ty(ty)
                    || matches!(ty, Ty::Class(..))
                        && !ty.contains_unknown()
                        && has_declared_type(expr)
            }
            _ => false,
        });
        args_simple
            && sigs.iter().all(|(candidate, sig)| {
                sig.n_type_params == 0
                    && sig.params.iter().all(|param| {
                        let param = param.subst(&candidate.subst);
                        match &param {
                            Ty::Array(element) if sig.varargs => self.is_simple_ty(element),
                            other => self.is_simple_ty(other),
                        }
                    })
            })
    }

    /// 候选确定不接受这组实参：参数个数对不上，或者有一个实参确定传不进对应的形参。一般只看擦除
    /// 后的类，类型实参（包括通配符和方法自己的类型参数）不影响结论（`addAll("x")` 对
    /// `Collection<? extends E>`）；实参和形参的类型都确定时按带类型实参的子类型判断
    /// （`List<Integer>` 传给 `List<String>`）。
    fn candidate_rejects(
        &self,
        candidate: &MethodCandidate,
        sig: &crate::lower::MethodSig,
        args: &[Arg],
        arg_exprs: &[ast::Expr],
        call_receiver: &super::CallReceiver,
    ) -> bool {
        let db = self.db;
        let fixed = if sig.varargs {
            if args.len() + 1 < sig.params.len() {
                return true;
            }
            sig.params.len() - 1
        } else if sig.params.len() != args.len() {
            return true;
        } else {
            sig.params.len()
        };
        if sig.n_type_params > 0
            && self.generic_constraints_conflict(
                candidate,
                sig,
                fixed,
                args,
                arg_exprs,
                call_receiver,
            )
        {
            return true;
        }
        (0..fixed).any(|idx| {
            let Arg::Ty(arg) = &args[idx] else {
                return false;
            };
            let generic = !self.suppress_unresolved
                && !self.inference_overlaps_scope(&[GenericOwner::Method(candidate.id)])
                && self.candidate_subst_certain(call_receiver, candidate.id)
                && self.type_is_certain(&arg_exprs[idx])
                && self.certainly_incompatible(arg, &sig.params[idx].subst(&candidate.subst));
            if generic {
                return true;
            }
            let Some(arg) = self.erased_arg(arg, &arg_exprs[idx]) else {
                return false;
            };
            let param = sig.params[idx].subst(&candidate.subst);
            let param = match &param {
                Ty::Primitive(_) => param.clone(),
                Ty::Class(class, _) if self.hierarchy_is_reliable(*class) => Ty::class(*class),
                _ => return false,
            };
            !crate::subtype::is_assignable(db, &arg, &param)
        })
    }

    /// 泛型方法的类型参数由实参得到的约束自相矛盾，因此候选确定不适用（`<T> f(List<T>, List<T>)`
    /// 收到 `List<String>` 和 `List<Integer>`，`copy(List<? super T>, List<? extends T>)` 收到
    /// `List<Integer>` 和 `List<String>`）。
    ///
    /// 只用类型确定、已知、不含类型变量和原始类型的实参；每个实参给出类型参数的等式约束（出现在
    /// 不变的类型实参位置）、下界（形参就是 `T`、`T[]` 或 `? extends T`）或上界（`? super T`）。
    /// 只取一部分约束是安全的：一部分已经矛盾，加上别的实参（lambda 等）也不会变得可解。
    /// 矛盾指：两个等式约束不同，下界不是等式约束 / 上界的子类型，等式约束不是上界的子类型。
    fn generic_constraints_conflict(
        &self,
        candidate: &MethodCandidate,
        sig: &crate::lower::MethodSig,
        fixed: usize,
        args: &[Arg],
        arg_exprs: &[ast::Expr],
        call_receiver: &super::CallReceiver,
    ) -> bool {
        let db = self.db;
        let owner = GenericOwner::Method(candidate.id);
        if self.suppress_unresolved
            || self.inference_overlaps_scope(&[owner])
            || !self.candidate_subst_certain(call_receiver, candidate.id)
        {
            return false;
        }
        let mut constraints: Vec<(u32, Ty, Bound)> = Vec::new();
        for idx in 0..fixed {
            let Arg::Ty(arg) = &args[idx] else {
                continue;
            };
            let usable = match arg {
                Ty::Primitive(_) => true,
                Ty::Class(..) | Ty::Array(_) => {
                    !arg.contains_unknown()
                        && !mentions_type_param(arg)
                        && !crate::subtype::involves_raw(db, arg)
                        && arg
                            .as_class()
                            .is_none_or(|class| self.hierarchy_is_reliable(class))
                }
                _ => false,
            };
            if !usable || !self.type_is_certain(&arg_exprs[idx]) {
                continue;
            }
            let Some(formal) = sig.params.get(idx).map(|p| p.subst(&candidate.subst)) else {
                continue;
            };
            if formal.contains_unknown() || formal.mentions_params_where(&|p| p.owner != owner) {
                continue;
            }
            collect_constraints(db, owner, &formal, arg, Bound::Lower, &mut constraints);
        }
        if constraints.is_empty() {
            return false;
        }
        let incompatible = |from: &Ty, to: &Ty| self.certainly_incompatible(from, to);
        (0..sig.n_type_params).any(|param| {
            let of = |kind: Bound| -> Vec<&Ty> {
                constraints
                    .iter()
                    .filter(|(p, _, k)| *p == param && *k == kind)
                    .map(|(_, ty, _)| ty)
                    .collect()
            };
            let (eqs, lowers, uppers) = (of(Bound::Eq), of(Bound::Lower), of(Bound::Upper));
            let eq_conflict = eqs.iter().enumerate().any(|(i, a)| {
                eqs[i + 1..]
                    .iter()
                    .any(|b| incompatible(a, b) || incompatible(b, a))
            });
            eq_conflict
                || eqs
                    .iter()
                    .any(|e| lowers.iter().any(|l| incompatible(l, e)))
                || eqs
                    .iter()
                    .any(|e| uppers.iter().any(|u| incompatible(e, u)))
                || lowers
                    .iter()
                    .any(|l| uppers.iter().any(|u| incompatible(l, u)))
        })
    }

    /// 选中的方法是确定的：参数个数合得上的别的候选都确定不接受这组实参。
    fn choice_is_certain(
        &self,
        chosen: MethodId,
        arg_list: &ast::ArgList,
        call_receiver: &super::CallReceiver,
    ) -> bool {
        let Some(info) = self.result.calls.get(&arg_list.syntax().text_range()) else {
            return false;
        };
        let arg_exprs: Vec<ast::Expr> = arg_list.args().collect();
        let args: Vec<Arg> = arg_exprs
            .iter()
            .map(|arg| match arg {
                ast::Expr::LambdaExpr(_) | ast::Expr::MethodRef(_) => {
                    Arg::MethodRef { arities: None }
                }
                other => Arg::Ty(
                    self.result
                        .type_of(other.syntax().text_range())
                        .cloned()
                        .unwrap_or_default(),
                ),
            })
            .collect();
        info.candidates
            .iter()
            .filter(|candidate| candidate.id != chosen)
            .all(|candidate| {
                let sig = method_sig(self.db, candidate.id);
                self.candidate_rejects(candidate, &sig, &args, &arg_exprs, call_receiver)
            })
    }

    /// 实参擦除后的类型，只在它确定、且能不能传给某个类只取决于这个擦除时给出：基本类型、
    /// 非泛型类，或者类型是声明出来的参数化类型；类的层次结构要可靠。
    fn erased_arg(&self, ty: &Ty, expr: &ast::Expr) -> Option<Ty> {
        match ty {
            Ty::Primitive(_) if self.has_target_free_type(expr) => Some(ty.clone()),
            // `Object` 常常是推断不出来时的退路，不拿它下结论
            Ty::Class(class, _)
                if !ty.contains_unknown()
                    && class.binary_name(self.db) != "java/lang/Object"
                    && self.has_target_free_type(expr)
                    && self.hierarchy_is_reliable(*class) =>
            {
                Some(Ty::class(*class))
            }
            _ => None,
        }
    }

    /// 二元运算符的操作数类型检查（只看两边都是简单类型的情形）。
    #[inline(never)]
    fn check_operands(&mut self, expr: &ast::BinaryExpr, lhs: &Ty, rhs: &Ty) {
        let Some(op) = expr.op_token() else { return };
        let db = self.db;
        // `"" + voidCall()`
        let void_call = |e: Option<ast::Expr>, ty: &Ty| {
            *ty == Ty::Void && matches!(e, Some(ast::Expr::MethodCall(_)))
        };
        let has_void = void_call(expr.lhs(), lhs) || void_call(expr.rhs(), rhs);
        // `count == null`（`int count`）
        let primitive_vs_null = matches!(op.kind(), SyntaxKind::EQ_EQ | SyntaxKind::NEQ)
            && matches!(
                (lhs, rhs),
                (Ty::Primitive(_), Ty::Null) | (Ty::Null, Ty::Primitive(_))
            );
        let ok = if has_void || primitive_vs_null {
            false
        } else if self.is_simple_ty(lhs) && self.is_simple_ty(rhs) {
            self.binary_operands_ok(op.kind(), lhs, rhs)
        } else {
            true
        };
        if !ok {
            self.diagnostic(
                expr.syntax().text_range(),
                InferDiagnosticKind::BadOperand {
                    op: op.text().to_string(),
                    operands: format!("{}, {}", lhs.display(db), rhs.display(db)),
                },
            );
        }
    }

    /// 两边都是简单类型时，二元运算符能否用在这对操作数上。
    fn binary_operands_ok(&self, op: SyntaxKind, lhs: &Ty, rhs: &Ty) -> bool {
        use SyntaxKind::*;
        let db = self.db;
        let numeric = |ty: &Ty| ty.unboxed(db).is_some_and(|p| p.is_numeric());
        let integral = |ty: &Ty| self.is_integral(ty);
        let boolean = |ty: &Ty| ty.unboxed(db) == Some(PrimitiveType::Boolean);
        match op {
            PLUS => self.is_string(lhs) || self.is_string(rhs) || (numeric(lhs) && numeric(rhs)),
            MINUS | STAR | SLASH | PERCENT | LT | GT | LT_EQ | GT_EQ => {
                numeric(lhs) && numeric(rhs)
            }
            SHL | SHR | USHR => integral(lhs) && integral(rhs),
            AMP_AMP | PIPE_PIPE => boolean(lhs) && boolean(rhs),
            AMP | PIPE | CARET => {
                (boolean(lhs) && boolean(rhs)) || (integral(lhs) && integral(rhs))
            }
            EQ_EQ | NEQ => {
                let class_info = |ty: &Ty| match ty {
                    Ty::Class(class, _) => class_header(db, *class).map(|d| d.is_interface()),
                    _ => None,
                };
                let is_concrete_class = |ty: &Ty| class_info(ty) == Some(false);
                match (lhs, rhs) {
                    // 基本类型之间：数值和 boolean 不能比较
                    (Ty::Primitive(_), Ty::Primitive(_)) => numeric(lhs) == numeric(rhs),
                    // 基本类型和引用类型：引用类型要能拆箱成同一类（数值 / boolean）的基本类型。
                    // 只对不是包装类的 final 类（`String`）和包装类下结论
                    (Ty::Primitive(_), Ty::Class(class, _))
                    | (Ty::Class(class, _), Ty::Primitive(_)) => {
                        let (prim, other) = if lhs.is_primitive() {
                            (lhs, rhs)
                        } else {
                            (rhs, lhs)
                        };
                        match other.unboxed(db) {
                            Some(_) => numeric(prim) == numeric(other),
                            None => !class_header(db, *class)
                                .is_some_and(|d| !d.is_interface() && d.flags.is_final()),
                        }
                    }
                    _ if is_concrete_class(lhs) && is_concrete_class(rhs) => {
                        is_subtype(db, lhs, rhs) || is_subtype(db, rhs, lhs)
                    }
                    _ => true,
                }
            }
            _ => true,
        }
    }

    /// 复合赋值（`b += 1`、`x &= true`）：对应的二元运算本身不成立，或者把字符串拼接的结果
    /// 赋回基本类型的变量（`int x; x += "a"`）。
    #[inline(never)]
    pub(super) fn check_compound_assign(
        &mut self,
        expr: &ast::AssignExpr,
        op: &syntax::SyntaxToken,
        lhs: &Ty,
        rhs: &Ty,
    ) {
        use SyntaxKind::*;
        if !self.is_simple_ty(lhs) || !self.is_simple_ty(rhs) {
            return;
        }
        let binary = match op.kind() {
            PLUS_EQ => PLUS,
            MINUS_EQ => MINUS,
            STAR_EQ => STAR,
            SLASH_EQ => SLASH,
            PERCENT_EQ => PERCENT,
            AMP_EQ => AMP,
            PIPE_EQ => PIPE,
            CARET_EQ => CARET,
            SHL_EQ => SHL,
            SHR_EQ => SHR,
            USHR_EQ => USHR,
            _ => return,
        };
        let ok = if binary == PLUS && self.is_string(lhs) {
            true
        } else if binary == PLUS && self.is_string(rhs) {
            lhs.unboxed(self.db).is_none()
        } else {
            self.binary_operands_ok(binary, lhs, rhs)
        };
        if !ok {
            self.diagnostic(
                expr.syntax().text_range(),
                InferDiagnosticKind::BadOperand {
                    op: op.text().to_string(),
                    operands: format!("{}, {}", lhs.display(self.db), rhs.display(self.db)),
                },
            );
        }
    }

    /// 表达式的类型不依赖目标类型：声明出来的类型、字面量、运算结果、非泛型方法的调用。
    pub(super) fn has_target_free_type(&self, expr: &ast::Expr) -> bool {
        match expr {
            ast::Expr::Literal(_) | ast::Expr::BinaryExpr(_) | ast::Expr::UnaryExpr(_) => true,
            ast::Expr::ParenExpr(paren) => {
                paren.expr().is_some_and(|e| self.has_target_free_type(&e))
            }
            _ => has_declared_type(expr) || self.is_certain_call(expr),
        }
    }

    /// 非泛型方法的调用，并且参数个数合得上的候选只有一个：返回类型不取决于重载决议的细节。
    pub(super) fn is_certain_call(&self, expr: &ast::Expr) -> bool {
        let ast::Expr::MethodCall(call) = expr else {
            return false;
        };
        let Some(args) = call.arg_list() else {
            return false;
        };
        if !self.is_non_generic_call(expr) {
            return false;
        }
        let n = args.args().count();
        self.result
            .calls
            .get(&args.syntax().text_range())
            .is_some_and(|info| {
                info.candidates
                    .iter()
                    .filter(|candidate| {
                        let sig = method_sig(self.db, candidate.id);
                        if sig.varargs {
                            n + 1 >= sig.params.len()
                        } else {
                            sig.params.len() == n
                        }
                    })
                    .count()
                    == 1
            })
    }

    /// 表达式的类型完全确定：不依赖目标类型，也不依赖可能出错的推断（泛型方法、菱形、`var`、
    /// 隐式类型的 lambda 形参），一路经过的接收者都不是原始类型。只有这样的类型才能拿来对
    /// 参数化类型下"不兼容"的结论。
    pub(crate) fn type_is_certain(&self, expr: &ast::Expr) -> bool {
        match expr {
            ast::Expr::Literal(_)
            | ast::Expr::CastExpr(_)
            | ast::Expr::ThisExpr(_)
            | ast::Expr::SuperExpr(_)
            | ast::Expr::ClassLiteral(_)
            | ast::Expr::ArrayCreationExpr(_) => true,
            ast::Expr::ParenExpr(it) => it.expr().is_some_and(|e| self.type_is_certain(&e)),
            ast::Expr::BinaryExpr(it) => {
                it.lhs().is_some_and(|e| self.type_is_certain(&e))
                    && it.rhs().is_some_and(|e| self.type_is_certain(&e))
            }
            ast::Expr::UnaryExpr(it) => it.operand().is_some_and(|e| self.type_is_certain(&e)),
            ast::Expr::NewExpr(it) => it.qualifier().is_none() && has_declared_type(expr),
            ast::Expr::ArrayAccess(it) => it.array().is_some_and(|e| self.type_is_certain(&e)),
            ast::Expr::NameExpr(it) => {
                let Some(name) = it.name_ref() else {
                    return false;
                };
                match self.result.resolution(name.syntax().text_range()) {
                    Some(Resolution::Local(local)) => !self.uncertain_locals.contains(local),
                    Some(Resolution::Field(field)) => {
                        self.field_is_static(*field) || self.implicit_receiver_certain(field.class)
                    }
                    _ => false,
                }
            }
            ast::Expr::FieldAccess(it) => {
                let Some(name) = it.name_ref() else {
                    return false;
                };
                match self.result.resolution(name.syntax().text_range()) {
                    Some(Resolution::ArrayLength) => true,
                    Some(Resolution::Field(field)) => {
                        self.field_is_static(*field)
                            || it
                                .receiver()
                                .is_some_and(|r| self.receiver_certain(&r, field.class))
                    }
                    _ => false,
                }
            }
            ast::Expr::MethodCall(it) => {
                let Some(name) = it.name_ref() else {
                    return false;
                };
                let Some(Resolution::Method(method)) =
                    self.result.resolution(name.syntax().text_range())
                else {
                    return false;
                };
                if !self.is_certain_call(expr) {
                    return false;
                }
                // `getClass()` 的类型取决于接收者的静态类型
                if name.text() == "getClass" {
                    return it.receiver().is_none_or(|r| self.type_is_certain(&r));
                }
                method_flags(self, *method).is_static()
                    || match it.receiver() {
                        Some(receiver) => self.receiver_certain(&receiver, method.class),
                        None => self.implicit_receiver_certain(method.class),
                    }
            }
            _ => false,
        }
    }

    /// 类型里有原始类型（泛型类不带类型实参）。
    pub(super) fn mentions_raw(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Class(class, args) => {
                args.is_empty()
                    && class_header(self.db, *class).is_some_and(|d| !d.type_params.is_empty())
                    || args.iter().any(|a| self.mentions_raw(a))
            }
            Ty::Array(element) => self.mentions_raw(element),
            Ty::Wildcard(crate::ty::Wildcard::Extends(b) | crate::ty::Wildcard::Super(b)) => {
                self.mentions_raw(b)
            }
            Ty::Intersection(parts) => parts.iter().any(|p| self.mentions_raw(p)),
            _ => false,
        }
    }

    fn field_is_static(&self, field: hir_def::FieldId) -> bool {
        crate::lower::field_flags(self.db, field).is_some_and(|flags| flags.is_static())
    }

    /// 通过表达式 `receiver` 访问 `declaring` 类的实例成员时，成员的类型是确定的。
    fn receiver_certain(&self, receiver: &ast::Expr, declaring: ClassId) -> bool {
        self.type_is_certain(receiver)
            && !self.inner_of_generic(declaring)
            && self
                .result
                .type_of(receiver.syntax().text_range())
                .is_some_and(|ty| self.member_subst_certain(ty, declaring))
    }

    /// 非静态的内部类，外层类（一直往外）有类型参数：它的成员类型可能用到外层类的类型参数，
    /// 通过别的实例访问时具体是哪个实例化不知道（`Outer<String>.Inner`）。
    fn inner_of_generic(&self, class: ClassId) -> bool {
        let mut current = class;
        loop {
            let Some(data) = class_header(self.db, current) else {
                return true;
            };
            let implicitly_static = data.is_interface()
                || matches!(
                    data.kind,
                    hir_def::ClassKind::Enum | hir_def::ClassKind::Record
                );
            if data.flags.is_static() || implicitly_static {
                return false;
            }
            let Some(outer) = self.outer_class(current) else {
                return false;
            };
            if class_header(self.db, outer).is_some_and(|d| !d.type_params.is_empty()) {
                return true;
            }
            current = outer;
        }
    }

    /// 在类型为 `receiver` 的值上访问 `declaring` 类的实例成员时，代换声明类的类型参数用的
    /// 实参是可靠的：声明类不是泛型类，或者从接收者到声明类一路都没有经过原始类型
    /// （原始类型的成员类型是擦除后的，这里的代换会把类型参数换成 `Object`，不准）。
    pub(crate) fn member_subst_certain(&self, receiver: &Ty, declaring: ClassId) -> bool {
        let Some(data) = class_header(self.db, declaring) else {
            return false;
        };
        if data.type_params.is_empty() {
            return true;
        }
        if !matches!(receiver, Ty::Class(..) | Ty::TypeParam(_)) {
            return false;
        }
        let Some(found) = crate::subtype::find_super_keeping_raw(self.db, receiver, declaring)
        else {
            return false;
        };
        // 通配符实参原样代换进成员类型，丢了捕获变量的声明上界：`Segment<K, V, E extends
        // Entry<K, V, E>, ..>` 的 `seg.table` 在 `Segment<.., ?, ..>` 上实际是
        // `AtomicReferenceArray<CAP extends Entry<..>>`，代换出来却成了 `AtomicReferenceArray<?>`
        !found.type_args().is_empty()
            && found
                .type_args()
                .iter()
                .zip(&data.type_params)
                .all(|(arg, param)| !arg.is_wildcard() || param.bounds.is_empty())
    }

    /// 不带限定符地访问 `declaring` 类的实例成员（接收者是某一层的 `this`）时，成员的类型是确定的。
    pub(crate) fn implicit_receiver_certain(&self, declaring: ClassId) -> bool {
        // 泛型外层类的内部类的成员可能用到外层类的类型参数；只有在内部类本身或它的外层类里
        // 访问时这些类型参数才就是作用域里的那个，通过子类（`class Y<B> extends Red<B>.Orange`）
        // 继承来的成员里外层类的类型参数没有代换
        if self.inner_of_generic(declaring) && !self.lexically_within(declaring) {
            return false;
        }
        if class_header(self.db, declaring).is_some_and(|d| d.type_params.is_empty()) {
            return true;
        }
        for frame in self.frames.iter().rev() {
            if crate::subtype::find_super_keeping_raw(self.db, &frame.this_ty, declaring).is_some()
            {
                return !frame.anonymous && self.member_subst_certain(&frame.this_ty, declaring);
            }
        }
        let mut outer = self.outer_class(self.class);
        while let Some(class) = outer {
            let this = this_ty(self.db, class);
            if crate::subtype::find_super_keeping_raw(self.db, &this, declaring).is_some() {
                return self.member_subst_certain(&this, declaring);
            }
            outer = self.outer_class(class);
        }
        false
    }

    /// 当前所在的类就是 `class`，或者在 `class` 里面（嵌套在它里头）。
    fn lexically_within(&self, class: ClassId) -> bool {
        let mut current = Some(self.class);
        while let Some(c) = current {
            if c == class {
                return true;
            }
            current = self.outer_class(c);
        }
        false
    }

    /// 待推断的类型参数里有当前作用域里也看得见的（递归调用自己、在类里面用菱形构造自己）：
    /// 这时形参类型里的类型参数分不清是待推断的还是作用域里确定的类型变量，不拿它下结论。
    fn inference_overlaps_scope(&self, owners: &[GenericOwner]) -> bool {
        owners.iter().any(|owner| {
            let n = match owner {
                GenericOwner::Method(method) => method_sig(self.db, *method).n_type_params,
                GenericOwner::Class(class) => {
                    class_header(self.db, *class).map_or(0, |d| d.type_params.len() as u32)
                }
            };
            n > 0
                && self.type_param_in_scope(hir_def::TypeParamId {
                    owner: *owner,
                    idx: 0,
                })
        })
    }

    /// 候选方法的形参类型（按接收者代换之后）是可靠的。
    fn candidate_subst_certain(&self, receiver: &super::CallReceiver, method: MethodId) -> bool {
        if method_flags(self, method).is_static() {
            return true;
        }
        match receiver {
            // 隐式接收者自己会看外层类的类型参数有没有代换
            super::CallReceiver::Implicit => self.implicit_receiver_certain(method.class),
            // 泛型外层类的内部类：成员类型里外层类的类型参数没有按接收者代换
            _ if self.inner_of_generic(method.class) => false,
            _ if class_header(self.db, method.class).is_some_and(|d| d.type_params.is_empty()) => {
                true
            }
            super::CallReceiver::Uncertain => false,
            super::CallReceiver::Certain(ty) => self.member_subst_certain(ty, method.class),
        }
    }

    /// 擦除后的类（类型完全已知、层次结构可靠时）。
    pub(super) fn reliable_class(&self, ty: &Ty) -> Option<ClassId> {
        match ty {
            Ty::Class(class, _)
                if !ty.contains_unknown()
                    && !mentions_type_param(ty)
                    && self.hierarchy_is_reliable(*class) =>
            {
                Some(*class)
            }
            _ => None,
        }
    }

    /// `from` 类型的值确定不能强制转换成 `to`（JLS §5.5）。只对基本类型和类型完全已知的类下结论；
    /// 数组、类型变量、交叉类型一律放过。
    fn cast_is_impossible(&self, from: &Ty, to: &Ty) -> bool {
        let db = self.db;
        match (from, to) {
            (Ty::Primitive(a), Ty::Primitive(b)) => {
                (*a == PrimitiveType::Boolean) != (*b == PrimitiveType::Boolean)
            }
            // 装箱后拓宽：`(Object) 1`、`(Number) 1`
            (Ty::Primitive(_), Ty::Class(..)) => match self.reliable_class(to) {
                Some(class) => !is_subtype(db, &from.boxed(db), &Ty::class(class)),
                None => false,
            },
            // 拆箱后拓宽（`(long) integer`），或者先收窄到包装类再拆箱（`(int) object`）
            (Ty::Class(..), Ty::Primitive(target)) => match self.reliable_class(from) {
                Some(class) => match from.unboxed(db) {
                    Some(unboxed) => !crate::subtype::primitive_widens(unboxed, *target),
                    None => !is_subtype(db, &to.boxed(db), &Ty::class(class)),
                },
                None => false,
            },
            (Ty::Class(..), Ty::Class(..)) => {
                let (Some(a), Some(b)) = (self.reliable_class(from), self.reliable_class(to))
                else {
                    return false;
                };
                let (raw_a, raw_b) = (Ty::class(a), Ty::class(b));
                if is_subtype(db, &raw_a, &raw_b) || is_subtype(db, &raw_b, &raw_a) {
                    return false;
                }
                let (Some(data_a), Some(data_b)) = (class_header(db, a), class_header(db, b))
                else {
                    return false;
                };
                match (data_a.is_interface(), data_b.is_interface()) {
                    (false, false) => true,
                    (true, false) => data_b.flags.is_final(),
                    (false, true) => data_a.flags.is_final(),
                    (true, true) => false,
                }
            }
            _ => false,
        }
    }

    /// 引用的是 catch 形参：多重 catch 的形参类型是各个备选的最小上界，这里只记了第一个。
    fn is_catch_param(&self, expr: &ast::Expr) -> bool {
        let ast::Expr::NameExpr(name) = expr else {
            return false;
        };
        name.name_ref().is_some_and(|name_ref| {
            matches!(
                self.result.resolution(name_ref.syntax().text_range()),
                Some(Resolution::Local(local))
                    if self.result.locals[*local as usize].kind == LocalKind::CatchParam
            )
        })
    }

    /// 强制转换 / `instanceof`：值的类型确定转换不过去时报类型不匹配。
    fn check_castable(&mut self, operand: &ast::Expr, from: &Ty, to: &Ty) {
        if self.suppress_unresolved
            || !self.has_target_free_type(operand)
            || self.is_catch_param(operand)
            || !self.cast_is_impossible(from, to)
        {
            return;
        }
        self.diagnostic(
            operand.syntax().text_range(),
            InferDiagnosticKind::TypeMismatch {
                expected: to.display(self.db),
                actual: from.display(self.db),
            },
        );
    }

    /// 函数式接口类型的抽象方法签名：(形参类型, 返回类型)。通配符实参取其界。
    fn functional_sig(&self, target: &Ty) -> Option<(Vec<Ty>, Ty)> {
        let db = self.db;
        let method = functional_method(db, target)?;
        let subst = method.subst.map_types(|ty| ty.wildcard_bound(db));
        let sig = method_sig(db, method.id);
        Some((
            sig.params.iter().map(|p| p.subst(&subst)).collect(),
            sig.ret.subst(&subst),
        ))
    }

    /// 目标类型确定的 lambda（已经按这个目标类型推断过）：检查形参个数、函数体和 void /
    /// 返回值的兼容性，以及返回值的类型。只在目标是层次结构完整、没有未知部分的函数式接口时下结论。
    pub(super) fn check_lambda(&mut self, lambda: &ast::LambdaExpr, target: &Ty) {
        self.check_lambda_against(lambda, target, false);
    }

    /// 泛型方法的实参 lambda：目标类型里还有待推断的类型参数，但函数式接口是哪一个已经由
    /// 声明的形参类型确定，只检查形状——形参个数，以及有没有返回值。
    fn check_lambda_shape(&mut self, lambda: &ast::LambdaExpr, formal: &Ty) {
        self.check_lambda_against(lambda, formal, true);
    }

    fn check_lambda_against(&mut self, lambda: &ast::LambdaExpr, target: &Ty, shape_only: bool) {
        let db = self.db;
        let Ty::Class(class, _) = target else {
            return;
        };
        if (!shape_only && target.contains_unknown())
            || !self.hierarchy_is_reliable(*class)
            || lambda
                .syntax()
                .descendants()
                .any(|n| n.kind() == SyntaxKind::ERROR)
        {
            return;
        }
        let Some(body_range) = lambda
            .body_expr()
            .map(|e| e.syntax().text_range())
            .or_else(|| lambda.body_block().map(|b| b.syntax().text_range()))
        else {
            return;
        };
        let Some(method) = functional_method(db, target) else {
            return;
        };
        let sig = method_sig(db, method.id);
        // 泛型的函数式方法不能用 lambda 实现，那是另一种错误
        if sig.n_type_params != 0 {
            return;
        }
        let arity = lambda.param_list().map_or(0, |p| p.params().count());
        if arity != sig.params.len() {
            self.diagnostic(
                lambda.syntax().text_range(),
                InferDiagnosticKind::LambdaArity {
                    target: target.display(db),
                    expected: sig.params.len(),
                    found: arity,
                },
            );
            return;
        }
        let ret = if shape_only {
            sig.ret.clone()
        } else {
            let Some((_, ret)) = self.functional_sig(target) else {
                return;
            };
            ret
        };
        let returns_value = ret != Ty::Void;
        if lambda_shape_fits(lambda, returns_value) == Some(false) {
            let kind = if returns_value {
                InferDiagnosticKind::LambdaMissingValue {
                    target: target.display(db),
                    expected: ret.display(db),
                }
            } else {
                InferDiagnosticKind::LambdaReturnsValue {
                    target: target.display(db),
                }
            };
            self.diagnostic(body_range, kind);
            return;
        }
        if !returns_value || shape_only {
            return;
        }
        let values = match lambda.body_expr() {
            Some(body) => vec![body],
            None => lambda
                .body_block()
                .map(|block| own_return_values(&block))
                .unwrap_or_default(),
        };
        for value in values {
            let range = value.syntax().text_range();
            if let Some(ty) = self.result.type_of(range).cloned() {
                self.check_assignable(range, &ty, &ret, &value);
            }
        }
    }

    /// 推断 lambda，返回函数体的结果类型（块体没有 `return 值` 时为 `Void`）。
    fn infer_lambda(&mut self, lambda: &ast::LambdaExpr, target: Option<&Ty>) -> Ty {
        let functional = target.and_then(|t| self.functional_sig(t));
        self.push_scope();
        // 隐式类型的形参的类型来自目标类型，只有调用方确认目标类型可靠时才算确定
        let params_certain = std::mem::take(&mut self.lambda_params_certain);
        if let Some(params) = lambda.param_list() {
            for (idx, param) in params.params().enumerate() {
                let (ty, inferred) = match param.ty() {
                    Some(t) if !lower_type(&t).is_var() => (self.lower_ty(&t), false),
                    _ => (
                        functional
                            .as_ref()
                            .and_then(|(params, _)| params.get(idx).cloned())
                            .unwrap_or(Ty::Unknown),
                        true,
                    ),
                };
                if let Some(name) = param.name() {
                    let id = self.declare(&name, ty, LocalKind::LambdaParam);
                    if inferred && !params_certain {
                        self.uncertain_locals.insert(id);
                    }
                }
            }
        }

        // 返回类型还是待推断的类型参数时，不拿它当期望类型
        let expected_ret = functional
            .as_ref()
            .map(|(_, ret)| ret.clone())
            .filter(|ret| !matches!(ret, Ty::Void | Ty::TypeParam(_) | Ty::Unknown));
        self.ret_expected.push(expected_ret.clone());
        self.return_tys.push(Vec::new());

        let mut result = Ty::Void;
        if let Some(block) = lambda.body_block() {
            self.infer_block(&block);
        } else if let Some(body) = lambda.body_expr() {
            result = self.infer_expr(&body, expected_ret.as_ref());
        }

        let returns = self.return_tys.pop().unwrap_or_default();
        self.ret_expected.pop();
        self.pop_scope();

        if lambda.body_block().is_some() {
            result = if returns.is_empty() {
                Ty::Void
            } else {
                returns
                    .into_iter()
                    .find(|ty| !matches!(ty, Ty::Unknown | Ty::Null))
                    .unwrap_or(Ty::Unknown)
            };
        }
        result
    }

    /// 方法引用能匹配哪些函数类型形参个数（JLS 15.12.2.1）：`Type::m` 的静态方法取 m 的
    /// 形参个数，实例方法再加上接收者；`expr::m` 只看实例方法；`Type::new` 看构造器。
    /// 接收者、候选可能不全时返回 `None`。
    fn method_ref_arities(&mut self, method_ref: &ast::MethodRef) -> Option<Vec<(usize, bool)>> {
        let db = self.db;
        let (receiver, is_type) = if let Some(t) = method_ref.receiver_type() {
            (self.lower_ty(&t), true)
        } else {
            let e = method_ref.receiver_expr()?;
            // 选定方法之后接收者还会再推断一遍：这里只推断简单的名字，诊断也不留
            if !matches!(
                e,
                ast::Expr::NameExpr(_) | ast::Expr::FieldAccess(_) | ast::Expr::ThisExpr(_)
            ) {
                return None;
            }
            let n_diagnostics = self.result.diagnostics.len();
            let value = self.infer_value(&e, None);
            self.result.diagnostics.truncate(n_diagnostics);
            match value {
                Value::Ty(ty) => (ty, false),
                Value::Type(class) => (Ty::class(class), true),
                Value::Package(_) => return None,
            }
        };
        let Ty::Class(class, _) = &receiver else {
            return None;
        };
        if receiver.contains_unknown() || !self.hierarchy_is_reliable(*class) {
            return None;
        }
        let constructor = method_ref.is_constructor();
        let candidates = if constructor {
            if !is_type {
                return None;
            }
            constructors(db, *class, &Subst::empty())
        } else {
            lookup_methods(db, &receiver, &method_ref.name_ref()?.text())
        };
        let mut arities = Vec::new();
        for candidate in &candidates {
            let sig = method_sig(db, candidate.id);
            let is_static = !constructor && method_flags(self, candidate.id).is_static();
            let n = match (is_type && !constructor, is_static) {
                (true, true) | (false, false) => sig.params.len(),
                (true, false) => sig.params.len() + 1,
                // `expr::m` 不能引用静态方法
                (false, true) => continue,
            };
            arities.push(if sig.varargs {
                (n - 1, true)
            } else {
                (n, false)
            });
        }
        (!arities.is_empty()).then_some(arities)
    }

    /// 解析方法引用，返回被引用方法的返回类型（构造器引用返回被构造的类型）。
    fn infer_method_ref(&mut self, method_ref: &ast::MethodRef, target: Option<&Ty>) -> Ty {
        let db = self.db;
        let fn_params = target
            .and_then(|t| self.functional_sig(t))
            .map(|(params, _)| params);

        // (接收者类型, 接收者是否是类型名)
        let (receiver, is_type) = if let Some(t) = method_ref.receiver_type() {
            (self.lower_ty(&t), true)
        } else if let Some(e) = method_ref.receiver_expr() {
            match self.infer_value(&e, None) {
                Value::Ty(ty) => (ty, false),
                Value::Type(class) => (Ty::class(class), true),
                Value::Package(_) => return Ty::Unknown,
            }
        } else {
            return Ty::Unknown;
        };

        if method_ref.is_constructor() {
            if !is_type {
                return Ty::Unknown;
            }
            // `Foo::new`：按函数类型的形参选构造器，记在整个方法引用上（跳转、悬停用）
            if let Ty::Class(class, _) = &receiver {
                let candidates = constructors(db, *class, &crate::ty::Subst::empty());
                let chosen = method_ref_target(db, &candidates, fn_params.as_deref(), &|_| false);
                if let Some(chosen) = chosen {
                    self.result.resolutions.insert(
                        method_ref.syntax().text_range(),
                        Resolution::Method(chosen.id),
                    );
                }
            }
            return receiver;
        }
        let Some(name_ref) = method_ref.name_ref() else {
            return Ty::Unknown;
        };
        // `List::stream` 用在函数类型的第一个形参是 `List<Integer>` 的地方：接收者是这个参数化
        // （JLS §15.13.1），不是原始类型
        let receiver = match &receiver {
            Ty::Class(class, args)
                if is_type
                    && args.is_empty()
                    && class_header(db, *class).is_some_and(|d| !d.type_params.is_empty()) =>
            {
                fn_params
                    .as_ref()
                    .and_then(|params| params.first().cloned())
                    .filter(|first| !first.contains_unknown())
                    .and_then(|first| crate::subtype::find_super_keeping_raw(db, &first, *class))
                    .filter(|lifted| !lifted.type_args().is_empty())
                    .unwrap_or(receiver)
            }
            _ => receiver,
        };
        let candidates = lookup_methods(db, &receiver, &name_ref.text());

        // `Type::instanceMethod`：函数类型的第一个形参当接收者
        let takes_receiver =
            |candidate: &MethodCandidate| is_type && !method_flags(self, candidate.id).is_static();
        let chosen =
            method_ref_target(db, &candidates, fn_params.as_deref(), &takes_receiver).cloned();
        match chosen {
            Some(candidate) => {
                self.result.resolutions.insert(
                    name_ref.syntax().text_range(),
                    Resolution::Method(candidate.id),
                );
                // `Map.Entry::getKey`：接收者写的是不带实参的泛型类，真正的类型实参要靠
                // 目标类型推断，这里得不到，按未知处理（否则会当成原始类型擦除成 Object）
                let raw_generic_receiver = is_type
                    && matches!(&receiver, Ty::Class(class, args) if args.is_empty()
                        && hir_def::class_header(db, *class).is_some_and(|d| !d.type_params.is_empty()));
                // 返回类型不涉及类的类型参数时（`List::size`）不受影响
                if raw_generic_receiver && mentions_type_param(&method_sig(db, candidate.id).ret) {
                    return Ty::Unknown;
                }
                candidate
                    .ret_ty(db)
                    .erase_params_of(GenericOwner::Method(candidate.id))
            }
            None => Ty::Unknown,
        }
    }

    // ---- 运算 ----

    fn infer_array_initializer(&mut self, init: &ast::ArrayInitializer, array_ty: &Ty) {
        let element = match array_ty {
            Ty::Array(element) => Some((**element).clone()),
            _ => None,
        };
        for expr in init.exprs() {
            let actual = self.infer_expr(&expr, element.as_ref());
            if let Some(element) = &element {
                if !matches!(expr, ast::Expr::ArrayInitializer(_)) && !element.contains_unknown() {
                    self.check_assignable(expr.syntax().text_range(), &actual, element, &expr);
                }
            }
        }
    }

    /// 数组下标和数组长度要能提升成 int（`a["x"]`、`new int[1L]`）。
    #[inline(never)]
    fn check_index(&mut self, index: &ast::Expr, ty: &Ty) {
        let integral = matches!(
            ty.unboxed(self.db),
            Some(
                PrimitiveType::Byte
                    | PrimitiveType::Short
                    | PrimitiveType::Char
                    | PrimitiveType::Int
            )
        );
        if !integral && self.is_simple_ty(ty) && self.has_target_free_type(index) {
            self.diagnostic(
                index.syntax().text_range(),
                InferDiagnosticKind::TypeMismatch {
                    expected: Ty::INT.display(self.db),
                    actual: ty.display(self.db),
                },
            );
        }
    }

    fn unary_promote(&self, ty: &Ty) -> Ty {
        match ty.unboxed(self.db) {
            Some(
                PrimitiveType::Byte
                | PrimitiveType::Short
                | PrimitiveType::Char
                | PrimitiveType::Int,
            ) => Ty::INT,
            Some(PrimitiveType::Boolean) | None => Ty::Unknown,
            Some(other) => Ty::Primitive(other),
        }
    }

    fn is_string(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Class(class, _) if class.binary_name(self.db) == "java/lang/String")
    }

    fn numeric_result(&self, lhs: &Ty, rhs: &Ty) -> Ty {
        match (lhs.unboxed(self.db), rhs.unboxed(self.db)) {
            (Some(a), Some(b)) if a.is_numeric() && b.is_numeric() => {
                Ty::Primitive(binary_numeric_promotion(a, b))
            }
            _ => Ty::Unknown,
        }
    }

    fn is_integral(&self, ty: &Ty) -> bool {
        matches!(
            ty.unboxed(self.db),
            Some(
                PrimitiveType::Byte
                    | PrimitiveType::Short
                    | PrimitiveType::Char
                    | PrimitiveType::Int
                    | PrimitiveType::Long
            )
        )
    }

    fn binary_result(&self, op: Option<SyntaxKind>, lhs: &Ty, rhs: &Ty) -> Ty {
        use SyntaxKind::*;
        match op {
            Some(EQ_EQ | NEQ | LT | GT | LT_EQ | GT_EQ | AMP_AMP | PIPE_PIPE) => Ty::BOOLEAN,
            Some(PLUS) if self.is_string(lhs) || self.is_string(rhs) => Ty::string(self.db),
            Some(AMP | PIPE | CARET) => {
                let is_bool = |ty: &Ty| ty.unboxed(self.db) == Some(PrimitiveType::Boolean);
                if is_bool(lhs) && is_bool(rhs) {
                    Ty::BOOLEAN
                } else if self.is_integral(lhs) && self.is_integral(rhs) {
                    self.numeric_result(lhs, rhs)
                } else {
                    Ty::Unknown
                }
            }
            // 移位的结果是左操作数提升后的类型；浮点操作数本身就是错误，结果不再往下传
            Some(SHL | SHR | USHR) => {
                let non_integral = |ty: &Ty| ty.unboxed(self.db).is_some() && !self.is_integral(ty);
                if non_integral(lhs) || non_integral(rhs) {
                    Ty::Unknown
                } else {
                    self.unary_promote(lhs)
                }
            }
            Some(PLUS | MINUS | STAR | SLASH | PERCENT) => self.numeric_result(lhs, rhs),
            _ => Ty::Unknown,
        }
    }

    /// 条件表达式两个分支的合并类型（JLS §15.25 的简化版）。
    fn merge_branches(&self, a: &Ty, b: &Ty) -> Ty {
        let db = self.db;
        if a == b {
            return a.clone();
        }
        match (a, b) {
            // 另一个分支是 `null` 时结果就是那个推不出来的类型，不能当作 `null` 往下用
            (Ty::Unknown, Ty::Null) | (Ty::Null, Ty::Unknown) => Ty::Unknown,
            (Ty::Unknown, other) | (other, Ty::Unknown) => other.clone(),
            (Ty::Null, other) | (other, Ty::Null) => other.boxed(db),
            _ => {
                if a.is_primitive() || b.is_primitive() {
                    // 基本类型和它的包装类（`byte` 和 `Byte`）得到这个基本类型，`byte` 和 `short`
                    // 得到 `short`，不做二元数值提升（JLS §15.25）
                    if let (Some(x), Some(y)) = (a.unboxed(db), b.unboxed(db)) {
                        use PrimitiveType::{Byte, Short};
                        if x == y {
                            return Ty::Primitive(x);
                        }
                        if matches!((x, y), (Byte, Short) | (Short, Byte)) {
                            return Ty::Primitive(Short);
                        }
                    }
                    let numeric = self.numeric_result(a, b);
                    if !numeric.is_unknown() {
                        return numeric;
                    }
                }
                let (a, b) = (a.boxed(db), b.boxed(db));
                if is_subtype(db, &a, &b) {
                    b
                } else {
                    a
                }
            }
        }
    }
}

/// 表达式的类型直接来自声明，不依赖推断：变量、字段、`this`、强制转换、显式写出类型实参
/// （或非泛型）的 `new`。
pub(crate) fn has_declared_type(expr: &ast::Expr) -> bool {
    match expr {
        ast::Expr::NameExpr(_)
        | ast::Expr::FieldAccess(_)
        | ast::Expr::ThisExpr(_)
        | ast::Expr::CastExpr(_)
        | ast::Expr::ArrayAccess(_) => true,
        ast::Expr::ParenExpr(paren) => paren.expr().is_some_and(|e| has_declared_type(&e)),
        ast::Expr::NewExpr(new) => {
            new.body().is_none()
                && new
                    .ty()
                    .is_some_and(|t| !t.syntax().text().to_string().contains("<>"))
        }
        _ => false,
    }
}
