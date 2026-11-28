//! 声明层面和上下文相关的类型检查：
//!
//! - 给 `final` 变量 / 字段赋值；
//! - 带限定符访问别的类的私有成员；
//! - `void` 方法里 `return 值;`、非 `void` 方法里空的 `return;`；
//! - 静态上下文里用简单名引用实例成员；
//! - 非抽象类没有实现继承来的抽象方法；
//! - 覆写时收窄了访问级别、覆写了 `final` 方法、返回类型不兼容（父类型的类型实参代换之后
//!   比较）；从父类继承来、用来实现接口方法的方法不合格；
//! - 继承 sealed 类型却不在它允许的子类型里（包括匿名类和局部类）；
//! - 对枚举的 switch 表达式没有覆盖所有常量；
//! - 泛型类的类型实参不在类型参数的上界之内（`Box<String>`，而 `Box<T extends Number>`）；
//! - 类型实参是基本类型或个数不对，静态上下文里引用外层类的类型参数；
//! - 父类没有无参构造器，子类却隐式调用 `super()`。
//!
//! 和其它语义诊断一样只报确定的：涉及泛型、解析不全的继承链、Lombok 的地方一律跳过。

use base_db::{Db, SourceFile};
use hir::{
    all_super_tys, class_data, class_header, is_accessible, is_subtype, method_sig, BodyId,
    ClassId, ClassKind, GenericOwner, InferenceResult, MethodId, Modifiers, PrimitiveType,
    Resolution, Semantics, Subst, Ty, Visibility, Wildcard,
};
use syntax::{
    ast::{self, AstNode},
    SyntaxKind, SyntaxNode, TextRange,
};

use crate::{hierarchy_is_resolved, view::View, Diagnostic, DiagnosticCode, Severity};

fn error(range: TextRange, code: DiagnosticCode, message: String) -> Diagnostic {
    Diagnostic {
        range,
        message,
        severity: Severity::Error,
        code,
        unused: false,
    }
}

fn uses_lombok(db: &dyn Db, class: ClassId) -> bool {
    class_header(db, class)
        .is_some_and(|data| data.annotations.iter().any(|a| a.contains("lombok")))
}

fn has_final(node: &SyntaxNode) -> bool {
    node.children()
        .find_map(ast::ModifierList::cast)
        .is_some_and(|list| list.has(SyntaxKind::FINAL_KW))
}

/// 声明的类型是 Lombok 的 `val`（隐含 `final`）。
fn is_lombok_val(db: &dyn Db, decl: &SyntaxNode) -> bool {
    let Some(ty) = decl.children().find_map(ast::Type::cast) else {
        return false;
    };
    let text = ty.syntax().text().to_string();
    matches!(text.trim(), "val" | "lombok.val") && hir::lookup_class(db, "lombok/val").is_some()
}

fn strip_parens(mut node: SyntaxNode) -> SyntaxNode {
    while node.kind() == SyntaxKind::PAREN_EXPR {
        match node.children().find(|c| ast::Expr::can_cast(c.kind())) {
            Some(inner) => node = inner,
            None => break,
        }
    }
    node
}

/// 名字表达式或字段访问里被引用的那个名字节点，以及它是否带限定符。
fn referenced_name(expr: &SyntaxNode) -> Option<(SyntaxNode, bool)> {
    let qualified = match expr.kind() {
        SyntaxKind::NAME_EXPR => false,
        SyntaxKind::FIELD_ACCESS => true,
        _ => return None,
    };
    let name = expr
        .children()
        .filter(|c| c.kind() == SyntaxKind::NAME_REF)
        .last()?;
    Some((name, qualified))
}

fn field_flags(db: &dyn Db, field: hir::FieldId) -> Option<Modifiers> {
    hir::field_flags(db, field)
}

fn method_flags(db: &dyn Db, method: MethodId) -> Option<(Modifiers, bool)> {
    hir::method_data(db, method).map(|m| (m.flags, m.is_constructor))
}

/// 被赋值的表达式（`x = ..`、`x += ..`、`x++`、`--x` 的 `x`）。
fn assignment_targets(body: &SyntaxNode) -> Vec<SyntaxNode> {
    let mut res = Vec::new();
    for node in body.descendants() {
        let target = match node.kind() {
            SyntaxKind::ASSIGN_EXPR => node.children().find(|c| ast::Expr::can_cast(c.kind())),
            SyntaxKind::UNARY_EXPR | SyntaxKind::POSTFIX_EXPR => {
                let mutates = node
                    .children_with_tokens()
                    .any(|e| matches!(e.kind(), SyntaxKind::PLUS_PLUS | SyntaxKind::MINUS_MINUS));
                if mutates {
                    node.children().find(|c| ast::Expr::can_cast(c.kind()))
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(target) = target {
            res.push(strip_parens(target));
        }
    }
    res
}

fn final_assignments(
    db: &dyn Db,
    sema: &Semantics<'_>,
    file: SourceFile,
    body: &SyntaxNode,
    result: &InferenceResult,
    out: &mut Vec<Diagnostic>,
) {
    for target in assignment_targets(body) {
        let Some((name, _)) = referenced_name(&target) else {
            continue;
        };
        let range = name.text_range();
        match result.resolution(range) {
            Some(Resolution::Local(id)) => {
                let local = result.local(*id);
                if !body.text_range().contains_range(local.decl_range) {
                    continue;
                }
                let decl = match body.covering_element(local.decl_range) {
                    syntax::NodeOrToken::Node(node) => Some(node),
                    syntax::NodeOrToken::Token(token) => token.parent(),
                };
                let Some(declarator) = decl.and_then(|n| {
                    n.ancestors().find(|a| {
                        matches!(
                            a.kind(),
                            SyntaxKind::VARIABLE_DECLARATOR
                                | SyntaxKind::PARAM
                                | SyntaxKind::RESOURCE
                        )
                    })
                }) else {
                    continue;
                };
                let is_final = match declarator.kind() {
                    // try-with-resources 的资源隐含 final
                    SyntaxKind::RESOURCE => true,
                    SyntaxKind::PARAM => has_final(&declarator) || is_lombok_val(db, &declarator),
                    // `final int x;` 之后的第一次赋值是合法的，需要"确定未赋值"分析，这里只看带初值的
                    _ => {
                        let has_initializer = ast::VariableDeclarator::cast(declarator.clone())
                            .is_some_and(|d| d.initializer().is_some());
                        has_initializer
                            && declarator
                                .parent()
                                .is_some_and(|p| has_final(&p) || is_lombok_val(db, &p))
                    }
                };
                if is_final {
                    out.push(error(
                        range,
                        DiagnosticCode::AssignToFinal,
                        base_db::tr!(
                            "不能给 final 变量 `{}` 赋值",
                            "Cannot assign a value to final variable `{}`",
                            local.name
                        ),
                    ));
                }
            }
            Some(Resolution::Field(field)) => {
                if !field_flags(db, *field).is_some_and(|f| f.contains(Modifiers::FINAL)) {
                    continue;
                }
                // 本类的构造器、初始化块和字段初值里可以给没有初值的 final 字段赋初值
                if crate::final_fields::may_assign_final_field(db, sema, file, &target, *field)
                    != Some(false)
                {
                    continue;
                }
                out.push(error(
                    range,
                    DiagnosticCode::AssignToFinal,
                    base_db::tr!(
                        "不能给 final 字段 `{}` 赋值",
                        "Cannot assign a value to final field `{}`",
                        name.text()
                    ),
                ));
            }
            _ => {}
        }
    }
}

/// `obj.secret` / `obj.secret()`：成员是别的顶层类的私有成员。
fn private_access(
    db: &dyn Db,
    body: BodyId,
    node: &SyntaxNode,
    result: &InferenceResult,
    out: &mut Vec<Diagnostic>,
) {
    for access in node.descendants() {
        let name = match access.kind() {
            SyntaxKind::FIELD_ACCESS => access
                .children()
                .filter(|c| c.kind() == SyntaxKind::NAME_REF)
                .last(),
            SyntaxKind::METHOD_CALL => {
                let call = ast::MethodCall::cast(access.clone());
                call.filter(|c| c.receiver().is_some())
                    .and_then(|c| c.name_ref())
                    .map(|n| n.syntax().clone())
            }
            _ => None,
        };
        let Some(name) = name else { continue };
        let (flags, declaring) = match result.resolution(name.text_range()) {
            Some(Resolution::Field(field)) => match field_flags(db, *field) {
                Some(flags) => (flags, field.class),
                None => continue,
            },
            Some(Resolution::Method(method)) => match method_flags(db, *method) {
                Some((flags, false)) => (flags, method.class),
                _ => continue,
            },
            _ => continue,
        };
        if flags.visibility() == Visibility::Private
            && !is_accessible(db, flags, declaring, Some(body.class()))
        {
            let owner = class_header(db, declaring)
                .map(|d| d.name.to_string())
                .unwrap_or_default();
            out.push(error(
                name.text_range(),
                DiagnosticCode::InaccessibleMember,
                base_db::tr!(
                    "`{}` 是 `{owner}` 的私有成员，这里不能访问",
                    "`{}` has private access in `{owner}`",
                    name.text()
                ),
            ));
        }
    }
}

/// 静态上下文里用简单名引用实例字段 / 实例方法。
fn static_context(
    db: &dyn Db,
    body: BodyId,
    node: &SyntaxNode,
    result: &InferenceResult,
    out: &mut Vec<Diagnostic>,
) {
    let is_static = match body {
        BodyId::Method(method) => {
            method_flags(db, method).is_some_and(|(flags, ctor)| flags.is_static() && !ctor)
        }
        BodyId::Field(field) => field_flags(db, field).is_some_and(|f| f.is_static()),
        BodyId::Initializer { .. } => node
            .children_with_tokens()
            .any(|e| e.kind() == SyntaxKind::STATIC_KW),
    };
    if !is_static {
        return;
    }
    // 匿名类 / 局部类的类体有自己的 this
    let in_nested_class = |n: &SyntaxNode| {
        n.ancestors()
            .take_while(|a| a != node)
            .any(|a| a.kind() == SyntaxKind::CLASS_BODY || ast::TypeDecl::can_cast(a.kind()))
    };
    for this in node.descendants().filter(|n| {
        matches!(n.kind(), SyntaxKind::THIS_EXPR | SyntaxKind::SUPER_EXPR)
            // `Outer.this` / `Iface.super` 带限定符的形式不在这里判断
            && n.children().next().is_none()
    }) {
        if !in_nested_class(&this) {
            out.push(error(
                this.text_range(),
                DiagnosticCode::StaticContext,
                base_db::tr!(
                    "不能在静态上下文里使用 `{}`",
                    "Cannot use `{}` in a static context",
                    this.text()
                ),
            ));
        }
    }
    for name in node
        .descendants()
        .filter(|n| n.kind() == SyntaxKind::NAME_REF)
    {
        let Some(parent) = name.parent() else {
            continue;
        };
        let unqualified = match parent.kind() {
            SyntaxKind::NAME_EXPR => true,
            SyntaxKind::METHOD_CALL => {
                ast::MethodCall::cast(parent.clone()).is_some_and(|c| c.receiver().is_none())
            }
            _ => false,
        };
        if !unqualified {
            continue;
        }
        if in_nested_class(&name) {
            continue;
        }
        let (flags, declaring, what) = match result.resolution(name.text_range()) {
            Some(Resolution::Field(field)) => match field_flags(db, *field) {
                Some(flags) => (flags, field.class, base_db::trs!("字段", "field")),
                None => continue,
            },
            Some(Resolution::Method(method)) => match method_flags(db, *method) {
                Some((flags, false)) => (flags, method.class, base_db::trs!("方法", "method")),
                _ => continue,
            },
            _ => continue,
        };
        // 接口里的字段隐含 static
        let Some(owner) = class_header(db, declaring) else {
            continue;
        };
        if flags.is_static() || (what == base_db::trs!("字段", "field") && owner.is_interface()) {
            continue;
        }
        out.push(error(
            name.text_range(),
            DiagnosticCode::StaticContext,
            base_db::tr!(
                "不能在静态上下文里引用实例{what} `{}`",
                "Cannot reference instance {what} `{}` from a static context",
                name.text()
            ),
        ));
    }
}

/// `new` 一个抽象类或接口（不带类体）。
fn abstract_instantiations(
    db: &dyn Db,
    node: &SyntaxNode,
    result: &InferenceResult,
    out: &mut Vec<Diagnostic>,
) {
    for new in node.descendants().filter_map(ast::NewExpr::cast) {
        if new.body().is_some() {
            continue;
        }
        let Some(ast::Type::ClassType(ty)) = new.ty() else {
            continue;
        };
        let Some(Ty::Class(class, _)) = result.type_of(new.syntax().text_range()) else {
            continue;
        };
        let Some(data) = class_header(db, *class) else {
            continue;
        };
        let abstract_class = data.flags.contains(hir::Modifiers::ABSTRACT);
        if !(data.is_interface() || abstract_class) || data.kind == ClassKind::Enum {
            continue;
        }
        let name = data.name.clone();
        out.push(error(
            ty.syntax().text_range(),
            DiagnosticCode::AbstractInstantiation,
            if data.is_interface() {
                base_db::tr!(
                    "`{name}` 是接口，不能实例化",
                    "`{name}` is an interface and cannot be instantiated"
                )
            } else {
                base_db::tr!(
                    "`{name}` 是抽象类，不能实例化",
                    "`{name}` is abstract and cannot be instantiated"
                )
            },
        ));
    }
}

/// `break` / `continue` 不在循环（`break` 也可以在 switch 语句）里，或者标签不存在。
fn misplaced_jumps(node: &SyntaxNode, out: &mut Vec<Diagnostic>) {
    for jump in node.descendants() {
        let (is_break, label) = match jump.kind() {
            SyntaxKind::BREAK_STMT => (
                true,
                ast::BreakStmt::cast(jump.clone()).and_then(|b| b.label()),
            ),
            SyntaxKind::CONTINUE_STMT => (
                false,
                ast::ContinueStmt::cast(jump.clone()).and_then(|c| c.label()),
            ),
            _ => continue,
        };
        let is_loop = |kind: SyntaxKind| {
            matches!(
                kind,
                SyntaxKind::FOR_STMT
                    | SyntaxKind::FOREACH_STMT
                    | SyntaxKind::WHILE_STMT
                    | SyntaxKind::DO_WHILE_STMT
            )
        };
        let mut found = false;
        for ancestor in jump.ancestors().skip(1) {
            let kind = ancestor.kind();
            // 跳转不能越过方法、lambda、类体和 switch 表达式
            if matches!(
                kind,
                SyntaxKind::METHOD_DECL
                    | SyntaxKind::CONSTRUCTOR_DECL
                    | SyntaxKind::INITIALIZER_BLOCK
                    | SyntaxKind::LAMBDA_EXPR
                    | SyntaxKind::CLASS_BODY
                    | SyntaxKind::SWITCH_EXPR
                    | SyntaxKind::FIELD_DECL
            ) {
                break;
            }
            match &label {
                Some(label) => {
                    let Some(labeled) = ast::LabeledStmt::cast(ancestor.clone()) else {
                        continue;
                    };
                    if labeled.label().is_some_and(|l| l.text() == label.text()) {
                        // `continue L` 的 L 必须标在循环上
                        found =
                            is_break || labeled.body().is_some_and(|b| is_loop(b.syntax().kind()));
                        break;
                    }
                }
                None => {
                    if is_loop(kind) || (is_break && kind == SyntaxKind::SWITCH_STMT) {
                        found = true;
                        break;
                    }
                }
            }
        }
        // switch 表达式里的跳转规则另有讲究，不在这里判断
        let crossed_switch_expr = jump
            .ancestors()
            .skip(1)
            .take_while(|a| {
                !matches!(
                    a.kind(),
                    SyntaxKind::METHOD_DECL
                        | SyntaxKind::CONSTRUCTOR_DECL
                        | SyntaxKind::LAMBDA_EXPR
                        | SyntaxKind::CLASS_BODY
                )
            })
            .any(|a| a.kind() == SyntaxKind::SWITCH_EXPR);
        if found || crossed_switch_expr {
            continue;
        }
        let keyword = if is_break { "break" } else { "continue" };
        let message = match &label {
            Some(label) => base_db::tr!(
                "`{keyword}` 的标签 `{}` 不存在或者不能用在这里",
                "Label `{}` of `{keyword}` is undefined or cannot be used here",
                label.text()
            ),
            None if is_break => base_db::trs!(
                "`break` 不在循环或 switch 里",
                "`break` outside of a loop or switch"
            )
            .to_owned(),
            None => {
                base_db::trs!("`continue` 不在循环里", "`continue` outside of a loop").to_owned()
            }
        };
        out.push(error(
            jump.text_range(),
            DiagnosticCode::MisplacedJump,
            message,
        ));
    }
}

/// 同一个 switch 里重复的常量标签（字面量、枚举常量、`default`）。
fn duplicate_case_labels(node: &SyntaxNode, out: &mut Vec<Diagnostic>) {
    for block in node
        .descendants()
        .filter(|n| n.kind() == SyntaxKind::SWITCH_BLOCK)
    {
        let mut seen: Vec<String> = Vec::new();
        for label in block
            .children()
            .filter_map(ast::SwitchCase::cast)
            .filter_map(|c| c.label())
        {
            if label.is_default() {
                if seen.iter().any(|s| s == "default") {
                    out.push(error(
                        label.syntax().text_range(),
                        DiagnosticCode::DuplicateCaseLabel,
                        base_db::trs!("重复的 `default` 标签", "Duplicate `default` label")
                            .to_owned(),
                    ));
                }
                seen.push("default".to_owned());
                continue;
            }
            for expr in label.exprs() {
                let key = match &expr {
                    ast::Expr::Literal(_) | ast::Expr::NameExpr(_) => {
                        expr.syntax().text().to_string()
                    }
                    _ => continue,
                };
                if seen.contains(&key) {
                    out.push(error(
                        expr.syntax().text_range(),
                        DiagnosticCode::DuplicateCaseLabel,
                        base_db::tr!("重复的 case 标签 `{key}`", "Duplicate case label `{key}`"),
                    ));
                } else {
                    seen.push(key);
                }
            }
        }
    }
}

/// 用类名限定的实例成员：`List.size()`、`Main.helper()`、`Point.x`。
fn type_qualified_instance_members(
    db: &dyn Db,
    node: &SyntaxNode,
    result: &InferenceResult,
    out: &mut Vec<Diagnostic>,
) {
    for qualified in node.descendants() {
        let (receiver, name) = match qualified.kind() {
            SyntaxKind::METHOD_CALL => {
                let Some(call) = ast::MethodCall::cast(qualified.clone()) else {
                    continue;
                };
                // 实参类型不知道时选中的重载不可靠（可能还有同名的静态重载）
                let args_known = call.arg_list().is_none_or(|list| {
                    list.args().all(|arg| {
                        result
                            .type_of(arg.syntax().text_range())
                            .is_some_and(|ty| !ty.contains_unknown())
                    })
                });
                if !args_known {
                    continue;
                }
                (call.receiver(), call.name_ref())
            }
            SyntaxKind::FIELD_ACCESS => {
                let Some(access) = ast::FieldAccess::cast(qualified.clone()) else {
                    continue;
                };
                (access.receiver(), access.name_ref())
            }
            _ => continue,
        };
        let (Some(receiver), Some(name)) = (receiver, name) else {
            continue;
        };
        // 接收者是类型名
        let receiver_name = match &receiver {
            ast::Expr::NameExpr(n) => n.name_ref(),
            ast::Expr::FieldAccess(a) => a.name_ref(),
            _ => None,
        };
        let is_type = receiver_name.is_some_and(|r| {
            matches!(
                result.resolution(r.syntax().text_range()),
                Some(Resolution::Class(_))
            )
        });
        if !is_type {
            continue;
        }
        let (flags, declaring, what) = match result.resolution(name.syntax().text_range()) {
            Some(Resolution::Field(field)) => match field_flags(db, *field) {
                Some(flags) => (flags, field.class, base_db::trs!("字段", "field")),
                None => continue,
            },
            Some(Resolution::Method(method)) => match method_flags(db, *method) {
                Some((flags, false)) => (flags, method.class, base_db::trs!("方法", "method")),
                _ => continue,
            },
            _ => continue,
        };
        let Some(owner) = class_header(db, declaring) else {
            continue;
        };
        if flags.is_static() || (what == base_db::trs!("字段", "field") && owner.is_interface()) {
            continue;
        }
        out.push(error(
            name.syntax().text_range(),
            DiagnosticCode::StaticContext,
            base_db::tr!(
                "不能通过类名引用实例{what} `{}`",
                "Cannot reference instance {what} `{}` through the class name",
                name.text()
            ),
        ));
    }
}

/// 直接属于 `callable` 的 `return` 语句（不进入 lambda 和类体）。
fn own_returns(callable: &SyntaxNode) -> Vec<ast::ReturnStmt> {
    fn walk(node: &SyntaxNode, out: &mut Vec<ast::ReturnStmt>) {
        for child in node.children() {
            if matches!(
                child.kind(),
                SyntaxKind::LAMBDA_EXPR | SyntaxKind::CLASS_BODY | SyntaxKind::SWITCH_EXPR
            ) || ast::TypeDecl::can_cast(child.kind())
            {
                continue;
            }
            if let Some(ret) = ast::ReturnStmt::cast(child.clone()) {
                out.push(ret);
            }
            walk(&child, out);
        }
    }
    let mut out = Vec::new();
    walk(callable, &mut out);
    out
}

fn return_values(view: &View<'_>, out: &mut Vec<Diagnostic>) {
    for node in view.nodes() {
        let returns_value = match node.kind() {
            SyntaxKind::METHOD_DECL => {
                let Some(method) = ast::MethodDecl::cast(node.clone()) else {
                    continue;
                };
                if method.body().is_none() {
                    continue;
                }
                match method.return_type() {
                    Some(ty) => ty.syntax().text() != "void",
                    None => continue,
                }
            }
            SyntaxKind::CONSTRUCTOR_DECL | SyntaxKind::INITIALIZER_BLOCK => false,
            _ => continue,
        };
        for ret in own_returns(&node) {
            let has_value = ret.expr().is_some();
            if has_value && !returns_value {
                out.push(error(
                    ret.syntax().text_range(),
                    DiagnosticCode::TypeMismatch,
                    base_db::tr!(
                        "这里不能返回值：所在的方法没有返回类型",
                        "Cannot return a value here: the enclosing method has no return type"
                    ),
                ));
            } else if !has_value && returns_value {
                out.push(error(
                    ret.syntax().text_range(),
                    DiagnosticCode::TypeMismatch,
                    base_db::tr!("缺少返回值", "Missing return value"),
                ));
            }
        }
    }
}

/// `Object` 的公有方法：接口里重新声明它们不算抽象方法。
fn is_object_method(name: &str, arity: usize) -> bool {
    matches!(
        (name, arity),
        ("equals", 1) | ("hashCode", 0) | ("toString", 0)
    )
}

/// 枚举声明里有带类体的常量。
fn enum_has_constant_bodies(decl: &SyntaxNode) -> bool {
    decl.kind() == SyntaxKind::ENUM_DECL
        && decl
            .children()
            .filter(|n| n.kind() == SyntaxKind::CLASS_BODY)
            .flat_map(|body| body.children().filter_map(ast::EnumConstant::cast))
            .any(|constant| constant.body().is_some())
}

/// 类（名字是 `name`，诊断报在 `range` 上）和它继承来的抽象方法之间的检查：
///
/// - 具体类没有实现某个抽象方法（返回类型不兼容的同签名方法不算实现）；
/// - 从父类继承来、用来实现抽象方法的方法不合格：静态方法、访问级别更窄、返回类型不兼容
///   （javac 报在类上："`A.m()` 不能实现 `I.m()`"）。
fn missing_implementation(
    db: &dyn Db,
    class: ClassId,
    name: &str,
    range: TextRange,
    out: &mut Vec<Diagnostic>,
) {
    let Some(data) = class_data(db, class) else {
        return;
    };
    if !matches!(
        data.kind,
        ClassKind::Class | ClassKind::Record | ClassKind::Enum
    ) || uses_lombok(db, class)
        || !hierarchy_is_resolved(db, class)
    {
        return;
    }
    let Some(methods) = inherited_methods(db, class) else {
        return;
    };
    if let Some(message) = inherited_implementation_problem(db, class, &methods) {
        out.push(error(range, DiagnosticCode::InvalidOverride, message));
    }
    if data.flags.is_abstract() {
        return;
    }
    let missing = unimplemented_abstract_methods(db, class, &methods);
    let Some(first) = missing.first() else {
        return;
    };
    out.push(error(
        range,
        DiagnosticCode::MissingImplementation,
        base_db::tr!(
            "`{name}` 不是抽象类，却没有实现抽象方法 `{first}`{}",
            "`{name}` is not abstract and does not implement abstract method `{first}`{}",
            if missing.len() > 1 {
                base_db::tr!(" 等 {} 个方法", " and {} more", missing.len())
            } else {
                String::new()
            }
        ),
    ));
}

/// 类自己和父类型里声明的一个方法，父类型的类型实参已经代换进去。
struct InheritedMethod {
    owner: ClassId,
    owner_is_interface: bool,
    name: hir::Name,
    flags: Modifiers,
    /// 擦除后的形参类型，见 [`erased_param_keys`]
    keys: Vec<Option<String>>,
    params: Vec<Ty>,
    ret: Ty,
}

impl InheritedMethod {
    fn is_abstract(&self) -> bool {
        self.flags.is_abstract() && !self.flags.is_static()
    }

    /// 两个方法的形参类型完全相同（不只是擦除后相同）。
    fn same_params(&self, db: &dyn Db, other: &InheritedMethod) -> bool {
        self.params.len() == other.params.len()
            && self
                .params
                .iter()
                .zip(&other.params)
                .all(|(a, b)| same_ty(db, a, b))
    }

    /// 访问级别；接口的方法隐含 public。
    fn rank(&self) -> u8 {
        if self.owner_is_interface {
            3
        } else {
            visibility_rank(self.flags.visibility())
        }
    }
}

/// 经由原始类型继承来的父类型：某个父类型（或类自己）把它、或它的某个子类型写成了原始类型。
/// 原始类型的成员签名和它的父类型都要擦除（JLS §4.8），不能把类型参数换成 `Object` 了事：
/// `implements Foo` 时 `Supplier<Optional<T>> get()` 的签名是 `Supplier get()`。
fn raw_inherited_classes(db: &dyn Db, class: ClassId) -> rustc_hash::FxHashSet<ClassId> {
    let mut raw = rustc_hash::FxHashSet::default();
    for current in std::iter::once(class).chain(hir::all_supers(db, class).iter().copied()) {
        for sup in hir::class_supertypes(db, current).iter() {
            if let Ty::Class(id, _) = sup {
                if is_raw(db, sup) && raw.insert(*id) {
                    raw.extend(hir::all_supers(db, *id).iter().copied());
                }
            }
        }
    }
    raw
}

/// 类和它所有父类型（广度优先，自己在最前）里声明的方法（不含构造器）。父类型解析不全、
/// 用了 Lombok 时返回 `None`。
fn inherited_methods(db: &dyn Db, class: ClassId) -> Option<Vec<InheritedMethod>> {
    let mut res = Vec::new();
    let raw = raw_inherited_classes(db, class);
    for ty in all_super_tys(db, &hir::this_ty(db, class)) {
        let Ty::Class(owner, args) = &ty else {
            continue;
        };
        let owner = *owner;
        let erase = raw.contains(&owner);
        let owner_data = class_data(db, owner)?;
        if uses_lombok(db, owner) {
            return None;
        }
        let subst = Subst::for_class(db, owner, args);
        for (idx, method) in owner_data.methods.iter().enumerate() {
            if method.is_constructor {
                continue;
            }
            let id = MethodId {
                class: owner,
                idx: idx as u32,
            };
            let sig = method_sig(db, id);
            res.push(InheritedMethod {
                owner,
                owner_is_interface: owner_data.is_interface(),
                name: method.name.clone(),
                flags: method.flags,
                keys: erased_param_keys(db, id, &subst),
                params: sig
                    .params
                    .iter()
                    .map(|p| erase_if(db, p.subst(&subst), erase))
                    .collect(),
                ret: erase_if(db, sig.ret.subst(&subst), erase),
            });
        }
    }
    Some(res)
}

/// 方法在某个父类型里看到的形参类型（父类型的类型实参代换之后再擦除），用于判断覆写等价。
/// 说不准的形参是 `None`：类型里有未知部分，或者代换后还提到类的类型参数（外层类的类型参数
/// 等没法可靠代换的情形），这样的形参和任何类型都算匹配。
fn erased_param_keys(db: &dyn Db, method: MethodId, subst: &Subst) -> Vec<Option<String>> {
    method_sig(db, method)
        .params
        .iter()
        .map(|param| {
            let ty = param.subst(subst);
            let mentions_class_param =
                ty.mentions_params_where(&|p| matches!(p.owner, GenericOwner::Class(_)));
            let erased = ty.erasure(db);
            if mentions_class_param || ty.contains_unknown() || erased.contains_unknown() {
                return None;
            }
            Some(erased.display_qualified(db))
        })
        .collect()
}

fn erase_if(db: &dyn Db, ty: Ty, erase: bool) -> Ty {
    if erase {
        ty.erasure(db)
    } else {
        ty
    }
}

fn param_keys_match(a: &[Option<String>], b: &[Option<String>]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|(x, y)| match (x, y) {
            (Some(x), Some(y)) => x == y,
            _ => true,
        })
}

fn unimplemented_abstract_methods(
    db: &dyn Db,
    class: ClassId,
    methods: &[InheritedMethod],
) -> Vec<String> {
    // 直接父类不是抽象类时，父类那条继承链上的抽象方法由父类负责（javac 也只在父类上报）。
    // 枚举常量的类体例外：枚举可以把抽象方法留给每个常量的类体实现
    let mut settled_by_superclass: Vec<ClassId> = Vec::new();
    for sup in hir::direct_supers(db, class).iter().copied() {
        if class_header(db, sup).is_some_and(|d| {
            !d.is_interface() && !d.flags.is_abstract() && d.kind != ClassKind::Enum
        }) {
            settled_by_superclass.push(sup);
            settled_by_superclass.extend(hir::all_supers(db, sup).iter().copied());
        }
    }
    // 继承链上任何地方有非抽象的、同名且形参类型覆写等价、返回类型兼容的方法，就认为实现了。
    // 同名的静态方法是另一种错误（静态方法不能隐藏实例方法），这里按"有实现"处理
    let implements = |concrete: &InheritedMethod, abstract_method: &InheritedMethod| {
        concrete.name == abstract_method.name
            && param_keys_match(&concrete.keys, &abstract_method.keys)
            && (concrete.flags.is_static()
                || return_type_compatible(
                    db,
                    &concrete.ret,
                    &abstract_method.ret,
                    concrete.same_params(db, abstract_method),
                ))
    };
    let mut missing: Vec<String> = methods
        .iter()
        .filter(|m| m.is_abstract() && !settled_by_superclass.contains(&m.owner))
        .filter(|m| {
            !is_object_method(&m.name, m.keys.len())
                && is_accessible(db, m.flags, m.owner, Some(class))
                && !methods.iter().any(|c| !c.is_abstract() && implements(c, m))
        })
        .map(|m| m.name.to_string())
        .collect();
    missing.sort();
    missing.dedup();
    missing
}

/// 从父类继承来、实现某个抽象方法的方法不合格时的说明（javac 的 `checkImplementations`）。
/// 实现是沿父类链（自己、父类、父类的父类……）找到的第一个同签名方法；类自己声明的方法
/// 在方法上单独检查。只看形参类型都确定的抽象方法。
fn inherited_implementation_problem(
    db: &dyn Db,
    class: ClassId,
    methods: &[InheritedMethod],
) -> Option<String> {
    for abstract_method in methods.iter().filter(|m| m.is_abstract()) {
        if abstract_method.keys.iter().any(Option::is_none)
            || !is_accessible(
                db,
                abstract_method.flags,
                abstract_method.owner,
                Some(class),
            )
        {
            continue;
        }
        let Some(implementation) = methods.iter().find(|m| {
            !m.owner_is_interface
                && m.name == abstract_method.name
                && m.keys == abstract_method.keys
        }) else {
            continue;
        };
        if implementation.owner == class || implementation.is_abstract() {
            continue;
        }
        let owner_name =
            |id: ClassId| class_header(db, id).map_or_else(String::new, |d| d.name.to_string());
        let (implementer, implemented) = (
            owner_name(implementation.owner),
            owner_name(abstract_method.owner),
        );
        let method = &abstract_method.name;
        let reason = if implementation.flags.is_static() {
            base_db::tr!("它是静态方法", "it is static")
        } else if implementation.rank() < abstract_method.rank() {
            base_db::tr!("访问级别更窄", "it has weaker access")
        } else if !return_type_compatible(
            db,
            &implementation.ret,
            &abstract_method.ret,
            implementation.same_params(db, abstract_method),
        ) {
            base_db::tr!(
                "返回类型 `{}` 和 `{}` 不兼容",
                "return type `{}` is not compatible with `{}`",
                implementation.ret.display(db),
                abstract_method.ret.display(db)
            )
        } else {
            continue;
        };
        return Some(base_db::tr!(
            "`{implementer}.{method}` 不能实现 `{implemented}.{method}`：{reason}",
            "`{implementer}.{method}` cannot implement `{implemented}.{method}`: {reason}"
        ));
    }
    None
}

fn visibility_rank(visibility: Visibility) -> u8 {
    match visibility {
        Visibility::Private => 0,
        Visibility::Package => 1,
        Visibility::Protected => 2,
        Visibility::Public => 3,
    }
}

/// 类型里不含类型参数、通配符和未知部分，可以直接比较。
fn is_plain(db: &dyn Db, ty: &Ty) -> bool {
    match ty {
        Ty::Primitive(_) | Ty::Void => true,
        Ty::Class(class, args) => {
            args.is_empty() && class_header(db, *class).is_some_and(|d| d.type_params.is_empty())
        }
        Ty::Array(element) => is_plain(db, element),
        _ => false,
    }
}

/// 两个类型相同：结构相同，或者不含类型参数时全限定名相同（同名类的两份副本）。
/// 无界通配符 `?` 与 `? extends Object` 也等价。
fn same_ty(db: &dyn Db, a: &Ty, b: &Ty) -> bool {
    if a == b
        || (!a.mentions_params_where(&|_| true)
            && !b.mentions_params_where(&|_| true)
            && a.display_qualified(db) == b.display_qualified(db))
    {
        return true;
    }
    // 类型参数 T 代换成 Object 后，`? extends T` 与 `?` 等价。
    match (a, b) {
        (Ty::Wildcard(Wildcard::Unbounded), Ty::Wildcard(Wildcard::Extends(bound)))
        | (Ty::Wildcard(Wildcard::Extends(bound)), Ty::Wildcard(Wildcard::Unbounded)) => {
            same_ty(db, bound, &Ty::object(db))
        }
        (Ty::Class(ac, aa), Ty::Class(bc, ba)) => {
            ac.binary_name(db) == bc.binary_name(db)
                && aa.len() == ba.len()
                && aa.iter().zip(ba.iter()).all(|(a, b)| same_ty(db, a, b))
        }
        (Ty::Array(a), Ty::Array(b))
        | (Ty::Wildcard(Wildcard::Extends(a)), Ty::Wildcard(Wildcard::Extends(b)))
        | (Ty::Wildcard(Wildcard::Super(a)), Ty::Wildcard(Wildcard::Super(b))) => same_ty(db, a, b),
        _ => false,
    }
}

/// 类类型是原始类型（泛型类不带类型实参）。
fn is_raw(db: &dyn Db, ty: &Ty) -> bool {
    match ty {
        Ty::Class(class, args) => {
            args.is_empty() && class_header(db, *class).is_some_and(|d| !d.type_params.is_empty())
        }
        Ty::Array(element) => is_raw(db, element),
        _ => false,
    }
}

/// 覆写方法的返回类型和被覆写方法（代换之后）的返回类型是否兼容（JLS §8.4.8.3）。说不准时
/// 返回 `true`。`exact` 表示两个方法的签名相同（不是靠擦除才覆写等价的）。
fn return_type_compatible(db: &dyn Db, own: &Ty, sup: &Ty, exact: bool) -> bool {
    if own.contains_unknown() || sup.contains_unknown() {
        return true;
    }
    match (own, sup) {
        (Ty::Void, Ty::Void) => return true,
        (Ty::Void, _) | (_, Ty::Void) => return false,
        (Ty::Primitive(a), Ty::Primitive(b)) => return a == b,
        (Ty::Primitive(_), _) | (_, Ty::Primitive(_)) => return false,
        _ => {}
    }
    if is_subtype(db, own, sup) {
        return true;
    }
    let (own_erased, sup_erased) = (own.erasure(db), sup.erasure(db));
    if own_erased.contains_unknown() || sup_erased.contains_unknown() {
        return true;
    }
    if !is_subtype(db, &own_erased, &sup_erased) {
        return false;
    }
    // 擦除后兼容：原始类型经非受检转换、或靠擦除覆写时返回擦除后的类型都允许；只有签名相同、
    // 两边都是不含类型参数的参数化类型时，才按带类型实参的子类型关系判断
    if !exact || is_raw(db, own) {
        return true;
    }
    let plain =
        |ty: &Ty| !ty.mentions_params_where(&|_| true) && !matches!(ty, Ty::Intersection(_));
    !(plain(own) && plain(sup) && !own.type_args().is_empty() && !sup.type_args().is_empty())
}

fn override_checks(
    db: &dyn Db,
    method: MethodId,
    name_range: TextRange,
    override_range: Option<TextRange>,
    out: &mut Vec<Diagnostic>,
) {
    let Some(decl) = hir::method_data(db, method) else {
        return;
    };
    let Some(data) = class_header(db, method.class) else {
        return;
    };
    if decl.is_constructor || uses_lombok(db, method.class) {
        return;
    }
    let sig = method_sig(db, method);
    if sig.params.iter().any(Ty::contains_unknown) {
        return;
    }
    // 接口里的方法隐含 public
    let own_rank = if data.is_interface() {
        3
    } else {
        visibility_rank(decl.flags.visibility())
    };
    let own_generic = !decl.type_params.is_empty();
    let raw = raw_inherited_classes(db, method.class);
    let mut unmatched_annotation = override_range;

    for super_ty in all_super_tys(db, &hir::this_ty(db, method.class)) {
        let Ty::Class(owner, args) = &super_ty else {
            continue;
        };
        let owner = *owner;
        if owner == method.class {
            continue;
        }
        let erase = raw.contains(&owner);
        let Some(owner_data) = class_data(db, owner) else {
            unmatched_annotation = None;
            continue;
        };
        let class_subst = Subst::for_class(db, owner, args);
        for (idx, candidate) in owner_data.methods.iter().enumerate() {
            if candidate.is_constructor
                || candidate.name != decl.name
                || candidate.params.len() != decl.params.len()
            {
                continue;
            }
            // 泛型方法只和类型参数个数相同的泛型方法比较（类型参数按位置对应）；非泛型方法
            // 可以靠擦除覆写泛型方法
            if own_generic && candidate.type_params.len() != decl.type_params.len() {
                continue;
            }
            let super_rank = if owner_data.is_interface() {
                3
            } else {
                visibility_rank(candidate.flags.visibility())
            };
            // 接口的静态方法和私有方法不被继承
            if owner_data.is_interface()
                && (candidate.flags.is_static()
                    || candidate.flags.visibility() == Visibility::Private)
            {
                continue;
            }
            // 私有方法不被继承；包私有的只在同一个包里才被继承
            let same_package = {
                let package = |name: &str| name.rsplit_once('/').map(|(p, _)| p.to_owned());
                package(&owner_data.binary_name) == package(&data.binary_name)
            };
            if super_rank == 0 || (super_rank == 1 && !same_package) {
                continue;
            }
            let candidate_id = MethodId {
                class: owner,
                idx: idx as u32,
            };
            let mut subst = class_subst.clone();
            if own_generic {
                for i in 0..decl.type_params.len() as u32 {
                    subst.set(
                        hir::TypeParamId {
                            owner: GenericOwner::Method(candidate_id),
                            idx: i,
                        },
                        Ty::TypeParam(hir::TypeParamId {
                            owner: GenericOwner::Method(method),
                            idx: i,
                        }),
                    );
                }
            }
            let super_sig = method_sig(db, candidate_id);
            let super_params: Vec<Ty> = super_sig
                .params
                .iter()
                .map(|p| erase_if(db, p.subst(&subst), erase))
                .collect();
            if super_params.iter().any(Ty::contains_unknown) {
                unmatched_annotation = None;
                continue;
            }
            // 签名相同，或者（非泛型的）覆写方法的签名等于被覆写方法签名的擦除
            let exact = sig
                .params
                .iter()
                .zip(&super_params)
                .all(|(own, sup)| same_ty(db, own, sup));
            let by_erasure = !exact
                && !own_generic
                && sig.params.iter().zip(&super_params).all(|(own, sup)| {
                    let erased = sup.erasure(db);
                    !erased.contains_unknown() && same_ty(db, own, &erased)
                });
            if !exact && !by_erasure {
                // 菱形构造的匿名类在这里可能丢失推断出的父类型实参。
                // 尚未代换的类型参数也可能掩盖相同的签名。
                if unmatched_annotation.is_some()
                    && !candidate.flags.is_static()
                    && (sig
                        .params
                        .iter()
                        .chain(&super_params)
                        .any(|p| p.mentions_params_where(&|_| true))
                        || (data.flags.contains(Modifiers::ANONYMOUS)
                            && erase
                            && super_sig
                                .params
                                .iter()
                                .any(|p| p.mentions_params_where(&|_| true))))
                {
                    unmatched_annotation = None;
                }
                continue;
            }
            if !candidate.flags.is_static()
                && !decl.flags.is_static()
                && decl.flags.visibility() != Visibility::Private
                && (!data.is_interface()
                    || owner_data.binary_name != "java/lang/Object"
                    // 接口上标注 @Override 只能重声明 Object 的 public（级别 3）方法。
                    || super_rank == 3)
            {
                unmatched_annotation = None;
            }
            let owner_name = &owner_data.name;
            if candidate.flags.is_static() != decl.flags.is_static() {
                let message = if decl.flags.is_static() {
                    base_db::tr!(
                        "静态方法 `{}` 不能隐藏 `{owner_name}` 里的实例方法",
                        "Static method `{}` cannot hide the instance method in `{owner_name}`",
                        decl.name
                    )
                } else {
                    base_db::tr!(
                        "实例方法 `{}` 不能覆写 `{owner_name}` 里的静态方法",
                        "Instance method `{}` cannot override the static method in `{owner_name}`",
                        decl.name
                    )
                };
                out.push(error(name_range, DiagnosticCode::InvalidOverride, message));
                return;
            }
            if candidate.flags.contains(Modifiers::FINAL) {
                out.push(error(
                    name_range,
                    DiagnosticCode::InvalidOverride,
                    base_db::tr!(
                        "不能覆写 `{owner_name}` 里的 final 方法 `{}`",
                        "Cannot override final method `{}` in `{owner_name}`",
                        decl.name
                    ),
                ));
                return;
            }
            if own_rank < super_rank {
                out.push(error(
                    name_range,
                    DiagnosticCode::InvalidOverride,
                    base_db::tr!(
                        "覆写 `{owner_name}.{}` 时不能收窄访问级别",
                        "Cannot reduce the visibility when overriding `{owner_name}.{}`",
                        decl.name
                    ),
                ));
                return;
            }
            let super_ret = erase_if(db, super_sig.ret.subst(&subst), erase);
            if !return_type_compatible(db, &sig.ret, &super_ret, exact) {
                out.push(error(
                    name_range,
                    DiagnosticCode::InvalidOverride,
                    base_db::tr!(
                        "返回类型 `{}` 和被覆写的 `{owner_name}.{}` 的返回类型 `{}` 不兼容", "Return type `{}` is incompatible with overridden `{owner_name}.{}`, which returns `{}`",
                        sig.ret.display(db),
                        decl.name,
                        super_ret.display(db)
                    ),
                ));
                return;
            }
        }
    }
    if let Some(range) = unmatched_annotation.filter(|_| {
        hierarchy_is_resolved(db, method.class)
            && hir::lookup_class(db, "java/lang/Object").is_some()
            && !std::iter::once(method.class)
                .chain(hir::all_supers(db, method.class).iter().copied())
                .any(|class| lombok_involved(db, class))
            // JLS 9.6.4.4 也允许显式声明的记录组件访问器标注 @Override。
            && !(data.kind == ClassKind::Record
                && decl.params.is_empty()
                && !decl.flags.is_static()
                && class_data(db, method.class).is_some_and(|data| {
                    data.fields.iter().any(|field| !field.flags.is_static() && field.name == decl.name)
                }))
    }) {
        out.push(error(
            range,
            DiagnosticCode::InvalidOverride,
            base_db::tr!(
                "方法没有覆写或实现父类型中的方法",
                "Method does not override or implement a method from a supertype"
            ),
        ));
    }
}

/// 基本类型之间的转换是否无条件精确：恒等，或者不丢信息的拓宽（`int` → `long`、`int` → `double`，
/// 但 `int` → `float` 不算）。
fn exact_primitive(from: PrimitiveType, to: PrimitiveType) -> bool {
    use PrimitiveType::*;
    from == to
        || matches!(
            (from, to),
            (Byte, Short | Int | Long | Float | Double)
                | (Short | Char, Int | Long | Float | Double)
                | (Int, Long | Double)
                | (Float, Double)
        )
}

/// 类型为 `pattern` 的类型模式是否无条件匹配 `ty` 的所有（非 null）值。引用类型只比较擦除后的类，
/// 涉及类型变量等说不准的情形返回 `None`。
fn is_unconditional(db: &dyn Db, ty: &Ty, pattern: &Ty) -> Option<bool> {
    match (ty, pattern) {
        (Ty::Primitive(a), Ty::Primitive(b)) => Some(exact_primitive(*a, *b)),
        // 装箱之后再做引用类型的拓宽：`int` 对 `Integer` / `Number` / `Object`
        (Ty::Primitive(_), Ty::Class(..)) => Some(is_subtype(db, &ty.boxed(db), pattern)),
        // 拆箱之后再做精确的基本类型转换：`Integer` 对 `int` / `long`
        (Ty::Class(..), Ty::Primitive(b)) => {
            Some(ty.unboxed(db).is_some_and(|a| exact_primitive(a, *b)))
        }
        (Ty::Class(c, _), Ty::Class(p, _)) => Some(hir::is_subclass_of(db, *c, *p)),
        _ => None,
    }
}

/// 涉及基本类型时，类型为 `ty` 的值能否匹配类型为 `pattern` 的模式（`String` 永远匹配不了
/// `int`）。两边都是引用类型、或者说不准时返回 `None`。
fn primitive_pattern_applicable(db: &dyn Db, ty: &Ty, pattern: &Ty) -> Option<bool> {
    let is_boolean = |p: PrimitiveType| p == PrimitiveType::Boolean;
    match (ty, pattern) {
        (Ty::Primitive(a), Ty::Primitive(b)) => Some(is_boolean(*a) == is_boolean(*b)),
        (Ty::Primitive(_), Ty::Class(_, args)) if args.is_empty() => {
            Some(is_subtype(db, &ty.boxed(db), pattern))
        }
        (Ty::Class(_, args), Ty::Primitive(b)) if args.is_empty() => match ty.unboxed(db) {
            Some(a) => Some(is_boolean(a) == is_boolean(*b)),
            None => Some(is_subtype(db, &pattern.boxed(db), ty)),
        },
        _ => None,
    }
}

/// `ty` 的所有值是否都被 `patterns`（不带守卫的模式的类型）或 `constants`（枚举常量名）覆盖。
fn is_covered(
    db: &dyn Db,
    class: ClassId,
    patterns: &[Ty],
    constants: &[String],
    depth: u32,
) -> bool {
    let ty = Ty::class(class);
    if patterns.iter().any(|pattern| match pattern {
        Ty::Class(p, _) => hir::is_subclass_of(db, class, *p),
        _ => is_subtype(db, &ty, pattern),
    }) {
        return true;
    }
    let Some(data) = class_data(db, class) else {
        return false;
    };
    if data.kind == ClassKind::Enum {
        return data
            .fields
            .iter()
            .filter(|f| f.is_enum_constant())
            .all(|f| constants.iter().any(|c| c == f.name.as_str()));
    }
    // sealed 的抽象类 / 接口：每个允许的子类型都被覆盖
    if depth > 8 || !(data.is_interface() || data.flags.is_abstract()) {
        return false;
    }
    match hir::permitted_subclasses(db, class) {
        Some(subs) if !subs.is_empty() => subs
            .iter()
            .all(|sub| is_covered(db, *sub, patterns, constants, depth + 1)),
        _ => false,
    }
}

/// 记录模式是否无条件匹配它的类型：每个子模式都是 `var` / 不带类型限制的绑定，这里只认
/// "子模式的类型正好是组件的声明类型"这一种，其它情形按不确定处理。
fn record_pattern_is_total(
    sema: &Semantics<'_>,
    file: SourceFile,
    pattern: &ast::RecordPattern,
) -> Option<bool> {
    let ty = sema.resolve_type(file, &pattern.ty()?);
    let Ty::Class(class, _) = &ty else {
        return None;
    };
    let data = class_data(sema.db, *class)?;
    let components: Vec<_> = data
        .fields
        .iter()
        .filter(|f| !f.flags.is_static())
        .collect();
    let subs: Vec<ast::Pattern> = pattern.patterns().collect();
    if components.len() != subs.len() {
        return None;
    }
    for (idx, sub) in subs.iter().enumerate() {
        match sub {
            ast::Pattern::UnnamedPattern(_) => {}
            ast::Pattern::TypePattern(type_pattern) => {
                let written = type_pattern.ty()?;
                if written.syntax().text() == "var" {
                    continue;
                }
                let sub_ty = sema.resolve_type(file, &written);
                let component_ty = hir::field_ty(
                    sema.db,
                    hir::FieldId {
                        class: *class,
                        idx: data
                            .fields
                            .iter()
                            .position(|f| std::ptr::eq(f, components[idx]))?
                            as u32,
                    },
                );
                if sub_ty.contains_unknown() || component_ty.contains_unknown() {
                    return None;
                }
                // 基本类型的组件：子模式的类型只要是精确转换的目标就无条件匹配（`double x` 对 `int x`）
                if matches!(sub_ty, Ty::Primitive(_)) || matches!(component_ty, Ty::Primitive(_)) {
                    match is_unconditional(sema.db, &component_ty, &sub_ty) {
                        Some(true) => continue,
                        other => return other,
                    }
                }
                // 子模式的类型不比组件类型宽时可能匹配不上；涉及泛型时不下结论
                if sub_ty != component_ty && !is_subtype(sema.db, &component_ty, &sub_ty) {
                    return if is_plain(sema.db, &sub_ty) && is_plain(sema.db, &component_ty) {
                        Some(false)
                    } else {
                        None
                    };
                }
            }
            ast::Pattern::RecordPattern(_) => return None,
        }
    }
    Some(true)
}

/// switch 表达式（以及带模式的 switch 语句）没有 `default` 时必须穷尽。
fn switch_exhaustiveness(
    db: &dyn Db,
    sema: &Semantics<'_>,
    file: SourceFile,
    node: &SyntaxNode,
    result: &InferenceResult,
    out: &mut Vec<Diagnostic>,
) {
    for switch in node.descendants() {
        let is_expr = switch.kind() == SyntaxKind::SWITCH_EXPR;
        if !is_expr && switch.kind() != SyntaxKind::SWITCH_STMT {
            continue;
        }
        let Some(scrutinee) = switch.children().find_map(ast::Expr::cast) else {
            continue;
        };
        let Some(block) = switch.children().find_map(ast::SwitchBlock::cast) else {
            continue;
        };
        let Some(scrutinee_ty) = result.type_of(scrutinee.syntax().text_range()) else {
            continue;
        };
        if scrutinee_ty.contains_unknown() {
            continue;
        }

        let mut constants: Vec<String> = Vec::new();
        let mut patterns: Vec<Ty> = Vec::new();
        let mut has_pattern = false;
        let mut certain = true;
        let mut has_default = false;
        for case in block.cases() {
            let Some(label) = case.label() else {
                certain = false;
                continue;
            };
            // `default` 和 `case null, default` 两种写法
            if label
                .syntax()
                .children_with_tokens()
                .any(|e| e.kind() == SyntaxKind::DEFAULT_KW)
            {
                has_default = true;
            }
            let guarded = label.guard().is_some();
            for pattern in label.patterns() {
                has_pattern = true;
                if guarded {
                    continue;
                }
                match &pattern {
                    ast::Pattern::TypePattern(type_pattern) => match type_pattern.ty() {
                        Some(ty) => patterns.push(sema.resolve_type(file, &ty)),
                        None => certain = false,
                    },
                    ast::Pattern::RecordPattern(record) => {
                        match (record_pattern_is_total(sema, file, record), record.ty()) {
                            (Some(true), Some(ty)) => patterns.push(sema.resolve_type(file, &ty)),
                            (Some(false), _) => {}
                            _ => certain = false,
                        }
                    }
                    ast::Pattern::UnnamedPattern(_) => certain = false,
                }
            }
            for expr in label.exprs() {
                if let Some((name, _)) = referenced_name(expr.syntax()) {
                    constants.push(name.text().to_string());
                } else if let ast::Expr::Literal(literal) = &expr {
                    let text = literal.syntax().text().to_string();
                    if text == "true" || text == "false" {
                        constants.push(text);
                    }
                }
            }
        }
        // 普通的 switch 语句不要求穷尽
        if has_default || !certain || (!is_expr && !has_pattern) {
            continue;
        }
        if patterns.iter().any(Ty::contains_unknown) {
            continue;
        }

        let exhaustive = match scrutinee_ty {
            Ty::Class(class, _) => {
                let boxed_or_string = scrutinee_ty.unboxed(db).is_some()
                    || class_header(db, *class)
                        .is_some_and(|d| d.binary_name == "java/lang/String");
                if boxed_or_string && !has_pattern {
                    false
                } else {
                    // 包装类也可以被基本类型的模式覆盖：`Integer` 对 `case int i`
                    patterns.iter().any(|p| {
                        matches!(p, Ty::Primitive(_))
                            && is_unconditional(db, scrutinee_ty, p) == Some(true)
                    }) || is_covered(db, *class, &patterns, &constants, 0)
                }
            }
            // 基本类型：无条件的模式（精确转换或装箱），或者 boolean 的 `true` 和 `false` 都有
            Ty::Primitive(p) => {
                patterns
                    .iter()
                    .any(|pattern| is_unconditional(db, scrutinee_ty, pattern) == Some(true))
                    || (*p == PrimitiveType::Boolean
                        && ["true", "false"]
                            .iter()
                            .all(|b| constants.iter().any(|c| c == b)))
            }
            _ => continue,
        };
        if exhaustive {
            continue;
        }
        let range = switch
            .first_token()
            .map_or_else(|| switch.text_range(), |t| t.text_range());
        let what = if is_expr {
            base_db::trs!("switch 表达式", "switch expression")
        } else {
            base_db::trs!("switch 语句", "switch statement")
        };
        out.push(error(
            range,
            DiagnosticCode::NonExhaustiveSwitch,
            base_db::tr!(
                "{what}没有覆盖所有可能的输入值",
                "The {what} does not cover all possible input values"
            ),
        ));
    }
}

/// switch 标签的支配关系：前面不带守卫的类型模式能匹配的值，后面的标签就永远轮不到；
/// 无条件的模式和 `default` 不能同时出现。
fn switch_dominance(
    db: &dyn Db,
    sema: &Semantics<'_>,
    file: SourceFile,
    node: &SyntaxNode,
    result: &InferenceResult,
    out: &mut Vec<Diagnostic>,
) {
    let dominated = |range: TextRange| {
        error(
            range,
            DiagnosticCode::DominatedCase,
            base_db::trs!(
                "这个 case 标签被前面的 case 标签支配，永远不会匹配到",
                "This case label is dominated by a preceding case label"
            )
            .to_string(),
        )
    };
    for switch in node.descendants() {
        if !matches!(
            switch.kind(),
            SyntaxKind::SWITCH_EXPR | SyntaxKind::SWITCH_STMT
        ) {
            continue;
        }
        let Some(scrutinee) = switch.children().find_map(ast::Expr::cast) else {
            continue;
        };
        let Some(block) = switch.children().find_map(ast::SwitchBlock::cast) else {
            continue;
        };
        let Some(scrutinee_ty) = result.type_of(scrutinee.syntax().text_range()) else {
            continue;
        };
        if scrutinee_ty.contains_unknown() {
            continue;
        }
        // 前面不带守卫的类型模式的类型
        let mut dominators: Vec<Ty> = Vec::new();
        let mut default_label: Option<TextRange> = None;
        let mut unconditional: Option<TextRange> = None;
        for case in block.cases() {
            let Some(label) = case.label() else {
                break;
            };
            let guarded = label.guard().is_some();
            if label
                .syntax()
                .children_with_tokens()
                .any(|e| e.kind() == SyntaxKind::DEFAULT_KW)
            {
                let range = label.syntax().text_range();
                if unconditional.is_some() {
                    out.push(error(
                        range,
                        DiagnosticCode::DominatedCase,
                        base_db::trs!(
                            "switch 里同时有无条件的模式和 `default` 标签",
                            "The switch has both an unconditional pattern and a `default` label"
                        )
                        .to_string(),
                    ));
                }
                default_label.get_or_insert(range);
            }
            for pattern in label.patterns() {
                let (ty, type_pattern) = match &pattern {
                    ast::Pattern::TypePattern(it) => match it.ty() {
                        Some(t) if t.syntax().text() != "var" => {
                            (sema.resolve_type(file, &t), true)
                        }
                        _ => continue,
                    },
                    ast::Pattern::RecordPattern(it) => match it.ty() {
                        Some(t) => (sema.resolve_type(file, &t), false),
                        None => continue,
                    },
                    ast::Pattern::UnnamedPattern(_) => continue,
                };
                if ty.contains_unknown() {
                    continue;
                }
                let range = pattern.syntax().text_range();
                if dominators
                    .iter()
                    .any(|d| is_unconditional(db, &ty, d) == Some(true))
                {
                    out.push(dominated(range));
                    continue;
                }
                if type_pattern && !guarded {
                    if is_unconditional(db, scrutinee_ty, &ty) == Some(true) {
                        if default_label.is_some() || unconditional.is_some() {
                            out.push(error(
                                range,
                                DiagnosticCode::DominatedCase,
                                base_db::trs!(
                                    "switch 里同时有无条件的模式和 `default` 标签",
                                    "The switch has both an unconditional pattern and a `default` label"
                                )
                                .to_string(),
                            ));
                        }
                        unconditional.get_or_insert(range);
                    }
                    dominators.push(ty);
                }
            }
            for expr in label.exprs() {
                if expr.syntax().text() == "null" {
                    continue;
                }
                // 枚举常量的简单名不一定有类型记录，它的类型就是选择器的类型
                let ty = match result.type_of(expr.syntax().text_range()) {
                    Some(ty) => ty.clone(),
                    None if expr.syntax().kind() == SyntaxKind::NAME_EXPR => scrutinee_ty.clone(),
                    None => continue,
                };
                if ty.contains_unknown() {
                    continue;
                }
                if dominators
                    .iter()
                    .any(|d| is_unconditional(db, &ty, d) == Some(true))
                {
                    out.push(dominated(expr.syntax().text_range()));
                }
            }
        }
    }
}

/// 涉及基本类型的模式（`instanceof` 和 switch 的标签）：值的类型和模式的类型必须可以互相转换。
fn primitive_pattern_applicability(
    db: &dyn Db,
    sema: &Semantics<'_>,
    file: SourceFile,
    node: &SyntaxNode,
    result: &InferenceResult,
    out: &mut Vec<Diagnostic>,
) {
    let mut check = |operand: &Ty, written: &ast::Type, range: TextRange| {
        if written.syntax().text() == "var" || operand.contains_unknown() {
            return;
        }
        let ty = sema.resolve_type(file, written);
        if ty.contains_unknown() {
            return;
        }
        if primitive_pattern_applicable(db, operand, &ty) == Some(false) {
            out.push(error(
                range,
                DiagnosticCode::TypeMismatch,
                base_db::tr!(
                    "`{}` 类型的值不可能匹配 `{}`",
                    "A value of type `{}` can never match `{}`",
                    operand.display(db),
                    ty.display(db)
                ),
            ));
        }
    };
    for n in node.descendants() {
        match n.kind() {
            SyntaxKind::INSTANCEOF_EXPR => {
                let Some(operand) = n
                    .children()
                    .find_map(ast::Expr::cast)
                    .and_then(|e| result.type_of(e.syntax().text_range()))
                else {
                    continue;
                };
                for child in n.children() {
                    if let Some(written) = ast::Type::cast(child.clone()) {
                        check(operand, &written, child.text_range());
                    } else if let Some(ast::Pattern::TypePattern(p)) = ast::Pattern::cast(child) {
                        if let Some(written) = p.ty() {
                            check(operand, &written, p.syntax().text_range());
                        }
                    }
                }
            }
            SyntaxKind::SWITCH_EXPR | SyntaxKind::SWITCH_STMT => {
                let Some(operand) = n
                    .children()
                    .find_map(ast::Expr::cast)
                    .and_then(|e| result.type_of(e.syntax().text_range()))
                else {
                    continue;
                };
                let Some(block) = n.children().find_map(ast::SwitchBlock::cast) else {
                    continue;
                };
                for label in block.cases().filter_map(|c| c.label()) {
                    for pattern in label.patterns() {
                        if let ast::Pattern::TypePattern(p) = pattern {
                            if let Some(written) = p.ty() {
                                check(operand, &written, p.syntax().text_range());
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// `sub`（`None` 表示匿名类或局部类）直接继承 `sup` 时，如果 `sup` 是 sealed 的而 `sub`
/// 不在它允许的子类型里，返回诊断文本。允许的子类型解析不全时不下结论。
fn sealed_violation(db: &dyn Db, sup: ClassId, sub: Option<ClassId>) -> Option<String> {
    let data = class_header(db, sup)?;
    if !data.flags.contains(Modifiers::SEALED) {
        return None;
    }
    let permitted = hir::permitted_subclasses(db, sup)?;
    if sub.is_some_and(|sub| permitted.contains(&sub)) {
        return None;
    }
    let what = if data.is_interface() {
        base_db::trs!("接口", "interface")
    } else {
        base_db::trs!("类", "class")
    };
    Some(match sub.and_then(|sub| class_header(db, sub)) {
        Some(sub) => base_db::tr!(
            "`{}` 不在 sealed {what} `{}` 允许的子类型里",
            "`{}` is not allowed to extend the sealed {what} `{}`",
            sub.name,
            data.name
        ),
        None => base_db::tr!(
            "匿名类和局部类不能继承 sealed {what} `{}`",
            "Anonymous and local classes cannot extend the sealed {what} `{}`",
            data.name
        ),
    })
}

fn mentions_type_param(ty: &Ty) -> bool {
    match ty {
        Ty::TypeParam(_) => true,
        Ty::Class(_, args) | Ty::Intersection(args) => args.iter().any(mentions_type_param),
        Ty::Array(element) => mentions_type_param(element),
        Ty::Wildcard(_) => true,
        _ => false,
    }
}

/// `Box<String>`：写明的类型实参是否在类型参数的上界之内。
///
/// 只看实参和（代换后的）上界都是已知的具体类型的情形；通配符、类型变量、继承链解析不全的跳过。
/// 类型引用上的检查。三项检查共用一次类型解析；明显用不到解析结果的跳过解析。
fn class_type_checks(
    db: &dyn Db,
    sema: &Semantics<'_>,
    file: SourceFile,
    class_ty: &ast::ClassType,
    out: &mut Vec<Diagnostic>,
) {
    let has_args = class_ty
        .type_arg_list()
        .is_some_and(|list| list.args().next().is_some());
    // 只有外层的类型声明了同名的类型参数时，简单名才可能是类的类型参数
    let may_be_class_type_param =
        class_ty.qualifier().is_none() && class_ty.type_arg_list().is_none() && {
            let name = class_ty.syntax().text().to_string();
            class_ty
                .syntax()
                .ancestors()
                .filter_map(ast::TypeDecl::cast)
                .filter_map(|decl| decl.type_param_list())
                .any(|list| {
                    list.type_params()
                        .any(|p| p.name().is_some_and(|n| n.text() == name.as_str()))
                })
        };
    if !has_args && !may_be_class_type_param {
        return;
    }
    let ty = sema.resolve_type(file, &ast::Type::ClassType(class_ty.clone()));
    if has_args {
        type_arg_shape(db, &ty, class_ty, out);
        type_arg_bounds(db, &ty, class_ty, out);
    } else {
        static_type_param(sema, file, &ty, class_ty, out);
    }
}

fn type_arg_bounds(db: &dyn Db, ty: &Ty, class_ty: &ast::ClassType, out: &mut Vec<Diagnostic>) {
    let Some(arg_nodes) = class_ty
        .type_arg_list()
        .map(|l| l.args().collect::<Vec<_>>())
    else {
        return;
    };
    if arg_nodes.is_empty() {
        return;
    }
    let Ty::Class(class, args) = ty else {
        return;
    };
    let class = *class;
    if args.len() != arg_nodes.len() {
        return;
    }
    let subst = hir::Subst::for_class(db, class, args);
    for (idx, (arg, node)) in args.iter().zip(&arg_nodes).enumerate() {
        let clear = matches!(arg, Ty::Class(..) | Ty::Array(_))
            && !arg.contains_unknown()
            && !mentions_type_param(arg);
        if !clear {
            continue;
        }
        if let Ty::Class(arg_class, _) = arg {
            if !hierarchy_is_resolved(db, *arg_class) {
                continue;
            }
        }
        let param = hir::TypeParamId {
            owner: hir::GenericOwner::Class(class),
            idx: idx as u32,
        };
        for bound in hir::type_param_bounds(db, param).iter() {
            let bound = bound.subst(&subst);
            if bound.contains_unknown() || mentions_type_param(&bound) {
                continue;
            }
            if !is_subtype(db, arg, &bound) {
                out.push(error(
                    node.syntax().text_range(),
                    DiagnosticCode::TypeArgOutOfBounds,
                    base_db::tr!(
                        "类型实参 `{}` 不在类型变量 `{}` 的上界 `{}` 之内",
                        "Type argument `{}` is not within the bounds of type variable `{}` (`{}`)",
                        arg.display(db),
                        hir::type_param_name(db, param),
                        bound.display(db)
                    ),
                ));
                break;
            }
        }
    }
}

/// 类型实参的写法本身就不对：基本类型（`List<int>`），或者个数和类型参数对不上（`Map<String>`）。
fn type_arg_shape(db: &dyn Db, ty: &Ty, class_ty: &ast::ClassType, out: &mut Vec<Diagnostic>) {
    let Some(list) = class_ty.type_arg_list() else {
        return;
    };
    let arg_nodes: Vec<ast::Type> = list.args().collect();
    if arg_nodes.is_empty() {
        return;
    }
    for node in &arg_nodes {
        if let ast::Type::PrimitiveType(prim) = node {
            out.push(error(
                prim.syntax().text_range(),
                DiagnosticCode::TypeMismatch,
                base_db::tr!(
                    "类型实参不能是基本类型 `{}`，应当用它的包装类",
                    "Type argument cannot be the primitive type `{}`; use its wrapper class",
                    prim.syntax().text()
                ),
            ));
        }
    }
    // 带限定符的类型（`Outer<A>.Inner<B>`）各段的类型实参分属不同的类，这里只看单段的
    if class_ty.qualifier().is_some()
        || class_ty
            .syntax()
            .parent()
            .is_some_and(|p| p.kind() == SyntaxKind::CLASS_TYPE)
    {
        return;
    }
    let Ty::Class(class, _) = ty else {
        return;
    };
    let Some(data) = class_header(db, *class) else {
        return;
    };
    let expected = data.type_params.len();
    if expected != arg_nodes.len() {
        let message = if expected == 0 {
            base_db::tr!(
                "类型 `{}` 不是泛型，不能带类型实参",
                "Type `{}` does not take type arguments",
                data.name
            )
        } else {
            base_db::tr!(
                "类型 `{}` 需要 {} 个类型实参，这里给了 {} 个",
                "Type `{}` takes {} type argument(s), but {} were given",
                data.name,
                expected,
                arg_nodes.len()
            )
        };
        out.push(error(
            list.syntax().text_range(),
            DiagnosticCode::TypeMismatch,
            message,
        ));
    }
}

/// 在静态上下文里用到了外层类的类型参数（`static T value;`、`static List<T> of()`）。
fn static_type_param(
    sema: &Semantics<'_>,
    file: SourceFile,
    ty: &Ty,
    class_ty: &ast::ClassType,
    out: &mut Vec<Diagnostic>,
) {
    if class_ty.qualifier().is_some() || class_ty.type_arg_list().is_some() {
        return;
    }
    let Ty::TypeParam(param) = ty else {
        return;
    };
    let hir::GenericOwner::Class(owner) = param.owner else {
        return;
    };
    let has_static = |node: &SyntaxNode| {
        node.children()
            .find_map(ast::ModifierList::cast)
            .is_some_and(|list| list.has(SyntaxKind::STATIC_KW))
    };
    // 方法 / 构造器 / 内层类自己声明了同名的类型参数时，引用的是它（遮蔽了外层类的）
    let name = class_ty.syntax().text().to_string();
    let declares_same = |node: &SyntaxNode| {
        node.children()
            .find_map(ast::TypeParamList::cast)
            .is_some_and(|list| {
                list.type_params()
                    .any(|p| p.name().is_some_and(|n| n.text() == name.as_str()))
            })
    };
    let mut static_seen = false;
    for ancestor in class_ty.syntax().ancestors().skip(1) {
        if matches!(
            ancestor.kind(),
            SyntaxKind::METHOD_DECL | SyntaxKind::CONSTRUCTOR_DECL
        ) && declares_same(&ancestor)
        {
            return;
        }
        match ancestor.kind() {
            SyntaxKind::METHOD_DECL | SyntaxKind::FIELD_DECL => {
                static_seen |= has_static(&ancestor);
            }
            SyntaxKind::INITIALIZER_BLOCK => {
                static_seen |= has_static(&ancestor)
                    || ancestor
                        .children_with_tokens()
                        .any(|e| e.kind() == SyntaxKind::STATIC_KW);
            }
            // 局部类、匿名类：外层类的判断交给更外层
            SyntaxKind::BLOCK | SyntaxKind::NEW_EXPR => {}
            _ => {
                let Some(decl) = ast::TypeDecl::cast(ancestor.clone()) else {
                    continue;
                };
                // 局部类不在全局索引里，拿不到它的类，没法判断类型参数是不是它的
                let Some(class) = sema.class_of_decl(file, &decl) else {
                    return;
                };
                if class != owner && declares_same(&ancestor) {
                    return;
                }
                if class == owner {
                    if static_seen {
                        out.push(error(
                            class_ty.syntax().text_range(),
                            DiagnosticCode::StaticContext,
                            base_db::tr!(
                                "不能在静态上下文里引用类型参数 `{}`",
                                "Non-static type variable `{}` cannot be referenced from a static context",
                                class_ty.syntax().text()
                            ),
                        ));
                    }
                    return;
                }
                // 静态成员类，以及隐含静态的成员接口 / 枚举 / 记录
                static_seen |=
                    has_static(&ancestor) || !matches!(ancestor.kind(), SyntaxKind::CLASS_DECL);
            }
        }
    }
}

/// 类或它所在的文件用了 Lombok（可能生成构造器）。
pub(crate) fn lombok_involved(db: &dyn Db, class: ClassId) -> bool {
    uses_lombok(db, class)
        || hir::class_source_file(db, class)
            .is_some_and(|file| hir::file_scope(db, file).imports_lombok())
}

/// 父类没有无参构造器时，子类的构造器必须显式调用 `super(...)`：没有声明构造器（默认构造器），
/// 或者构造器体不以 `this(...)` / `super(...)` 开头，都会隐式调用 `super()`。
fn implicit_super_calls(
    db: &dyn Db,
    class: ClassId,
    decl: &ast::TypeDecl,
    out: &mut Vec<Diagnostic>,
) {
    let Some(data) = class_data(db, class) else {
        return;
    };
    if data.kind != ClassKind::Class
        || data.superclass.is_none()
        || lombok_involved(db, class)
        || !hierarchy_is_resolved(db, class)
    {
        return;
    }
    let Some(Ty::Class(sup, _)) = hir::class_supertypes(db, class).first().cloned() else {
        return;
    };
    // 只看源码里的父类：class 文件里内部类的构造器带着合成的外层实例形参
    if hir::class_source_file(db, sup).is_none() || lombok_involved(db, sup) {
        return;
    }
    let Some(sup_data) = class_data(db, sup) else {
        return;
    };
    if sup_data.kind != ClassKind::Class || sup_data.constructors().next().is_none() {
        return;
    }
    let has_no_arg = sup_data
        .constructors()
        .any(|(_, ctor)| ctor.params.is_empty() || (ctor.is_varargs() && ctor.params.len() == 1));
    if has_no_arg {
        return;
    }
    let message = base_db::tr!(
        "`{}` 没有无参构造器，这里会隐式调用 `super()`，需要显式调用 `super(...)`",
        "`{}` has no no-arg constructor; the implicit `super()` call here does not compile",
        sup_data.name
    );
    let Some(body) = decl.body() else {
        return;
    };
    let ctors: Vec<ast::ConstructorDecl> = body
        .members()
        .filter_map(|member| match member {
            ast::Member::ConstructorDecl(ctor) => Some(ctor),
            _ => None,
        })
        .collect();
    if ctors.is_empty() {
        if let Some(name) = decl.name() {
            out.push(error(
                name.syntax().text_range(),
                DiagnosticCode::ArgumentMismatch,
                message,
            ));
        }
        return;
    }
    for ctor in ctors {
        let Some(block) = ctor.body() else {
            continue;
        };
        // 灵活构造器体里 `super(...)` 前面可以有别的语句，所以看所有顶层语句
        let explicit = block.statements().any(|stmt| {
            matches!(&stmt, ast::Stmt::ExprStmt(it)
                if matches!(it.expr(), Some(ast::Expr::ExplicitConstructorCall(_))))
        });
        if !explicit {
            if let Some(name) = ctor.name() {
                out.push(error(
                    name.syntax().text_range(),
                    DiagnosticCode::ArgumentMismatch,
                    message.clone(),
                ));
            }
        }
    }
}

pub(crate) fn typeck_diagnostics(view: &View<'_>, out: &mut Vec<Diagnostic>) {
    crate::timing::timed("typeck::return_values", || return_values(view, out));
    crate::timing::timed("typeck::declarations", || declaration_checks(view, out));
    crate::timing::timed("typeck::bodies", || body_checks(view, out));
}

/// 类型声明、方法声明、类型引用上的检查。
fn declaration_checks(view: &View<'_>, out: &mut Vec<Diagnostic>) {
    let (db, sema, file) = (view.db, &view.sema, view.file);
    for node in view.nodes() {
        if let Some(class_ty) = ast::ClassType::cast(node.clone()) {
            class_type_checks(db, sema, file, &class_ty, out);
            continue;
        }
        if let Some(new_expr) = ast::NewExpr::cast(node.clone()) {
            // 匿名类不能继承 sealed 类型
            if new_expr.body().is_some() {
                if let Some(ty) = new_expr.ty() {
                    if let Ty::Class(sup, _) = sema.resolve_type(file, &ty) {
                        if let Some(message) = sealed_violation(db, sup, None) {
                            out.push(error(
                                ty.syntax().text_range(),
                                DiagnosticCode::SealedSubtype,
                                message,
                            ));
                        }
                    }
                    let anonymous = new_expr
                        .body()
                        .and_then(|body| sema.anonymous_class_of_body(file, body.syntax()));
                    if let Some(class) = anonymous {
                        let name = Ty::class(class).display(db);
                        missing_implementation(db, class, &name, ty.syntax().text_range(), out);
                    }
                }
            }
            continue;
        }
        if let Some(decl) = ast::TypeDecl::cast(node.clone()) {
            // 局部类（及其成员类）：class_of_decl 拿不到，按声明节点找
            let is_local = node
                .ancestors()
                .skip(1)
                .any(|a| a.kind() == SyntaxKind::BLOCK);
            if is_local {
                // 局部类不可能是 sealed 类型允许的子类型
                let supertypes = node
                    .children()
                    .filter(|n| {
                        matches!(
                            n.kind(),
                            SyntaxKind::EXTENDS_CLAUSE | SyntaxKind::IMPLEMENTS_CLAUSE
                        )
                    })
                    .flat_map(|clause| clause.children().filter_map(ast::Type::cast));
                for ty in supertypes {
                    if let Ty::Class(sup, _) = sema.resolve_type(file, &ty) {
                        if let Some(message) = sealed_violation(db, sup, None) {
                            out.push(error(
                                ty.syntax().text_range(),
                                DiagnosticCode::SealedSubtype,
                                message,
                            ));
                        }
                    }
                }
                let local = sema.local_class_of_decl(file, &decl);
                if let (Some(class), Some(name)) = (local, decl.name()) {
                    let range = name.syntax().text_range();
                    missing_implementation(db, class, &name.text(), range, out);
                }
                continue;
            }
            let Some(class) = sema.class_of_decl(file, &decl) else {
                continue;
            };
            if let Some(name) = node.children().find_map(ast::Name::cast) {
                for sup in hir::direct_supers(db, class).iter() {
                    if let Some(message) = sealed_violation(db, *sup, Some(class)) {
                        out.push(error(
                            name.syntax().text_range(),
                            DiagnosticCode::SealedSubtype,
                            message,
                        ));
                    }
                }
            }
            implicit_super_calls(db, class, &decl, out);
            // 有常量带类体的枚举：抽象方法可以由常量的类体实现，在常量上检查
            if let Some(name) = node.children().find_map(ast::Name::cast) {
                if !enum_has_constant_bodies(&node) {
                    let range = name.syntax().text_range();
                    missing_implementation(db, class, &name.text(), range, out);
                }
            }
        } else if let Some(constant) = ast::EnumConstant::cast(node.clone()) {
            let body = node.children().find(|n| n.kind() == SyntaxKind::CLASS_BODY);
            let class = body.and_then(|body| sema.anonymous_class_of_body(file, &body));
            if let (Some(class), Some(name)) = (class, constant.name()) {
                let range = name.syntax().text_range();
                missing_implementation(db, class, &name.text(), range, out);
            }
        } else if let Some(method) = ast::MethodDecl::cast(node.clone()) {
            let in_local_class = node.ancestors().skip(1).any(|a| {
                matches!(
                    a.kind(),
                    SyntaxKind::BLOCK | SyntaxKind::NEW_EXPR | SyntaxKind::ENUM_CONSTANT
                )
            });
            let id = if in_local_class {
                sema.local_class_method(file, &node)
            } else {
                sema.method_of_decl(file, &node)
            };
            if let (Some(id), Some(name)) = (id, method.name()) {
                let override_range = method
                    .modifier_list()
                    .into_iter()
                    .flat_map(|mods| mods.annotations())
                    .chain(
                        method
                            .type_param_list()
                            .and_then(|_| method.return_type())
                            .into_iter()
                            .flat_map(|ty| ty.syntax().descendants().filter_map(ast::Annotation::cast)),
                    )
                    .filter_map(|a| a.name())
                    .find(|ann| {
                        ann.name_ref().is_some_and(|n| n.text() == "Override")
                            && matches!(
                                hir::resolve_type_path(db, &sema.type_scope(file, ann.syntax()), &ann.segments()),
                                Some(hir::TypeNs::Class(class)) if class.binary_name(db) == "java/lang/Override"
                            )
                    })
                    .map(|ann| ann.syntax().text_range());
                override_checks(db, id, name.syntax().text_range(), override_range, out);
            }
        }
    }
}

/// 逐个体的检查。
fn body_checks(view: &View<'_>, out: &mut Vec<Diagnostic>) {
    let (db, sema, file) = (view.db, &view.sema, view.file);
    for file_body in &view.bodies {
        db.unwind_if_revision_cancelled();
        let body = file_body.id;
        let node = file_body.node.clone();
        let result = file_body.result(view);
        final_assignments(db, sema, file, &node, &result, out);
        private_access(db, body, &node, &result, out);
        static_context(db, body, &node, &result, out);
        type_qualified_instance_members(db, &node, &result, out);
        abstract_instantiations(db, &node, &result, out);
        misplaced_jumps(&node, out);
        duplicate_case_labels(&node, out);
        switch_exhaustiveness(db, sema, file, &node, &result, out);
        switch_dominance(db, sema, file, &node, &result, out);
        primitive_pattern_applicability(db, sema, file, &node, &result, out);
    }
}
