//! 跳转：定义、声明、类型定义、实现，以及工作区符号搜索。

use base_db::{workspace, Db, SourceFile};
use hir::{
    all_supers, class_data, field_ty, method_sig, ClassId, Definition, MethodId, Semantics, Ty,
};
use ide_db::{search::refers_to, symbol_index::search_symbols, SymbolKind};
use rustc_hash::FxHashSet;
use smol_str::SmolStr;
use syntax::{
    algo::pick_ident_token,
    ast::{self, AstNode},
    SyntaxKind, TextRange, TextSize,
};

use crate::{
    library::{erased_type_key, LibraryMember, LibraryMemberKind},
    DefKey, FileId, FilePosition, RangeInfo,
};

/// 目标所在的文件。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NavFile {
    /// 已在数据库里的源码文件
    Source(FileId),
    /// 依赖库 / JDK 里的类：宿主负责找到源码或生成桩代码，再用
    /// [`crate::locate_in_library_source`] 定位
    Library {
        class: SmolStr,
        member: Option<LibraryMember>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NavigationTarget {
    pub file: NavFile,
    /// 整个声明（`NavFile::Library` 时为空范围）
    pub full_range: TextRange,
    /// 名字
    pub focus_range: TextRange,
    pub name: SmolStr,
    pub kind: SymbolKind,
    /// 所在的类或包（点分）
    pub container: Option<String>,
    /// 一行签名
    pub detail: Option<String>,
    pub deprecated: bool,
    /// 之后再找回这个定义用的稳定标识（层级视图的往返）
    pub key: Option<DefKey>,
}

pub(crate) fn def_key(db: &dyn Db, def: &Definition) -> Option<DefKey> {
    match def {
        Definition::Class(class) => Some(DefKey::Class {
            binary_name: class.key(db),
        }),
        Definition::Method(method) => Some(DefKey::Method {
            class: method.class.key(db),
            idx: method.idx,
        }),
        Definition::Field(field) => Some(DefKey::Field {
            class: field.class.key(db),
            idx: field.idx,
        }),
        _ => None,
    }
}

fn container_name(db: &dyn Db, def: &Definition) -> Option<String> {
    match def {
        Definition::Class(class) => {
            let name = class.binary_name(db);
            let idx = name.rfind(['/', '$'])?;
            Some(name[..idx].replace(['/', '$'], "."))
        }
        _ => def.container_class().map(|class| class.qualified_name(db)),
    }
}

/// 匿名类没有名字：用创建它的表达式（`new Runnable() {…}`）或枚举常量（`RED {…}`）
/// 当作名字，焦点放在类型名 / 常量名上。
fn anonymous_class_label(
    db: &dyn Db,
    def: &Definition,
    source: &hir::DeclSource,
) -> Option<(SmolStr, TextRange)> {
    let Definition::Class(class) = def else {
        return None;
    };
    if !class_data(db, *class)?
        .flags
        .contains(hir::Modifiers::ANONYMOUS)
    {
        return None;
    }
    let root = base_db::parse(db, source.file).syntax_node();
    let body = root
        .covering_element(source.full_range)
        .ancestors()
        .find(|n| n.kind() == SyntaxKind::CLASS_BODY)?;
    let parent = body.parent()?;
    if let Some(new) = ast::NewExpr::cast(parent.clone()) {
        let ty = new.ty()?;
        let text: String = ty
            .syntax()
            .text()
            .to_string()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        return Some((
            SmolStr::new(format!("new {text}() {{…}}")),
            ty.syntax().text_range(),
        ));
    }
    let constant = ast::EnumConstant::cast(parent)?;
    let name = constant.name()?;
    Some((
        SmolStr::new(format!("{} {{…}}", name.text())),
        name.syntax().text_range(),
    ))
}

/// 把定义变成跳转目标。包没有位置，返回 `None`。
pub(crate) fn to_nav(db: &dyn Db, def: &Definition) -> Option<NavigationTarget> {
    let name = def.name(db)?;
    let kind = SymbolKind::of_definition(db, def);
    let container = container_name(db, def);
    let deprecated = ide_db::definition_flags(db, def).is_deprecated();
    let key = def_key(db, def);
    let detail = match def {
        Definition::Package(_) => None,
        _ => Some(ide_db::render::definition_signature(db, def)),
    };
    let target = |file, full_range, focus_range| NavigationTarget {
        file,
        full_range,
        focus_range,
        name: name.clone(),
        kind,
        container: container.clone(),
        detail: detail.clone(),
        deprecated,
        key: key.clone(),
    };

    if let Some(source) = def.source(db) {
        let file_id = source.file.file_id(db);
        if let Some((name, focus_range)) = anonymous_class_label(db, def, &source) {
            return Some(NavigationTarget {
                name,
                ..target(NavFile::Source(file_id), source.full_range, focus_range)
            });
        }
        return Some(target(
            NavFile::Source(file_id),
            source.full_range,
            source.focus_range,
        ));
    }

    let (class, member) = match def {
        Definition::Class(class) => (*class, None),
        Definition::Field(field) => {
            let member = LibraryMember {
                name: name.clone(),
                kind: LibraryMemberKind::Field,
                params: Vec::new(),
            };
            (field.class, Some(member))
        }
        Definition::Method(method) => {
            let data = class_data(db, method.class)?;
            let m = data.methods.get(method.idx as usize)?;
            // 同名、同形参个数的重载在源码里只能靠形参类型区分
            let params = method_sig(db, *method)
                .params
                .iter()
                .map(|ty| erased_type_key(db, ty))
                .collect();
            let member = LibraryMember {
                name: name.clone(),
                kind: if m.is_constructor {
                    LibraryMemberKind::Constructor
                } else {
                    LibraryMemberKind::Method
                },
                params,
            };
            (method.class, Some(member))
        }
        _ => return None,
    };

    // 源码里的合成成员（隐式构造器、记录的访问器 …）没有自己的声明：落到所属的类上。
    // 依赖库的类即使打开了库源码，对不上的成员也交给宿主按名字在源码里定位
    let is_source = class_data(db, class).is_some_and(|d| d.is_source);
    if let Some(class_source) = Definition::Class(class).source(db).filter(|_| is_source) {
        let file_id = class_source.file.file_id(db);
        return Some(target(
            NavFile::Source(file_id),
            class_source.full_range,
            class_source.focus_range,
        ));
    }

    let empty = TextRange::empty(TextSize::from(0));
    Some(target(
        NavFile::Library {
            class: class.binary_name(db),
            member,
        },
        empty,
        empty,
    ))
}

/// 光标下的名字指向的定义，以及这个名字的范围。
pub(crate) fn definition_at(
    db: &dyn Db,
    file: SourceFile,
    offset: TextSize,
) -> Option<(TextRange, Definition)> {
    let sema = Semantics::new(db);
    let root = base_db::parse(db, file).syntax_node();
    // 文档注释里的 `{@link Foo#bar}`、`@param x` …
    if ide_db::doc_links::in_doc_comment(&root, offset) {
        return ide_db::doc_links::definition_at(db, file, &root, offset);
    }
    let token = pick_ident_token(&root, offset)?;
    let range = token.text_range();
    let parent = token.parent()?;
    let def = match token.kind() {
        SyntaxKind::THIS_KW | SyntaxKind::SUPER_KW => {
            sema.explicit_constructor_target(file, &parent)?
        }
        SyntaxKind::NEW_KW => sema.constructor_ref_target(file, &parent)?,
        _ => {
            if let Some(name_ref) = ast::NameRef::cast(parent.clone()) {
                match sema.classify_name_ref(file, &name_ref) {
                    Some(def) => def,
                    None => var_type(db, &sema, file, &name_ref)?,
                }
            } else {
                let name = ast::Name::cast(parent)?;
                sema.classify_name(file, &name)?
            }
        }
    };
    Some((range, def))
}

/// 局部变量（含 for-each、try 资源、lambda 形参）声明里的 `var`：推断出的类型的类。
fn var_type(
    db: &dyn Db,
    sema: &Semantics<'_>,
    file: SourceFile,
    name_ref: &ast::NameRef,
) -> Option<Definition> {
    if name_ref.text() != "var" {
        return None;
    }
    let ty_node = name_ref.syntax().parent()?;
    if ty_node.kind() != SyntaxKind::CLASS_TYPE {
        return None;
    }
    let decl = ty_node.parent()?;
    let name = match decl.kind() {
        SyntaxKind::LOCAL_VAR_DECL => decl
            .children()
            .find(|c| c.kind() == SyntaxKind::VARIABLE_DECLARATOR)?
            .children()
            .find_map(ast::Name::cast)?,
        SyntaxKind::FOREACH_STMT | SyntaxKind::PARAM | SyntaxKind::RESOURCE => {
            decl.children().find_map(ast::Name::cast)?
        }
        _ => return None,
    };
    let Definition::Local(local) = sema.classify_name(file, &name)? else {
        return None;
    };
    let ty = hir::infer(db, local.body).local(local.id).ty.clone();
    let mut classes = Vec::new();
    classes_of_ty(&ty.upper_bound(db), &mut classes);
    classes.first().map(|class| Definition::Class(*class))
}

pub(crate) fn position_file(db: &dyn Db, position: FilePosition) -> Option<SourceFile> {
    base_db::source_file(db, position.file_id)
}

pub(crate) fn goto_definition(
    db: &dyn Db,
    position: FilePosition,
) -> Option<RangeInfo<Vec<NavigationTarget>>> {
    let file = position_file(db, position)?;
    if let Some((placeholder, module)) = ide_db::spring::property_at(db, file, position.offset) {
        let targets = ide_db::spring::matching_properties(db, module, &placeholder.key)
            .into_iter()
            .map(|property| NavigationTarget {
                file: NavFile::Source(property.file_id),
                full_range: property.key_range,
                focus_range: property.key_range,
                name: property.key.as_str().into(),
                kind: SymbolKind::Field,
                container: Some(property.file_name.to_string()),
                detail: Some(property.value),
                deprecated: false,
                key: None,
            })
            .collect();
        return Some(RangeInfo {
            range: placeholder.key_range,
            info: targets,
        });
    }
    // HTTP 客户端方法的声明（名字或映射注解里的路径）：跳到匹配的服务端控制器方法
    if let Some((range, targets)) = crate::endpoints::goto_server(db, file, position.offset) {
        return Some(RangeInfo {
            range,
            info: targets,
        });
    }
    let (range, def) = definition_at(db, file, position.offset)?;
    let targets: Vec<NavigationTarget> = to_nav(db, &def).into_iter().collect();
    Some(RangeInfo {
        range,
        info: targets,
    })
}

/// 方法 `method` 直接覆写 / 实现的父类型方法。
pub(crate) fn super_methods(db: &dyn Db, method: MethodId) -> Vec<MethodId> {
    let target = Definition::Method(method);
    let mut res = Vec::new();
    for sup in all_supers(db, method.class).iter().copied() {
        let Some(data) = class_data(db, sup) else {
            continue;
        };
        let Some(name) = target.name(db) else {
            continue;
        };
        for (idx, _) in data.methods_named(&name) {
            let candidate = MethodId { class: sup, idx };
            if refers_to(db, &Definition::Method(candidate), &target) {
                res.push(candidate);
            }
        }
    }
    res
}

/// 声明：对方法是它覆写的父类型方法（最近的一个），其余同定义。
pub(crate) fn goto_declaration(
    db: &dyn Db,
    position: FilePosition,
) -> Option<RangeInfo<Vec<NavigationTarget>>> {
    let file = position_file(db, position)?;
    let (range, def) = definition_at(db, file, position.offset)?;
    if let Definition::Method(method) = &def {
        if let Some(sup) = super_methods(db, *method).into_iter().next() {
            let targets: Vec<_> = to_nav(db, &Definition::Method(sup)).into_iter().collect();
            if !targets.is_empty() {
                return Some(RangeInfo {
                    range,
                    info: targets,
                });
            }
        }
    }
    Some(RangeInfo {
        range,
        info: to_nav(db, &def).into_iter().collect(),
    })
}

fn classes_of_ty(ty: &Ty, out: &mut Vec<ClassId>) {
    match ty {
        Ty::Class(class, _) => out.push(*class),
        Ty::Array(element) => classes_of_ty(element, out),
        Ty::Intersection(parts) => parts.iter().for_each(|part| classes_of_ty(part, out)),
        _ => {}
    }
}

pub(crate) fn goto_type_definition(
    db: &dyn Db,
    position: FilePosition,
) -> Option<RangeInfo<Vec<NavigationTarget>>> {
    let file = position_file(db, position)?;
    let (range, def) = definition_at(db, file, position.offset)?;
    // 表达式里的引用（`xs.get(0)`、`box.item`）按表达式的实际类型跳：声明的类型里可能是
    // 类型参数（`E get(int)`），要用接收者的类型实参和调用的推断结果代换之后才有意义
    let expr_ty = match &def {
        Definition::Method(_) | Definition::Field(_) | Definition::Local(_) => {
            reference_expr_ty(db, file, position.offset)
        }
        _ => None,
    };
    let ty = match (expr_ty, &def) {
        (Some(ty), _) => ty,
        (None, Definition::Class(class)) => Ty::class(*class),
        (None, Definition::Field(field)) => field_ty(db, *field),
        (None, Definition::Method(method)) => method_sig(db, *method).ret.clone(),
        (None, Definition::Local(local)) => hir::infer(db, local.body).local(local.id).ty.clone(),
        (None, Definition::TypeParam(param)) => hir::type_param_bounds(db, *param)
            .first()
            .cloned()
            .unwrap_or(Ty::Unknown),
        (None, Definition::Package(_)) => return None,
    };
    let mut classes = Vec::new();
    classes_of_ty(&ty.upper_bound(db), &mut classes);
    let targets: Vec<NavigationTarget> = classes
        .into_iter()
        .filter_map(|class| to_nav(db, &Definition::Class(class)))
        .collect();
    Some(RangeInfo {
        range,
        info: targets,
    })
}

/// 光标处的名字作为方法调用名、字段访问或变量引用时，整个表达式推断出来的类型。
fn reference_expr_ty(db: &dyn Db, file: SourceFile, offset: TextSize) -> Option<Ty> {
    let sema = Semantics::new(db);
    let root = base_db::parse(db, file).syntax_node();
    let token = pick_ident_token(&root, offset)?;
    let name_ref = ast::NameRef::cast(token.parent()?)?;
    let parent = name_ref.syntax().parent()?;
    let is_own_name = match parent.kind() {
        SyntaxKind::METHOD_CALL => ast::MethodCall::cast(parent.clone())
            .and_then(|call| call.name_ref())
            .is_some_and(|n| n == name_ref),
        SyntaxKind::FIELD_ACCESS => ast::FieldAccess::cast(parent.clone())
            .and_then(|access| access.name_ref())
            .is_some_and(|n| n == name_ref),
        SyntaxKind::NAME_EXPR => true,
        _ => false,
    };
    if !is_own_name {
        return None;
    }
    let expr = ast::Expr::cast(parent)?;
    let ty = sema.type_of_expr(file, &expr)?;
    (!ty.contains_unknown() && !matches!(ty, Ty::Void | Ty::Null)).then_some(ty)
}

/// `class` 的所有（直接和间接）子类型：工作区源码里的，加上依赖库里的。
pub(crate) fn all_subclasses(db: &dyn Db, class: ClassId) -> Vec<ClassId> {
    let mut res = Vec::new();
    let mut seen: FxHashSet<ClassId> = FxHashSet::default();
    seen.insert(class);

    // 工作区源码里的局部类和匿名类也算（跳转时匿名类用 `new X() {…}` 当名字）
    for candidate in hir::source_subclasses(db, class) {
        if seen.insert(candidate) {
            res.push(candidate);
        }
    }

    // 依赖库：沿"直接子类型"表做广度优先遍历
    let class_path = workspace(db).class_path(db);
    let mut queue = vec![class.binary_name(db)];
    while let Some(name) = queue.pop() {
        for summary in class_path.direct_subtypes(&name) {
            if summary.is_anonymous_or_local() {
                continue;
            }
            let candidate = ClassId::from_binary_name(db, &summary.name);
            if seen.insert(candidate) {
                res.push(candidate);
                queue.push(summary.name.clone());
            }
        }
    }
    res
}

/// 父类型是 `class`（`direct` 为假时也可以是它的子类）的菱形匿名类的跳转目标。
pub(crate) fn diamond_anonymous_navs(
    db: &dyn Db,
    class: ClassId,
    direct: bool,
) -> Vec<NavigationTarget> {
    // 直接子类型的 `new` 里写的就是这个类的名字
    let name = class_data(db, class).map(|d| d.name.to_string());
    let words: Vec<&str> = match (&name, direct) {
        (Some(name), true) => vec![name.as_str()],
        _ => Vec::new(),
    };
    ide_db::diamond::find_diamond_anonymous(db, &words, |sup| {
        sup == class || (!direct && hir::is_subclass_of(db, sup, class))
    })
    .into_iter()
    .map(|(file, anon)| NavigationTarget {
        file: NavFile::Source(file.file_id(db)),
        full_range: anon.full_range,
        focus_range: anon.ty_range,
        name: anon.label.clone(),
        kind: SymbolKind::Class,
        container: None,
        detail: None,
        deprecated: false,
        key: None,
    })
    .collect()
}

/// 菱形匿名类里覆写 `methods` 中任何一个的方法声明（同名、同参数个数，所在的匿名类继承
/// 了声明它的类）：`(文件, 方法)`。
pub(crate) fn diamond_anonymous_overrides(
    db: &dyn Db,
    methods: &[MethodId],
) -> Vec<(SourceFile, ide_db::diamond::DiamondMethod)> {
    let keys: Vec<(ClassId, SmolStr, usize)> = methods
        .iter()
        .filter_map(|method| {
            let data = class_data(db, method.class)?;
            let m = data.methods.get(method.idx as usize)?;
            (!m.is_constructor && !m.flags.is_static())
                .then(|| (method.class, SmolStr::new(m.name.as_str()), m.params.len()))
        })
        .collect();
    diamond_anonymous_overrides_by_key(db, &keys)
}

/// 菱形匿名类里覆写"类 `class` 里名为 `name`、有 `arity` 个形参的方法"的方法声明。
/// 方法的签名刚被改过时，用改之前的名字和参数个数来找。
pub(crate) fn diamond_anonymous_overrides_by_key(
    db: &dyn Db,
    keys: &[(ClassId, SmolStr, usize)],
) -> Vec<(SourceFile, ide_db::diamond::DiamondMethod)> {
    if keys.is_empty() {
        return Vec::new();
    }
    let mut res: Vec<(SourceFile, ide_db::diamond::DiamondMethod)> = Vec::new();
    let words: Vec<&str> = keys.iter().map(|(_, name, _)| name.as_str()).collect();
    let found = ide_db::diamond::find_diamond_anonymous(db, &words, |sup| {
        keys.iter()
            .any(|(class, _, _)| sup == *class || hir::is_subclass_of(db, sup, *class))
    });
    for (file, anon) in found {
        for method in &anon.methods {
            let overrides = keys.iter().any(|(class, name, arity)| {
                *name == method.name
                    && *arity == method.arity
                    && (anon.super_class == *class
                        || hir::is_subclass_of(db, anon.super_class, *class))
            });
            if overrides
                && !res
                    .iter()
                    .any(|(f, m)| *f == file && m.name_range == method.name_range)
            {
                res.push((file, method.clone()));
            }
        }
    }
    res
}

/// 方法不可能被覆写：`static`、`private`、`final`、构造器，或者所在的类是 `final`。
/// 不用去扫子类（`Object.getClass()` 要扫遍整个类路径才知道没有覆写）。
fn cannot_be_overridden(db: &dyn Db, method: MethodId) -> bool {
    let Some(class) = class_data(db, method.class) else {
        return false;
    };
    let Some(data) = class.methods.get(method.idx as usize) else {
        return false;
    };
    use hir::Modifiers as M;
    data.is_constructor
        || [M::STATIC, M::PRIVATE, M::FINAL]
            .iter()
            .any(|flag| data.flags.contains(*flag))
        || class.flags.contains(M::FINAL)
}

/// 跳转到实现时最多列出的依赖库里的实现个数。
const LIBRARY_IMPLEMENTATIONS: usize = 100;

pub(crate) fn goto_implementation(
    db: &dyn Db,
    position: FilePosition,
) -> Option<RangeInfo<Vec<NavigationTarget>>> {
    let file = position_file(db, position)?;
    let Some((range, def)) = definition_at(db, file, position.offset) else {
        // 客户端方法映射注解里的路径
        let (range, targets) = crate::endpoints::goto_server(db, file, position.offset)?;
        return Some(RangeInfo {
            range,
            info: targets,
        });
    };
    let mut targets = Vec::new();
    // 依赖库里的实现只列出前一部分（源码里的排在前面，全部列出）：`Object` 的子类就是整个
    // 类路径，`toString()` 的覆写有几千个，宿主也只物化前面几十个
    let mut library_left = LIBRARY_IMPLEMENTATIONS;
    match &def {
        Definition::Class(class) => {
            for sub in all_subclasses(db, *class) {
                if !class_data(db, sub).is_some_and(|d| d.is_source) {
                    if library_left == 0 {
                        break;
                    }
                    library_left -= 1;
                }
                targets.extend(to_nav(db, &Definition::Class(sub)));
            }
            targets.extend(diamond_anonymous_navs(db, *class, false));
        }
        Definition::Method(method) if cannot_be_overridden(db, *method) => {}
        Definition::Method(method) => {
            let name = def.name(db)?;
            for sub in all_subclasses(db, method.class) {
                db.unwind_if_revision_cancelled();
                let Some(data) = class_data(db, sub) else {
                    continue;
                };
                if !data.is_source && library_left == 0 {
                    break;
                }
                for (idx, _) in data.methods_named(&name) {
                    let candidate = Definition::Method(MethodId { class: sub, idx });
                    if refers_to(db, &candidate, &def) {
                        targets.extend(to_nav(db, &candidate));
                        if !data.is_source {
                            library_left = library_left.saturating_sub(1);
                        }
                    }
                }
            }
            // 菱形匿名类里的覆写
            for (file, member) in diamond_anonymous_overrides(db, &[*method]) {
                targets.push(NavigationTarget {
                    file: NavFile::Source(file.file_id(db)),
                    full_range: member.full_range,
                    focus_range: member.name_range,
                    name: member.name.clone(),
                    kind: SymbolKind::Method,
                    container: None,
                    detail: None,
                    deprecated: false,
                    key: None,
                });
            }
            // HTTP 客户端方法的"实现"是它调用的服务端控制器方法；控制器本身就实现了
            // 这个方法（契约接口）时，继承关系已经找到它了，不重复列出
            for server in crate::endpoints::servers_of_method(db, &def) {
                let duplicate = targets
                    .iter()
                    .any(|t| t.file == server.file && t.focus_range == server.focus_range);
                if !duplicate {
                    targets.push(server);
                }
            }
            // 默认方法找不到其他实现时，其方法体就是可跳转的实现。
            if targets.is_empty()
                && ide_db::definition_flags(db, &def).contains(hir::Modifiers::DEFAULT)
            {
                targets.extend(to_nav(db, &def));
            }
        }
        // Spring 注入点（字段、构造器形参 …）的"实现"是注入进来的 Bean 定义
        _ => match crate::beans::injected_beans(db, &def) {
            Some(beans) if !beans.is_empty() => targets.extend(beans),
            _ => targets.extend(to_nav(db, &def)),
        },
    }
    Some(RangeInfo {
        range,
        info: targets,
    })
}

pub(crate) fn workspace_symbols(db: &dyn Db, query: &str, limit: usize) -> Vec<NavigationTarget> {
    // 带 `/` 的查询是在找 Web 端点（`/api/users`、`GET /orders`）
    if query.contains('/') {
        return crate::endpoints::search(db, query, limit);
    }
    // 查询非空时也搜依赖库和 JDK 里的公开类型（排在同等匹配的工作区符号之后）；
    // 它们的位置要由宿主物化源码或桩代码才知道，宿主只物化排在前面的一部分
    search_symbols(db, query, limit, !query.is_empty())
        .into_iter()
        .filter_map(|symbol| to_nav(db, &symbol.entry.def))
        .collect()
}
