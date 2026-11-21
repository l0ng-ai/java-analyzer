//! 类型名字解析（JLS §6.4.1、§6.5）。
//!
//! 简单名的查找顺序：
//! 1. 方法的类型参数；
//! 2. 由内到外每一层类的类型参数、成员类型（含继承来的）；
//! 3. 单类型 import；
//! 4. 同一文件的顶层类型、同包类型；
//! 5. 按需 import（`import a.b.*`）；
//! 6. `java.lang`。

use std::sync::Arc;

use base_db::{Db, SourceFile};
use rustc_hash::FxHashSet;
use smol_str::SmolStr;

use crate::{
    data::{ClassId, GenericOwner, MethodId, Name, TypeParamId, TypeRef},
    index::{
        class_decl_file, class_in_file, class_in_origin, class_origin, direct_supers, item_tree,
        lookup_class, nested_class, sibling_class,
    },
    signatures::{class_header, file_scope, method_type_param},
    visibility::lookup_class_from,
};

/// 解析类型名时所处的位置。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TypeScope {
    pub file: Option<SourceFile>,
    pub class: Option<ClassId>,
    pub method: Option<MethodId>,
    /// 正在解析 `class` 自己的头部（extends / implements / 类型参数约束）。
    /// 此时 `class` 自身的成员类型不在作用域内，否则会循环依赖。
    pub in_class_header: bool,
}

impl TypeScope {
    pub fn file(file: SourceFile) -> TypeScope {
        TypeScope {
            file: Some(file),
            class: None,
            method: None,
            in_class_header: false,
        }
    }

    pub fn class(db: &dyn Db, class: ClassId) -> TypeScope {
        TypeScope {
            file: class_decl_file(db, class),
            class: Some(class),
            method: None,
            in_class_header: false,
        }
    }

    pub fn class_header(db: &dyn Db, class: ClassId) -> TypeScope {
        TypeScope {
            in_class_header: true,
            ..TypeScope::class(db, class)
        }
    }

    pub fn method(db: &dyn Db, method: MethodId) -> TypeScope {
        TypeScope {
            method: Some(method),
            ..TypeScope::class(db, method.class)
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TypeNs {
    Class(ClassId),
    TypeParam(TypeParamId),
}

/// `class` 的成员类型 `name`：先看自己声明的，再看继承来的。
pub fn member_type(db: &dyn Db, class: ClassId, name: &str) -> Option<ClassId> {
    if let Some(found) = nested_class(db, class, name) {
        return Some(found);
    }
    let mut seen = FxHashSet::default();
    seen.insert(class);
    direct_supers(db, class)
        .iter()
        .find_map(|sup| inherited_member_type(db, *sup, name, &mut seen))
}

/// 子类能从 `class` 继承到的成员类型 `name`。
///
/// 父类型自己声明了同名的成员类型时，它隐藏更上层的同名类型：如果这个声明是私有的，
/// 沿这条路径就什么也继承不到（`WeakHashMap` 的私有 `Entry` 挡住了 `Map.Entry`）。
fn inherited_member_type(
    db: &dyn Db,
    class: ClassId,
    name: &str,
    seen: &mut FxHashSet<ClassId>,
) -> Option<ClassId> {
    if !seen.insert(class) {
        return None;
    }
    if let Some(found) = nested_class(db, class, name) {
        let private = class_header(db, found)
            .is_some_and(|data| data.flags.visibility() == crate::Visibility::Private);
        return (!private).then_some(found);
    }
    direct_supers(db, class)
        .iter()
        .find_map(|sup| inherited_member_type(db, *sup, name, seen))
}

/// 只在类型参数里找（方法的 → 各层类的）。
pub fn resolve_type_param(db: &dyn Db, scope: &TypeScope, name: &str) -> Option<TypeParamId> {
    if let Some(method) = scope.method {
        if let Some(idx) = method_type_param(db, method, name) {
            return Some(TypeParamId {
                owner: GenericOwner::Method(method),
                idx,
            });
        }
    }
    let mut current = scope.class;
    while let Some(class) = current {
        let data = class_header(db, class)?;
        if let Some(idx) = data.type_params.iter().position(|p| p.name == name) {
            return Some(TypeParamId {
                owner: GenericOwner::Class(class),
                idx: idx as u32,
            });
        }
        if data.flags.contains(crate::Modifiers::LOCAL_CLASS) {
            let found = local_class_owner(db, class)
                .and_then(|(outer, owner)| owner_method_type_param(db, outer, owner, name));
            if found.is_some() {
                return found;
            }
        }
        current = data
            .outer
            .as_deref()
            .and_then(|outer| sibling_class(db, class, outer));
    }
    None
}

/// 文件里的局部类和匿名类，不带声明下标：只有局部类的增删、改名会改变它。
#[derive(Clone, PartialEq, Eq, Debug)]
struct LocalClassInfo {
    name: Name,
    binary_name: SmolStr,
    outer: SmolStr,
    owner: Option<u32>,
}

#[salsa::tracked]
fn file_local_classes(db: &dyn Db, file: SourceFile) -> Arc<Vec<LocalClassInfo>> {
    Arc::new(
        item_tree(db, file)
            .local_classes
            .iter()
            .map(|l| LocalClassInfo {
                name: l.name.clone(),
                binary_name: l.binary_name.clone(),
                outer: l.outer.clone(),
                owner: l.owner,
            })
            .collect(),
    )
}

/// `outer` 的成员 `owner`（方法下标；`None` 是字段初始化式和初始化块）里声明的局部类 `name`。
fn local_class_in(db: &dyn Db, outer: ClassId, owner: Option<u32>, name: &str) -> Option<ClassId> {
    let file = class_decl_file(db, outer)?;
    let locals = file_local_classes(db, file);
    if locals.is_empty() {
        return None;
    }
    let outer_name = outer.binary_name(db);
    locals
        .iter()
        .find(|l| l.outer == outer_name && l.owner == owner && l.name == name)
        .map(|l| class_in_file(db, file, &l.binary_name))
}

/// 局部类（含匿名类）声明在哪里：`(直接外层的类, 所在方法的下标)`；在字段初始化式、
/// 初始化块里时方法下标为 `None`。
pub fn local_class_owner(db: &dyn Db, class: ClassId) -> Option<(ClassId, Option<u32>)> {
    let file = class_decl_file(db, class)?;
    let binary = class.binary_name(db);
    let locals = file_local_classes(db, file);
    let info = locals.iter().find(|l| l.binary_name == binary)?;
    Some((class_in_file(db, file, &info.outer), info.owner))
}

/// 局部类 `class` 所在的方法的类型参数 `name`（`<T> void m() { class L { T t; } }`）。
fn owner_method_type_param(
    db: &dyn Db,
    outer: ClassId,
    owner: Option<u32>,
    name: &str,
) -> Option<TypeParamId> {
    let method = MethodId {
        class: outer,
        idx: owner?,
    };
    let idx = method_type_param(db, method, name)?;
    Some(TypeParamId {
        owner: GenericOwner::Method(method),
        idx,
    })
}

/// 解析一个简单类型名。
pub fn resolve_simple_type(db: &dyn Db, scope: &TypeScope, name: &str) -> Option<TypeNs> {
    if let Some(method) = scope.method {
        if let Some(idx) = method_type_param(db, method, name) {
            return Some(TypeNs::TypeParam(TypeParamId {
                owner: GenericOwner::Method(method),
                idx,
            }));
        }
    }

    // 当前体里声明的局部类遮蔽外层的同名类型
    if let Some(class) = scope.class {
        let owner = scope.method.filter(|m| m.class == class).map(|m| m.idx);
        if let Some(found) = local_class_in(db, class, owner, name) {
            return Some(TypeNs::Class(found));
        }
    }

    let mut current = scope.class;
    while let Some(class) = current {
        let Some(data) = class_header(db, class) else {
            break;
        };
        if let Some(idx) = data.type_params.iter().position(|p| p.name == name) {
            return Some(TypeNs::TypeParam(TypeParamId {
                owner: GenericOwner::Class(class),
                idx: idx as u32,
            }));
        }
        let skip_members = scope.in_class_header && Some(class) == scope.class;
        if !skip_members {
            if let Some(found) = member_type(db, class, name) {
                return Some(TypeNs::Class(found));
            }
        }
        // 局部类：和它声明在同一个体里的局部类（包括它自己），然后是所在方法的类型参数
        if data.flags.contains(crate::Modifiers::LOCAL_CLASS) {
            if let Some((outer, owner)) = local_class_owner(db, class) {
                if let Some(found) = local_class_in(db, outer, owner, name) {
                    return Some(TypeNs::Class(found));
                }
                if let Some(param) = owner_method_type_param(db, outer, owner, name) {
                    return Some(TypeNs::TypeParam(param));
                }
            }
        }
        current = data
            .outer
            .as_deref()
            .and_then(|outer| sibling_class(db, class, outer));
    }

    if let Some(file) = scope.file {
        if let Some(found) = resolve_in_file(db, file, name) {
            return Some(TypeNs::Class(found));
        }
    } else if scope.class.is_none() {
        return lookup_class(db, &format!("java/lang/{name}")).map(TypeNs::Class);
    }
    None
}

/// 按文件的 import、所在的包、`java.lang` 和模块导入解析简单类名。
/// 每一步只接受这个文件看得到的类（模块依赖之外的类、主代码里的测试类都看不到），看不到时继续往后找；
/// 同名的类有多份时取这个文件看得到的、按类路径顺序最靠前的那一份。
///
/// 只读文件的 [`file_scope`]：改成员的签名、新增成员都不影响这里的结果。
fn resolve_in_file(db: &dyn Db, file: SourceFile, name: &str) -> Option<ClassId> {
    let scope = file_scope(db, file);

    for import in scope.imports().iter().filter(|i| !i.is_on_demand) {
        if import.segments.last().is_some_and(|last| last == name) {
            let found = if import.is_static {
                let (_, qualifier) = import.segments.split_last()?;
                resolve_qualified_class_visible(db, file, qualifier)
                    .and_then(|c| member_type(db, c, name))
            } else {
                resolve_qualified_class_visible(db, file, &import.segments)
            };
            if found.is_some() {
                return found;
            }
        }
    }

    // 紧凑源文件的隐式类不能按名字引用
    let implicit = |flags: crate::Modifiers| flags.contains(crate::Modifiers::IMPLICIT_CLASS);
    if let Some((_, binary_name)) = scope.top_level().find(|(n, _)| *n == name) {
        return Some(class_in_file(db, file, binary_name));
    }

    let in_package = if scope.package().is_empty() {
        name.to_owned()
    } else {
        format!("{}/{}", scope.package(), name)
    };
    if let Some(found) = lookup_class_from(db, Some(file), &in_package)
        .filter(|found| class_header(db, *found).is_none_or(|data| !implicit(data.flags)))
    {
        return Some(found);
    }

    for import in scope.imports().iter().filter(|i| i.is_on_demand) {
        if !import.is_static {
            let package = import.segments.join("/");
            // 按需 import 只带进别的包里的 public 类（`java.io.*` 不会带进包私有的 `java.io.FileSystem`）
            let found =
                lookup_class_from(db, Some(file), &format!("{package}/{name}")).filter(|found| {
                    class_header(db, *found)
                        .is_none_or(|data| data.flags.visibility() == crate::Visibility::Public)
                });
            if found.is_some() {
                return found;
            }
        }
        // `import a.b.Outer.*` / `import static a.b.Outer.*` 都能带进成员类型。
        // 和 javac 一致：非静态的只带进 `Outer` 自己声明的，静态的还包括继承来的。
        let found = resolve_qualified_class_visible(db, file, &import.segments).and_then(|outer| {
            if import.is_static {
                member_type(db, outer, name)
            } else {
                nested_class(db, outer, name)
            }
        });
        if found.is_some() {
            return found;
        }
    }

    if let Some(found) = lookup_class_from(db, Some(file), &format!("java/lang/{name}")) {
        return Some(found);
    }

    // 模块导入的优先级最低；两个模块导入带进同名的类时有歧义，不选
    match crate::modules::module_import_candidates(db, file, name).as_slice() {
        [single] => Some(*single),
        _ => None,
    }
}

/// 在文件 `file` 里解析完全限定名：最外层的类要对这个文件可见（有多份时取这个文件看得到的那一份），
/// 成员类型跟随外层类（继承来的成员类型可能声明在别的依赖里，不再单独检查）。
pub fn resolve_qualified_class_visible(
    db: &dyn Db,
    file: SourceFile,
    segments: &[Name],
) -> Option<ClassId> {
    resolve_qualified_class_with(db, segments, |binary_name| {
        lookup_class_from(db, Some(file), binary_name)
    })
}

/// 解析完全限定名 `a.b.Outer.Inner`：最短的包前缀优先（类型遮蔽包）。不看上下文，同名的类取主副本。
pub fn resolve_qualified_class(db: &dyn Db, segments: &[Name]) -> Option<ClassId> {
    resolve_qualified_class_with(db, segments, |binary_name| lookup_class(db, binary_name))
}

/// 从文件 `from` 出发解析完全限定名；`from` 未知时同 [`resolve_qualified_class`]。
pub fn resolve_qualified_class_from(
    db: &dyn Db,
    from: Option<SourceFile>,
    segments: &[Name],
) -> Option<ClassId> {
    match from {
        Some(file) => resolve_qualified_class_visible(db, file, segments),
        None => resolve_qualified_class(db, segments),
    }
}

/// 同 [`resolve_qualified_class`]，只是最外层的类用 `lookup` 按二进制名查找：
/// 找不到时把更长的前缀当包名继续找。
fn resolve_qualified_class_with(
    db: &dyn Db,
    segments: &[Name],
    lookup: impl Fn(&str) -> Option<ClassId>,
) -> Option<ClassId> {
    for class_pos in 0..segments.len() {
        let mut binary_name = segments[..class_pos].join("/");
        if !binary_name.is_empty() {
            binary_name.push('/');
        }
        binary_name.push_str(&segments[class_pos]);
        if let Some(mut class) = lookup(&binary_name) {
            for nested in &segments[class_pos + 1..] {
                class = member_type(db, class, nested)?;
            }
            return Some(class);
        }
    }
    None
}

/// 解析一条类型路径：第一段按简单名解析，失败则把前缀当包名；后续各段是成员类型。
pub fn resolve_type_path<S: AsRef<str>>(
    db: &dyn Db,
    scope: &TypeScope,
    segments: &[S],
) -> Option<TypeNs> {
    let (first, rest) = segments.split_first()?;
    if let Some(found) = resolve_simple_type(db, scope, first.as_ref()) {
        return match found {
            TypeNs::Class(mut class) => {
                for nested in rest {
                    class = member_type(db, class, nested.as_ref())?;
                }
                Some(TypeNs::Class(class))
            }
            TypeNs::TypeParam(_) if rest.is_empty() => Some(found),
            TypeNs::TypeParam(_) => None,
        };
    }
    let names: Vec<Name> = segments.iter().map(|s| Name::new(s.as_ref())).collect();
    resolve_qualified_class_from(db, scope.file, &names).map(TypeNs::Class)
}

/// 在作用域里按二进制名查找类（class 文件签名、Lombok 生成的成员里已经确定的类名）。
/// 同名的类有多份时：先找和当前类同一来源的那一份，再找这个文件看得到的；都没有时取主副本。
pub fn lookup_class_in_scope(db: &dyn Db, scope: &TypeScope, binary_name: &str) -> Option<ClassId> {
    // 所有类都按来源找，不只副本：主副本也可能和它的外层类不在同一个文件里（见 `sibling_class`）
    if let Some(found) = scope
        .class
        .and_then(|class| class_origin(db, class))
        .and_then(|origin| class_in_origin(db, binary_name, origin))
    {
        return Some(found);
    }
    match scope.file {
        Some(file) => {
            lookup_class_from(db, Some(file), binary_name).or_else(|| lookup_class(db, binary_name))
        }
        None => lookup_class(db, binary_name),
    }
}

/// 把签名里的类型引用解析到它的（擦除后的）类。类型变量、基本类型、数组返回 `None`。
pub fn resolve_type_ref_to_class(db: &dyn Db, scope: &TypeScope, ty: &TypeRef) -> Option<ClassId> {
    match ty {
        TypeRef::Path(segments) => {
            let names: Vec<&str> = segments.iter().map(|s| s.name.as_str()).collect();
            match resolve_type_path(db, scope, &names)? {
                TypeNs::Class(class) => Some(class),
                TypeNs::TypeParam(_) => None,
            }
        }
        TypeRef::Class { name, .. } => lookup_class_in_scope(db, scope, name),
        _ => None,
    }
}
