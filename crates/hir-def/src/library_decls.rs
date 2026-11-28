//! 依赖库 / JDK 的类在打开的库源码文件（解压出来的源码、生成的签名桩）里的声明。
//!
//! 库里的类以 class 文件为准：成员的顺序（也就是 `MethodId` / `FieldId`）不因为打开了源码而改变，
//! 工程代码里的引用因此不受影响。对应的库源码文件打开时：
//!
//! - class 文件里的成员按名字和形参对到源码里的声明上，记进 `decl`，于是方法体可以推断、
//!   声明处可以查引用；
//! - 源码里有、class 文件里没有的成员（`ct.sym` 只保留公开 API，私有方法都被去掉了）补在末尾；
//! - 只出现在库源码里的类（私有嵌套类、包私有的辅助类）也能按二进制名找到。
//!
//! 库源码只读：这些类的 `is_source` 始终为 `false`，不参与工作区的类索引和诊断。

use std::sync::Arc;

use base_db::{workspace, Db, FileKind, SourceFile};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::{
    data::{ClassData, FieldData, MethodData, Modifiers, TypeRef},
    index::item_tree,
    ClassId,
};

/// 打开的库源码文件里的具名类。
#[derive(Debug, Default, PartialEq, Eq)]
pub struct LibrarySourceIndex {
    classes: FxHashMap<SmolStr, (SourceFile, u32)>,
}

impl LibrarySourceIndex {
    pub fn get(&self, binary_name: &str) -> Option<(SourceFile, u32)> {
        self.classes.get(binary_name).copied()
    }
}

pub fn library_source_index(db: &dyn Db) -> Arc<LibrarySourceIndex> {
    library_source_index_tracked(db, workspace(db))
}

#[salsa::tracked]
fn library_source_index_tracked(db: &dyn Db, _ws: base_db::Workspace) -> Arc<LibrarySourceIndex> {
    let mut files: Vec<_> = workspace(db)
        .files(db)
        .iter()
        .filter(|(_, entry)| matches!(entry.kind, FileKind::Library))
        .map(|(id, entry)| (id, entry.source))
        .collect();
    files.sort_by_key(|(id, _)| *id);
    let mut index = LibrarySourceIndex::default();
    for (_, file) in files {
        let tree = item_tree(db, file);
        for (idx, class) in tree.classes.iter().enumerate() {
            index
                .classes
                .entry(class.binary_name.clone())
                .or_insert((file, idx as u32));
        }
    }
    Arc::new(index)
}

/// 类在打开的库源码文件里的位置：`(文件, ItemTree::classes 的下标)`。
///
/// 单独做成按类缓存的查询：打开另一个库文件时整张索引会变，但大多数类的结果不变，
/// 依赖它的 `class_data` 也就不必重算。
pub fn open_library_source(db: &dyn Db, class: ClassId) -> Option<(SourceFile, u32)> {
    open_library_source_tracked(db, workspace(db), class)
}

#[salsa::tracked]
fn open_library_source_tracked(
    db: &dyn Db,
    _ws: base_db::Workspace,
    class: ClassId,
) -> Option<(SourceFile, u32)> {
    library_source_index(db).get(&class.binary_name(db))
}

/// 类型在签名比较时的简单形式：只看最后一段名字和数组维数，类型实参忽略。
fn type_key(ty: &TypeRef) -> Option<String> {
    Some(match ty {
        TypeRef::Primitive(p) => p.name().to_owned(),
        TypeRef::Void => "void".to_owned(),
        TypeRef::Path(segments) => segments.last()?.name.to_string(),
        TypeRef::Class { name, .. } => name.rsplit(['/', '$']).next()?.to_owned(),
        TypeRef::TypeVar(name) => name.to_string(),
        TypeRef::Array(element) => format!("{}[]", type_key(element)?),
        TypeRef::Wildcard(_) | TypeRef::Intersection(_) | TypeRef::Error => return None,
    })
}

/// 两组形参类型是否对得上。拿不准的类型（没有泛型签名时被擦除成 `Object` 的类型变量等）不算不同。
fn params_match(binary: &[crate::data::ParamData], source: &[crate::data::ParamData]) -> bool {
    binary.len() == source.len()
        && binary
            .iter()
            .zip(source)
            .all(|(b, s)| match (type_key(&b.ty), type_key(&s.ty)) {
                (Some(b), Some(s)) => b == s || b == "Object",
                _ => true,
            })
}

/// class 文件里的方法在源码里对应哪一个（`source` 的下标）。
fn match_method(binary: &MethodData, source: &[MethodData], taken: &[bool]) -> Option<usize> {
    let candidates: Vec<usize> = source
        .iter()
        .enumerate()
        .filter(|(idx, s)| {
            !taken[*idx]
                && s.is_constructor == binary.is_constructor
                && (binary.is_constructor || s.name == binary.name)
        })
        .map(|(idx, _)| idx)
        .collect();
    // 形参完全对得上的
    let exact: Vec<usize> = candidates
        .iter()
        .copied()
        .filter(|&idx| params_match(&binary.params, &source[idx].params))
        .collect();
    if let Some(&first) = exact.first() {
        return Some(first);
    }
    // 内部类、枚举的构造器在 class 文件里多出前置的合成形参（外层实例、枚举常量名和序号）
    if binary.is_constructor {
        let suffix = candidates.iter().copied().find(|&idx| {
            let n = source[idx].params.len();
            n < binary.params.len()
                && params_match(
                    &binary.params[binary.params.len() - n..],
                    &source[idx].params,
                )
        });
        if suffix.is_some() {
            return suffix;
        }
    }
    // 名字唯一时直接对上
    (candidates.len() == 1).then(|| candidates[0])
}

/// 把打开的库源码里的声明位置合并进 class 文件得到的 `ClassData`。
pub(crate) fn merge_library_source(data: &mut ClassData, source: &ClassData) {
    data.decl = source.decl;

    let mut taken = vec![false; source.methods.len()];
    for method in &mut data.methods {
        if let Some(idx) = match_method(method, &source.methods, &taken) {
            taken[idx] = true;
            let matched = &source.methods[idx];
            method.decl = matched.decl;
            // 没有 `MethodParameters` 属性时 class 文件里没有形参名，用源码里的
            if method.params.len() == matched.params.len() {
                for (param, source_param) in method.params.iter_mut().zip(&matched.params) {
                    if param.name.is_none() {
                        param.name = source_param.name.clone();
                    }
                }
            }
        }
    }
    // 源码里有、class 文件里没有的方法（ct.sym 去掉的私有方法等）
    for (idx, method) in source.methods.iter().enumerate() {
        if !taken[idx] && method.decl.is_some() && !method.flags.contains(Modifiers::SYNTHETIC) {
            data.methods.push(method.clone());
        }
    }

    let mut extra_fields: Vec<FieldData> = Vec::new();
    for field in &source.fields {
        match data.fields.iter_mut().find(|f| f.name == field.name) {
            Some(existing) => existing.decl = field.decl,
            None if field.decl.is_some() && !field.flags.contains(Modifiers::SYNTHETIC) => {
                extra_fields.push(field.clone());
            }
            None => {}
        }
    }
    data.fields.extend(extra_fields);

    for nested in &source.nested {
        if !data.nested.contains(nested) {
            data.nested.push(nested.clone());
        }
    }
}

/// 只在库源码里出现的类：按源码的签名，但标记为非工作区源码。
pub(crate) fn library_only_class(source: &ClassData) -> ClassData {
    ClassData {
        is_source: false,
        ..source.clone()
    }
}
