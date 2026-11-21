//! 全局类索引：二进制名 → 类的来源与签名；包 → 内容。
//!
//! 索引把"工作区源码 + 全部依赖 + JDK"放在一个命名空间里。同一个二进制名可能有多份声明
//! （多个模块、源码和 jar、多个 jar），每一份是一个独立的 `ClassId`：按源码 > 依赖 > JDK 的顺序
//! 排第一的是主副本，`lookup_class` 这类不看上下文的查找返回它；其余副本带着来源（见 `CopyOrigin`）。
//! 某个文件能看到哪些类、同名时挑哪一份（按模块依赖隔离）由 `visibility` 在解析名字时决定。

use std::{cell::RefCell, sync::Arc};

use base_db::{workspace, Db, FileKind, SourceFile};
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use crate::{
    binary::lower_class_file,
    data::{ClassData, ClassId, CopyOrigin, DeclIdx, ItemTree, Name},
    library_decls::{
        library_only_class, library_source_index, merge_library_source, open_library_source,
    },
    lower::{lower_file_with, SourceMap},
    resolver::{resolve_type_ref_to_class, TypeScope},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ClassOrigin {
    Source {
        file: SourceFile,
        /// `ItemTree::classes` 的下标
        idx: u32,
    },
    /// 类路径上的第几个容器
    Binary { container: u32 },
}

#[salsa::tracked]
pub fn item_tree_and_map(db: &dyn Db, file: SourceFile) -> (Arc<ItemTree>, Arc<SourceMap>) {
    let parse = base_db::parse(db, file);
    let config = lombok_config(db, file.dir(db).clone());
    let (tree, map) = lower_file_with(&parse.tree(), || file.name(db).clone(), config);
    (Arc::new(tree), Arc::new(map))
}

/// 工作区里的 `lombok.config`：`(所在目录, 文本)`，按目录排序。只读资源文件；结果不变时
/// （改的是 Spring 配置文件）salsa 不会让下游失效。
#[salsa::tracked(returns(ref))]
fn lombok_config_files(db: &dyn Db) -> Vec<(SmolStr, Arc<str>)> {
    let mut files: Vec<(SmolStr, Arc<str>)> = workspace(db)
        .resources(db)
        .iter()
        .filter(|r| r.name == "lombok.config")
        .map(|r| (r.dir.clone(), r.text.clone()))
        .collect();
    files.sort();
    files
}

/// 目录 `dir` 里的源文件看到的 Lombok 配置：从这个目录往上找 `lombok.config`，遇到
/// `config.stopBubbling = true` 的为止，再从最外层往里叠加（里层的覆盖外层的，`+=` / `-=` /
/// `clear` 按顺序作用）。
///
/// 按目录缓存：某个 `lombok.config` 改了，只有它管辖的目录的结果会变，别处的条目树都不失效。
pub fn lombok_config(db: &dyn Db, dir: SmolStr) -> &crate::lombok::LombokConfig {
    lombok_config_tracked(db, workspace(db), dir)
}

// salsa 的追踪函数要求第一个参数是 salsa 结构体；键是普通值时借工作区单例占位，
// 多参数的追踪函数会自动把参数驻留。
#[salsa::tracked(returns(ref))]
fn lombok_config_tracked(
    db: &dyn Db,
    _ws: base_db::Workspace,
    dir: SmolStr,
) -> crate::lombok::LombokConfig {
    let files = lombok_config_files(db);
    // 由近及远
    let mut chain: Vec<&(SmolStr, Arc<str>)> = files
        .iter()
        .filter(|(config_dir, _)| base_db::dir_is_within(&dir, config_dir))
        .collect();
    chain.sort_by_key(|(config_dir, _)| std::cmp::Reverse(config_dir.len()));
    if let Some(stop) = chain
        .iter()
        .position(|(_, text)| crate::lombok::LombokConfig::stops_bubbling(text))
    {
        chain.truncate(stop + 1);
    }
    let mut config = crate::lombok::LombokConfig::default();
    for (_, text) in chain.iter().rev() {
        config.apply_file(text);
    }
    config
}

/// 文件的签名级摘要。方法体内的编辑不会改变返回值，salsa 因此不会让下游失效。
#[salsa::tracked]
pub fn item_tree(db: &dyn Db, file: SourceFile) -> Arc<ItemTree> {
    item_tree_and_map(db, file).0
}

#[salsa::tracked]
pub fn source_map(db: &dyn Db, file: SourceFile) -> Arc<SourceMap> {
    item_tree_and_map(db, file).1
}

/// 声明的"头部"（修饰符、注解、类型、形参……）：去掉方法体、类体之后的语法子树，位置从 0 开始。
///
/// 别的文件只需要看声明头时（比如注解）应当用它而不是整个文件的语法树：体内的编辑、
/// 让声明挪动位置的编辑都不会改变它，依赖它的查询也就不会失效。
pub fn decl_header(db: &dyn Db, file: SourceFile, decl: DeclIdx) -> Option<syntax::SyntaxNode> {
    decl_header_tracked(db, file, decl).map(syntax::SyntaxNode::new_root)
}

#[salsa::tracked]
fn decl_header_tracked(db: &dyn Db, file: SourceFile, decl: DeclIdx) -> Option<syntax::GreenNode> {
    let root = base_db::parse(db, file).syntax_node();
    let node = source_map(db, file).to_node(decl, &root)?;
    Some(syntax::algo::green_without_children(
        &node,
        &[syntax::SyntaxKind::BLOCK, syntax::SyntaxKind::CLASS_BODY],
    ))
}

/// 工作区源码里所有具名类的索引。
#[derive(Debug, Default, PartialEq, Eq)]
pub struct SourceClassIndex {
    /// 主副本：`(文件, 下标, 文件的角色)`
    classes: FxHashMap<SmolStr, (SourceFile, u32, FileKind)>,
    package_classes: FxHashMap<SmolStr, Vec<Name>>,
    subpackages: FxHashMap<SmolStr, Vec<Name>>,
    packages: FxHashSet<SmolStr>,
    /// 同一个二进制名在别的文件里的重复声明（多个模块里有同名的类），按文件号顺序
    shadowed: FxHashMap<SmolStr, Vec<(SourceFile, u32)>>,
}

impl SourceClassIndex {
    /// 主副本（第一个声明这个二进制名的文件）。
    pub fn get(&self, binary_name: &str) -> Option<(SourceFile, u32)> {
        self.classes
            .get(binary_name)
            .map(|&(file, idx, _)| (file, idx))
    }

    /// 主副本和它所在文件的角色（模块、源码根）。
    pub(crate) fn get_with_kind(&self, binary_name: &str) -> Option<(SourceFile, u32, FileKind)> {
        self.classes.get(binary_name).copied()
    }

    /// 声明了这个二进制名的所有 `(文件, 下标)`：主副本在前，重复的按文件号顺序在后。
    pub fn declarations(&self, binary_name: &str) -> impl Iterator<Item = (SourceFile, u32)> + '_ {
        self.get(binary_name).into_iter().chain(
            self.shadowed
                .get(binary_name)
                .into_iter()
                .flatten()
                .copied(),
        )
    }

    /// 这个二进制名是否在多个文件里都有声明。
    pub fn is_shadowed(&self, binary_name: &str) -> bool {
        self.shadowed.contains_key(binary_name)
    }

    /// 重复声明（不含主副本）：`(二进制名, 文件, 下标)`。
    pub fn iter_shadowed(&self) -> impl Iterator<Item = (&SmolStr, SourceFile, u32)> {
        self.shadowed
            .iter()
            .flat_map(|(name, copies)| copies.iter().map(move |(file, idx)| (name, *file, *idx)))
    }

    /// 主副本：`(二进制名, 文件, 下标)`。
    pub fn iter(&self) -> impl Iterator<Item = (&SmolStr, SourceFile, u32)> {
        self.classes
            .iter()
            .map(|(name, (file, idx, _))| (name, *file, *idx))
    }

    /// 所有声明，包括同名的重复声明：`(二进制名, 文件, 下标)`。
    pub fn iter_all(&self) -> impl Iterator<Item = (&SmolStr, SourceFile, u32)> {
        self.iter().chain(
            self.shadowed.iter().flat_map(|(name, copies)| {
                copies.iter().map(move |(file, idx)| (name, *file, *idx))
            }),
        )
    }

    pub fn len(&self) -> usize {
        self.classes.len()
    }

    /// 工作区源码里出现过的包（含祖先包），斜杠形式。
    pub fn packages(&self) -> impl Iterator<Item = &str> {
        self.packages.iter().map(SmolStr::as_str)
    }

    pub fn is_empty(&self) -> bool {
        self.classes.is_empty()
    }

    fn register_package(&mut self, package: &str) {
        let mut current = package;
        while !current.is_empty() && self.packages.insert(SmolStr::new(current)) {
            let (parent, last) = match current.rfind('/') {
                Some(i) => (&current[..i], &current[i + 1..]),
                None => ("", current),
            };
            self.subpackages
                .entry(SmolStr::new(parent))
                .or_default()
                .push(Name::new(last));
            current = parent;
        }
    }
}

/// 一组工作区源码文件和它们的签名摘要。
#[derive(PartialEq, Eq, Debug)]
pub struct ItemTreeChunk {
    pub files: Vec<(SourceFile, FileKind, Arc<ItemTree>)>,
}

/// 每组的文件数。
const CHUNK_SIZE: usize = 128;

/// 工作区源码文件（按文件号排序）和它们的角色。
#[salsa::tracked]
fn sorted_workspace_files(db: &dyn Db) -> Arc<Vec<(SourceFile, FileKind)>> {
    let files = workspace(db).files(db);
    Arc::new(
        files
            .workspace_files()
            .into_iter()
            .filter_map(|(file_id, file)| Some((file, files.get(file_id)?.kind)))
            .collect(),
    )
}

#[salsa::tracked]
fn item_tree_chunk(db: &dyn Db, _ws: base_db::Workspace, chunk: u32) -> Arc<ItemTreeChunk> {
    let files = sorted_workspace_files(db);
    let start = chunk as usize * CHUNK_SIZE;
    let end = (start + CHUNK_SIZE).min(files.len());
    Arc::new(ItemTreeChunk {
        files: files
            .get(start..end)
            .unwrap_or_default()
            .iter()
            .map(|&(file, kind)| (file, kind, item_tree(db, file)))
            .collect(),
    })
}

/// 全部工作区源码文件的签名摘要，按文件号顺序分组。
///
/// 要看遍整个工作区的查询（类索引、符号索引、模块图）应当通过它来读签名，而不是逐个文件调
/// [`item_tree`]：编辑一个文件之后，只有它所在的那一组需要逐个文件核对，其余各组整组复用。
/// 大工程里每次按键后的第一次查询因此不用把上万个文件的缓存挨个核对一遍。
pub fn workspace_item_trees(db: &dyn Db) -> Vec<Arc<ItemTreeChunk>> {
    let ws = workspace(db);
    let count = sorted_workspace_files(db).len().div_ceil(CHUNK_SIZE);
    (0..count as u32)
        .map(|chunk| item_tree_chunk(db, ws, chunk))
        .collect()
}

/// 一个文件里和类索引、模块图有关的部分：包名、各个类的名字、模块声明。
/// 改方法签名、字段类型、import 都不改变它。
#[derive(PartialEq, Eq, Debug)]
pub(crate) struct FileClassNames {
    pub(crate) package: SmolStr,
    /// `(二进制名, 简单名, 是不是具名的顶层类（不含紧凑源文件的隐式类）)`，顺序同 `ItemTree::classes`
    pub(crate) classes: Vec<(SmolStr, Name, bool)>,
    pub(crate) module: Option<crate::data::ModuleDeclData>,
}

/// 一组工作区源码文件的 [`FileClassNames`]（分组同 [`workspace_item_trees`]）。
#[derive(PartialEq, Eq, Debug)]
pub(crate) struct ClassNamesChunk {
    pub(crate) files: Vec<(SourceFile, FileKind, FileClassNames)>,
}

// 每次编辑所在的组之后都会重新计算（很便宜），但只要类名没变，结果就和上次相等：
// 全局类索引和模块图不必重建
#[salsa::tracked]
fn class_names_chunk(db: &dyn Db, ws: base_db::Workspace, chunk: u32) -> Arc<ClassNamesChunk> {
    let chunk = item_tree_chunk(db, ws, chunk);
    Arc::new(ClassNamesChunk {
        files: chunk
            .files
            .iter()
            .map(|(file, kind, tree)| {
                let classes = tree
                    .classes
                    .iter()
                    .map(|class| {
                        let top_level = class.outer.is_none()
                            && !class.flags.contains(crate::Modifiers::IMPLICIT_CLASS);
                        (class.binary_name.clone(), class.name.clone(), top_level)
                    })
                    .collect();
                let names = FileClassNames {
                    package: tree.package.clone(),
                    classes,
                    module: tree.module.clone(),
                };
                (*file, *kind, names)
            })
            .collect(),
    })
}

/// 全部工作区源码文件的 [`FileClassNames`]，按文件号顺序分组。
pub(crate) fn workspace_class_names(db: &dyn Db) -> Vec<Arc<ClassNamesChunk>> {
    let ws = workspace(db);
    let count = sorted_workspace_files(db).len().div_ceil(CHUNK_SIZE);
    (0..count as u32)
        .map(|chunk| class_names_chunk(db, ws, chunk))
        .collect()
}

#[salsa::tracked]
pub fn source_class_index(db: &dyn Db) -> Arc<SourceClassIndex> {
    let mut index = SourceClassIndex::default();
    let chunks = workspace_class_names(db);
    let files = chunks.iter().flat_map(|chunk| chunk.files.iter());
    for (file, kind, names) in files {
        let (file, kind) = (*file, *kind);
        index.register_package(&names.package);
        for (idx, (binary_name, name, top_level)) in names.classes.iter().enumerate() {
            if index.classes.contains_key(binary_name) {
                index
                    .shadowed
                    .entry(binary_name.clone())
                    .or_default()
                    .push((file, idx as u32));
                continue;
            }
            index
                .classes
                .insert(binary_name.clone(), (file, idx as u32, kind));
            if *top_level {
                index
                    .package_classes
                    .entry(names.package.clone())
                    .or_default()
                    .push(name.clone());
            }
        }
    }
    for names in index.package_classes.values_mut() {
        names.sort_unstable();
    }
    for names in index.subpackages.values_mut() {
        names.sort_unstable();
        names.dedup();
    }
    Arc::new(index)
}

/// 按二进制名查找类的主副本；不存在返回 `None`。
///
/// 这是不看上下文的全局查找（源码优先，然后按类路径顺序），适合 JDK 里的知名类。
/// 从某个文件出发解析名字时用 [`crate::lookup_class_from`]，它会选这个文件看得到的那一份。
pub fn lookup_class(db: &dyn Db, binary_name: &str) -> Option<ClassId> {
    if source_class_index(db).classes.contains_key(binary_name)
        || workspace(db).class_path(db).contains(binary_name)
        || library_source_index(db).get(binary_name).is_some()
    {
        Some(ClassId::from_binary_name(db, binary_name))
    } else {
        None
    }
}

/// 这个二进制名是否有多份声明（多个源码文件、源码和类路径、多个类路径容器）。
pub fn has_copies(db: &dyn Db, binary_name: &str) -> bool {
    let index = source_class_index(db);
    let class_path = workspace(db).class_path(db);
    if index.classes.contains_key(binary_name) {
        index.is_shadowed(binary_name) || class_path.contains(binary_name)
    } else {
        class_path.is_shadowed(binary_name)
    }
}

/// 一个二进制名的所有副本 `(id, 来源)`，按全局顺序：源码（文件号顺序）在前，类路径（容器顺序）在后。
/// 第一个是主副本。
pub fn class_copies(db: &dyn Db, binary_name: &str) -> Vec<(ClassId, ClassOrigin)> {
    let index = source_class_index(db);
    let class_path = workspace(db).class_path(db);
    let mut res = Vec::new();
    for (file, idx) in index.declarations(binary_name) {
        let id = if res.is_empty() {
            ClassId::from_binary_name(db, binary_name)
        } else {
            ClassId::copy(db, binary_name, CopyOrigin::Source(file.file_id(db).0))
        };
        res.push((id, ClassOrigin::Source { file, idx }));
    }
    for container in class_path.containers_of(binary_name) {
        let id = if res.is_empty() {
            ClassId::from_binary_name(db, binary_name)
        } else {
            ClassId::copy(db, binary_name, CopyOrigin::Container(container))
        };
        res.push((id, ClassOrigin::Binary { container }));
    }
    res
}

/// 某个来源里的这个二进制名的 id（主副本或带来源的副本）。这个来源里没有它时返回 `None`。
pub fn class_in_origin(db: &dyn Db, binary_name: &str, origin: ClassOrigin) -> Option<ClassId> {
    let index = source_class_index(db);
    match origin {
        ClassOrigin::Source { file, .. } => {
            let (primary, _) = index.get(binary_name)?;
            if primary == file {
                return Some(ClassId::from_binary_name(db, binary_name));
            }
            index
                .shadowed
                .get(binary_name)?
                .iter()
                .any(|(f, _)| *f == file)
                .then(|| ClassId::copy(db, binary_name, CopyOrigin::Source(file.file_id(db).0)))
        }
        ClassOrigin::Binary { container } => {
            let class_path = workspace(db).class_path(db);
            let mut containers = class_path.containers_of(binary_name);
            let first = containers.next()?;
            if first == container && !index.classes.contains_key(binary_name) {
                return Some(ClassId::from_binary_name(db, binary_name));
            }
            (first == container || containers.any(|c| c == container))
                .then(|| ClassId::copy(db, binary_name, CopyOrigin::Container(container)))
        }
    }
}

/// 源码文件 `file` 里声明的类 `binary_name` 的 id。
/// 文件不在工作区类索引里（打开的库源码文件）时是类路径上的那一份（没有时是主副本）。
pub fn class_in_file(db: &dyn Db, file: SourceFile, binary_name: &str) -> ClassId {
    let index = source_class_index(db);
    let primary = || ClassId::from_binary_name(db, binary_name);
    match index.get(binary_name) {
        Some((first, _)) if first != file => {
            let declared = index
                .is_shadowed(binary_name)
                .then(|| class_in_origin(db, binary_name, ClassOrigin::Source { file, idx: 0 }))
                .flatten();
            declared
                .or_else(|| binary_class(db, binary_name))
                .unwrap_or_else(primary)
        }
        _ => primary(),
    }
}

/// 类路径上（按容器顺序第一个）的这个类：库里的类的签名桩、打开的库源码文件对应的是这一份，
/// 即使工作区源码里也有同名的类。
pub fn binary_class(db: &dyn Db, binary_name: &str) -> Option<ClassId> {
    let container = workspace(db)
        .class_path(db)
        .containers_of(binary_name)
        .next()?;
    class_in_origin(db, binary_name, ClassOrigin::Binary { container })
}

/// 和 `of` 同一来源（同一个源码文件或同一个 jar）里的类 `binary_name`：成员类型、外层类都跟着
/// 所在的那一份走。
///
/// 不能按 `is_copy()` 走全局查找：主副本指的是"这个名字全局取哪一份"，和"这个类声明在哪个
/// 文件里"不是一回事。同名的类有多份而 `of` 是主副本时，`of` 的外层类完全可能只声明在
/// 别的副本里（另一个文件里的 `Dup` 没有 `Dup$Inner`，于是 `Inner` 只能来自那一份），
/// 这时按名字全局查会查到一个没有该外层类的副本，外层类的成员就全都解析失败。
pub fn sibling_class(db: &dyn Db, of: ClassId, binary_name: &str) -> Option<ClassId> {
    match class_origin(db, of)? {
        origin @ ClassOrigin::Source { .. } => class_in_origin(db, binary_name, origin),
        origin @ ClassOrigin::Binary { .. } => {
            class_in_origin(db, binary_name, origin).or_else(|| lookup_class(db, binary_name))
        }
    }
}

/// `class` 自己声明的成员类型 `name`（不看继承来的）。
pub fn nested_class(db: &dyn Db, class: ClassId, name: &str) -> Option<ClassId> {
    sibling_class(db, class, &format!("{}${name}", class.binary_name(db)))
}

/// 直接外层的类。
pub fn outer_class(db: &dyn Db, class: ClassId) -> Option<ClassId> {
    let data = crate::signatures::class_header(db, class)?;
    sibling_class(db, class, data.outer.as_deref()?)
}

/// 最外层的类（顶层类自己）。按二进制名截取，不读签名。
pub fn outermost_class(db: &dyn Db, class: ClassId) -> ClassId {
    let name = class.binary_name(db);
    match name.split_once('$') {
        // 外层类没有同名副本时，主副本的外层类也是主副本：不必查索引（访问性检查的热路径上）
        Some((outer, _)) if !class.is_copy() && !has_copies(db, outer) => {
            ClassId::from_binary_name(db, outer)
        }
        Some((outer, _)) => sibling_class(db, class, outer).unwrap_or(class),
        None => class,
    }
}

/// 按 [`ClassId::key`] 找回类；类已经不存在时返回 `None`。
pub fn class_by_key(db: &dyn Db, key: &str) -> Option<ClassId> {
    let id = ClassId::from_key(db, key);
    if id.is_copy() {
        class_origin(db, id).map(|_| id)
    } else {
        lookup_class(db, key)
    }
}

pub fn class_origin(db: &dyn Db, id: ClassId) -> Option<ClassOrigin> {
    if let Some(origin) = id.copy_origin(db) {
        let name = id.binary_name(db);
        return match origin {
            CopyOrigin::Source(file_id) => source_class_index(db)
                .shadowed
                .get(&name)?
                .iter()
                .find(|(file, _)| file.file_id(db).0 == file_id)
                .map(|&(file, idx)| ClassOrigin::Source { file, idx }),
            CopyOrigin::Container(container) => workspace(db)
                .class_path(db)
                .containers_of(&name)
                .any(|c| c == container)
                .then_some(ClassOrigin::Binary { container }),
        };
    }
    let name = id.binary_name(db);
    if let Some((file, idx)) = source_class_index(db).get(&name) {
        return Some(ClassOrigin::Source { file, idx });
    }
    if let Some(container) = workspace(db).class_path(db).containers_of(&name).next() {
        return Some(ClassOrigin::Binary { container });
    }
    // 只出现在打开的库源码文件里的类（私有嵌套类等）
    let (file, idx) = open_library_source(db, id)?;
    Some(ClassOrigin::Source { file, idx })
}

/// 类的声明所在的文件：工作区源码，或者（依赖库的类）打开的库源码文件。
/// `ClassData` 里的 `decl` 都是这个文件的 `SourceMap` 下标。
pub fn class_decl_file(db: &dyn Db, id: ClassId) -> Option<SourceFile> {
    match class_origin(db, id)? {
        ClassOrigin::Source { file, .. } => Some(file),
        ClassOrigin::Binary { .. } => open_library_source(db, id).map(|(file, _)| file),
    }
}

/// 类所在的源码文件（二进制类返回 `None`）。
pub fn class_source_file(db: &dyn Db, id: ClassId) -> Option<SourceFile> {
    match class_origin(db, id)? {
        ClassOrigin::Source { file, .. } => Some(file),
        ClassOrigin::Binary { .. } => None,
    }
}

/// 类的签名。源码类取自 `ItemTree`，二进制类按需读取 class 文件。
pub fn class_data(db: &dyn Db, id: ClassId) -> Option<Arc<ClassData>> {
    class_data_tracked(db, base_db::workspace(db), id)
}

// salsa 的追踪函数要求第一个参数是 salsa 结构体；键是普通值时借工作区单例占位，
// 多参数的追踪函数会自动把参数驻留。
#[salsa::tracked]
fn class_data_tracked(db: &dyn Db, _ws: base_db::Workspace, id: ClassId) -> Option<Arc<ClassData>> {
    match class_origin(db, id)? {
        ClassOrigin::Source { file, idx } => {
            let data = item_tree(db, file).classes.get(idx as usize).cloned()?;
            let is_library = workspace(db)
                .files(db)
                .get(file.file_id(db))
                .is_some_and(|entry| matches!(entry.kind, base_db::FileKind::Library));
            if is_library {
                Some(Arc::new(library_only_class(&data)))
            } else if crate::lombok_expand::needs_expansion(&data) {
                let mut data = (*data).clone();
                crate::lombok_expand::expand(db, id, &mut data);
                Some(Arc::new(data))
            } else {
                Some(data)
            }
        }
        ClassOrigin::Binary { container } => {
            let name = id.binary_name(db);
            let class_file = workspace(db).class_path(db).load_from(container, &name)?;
            let mut data = lower_class_file(&class_file);
            if let Some((file, idx)) = open_library_source(db, id) {
                if let Some(source) = item_tree(db, file).classes.get(idx as usize) {
                    merge_library_source(&mut data, source);
                }
            }
            Some(Arc::new(data))
        }
    }
}

pub fn package_exists(db: &dyn Db, package: &str) -> bool {
    source_class_index(db).packages.contains(package)
        || workspace(db).class_path(db).has_package(package)
}

/// 包下的顶层类简单名（源码与二进制合并、去重、排序）。
pub fn package_classes(db: &dyn Db, package: &str) -> Vec<Name> {
    let index = source_class_index(db);
    let mut res: Vec<Name> = index
        .package_classes
        .get(package)
        .cloned()
        .unwrap_or_default();
    res.extend(
        workspace(db)
            .class_path(db)
            .package_classes(package)
            .iter()
            .cloned(),
    );
    res.sort_unstable();
    res.dedup();
    res
}

/// 直接子包的最后一段名字；`""` 表示根。
pub fn subpackages(db: &dyn Db, package: &str) -> Vec<Name> {
    let index = source_class_index(db);
    let mut res: Vec<Name> = index.subpackages.get(package).cloned().unwrap_or_default();
    res.extend(
        workspace(db)
            .class_path(db)
            .subpackages(package)
            .iter()
            .cloned(),
    );
    res.sort_unstable();
    res.dedup();
    res
}

// ---------------------------------------------------------------------------
// 父类型
// ---------------------------------------------------------------------------

thread_local! {
    /// 正在解析父类型的类。只用于在非法的循环继承上截断递归，避免 salsa 报循环。
    static RESOLVING_SUPERS: RefCell<Vec<ClassId>> = const { RefCell::new(Vec::new()) };
}

fn direct_supers_query(db: &dyn Db, id: ClassId) -> Arc<Vec<ClassId>> {
    direct_supers_query_tracked(db, base_db::workspace(db), id)
}

// salsa 的追踪函数要求第一个参数是 salsa 结构体；键是普通值时借工作区单例占位，
// 多参数的追踪函数会自动把参数驻留。
#[salsa::tracked]
fn direct_supers_query_tracked(
    db: &dyn Db,
    _ws: base_db::Workspace,
    id: ClassId,
) -> Arc<Vec<ClassId>> {
    let Some(data) = class_data(db, id) else {
        return Arc::default();
    };
    let scope = TypeScope::class_header(db, id);
    let mut res = Vec::new();
    for ty in data.superclass.iter().chain(data.interfaces.iter()) {
        if let Some(class) = resolve_type_ref_to_class(db, &scope, ty) {
            if class != id && !res.contains(&class) {
                res.push(class);
            }
        }
    }
    Arc::new(res)
}

/// 直接父类型（父类在前，接口在后），已擦除类型实参。
pub fn direct_supers(db: &dyn Db, id: ClassId) -> Arc<Vec<ClassId>> {
    let cyclic = RESOLVING_SUPERS.with(|stack| stack.borrow().contains(&id));
    if cyclic {
        return Arc::default();
    }
    RESOLVING_SUPERS.with(|stack| stack.borrow_mut().push(id));
    let res = direct_supers_query(db, id);
    RESOLVING_SUPERS.with(|stack| {
        stack.borrow_mut().pop();
    });
    res
}

/// 所有祖先类型（不含自身），广度优先；`java.lang.Object` 总在其中（如果存在）。
pub fn all_supers(db: &dyn Db, id: ClassId) -> Vec<ClassId> {
    let mut res: Vec<ClassId> = Vec::new();
    let mut seen: FxHashSet<ClassId> = FxHashSet::default();
    seen.insert(id);
    let mut queue = std::collections::VecDeque::new();
    queue.push_back(id);
    while let Some(current) = queue.pop_front() {
        for sup in direct_supers(db, current).iter() {
            if seen.insert(*sup) {
                res.push(*sup);
                queue.push_back(*sup);
            }
        }
    }
    // 接口没有父类，但 Object 的成员对它同样可用
    if let Some(object) = lookup_class(db, "java/lang/Object") {
        if object != id && seen.insert(object) {
            res.push(object);
        }
    }
    res
}

/// 工作区源码类的"直接子类型"表：父类型 → 直接继承它的源码类。编辑方法体不会让它重算。
#[salsa::tracked]
pub fn source_direct_subtypes(db: &dyn Db) -> Arc<FxHashMap<ClassId, Vec<ClassId>>> {
    let mut map: FxHashMap<ClassId, Vec<ClassId>> = FxHashMap::default();
    let index = source_class_index(db);
    let mut names: Vec<&SmolStr> = index.iter().map(|(name, _, _)| name).collect();
    names.sort();
    let decls = names
        .into_iter()
        .flat_map(|name| index.declarations(name).map(move |(file, _)| (name, file)));
    for (binary, file) in decls {
        let class = class_in_file(db, file, binary);
        for sup in direct_supers(db, class).iter() {
            map.entry(*sup).or_default().push(class);
        }
    }
    Arc::new(map)
}

/// 工作区源码里 `class` 的所有（直接和间接）子类型，不含自身。
pub fn source_subclasses(db: &dyn Db, class: ClassId) -> Vec<ClassId> {
    let map = source_direct_subtypes(db);
    let mut res: Vec<ClassId> = Vec::new();
    let mut seen: FxHashSet<ClassId> = FxHashSet::default();
    seen.insert(class);
    let mut queue = vec![class];
    while let Some(current) = queue.pop() {
        for sub in map.get(&current).into_iter().flatten() {
            if seen.insert(*sub) {
                res.push(*sub);
                queue.push(*sub);
            }
        }
    }
    res
}

/// `sub` 是否等于 `sup` 或是它的子类型（按擦除后的类判断）。
/// `sealed` 类型允许的直接子类型。没写 `permits` 时是同一个编译单元里直接继承它的类型。
/// 不是 sealed、或者有解析不了的子类型时返回 `None`。
pub fn permitted_subclasses(db: &dyn Db, id: ClassId) -> Option<Vec<ClassId>> {
    let data = class_data(db, id)?;
    if !data.permits.is_empty() {
        let scope = TypeScope::class_header(db, id);
        return data
            .permits
            .iter()
            .map(|ty| resolve_type_ref_to_class(db, &scope, ty))
            .collect();
    }
    if !data.flags.contains(crate::data::Modifiers::SEALED) {
        return None;
    }
    let file = class_source_file(db, id)?;
    let tree = item_tree(db, file);
    Some(
        tree.classes
            .iter()
            .map(|class| class_in_file(db, file, &class.binary_name))
            .filter(|class| *class != id && direct_supers(db, *class).contains(&id))
            .collect(),
    )
}

pub fn is_subclass_of(db: &dyn Db, sub: ClassId, sup: ClassId) -> bool {
    sub == sup || all_supers(db, sub).contains(&sup)
}
