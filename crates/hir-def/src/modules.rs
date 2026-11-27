//! 模块图：类路径上的模块（JDK 的各个模块、模块化 jar、自动模块）和工作区里的 `module-info.java`。
//!
//! 用于 `import module M;`（JEP 511）的解析，以及 `module-info.java` 里的诊断和补全。

use std::sync::Arc;

use base_db::{workspace, Db, SourceFile};
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use crate::ClassId;

/// 一个模块。包名是斜杠形式。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleInfo {
    pub name: SmolStr,
    pub requires: Vec<(SmolStr, bool)>,
    /// `(包, 限定导出的目标模块)`；目标为空表示对所有模块导出
    pub exports: Vec<(SmolStr, Vec<SmolStr>)>,
    pub opens: Vec<(SmolStr, Vec<SmolStr>)>,
    /// 声明在工作区的哪个 `module-info.java` 里
    pub source: Option<SourceFile>,
    /// 没有模块描述的普通 jar 对应的自动模块（名字由文件名或清单推出来）
    pub automatic: bool,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct ModuleGraph {
    modules: FxHashMap<SmolStr, ModuleInfo>,
}

impl ModuleGraph {
    pub fn is_empty(&self) -> bool {
        self.modules.is_empty()
    }

    pub fn get(&self, name: &str) -> Option<&ModuleInfo> {
        self.modules.get(name)
    }

    pub fn iter(&self) -> impl Iterator<Item = &ModuleInfo> {
        self.modules.values()
    }

    /// 所有模块名（已排序）。
    pub fn names(&self) -> Vec<SmolStr> {
        let mut names: Vec<SmolStr> = self.modules.keys().cloned().collect();
        names.sort();
        names
    }

    /// `import module name;` 带进来的包：`name` 无条件导出的包，以及它经由 `requires transitive`
    /// （递归地）带来的模块无条件导出的包。模块不存在时返回 `None`。
    pub fn imported_packages(&self, name: &str) -> Option<Vec<SmolStr>> {
        self.modules.get(name)?;
        let mut seen: FxHashSet<&str> = FxHashSet::default();
        let mut stack = vec![name];
        let mut packages: Vec<SmolStr> = Vec::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            let Some(module) = self.modules.get(current) else {
                continue;
            };
            for (package, targets) in &module.exports {
                if targets.is_empty() && !packages.contains(package) {
                    packages.push(package.clone());
                }
            }
            for (required, transitive) in &module.requires {
                if *transitive {
                    stack.push(required);
                }
            }
        }
        Some(packages)
    }
}

pub fn module_graph(db: &dyn Db) -> Arc<ModuleGraph> {
    module_graph_tracked(db, workspace(db))
}

#[salsa::tracked]
fn module_graph_tracked(db: &dyn Db, _ws: base_db::Workspace) -> Arc<ModuleGraph> {
    let mut graph = ModuleGraph::default();
    // 工作区里的模块声明优先
    let chunks = crate::index::workspace_class_names(db);
    for (file, _, names) in chunks.iter().flat_map(|chunk| chunk.files.iter()) {
        let file = *file;
        let Some(module) = &names.module else {
            continue;
        };
        graph
            .modules
            .entry(module.name.clone())
            .or_insert_with(|| ModuleInfo {
                name: module.name.clone(),
                requires: module.requires.clone(),
                exports: module.exports.clone(),
                opens: module.opens.clone(),
                source: Some(file),
                automatic: false,
            });
    }
    for module in workspace(db).class_path(db).modules() {
        let name = SmolStr::new(&module.name);
        graph
            .modules
            .entry(name.clone())
            .or_insert_with(|| ModuleInfo {
                name,
                requires: module
                    .requires
                    .iter()
                    .map(|(name, transitive)| (SmolStr::new(name), *transitive))
                    .collect(),
                exports: module
                    .exports
                    .iter()
                    .map(|(package, targets)| {
                        (
                            SmolStr::new(package),
                            targets.iter().map(SmolStr::new).collect(),
                        )
                    })
                    .collect(),
                opens: module
                    .opens
                    .iter()
                    .map(|(package, targets)| {
                        (
                            SmolStr::new(package),
                            targets.iter().map(SmolStr::new).collect(),
                        )
                    })
                    .collect(),
                source: None,
                automatic: module.automatic,
            });
    }
    Arc::new(graph)
}

/// 文件里的模块导入（显式的 `import module M;`）。
pub fn module_imports(db: &dyn Db, file: SourceFile) -> Vec<SmolStr> {
    crate::signatures::file_scope(db, file)
        .module_imports()
        .to_vec()
}

/// 经由文件里的模块导入能看到的、简单名为 `name` 的公开顶层类（去重）。
/// 多于一个时这个名字有歧义。
pub fn module_import_candidates(db: &dyn Db, file: SourceFile, name: &str) -> Vec<ClassId> {
    let scope = crate::signatures::file_scope(db, file);
    if scope.module_imports().is_empty() {
        return Vec::new();
    }
    let graph = module_graph(db);
    let mut res: Vec<ClassId> = Vec::new();
    for module in scope.module_imports() {
        let Some(packages) = graph.imported_packages(module) else {
            continue;
        };
        for package in packages {
            let Some(class) =
                crate::lookup_class_from(db, Some(file), &format!("{package}/{name}"))
            else {
                continue;
            };
            let public = crate::class_header(db, class)
                .is_some_and(|data| data.flags.visibility() == crate::Visibility::Public);
            if public && !res.contains(&class) {
                res.push(class);
            }
        }
    }
    res
}
