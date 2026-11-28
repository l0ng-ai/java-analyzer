//! 工程模型的导入：把 Maven / Gradle / 手动配置统一成 `base_db::ProjectGraph`。

mod eclipse;
mod gradle;
mod jdk;
mod maven;
mod maven_settings;
mod runtime;
mod sources;
mod xml;

use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use base_db::{
    Dependency, DependencyTarget, LibraryData, LibraryId, ModuleData, ProjectGraph, Scope,
    SourceRoot, SourceRootKind,
};
use classfile::{ClassContainer, ClassPath, JarContainer};
use serde::Deserialize;

pub use crate::{
    gradle::cache_file as gradle_cache_file,
    jdk::{discover_jdk, jdk_containers, parse_feature_version, select_jdk},
    maven_settings::{set_client_setup as set_maven_setup, MavenSetup},
    runtime::{runtime_class_path, RuntimeClassPath},
    sources::{coordinates_of, download_sources, maven_repository, sources_path, Coordinates},
};

pub const CONFIG_FILE_NAME: &str = "java-analyzer.toml";

/// 工作区根目录下 `java-analyzer.toml` 的内容。
///
/// ```toml
/// [jdk]
/// home = "/path/to/jdk"
///
/// # Maven 的设置文件（相当于 `mvn -s`）和本地仓库；相对路径相对工作区根目录
/// [maven]
/// settings = "/opt/maven/conf/settings.xml"
/// local_repository = "/data/m2/repository"
///
/// [[module]]
/// name = "app"
/// root = "."
/// sources = ["src/main/java"]
/// test_sources = ["src/test/java"]
/// classpath = ["lib/*.jar", "/abs/path/dep.jar"]
/// # 编译输出目录（调试时拼运行时类路径用）；不写时按 target/classes、build/classes/java/main、bin 等约定找
/// output = "out/classes"
/// test_output = "out/test-classes"
/// language_level = 17
/// preview = false
/// # 依赖的其他模块（按名字）；不写时能看到所有其他模块
/// dependencies = ["core"]
/// ```
#[derive(Deserialize, Debug, Default, Clone)]
#[serde(default)]
pub struct ManualConfig {
    pub jdk: Option<JdkConfig>,
    pub maven: Option<MavenSetup>,
    #[serde(rename = "module")]
    pub modules: Vec<ManualModule>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct JdkConfig {
    pub home: PathBuf,
}

#[derive(Deserialize, Debug, Default, Clone)]
#[serde(default)]
pub struct ManualModule {
    pub name: Option<String>,
    pub root: Option<PathBuf>,
    pub sources: Vec<PathBuf>,
    pub test_sources: Vec<PathBuf>,
    pub classpath: Vec<String>,
    /// 主代码的编译输出目录
    pub output: Option<PathBuf>,
    /// 测试代码的编译输出目录
    pub test_output: Option<PathBuf>,
    pub language_level: Option<u32>,
    /// 开启预览特性（相当于 `javac --enable-preview`）
    pub preview: bool,
    /// 依赖的其他模块的名字（传递）。`None`（没写）表示依赖所有其他模块
    pub dependencies: Option<Vec<String>>,
}

/// 来自编辑器配置的导入选项。
#[derive(Debug, Clone)]
pub struct LoadOptions {
    pub jdk_home: Option<PathBuf>,
    /// 本地仓库缺件时是否调用 `mvn` 兜底
    pub maven_use_cli: bool,
    /// 是否允许调用 Gradle（关闭后只使用缓存的导入结果）
    pub gradle_allow_run: bool,
}

impl Default for LoadOptions {
    fn default() -> Self {
        LoadOptions {
            jdk_home: None,
            maven_use_cli: true,
            gradle_allow_run: true,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProjectKind {
    Manual,
    Maven,
    Gradle,
    /// 没有识别出构建系统，按目录约定猜的源码根
    Plain,
}

#[derive(Debug)]
pub struct LoadedProject {
    pub kind: ProjectKind,
    pub graph: ProjectGraph,
    /// 导入过程中需要告诉用户的问题（缺失的依赖、失败的命令 …）
    pub messages: Vec<String>,
    /// 这些文件变化后需要重新导入
    pub build_files: Vec<PathBuf>,
    /// 解析不到的依赖构件，合并多个工作区根时用来链接另一个根里的模块
    unresolved: Vec<UnresolvedDep>,
    /// 导入器报告的模块坐标（Gradle 的 `group` 和 `name`）；Maven 模块的坐标合并时从 pom 读
    coordinates: Vec<(base_db::ModuleId, String, String)>,
    /// 没有显式配置 JDK 时工程要求的 JDK 版本（见 [`requested_jdk_version`]）；显式配置了时为 `None`
    requested_jdk: Option<u32>,
}

/// 没有显式配置 JDK 时按什么版本挑：Maven toolchain 写了版本就用它，否则取各模块语言级别
/// （含测试代码的）里最高的。取最高的是因为低于某个模块语言级别的 JDK 编译不了、也运行不了
/// 它的类，而高版本的 JDK 可以按低语言级别编译和运行。
fn requested_jdk_version(graph: &ProjectGraph, toolchain: Option<u32>) -> Option<u32> {
    toolchain.or_else(|| {
        graph
            .modules
            .iter()
            .flat_map(|m| [m.language_level, m.test_language_level])
            .flatten()
            .max()
    })
}

/// JDK 版本低于某个模块的语言级别时记一条警告：这样的模块编译不了，运行时也加载不了它的类。
fn warn_if_jdk_too_old(graph: &ProjectGraph) {
    let Some(jdk) = &graph.jdk else {
        return;
    };
    for module in &graph.modules {
        let level = module.language_level.max(module.test_language_level);
        if let Some(level) = level.filter(|level| *level > jdk.version) {
            tracing::warn!(
                "模块 {} 的语言级别是 {level}，但 JDK 是 {}（{}）；请安装合适的 JDK，或者在 java-analyzer.toml 的 [jdk] home 里指定",
                module.name,
                jdk.version,
                jdk.home.display()
            );
        }
    }
}

/// 解析不到的依赖（Maven 本地仓库里没有的构件、Gradle 解析失败的依赖）：
/// 哪个模块、什么坐标、什么 scope。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnresolvedDep {
    pub module: base_db::ModuleId,
    pub group: String,
    pub artifact: String,
    pub scope: Scope,
}

/// 让 `modules` 里列出的模块继承它们所依赖的模块的依赖（scope 按 Maven 的传递规则合成），
/// 一直到不再变化。用在导入器没有展开传递依赖的地方：手动配置的模块依赖、Eclipse 插件之间的依赖、
/// 跨工作区根的模块链接。
pub(crate) fn inherit_module_dependencies(all: &mut [ModuleData], modules: &[base_db::ModuleId]) {
    for _ in 0..=all.len() {
        let mut changed = false;
        for &id in modules {
            let idx = id.0 as usize;
            let Some(module) = all.get(idx) else { continue };
            let mut inherited: Vec<Dependency> = Vec::new();
            for dep in &module.dependencies {
                let DependencyTarget::Module(target) = dep.target else {
                    continue;
                };
                let Some(target_module) = all.get(target.0 as usize) else {
                    continue;
                };
                if target == id {
                    continue;
                }
                for child in &target_module.dependencies {
                    let Some(scope) = maven::combine_scope(dep.scope, child.scope) else {
                        continue;
                    };
                    let is_self = matches!(child.target,
                        DependencyTarget::Module(m) | DependencyTarget::ModuleTests(m) if m == id);
                    if !is_self {
                        inherited.push(Dependency {
                            target: child.target,
                            scope,
                        });
                    }
                }
            }
            let module = &mut all[idx];
            for dep in inherited {
                match module
                    .dependencies
                    .iter_mut()
                    .find(|d| d.target == dep.target)
                {
                    Some(existing) => {
                        if maven::scope_rank(dep.scope) > maven::scope_rank(existing.scope) {
                            existing.scope = dep.scope;
                            changed = true;
                        }
                    }
                    None => {
                        module.dependencies.push(dep);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
}

fn absolutize(base: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    }
}

/// 展开 classpath 条目：jar 文件、目录（取其中的 jar）、`dir/*` 或 `dir/*.jar`。
fn expand_classpath_entry(base: &Path, entry: &str) -> Vec<PathBuf> {
    let (dir, wildcard) = match entry
        .strip_suffix("/*.jar")
        .or_else(|| entry.strip_suffix("/*"))
    {
        Some(dir) => (absolutize(base, Path::new(dir)), true),
        None => (absolutize(base, Path::new(entry)), false),
    };
    if wildcard || dir.is_dir() {
        let mut jars: Vec<PathBuf> = std::fs::read_dir(&dir)
            .map(|entries| {
                entries
                    .flatten()
                    .map(|e| e.path())
                    .filter(|p| p.extension().is_some_and(|ext| ext == "jar"))
                    .collect()
            })
            .unwrap_or_default();
        jars.sort();
        jars
    } else if dir.is_file() {
        vec![dir]
    } else {
        Vec::new()
    }
}

fn read_manual_config(root: &Path, messages: &mut Vec<String>) -> ManualConfig {
    let path = root.join(CONFIG_FILE_NAME);
    let Ok(content) = std::fs::read_to_string(&path) else {
        return ManualConfig::default();
    };
    match toml::from_str(&content) {
        Ok(config) => config,
        Err(err) => {
            messages.push(base_db::tr!(
                "{} 解析失败: {err}",
                "Failed to parse {}: {err}",
                path.display()
            ));
            ManualConfig::default()
        }
    }
}

fn manual_graph(root: &Path, config: &ManualConfig, messages: &mut Vec<String>) -> ProjectGraph {
    let mut graph = ProjectGraph::default();
    for (idx, module) in config.modules.iter().enumerate() {
        let module_root = absolutize(root, module.root.as_deref().unwrap_or(Path::new(".")));
        let mut source_roots = Vec::new();
        for (dirs, kind) in [
            (&module.sources, SourceRootKind::Main),
            (&module.test_sources, SourceRootKind::Test),
        ] {
            for dir in dirs {
                let path = absolutize(&module_root, dir);
                if path.is_dir() {
                    source_roots.push(SourceRoot { path, kind });
                } else {
                    messages.push(base_db::tr!(
                        "源码目录不存在: {}",
                        "Source directory does not exist: {}",
                        path.display()
                    ));
                }
            }
        }
        let mut dependencies = Vec::new();
        for entry in &module.classpath {
            let jars = expand_classpath_entry(&module_root, entry);
            if jars.is_empty() {
                messages.push(base_db::tr!(
                    "classpath 条目没有匹配到任何 jar: {entry}",
                    "Classpath entry matches no jar: {entry}"
                ));
            }
            for jar in jars {
                let id = match graph.libraries.iter().position(|lib| lib.jar == jar) {
                    Some(i) => LibraryId(i as u32),
                    None => {
                        let name = jar
                            .file_name()
                            .map(|n| n.to_string_lossy().into_owned())
                            .unwrap_or_default();
                        let sources = jar
                            .to_str()
                            .and_then(|s| s.strip_suffix(".jar"))
                            .map(|stem| PathBuf::from(format!("{stem}-sources.jar")))
                            .filter(|p| p.is_file());
                        graph.libraries.push(LibraryData { name, jar, sources });
                        LibraryId((graph.libraries.len() - 1) as u32)
                    }
                };
                dependencies.push(Dependency {
                    target: DependencyTarget::Library(id),
                    scope: Scope::Compile,
                });
            }
        }
        let output_dirs = if module.output.is_some() || module.test_output.is_some() {
            [
                (&module.output, SourceRootKind::Main),
                (&module.test_output, SourceRootKind::Test),
            ]
            .into_iter()
            .filter_map(|(dir, kind)| {
                dir.as_ref().map(|dir| SourceRoot {
                    path: absolutize(&module_root, dir),
                    kind,
                })
            })
            .collect()
        } else {
            conventional_output_dirs(&module_root)
        };
        graph.modules.push(ModuleData {
            name: module
                .name
                .clone()
                .unwrap_or_else(|| format!("module{idx}")),
            root: module_root,
            source_roots,
            language_level: module.language_level,
            api_release: module.language_level,
            test_language_level: None,
            preview: module.preview,
            dependencies,
            output_dirs,
            encoding: None,
            transitive_dependencies: false,
        });
    }
    // 模块之间的依赖：没写 `dependencies` 的模块能看到所有其他模块
    let ids: Vec<base_db::ModuleId> = (0..graph.modules.len())
        .map(|i| base_db::ModuleId(i as u32))
        .collect();
    for (idx, module) in config.modules.iter().enumerate() {
        let targets: Vec<base_db::ModuleId> = match &module.dependencies {
            None => ids
                .iter()
                .copied()
                .filter(|id| id.0 as usize != idx)
                .collect(),
            Some(names) => names
                .iter()
                .filter_map(|name| {
                    let found = graph.modules.iter().position(|m| &m.name == name);
                    if found.is_none() {
                        messages.push(base_db::tr!(
                            "模块 {} 依赖的模块 {name} 不存在",
                            "Module {} depends on unknown module {name}",
                            graph.modules[idx].name
                        ));
                    }
                    found.map(|i| base_db::ModuleId(i as u32))
                })
                .filter(|id| id.0 as usize != idx)
                .collect(),
        };
        for target in targets {
            graph.modules[idx].dependencies.push(Dependency {
                target: DependencyTarget::Module(target),
                scope: Scope::Compile,
            });
        }
    }
    inherit_module_dependencies(&mut graph.modules, &ids);
    graph
}

/// 没有构建系统给出输出目录时，按常见约定找已经存在的编译输出目录。
pub(crate) fn conventional_output_dirs(root: &Path) -> Vec<SourceRoot> {
    let candidates = [
        ("target/classes", SourceRootKind::Main),
        ("target/test-classes", SourceRootKind::Test),
        ("build/classes/java/main", SourceRootKind::Main),
        ("build/classes/java/test", SourceRootKind::Test),
        ("out/production/classes", SourceRootKind::Main),
        ("out/test/classes", SourceRootKind::Test),
        ("bin", SourceRootKind::Main),
        ("classes", SourceRootKind::Main),
        ("out", SourceRootKind::Main),
    ];
    let mut dirs: Vec<SourceRoot> = candidates
        .iter()
        .map(|(dir, kind)| SourceRoot {
            path: root.join(dir),
            kind: *kind,
        })
        .filter(|dir| dir.path.is_dir())
        .collect();
    // `out` 只在没有更具体的约定目录时才算，而且它下面得直接是类文件或包目录
    if dirs.len() > 1 {
        dirs.retain(|dir| !dir.path.ends_with("out"));
    }
    dirs
}

/// 没有构建文件时按目录约定猜源码根。
fn plain_graph(root: &Path) -> ProjectGraph {
    let conventional = [
        ("src/main/java", SourceRootKind::Main),
        ("src/test/java", SourceRootKind::Test),
    ];
    let mut source_roots: Vec<SourceRoot> = conventional
        .iter()
        .map(|(dir, kind)| SourceRoot {
            path: root.join(dir),
            kind: *kind,
        })
        .filter(|r| r.path.is_dir())
        .collect();
    if source_roots.is_empty() {
        let src = root.join("src");
        let path = if src.is_dir() {
            src
        } else {
            root.to_path_buf()
        };
        source_roots.push(SourceRoot {
            path,
            kind: SourceRootKind::Main,
        });
    }
    ProjectGraph {
        modules: vec![ModuleData {
            name: root
                .file_name()
                .map(|n| n.to_string_lossy().into_owned())
                .unwrap_or_else(|| "root".to_owned()),
            root: root.to_path_buf(),
            source_roots,
            language_level: None,
            api_release: None,
            test_language_level: None,
            preview: false,
            dependencies: Vec::new(),
            output_dirs: conventional_output_dirs(root),
            encoding: None,
            transitive_dependencies: false,
        }],
        libraries: Vec::new(),
        jdk: None,
    }
}

/// `root` 的 `java-analyzer.toml` 里的 `[maven]`，路径换成绝对的。
fn configured_maven_setup(root: &Path) -> Option<MavenSetup> {
    let mut ignored = Vec::new();
    let setup = read_manual_config(root, &mut ignored).maven?;
    let absolute = |path: Option<PathBuf>| {
        path.map(|p| {
            // `${user.home}` 这样的占位符开头的路径留给后面展开
            if p.to_string_lossy().starts_with("${") {
                p
            } else {
                absolutize(root, &p)
            }
        })
    };
    Some(MavenSetup {
        settings: absolute(setup.settings),
        local_repository: absolute(setup.local_repository),
    })
}

/// 和 [`std::fs::canonicalize`] 一样解析出规范的绝对路径，但在 Windows 上不带 `\\?\` 前缀：
/// 带前缀的路径和客户端（URI）、构建工具给出的 `C:\...` 路径比较时对不上，
/// 前缀后面的 `/` 也不再算分隔符，`java` 也不认这种类路径。
pub fn canonicalize(path: &Path) -> std::io::Result<PathBuf> {
    let path = std::fs::canonicalize(path)?;
    Ok(if cfg!(windows) {
        strip_verbatim_prefix(path)
    } else {
        path
    })
}

/// `\\?\C:\dir` → `C:\dir`，`\\?\UNC\server\share` → `\\server\share`。其他形式（卷 GUID 等）和
/// 去掉前缀后超出 `MAX_PATH` 的路径没有等价的普通写法，原样返回。
fn strip_verbatim_prefix(path: PathBuf) -> PathBuf {
    const MAX_PATH: usize = 260;
    let Some(text) = path.to_str() else {
        return path;
    };
    let plain = if let Some(rest) = text.strip_prefix(r"\\?\UNC\") {
        format!(r"\\{rest}")
    } else {
        match text.strip_prefix(r"\\?\") {
            Some(rest) if rest.as_bytes().get(1) == Some(&b':') => rest.to_owned(),
            _ => return path,
        }
    };
    if plain.len() >= MAX_PATH {
        return path;
    }
    PathBuf::from(plain)
}

/// 导入 `root` 处的工程。优先级：手动配置里的模块 → Maven → Gradle → 目录约定。
pub fn load_project(root: &Path, options: &LoadOptions) -> LoadedProject {
    load_projects(&[root.to_path_buf()], options)
}

fn load_root(root: &Path, options: &LoadOptions) -> LoadedProject {
    let mut messages = Vec::new();
    let config = read_manual_config(root, &mut messages);
    let mut build_files = vec![root.join(CONFIG_FILE_NAME)];

    let jdk_home = config
        .jdk
        .as_ref()
        .map(|j| j.home.clone())
        .or_else(|| options.jdk_home.clone());
    // 导入时先用默认的 JDK（显式配置 → `JAVA_HOME` → 最高版本）：Maven 按运行它的 JDK
    // 激活 `<activation><jdk>`，而运行 Maven 的通常就是 `JAVA_HOME`
    let jdk = discover_jdk(jdk_home.as_deref());
    let configured = jdk_home
        .as_deref()
        .is_some_and(|home| jdk.as_ref().is_some_and(|jdk| jdk.home == home));

    let pom = root.join("pom.xml");
    let mut unresolved = Vec::new();
    let mut coordinates = Vec::new();
    let mut toolchain_jdk = None;
    let (kind, mut graph) = if !config.modules.is_empty() {
        (
            ProjectKind::Manual,
            manual_graph(root, &config, &mut messages),
        )
    } else if pom.is_file() {
        match maven::import(&pom, options.maven_use_cli, jdk.as_ref().map(|j| j.version)) {
            Some(import) => {
                messages.extend(import.messages);
                for module in &import.modules {
                    build_files.push(module.root.join("pom.xml"));
                }
                unresolved = import.unresolved;
                toolchain_jdk = import.toolchain_jdk;
                let graph = ProjectGraph {
                    modules: import.modules,
                    libraries: import.libraries,
                    jdk: None,
                };
                (ProjectKind::Maven, graph)
            }
            None => {
                messages.push(base_db::tr!(
                    "无法解析 {}",
                    "Cannot parse {}",
                    pom.display()
                ));
                build_files.push(pom);
                (ProjectKind::Plain, plain_graph(root))
            }
        }
    } else if gradle::is_gradle_root(root) {
        build_files.extend(gradle::build_files(root));
        match gradle::import(root, options.gradle_allow_run) {
            Some(import) if !import.modules.is_empty() => {
                messages.extend(import.messages);
                unresolved = import.unresolved;
                coordinates = import.coordinates;
                let graph = ProjectGraph {
                    modules: import.modules,
                    libraries: import.libraries,
                    jdk: None,
                };
                (ProjectKind::Gradle, graph)
            }
            Some(import) => {
                messages.extend(import.messages);
                (ProjectKind::Plain, plain_graph(root))
            }
            None => {
                messages.push(base_db::tr!("Gradle 导入已被禁用且没有可用的缓存，按目录约定加载源码", "Gradle import is disabled and no cache is available; loading sources by directory convention"));
                (ProjectKind::Plain, plain_graph(root))
            }
        }
    } else {
        (ProjectKind::Plain, plain_graph(root))
    };

    // 没有显式配置时按工程要求的版本重新挑
    let requested_jdk = if configured {
        None
    } else {
        requested_jdk_version(&graph, toolchain_jdk)
    };
    graph.jdk = match requested_jdk {
        Some(wanted) if jdk.as_ref().is_none_or(|jdk| jdk.version != wanted) => {
            select_jdk(None, Some(wanted)).or(jdk)
        }
        _ => jdk,
    };
    if graph.jdk.is_none() {
        messages.push(
            base_db::tr!("没有找到 JDK：标准库的类型将无法解析。请设置 JAVA_HOME，或在 java-analyzer.toml 里配置 [jdk] home", "No JDK found: standard library types cannot be resolved. Set JAVA_HOME, or configure [jdk] home in java-analyzer.toml"),
        );
    }

    build_files.sort();
    build_files.dedup();
    LoadedProject {
        kind,
        graph,
        messages,
        build_files,
        unresolved,
        coordinates,
        requested_jdk,
    }
}

/// 只在没有构建文件或显式配置的目录里查找子工程；找到一个根就交给它自己的导入器处理。
fn discover_build_roots(dir: &Path, depth: usize, roots: &mut Vec<PathBuf>) {
    if dir.join(CONFIG_FILE_NAME).is_file()
        || dir.join("pom.xml").is_file()
        || gradle::is_gradle_root(dir)
    {
        roots.push(dir.to_path_buf());
        return;
    }
    if depth == 0 {
        return;
    }
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with('.') || matches!(name.as_ref(), "target" | "build" | "node_modules") {
            continue;
        }
        // 不跟随符号链接，避免扫描工作区之外的目录。
        if entry.file_type().is_ok_and(|kind| kind.is_dir()) {
            discover_build_roots(&entry.path(), depth - 1, roots);
        }
    }
}

/// 导入多个工作区根并合并成一张工程图。
///
/// 每个根各自按 [`load_project`] 的规则导入；合并时模块编号顺延，同一个 jar 只保留一份。
/// JDK 取第一个在 `java-analyzer.toml` 里配置了 `[jdk]` 的根，都没有配置时取第一个找到的。
/// 一个根的模块以 Maven 坐标依赖另一个根里的模块时（本地仓库里的 jar，或者解析不到的依赖），
/// 改成直接依赖那个模块的源码。模块的坐标：Maven 取 pom 里的 groupId:artifactId，
/// Gradle 取工程的 group 和 name。
pub fn load_projects(roots: &[PathBuf], options: &LoadOptions) -> LoadedProject {
    let mut expanded = Vec::new();
    for root in roots {
        let mut discovered = Vec::new();
        // shortcut: 只找四层目录以内的工程，更深的工程需要显式打开。
        discover_build_roots(root, 4, &mut discovered);
        if discovered.is_empty() {
            discovered.push(root.clone());
        }
        discovered.sort();
        for project in discovered {
            if !expanded.contains(&project) {
                expanded.push(project);
            }
        }
    }
    let roots = &expanded;
    // Maven 的设置和 JDK 一样整个工作区共用：取第一个在 `java-analyzer.toml` 里写了 `[maven]` 的根
    maven_settings::set_project_setup(
        roots
            .iter()
            .find_map(|root| configured_maven_setup(root))
            .unwrap_or_default(),
    );
    let mut merged = load_and_merge(roots, options);
    if roots.len() > 1 {
        let configured_jdk = roots.iter().find_map(|root| {
            let mut ignored = Vec::new();
            read_manual_config(root, &mut ignored).jdk.map(|j| j.home)
        });
        if let Some(jdk) = configured_jdk.and_then(|home| discover_jdk(Some(&home))) {
            merged.graph.jdk = Some(jdk);
        } else if let Some(wanted) = merged.requested_jdk {
            // 各个根要求的版本里取最高的
            if merged
                .graph
                .jdk
                .as_ref()
                .is_none_or(|jdk| jdk.version != wanted)
            {
                if let Some(jdk) = select_jdk(None, Some(wanted)) {
                    merged.graph.jdk = Some(jdk);
                }
            }
        }
        let mut coordinates: Vec<(base_db::ModuleId, String, String)> = merged
            .graph
            .modules
            .iter()
            .enumerate()
            .filter(|(i, _)| {
                !merged
                    .coordinates
                    .iter()
                    .any(|(id, _, _)| id.0 as usize == *i)
            })
            .filter_map(|(i, module)| {
                let (group, artifact) = maven::pom_coordinates(&module.root.join("pom.xml"))?;
                Some((base_db::ModuleId(i as u32), group, artifact))
            })
            .collect();
        coordinates.extend(merged.coordinates.iter().cloned());
        link_modules_by_coordinates(&mut merged.graph, &coordinates, &merged.unresolved);
    }
    warn_if_jdk_too_old(&merged.graph);
    merged
}

/// 把"依赖名为 `group:artifact:version` 的库"改成依赖坐标相同的工作区模块；
/// 本地仓库里没有、但坐标和另一个根里的模块相同的依赖，补上对那个模块的依赖。
/// 被链接的模块自己的依赖跟着传递过来（它的 jar 可能没装进本地仓库，传递依赖没有展开）。
fn link_modules_by_coordinates(
    graph: &mut ProjectGraph,
    coordinates: &[(base_db::ModuleId, String, String)],
    unresolved: &[UnresolvedDep],
) {
    if coordinates.is_empty() {
        return;
    }
    let mut linked: Vec<base_db::ModuleId> = Vec::new();
    let library_module: Vec<Option<base_db::ModuleId>> = graph
        .libraries
        .iter()
        .map(|lib| {
            let mut parts = lib.name.split(':');
            let (group, artifact) = (parts.next()?, parts.next()?);
            coordinates
                .iter()
                .find(|(_, g, a)| g == group && a == artifact)
                .map(|(id, _, _)| *id)
        })
        .collect();
    // `xxx-tests.jar`：依赖的是那个模块的测试代码
    let library_is_tests: Vec<bool> = graph
        .libraries
        .iter()
        .map(|lib| lib.jar.to_string_lossy().ends_with("-tests.jar"))
        .collect();
    for (i, module) in graph.modules.iter_mut().enumerate() {
        for dependency in &mut module.dependencies {
            if let DependencyTarget::Library(lib) = dependency.target {
                if let Some(Some(target)) = library_module.get(lib.0 as usize) {
                    if target.0 as usize != i {
                        dependency.target = if library_is_tests[lib.0 as usize] {
                            DependencyTarget::ModuleTests(*target)
                        } else {
                            DependencyTarget::Module(*target)
                        };
                        linked.push(base_db::ModuleId(i as u32));
                    }
                }
            }
        }
    }
    for dep in unresolved {
        let Some((target, _, _)) = coordinates
            .iter()
            .find(|(_, g, a)| *g == dep.group && *a == dep.artifact)
        else {
            continue;
        };
        if *target == dep.module {
            continue;
        }
        let Some(module) = graph.modules.get_mut(dep.module.0 as usize) else {
            continue;
        };
        let target = DependencyTarget::Module(*target);
        if !module.dependencies.iter().any(|d| d.target == target) {
            module.dependencies.push(Dependency {
                target,
                scope: dep.scope,
            });
        }
        linked.push(dep.module);
    }
    linked.sort();
    linked.dedup();
    inherit_module_dependencies(&mut graph.modules, &linked);
}

fn load_and_merge(roots: &[PathBuf], options: &LoadOptions) -> LoadedProject {
    let mut loaded = roots.iter().map(|root| load_root(root, options));
    let Some(mut merged) = loaded.next() else {
        return LoadedProject {
            kind: ProjectKind::Plain,
            graph: ProjectGraph::default(),
            messages: Vec::new(),
            build_files: Vec::new(),
            unresolved: Vec::new(),
            coordinates: Vec::new(),
            requested_jdk: None,
        };
    };
    for project in loaded {
        let module_offset = merged.graph.modules.len();
        let module_roots: Vec<PathBuf> = project
            .graph
            .modules
            .iter()
            .map(|m| m.root.clone())
            .collect();
        merge_graph(&mut merged.graph, project.graph);
        // 模块编号顺延；嵌套的根里被跳过的重复模块不再记
        let renumber = |module: base_db::ModuleId, graph: &ProjectGraph| {
            let root = module_roots.get(module.0 as usize)?;
            let idx = graph.modules[module_offset..]
                .iter()
                .position(|m| &m.root == root)?;
            Some(base_db::ModuleId((module_offset + idx) as u32))
        };
        for mut dep in project.unresolved {
            if let Some(module) = renumber(dep.module, &merged.graph) {
                dep.module = module;
                merged.unresolved.push(dep);
            }
        }
        for (module, group, artifact) in project.coordinates {
            if let Some(module) = renumber(module, &merged.graph) {
                merged.coordinates.push((module, group, artifact));
            }
        }
        for message in project.messages {
            if !merged.messages.contains(&message) {
                merged.messages.push(message);
            }
        }
        merged.build_files.extend(project.build_files);
        merged.requested_jdk = merged.requested_jdk.max(project.requested_jdk);
    }
    merged.build_files.sort();
    merged.build_files.dedup();
    merged
}

fn merge_graph(into: &mut ProjectGraph, other: ProjectGraph) {
    let module_offset = into.modules.len() as u32;
    // 另一张图里的库编号 → 合并后的编号
    let library_map: Vec<LibraryId> = other
        .libraries
        .into_iter()
        .map(|lib| {
            match into
                .libraries
                .iter()
                .position(|existing| existing.jar == lib.jar)
            {
                Some(idx) => LibraryId(idx as u32),
                None => {
                    into.libraries.push(lib);
                    LibraryId((into.libraries.len() - 1) as u32)
                }
            }
        })
        .collect();
    for mut module in other.modules {
        // 嵌套的工作区根（一个根在另一个根里面）会把同一个模块导入两次
        if into
            .modules
            .iter()
            .any(|existing| existing.root == module.root)
        {
            continue;
        }
        for dependency in &mut module.dependencies {
            dependency.target = match dependency.target {
                DependencyTarget::Module(id) => {
                    DependencyTarget::Module(base_db::ModuleId(id.0 + module_offset))
                }
                DependencyTarget::ModuleTests(id) => {
                    DependencyTarget::ModuleTests(base_db::ModuleId(id.0 + module_offset))
                }
                DependencyTarget::Library(id) => {
                    DependencyTarget::Library(library_map[id.0 as usize])
                }
            };
        }
        into.modules.push(module);
    }
    if into.jdk.is_none() {
        into.jdk = other.jdk;
    }
}

/// 为工程图建立二进制类路径索引：依赖库在前，JDK 在后。
pub fn build_class_path(graph: &ProjectGraph) -> ClassPath {
    let mut containers: Vec<Arc<dyn ClassContainer>> = graph
        .libraries
        .iter()
        .map(|lib| Arc::new(JarContainer::new(lib.jar.clone())) as Arc<dyn ClassContainer>)
        .collect();
    if let Some(jdk) = &graph.jdk {
        containers.extend(jdk_containers(jdk, graph.api_release()));
    }
    ClassPath::build(containers)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verbatim_prefix_is_stripped() {
        let strip = |s: &str| strip_verbatim_prefix(PathBuf::from(s));
        assert_eq!(strip(r"\\?\C:\work\app"), PathBuf::from(r"C:\work\app"));
        assert_eq!(
            strip(r"\\?\UNC\server\share\app"),
            PathBuf::from(r"\\server\share\app")
        );
        assert_eq!(strip("/home/me/app"), PathBuf::from("/home/me/app"));
        let volume = r"\\?\Volume{0a1b}\app";
        assert_eq!(strip(volume), PathBuf::from(volume));
        let long = format!(r"\\?\C:\{}", "a".repeat(300));
        assert_eq!(strip(&long), PathBuf::from(&long));
        // 真实路径：Windows 上不带前缀，其他系统和 std 的一样
        let dir = std::env::temp_dir();
        let canonical = canonicalize(&dir).unwrap();
        assert!(
            !canonical.to_string_lossy().starts_with(r"\\?\"),
            "{canonical:?}"
        );
        assert_eq!(
            canonical.canonicalize().unwrap(),
            dir.canonicalize().unwrap()
        );
    }

    #[test]
    fn parses_manual_config() {
        let config: ManualConfig = toml::from_str(
            r#"
            [jdk]
            home = "/opt/jdk"

            [[module]]
            name = "app"
            sources = ["src"]
            classpath = ["lib/*.jar"]
            language_level = 17
            preview = true
            "#,
        )
        .unwrap();
        assert_eq!(config.jdk.unwrap().home, PathBuf::from("/opt/jdk"));
        assert_eq!(config.modules.len(), 1);
        assert_eq!(config.modules[0].language_level, Some(17));
        assert!(config.modules[0].preview);
        assert!(config.modules[0].test_sources.is_empty());
    }

    /// `java-analyzer.toml` 手动配置的工程：显式的输出目录、classpath 里的 jar、模块之间的依赖。
    #[test]
    fn runtime_class_path_of_manual_modules() {
        let dir = std::env::temp_dir().join(format!("ja-manual-runtime-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let touch = |relative: &str| crate::runtime::tests::touch(&dir, relative);
        touch("app/src/");
        touch("core/src/");
        let app_out = touch("app/out/classes/");
        let app_test_out = touch("app/out/test-classes/");
        let core_out = touch("core/target/classes/");
        let lib = touch("lib/dep.jar");
        let config = r#"
            [[module]]
            name = "app"
            root = "app"
            sources = ["src"]
            output = "out/classes"
            test_output = "out/test-classes"
            dependencies = ["core"]
            language_level = 21

            [[module]]
            name = "core"
            root = "core"
            sources = ["src"]
            classpath = ["LIB/*.jar"]
            dependencies = []
            "#;
        // TOML 的基本字符串里 `\` 是转义符：Windows 路径换成 `/`
        let lib_dir = lib
            .parent()
            .unwrap()
            .display()
            .to_string()
            .replace('\\', "/");
        std::fs::write(dir.join(CONFIG_FILE_NAME), config.replace("LIB", &lib_dir)).unwrap();
        let options = LoadOptions {
            jdk_home: None,
            maven_use_cli: false,
            gradle_allow_run: false,
        };
        let graph = load_projects(std::slice::from_ref(&dir), &options).graph;
        let app =
            base_db::ModuleId(graph.modules.iter().position(|m| m.name == "app").unwrap() as u32);
        assert_eq!(
            crate::runtime_class_path(&graph, app, false).entries,
            [app_out.clone(), core_out.clone(), lib.clone()]
        );
        assert_eq!(
            crate::runtime_class_path(&graph, app, true).entries,
            [app_test_out, app_out, core_out, lib]
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn requested_jdk_is_the_highest_level_or_the_toolchain() {
        let module = |level: Option<u32>, test_level: Option<u32>| ModuleData {
            name: "m".into(),
            root: PathBuf::from("/m"),
            source_roots: Vec::new(),
            language_level: level,
            test_language_level: test_level,
            api_release: None,
            preview: false,
            dependencies: Vec::new(),
            output_dirs: Vec::new(),
            encoding: None,
            transitive_dependencies: false,
        };
        let graph = |modules| ProjectGraph {
            modules,
            libraries: Vec::new(),
            jdk: None,
        };
        let mixed = graph(vec![
            module(Some(8), None),
            module(None, None),
            module(Some(11), Some(17)),
        ]);
        assert_eq!(requested_jdk_version(&mixed, None), Some(17));
        assert_eq!(requested_jdk_version(&mixed, Some(21)), Some(21));
        assert_eq!(
            requested_jdk_version(&graph(vec![module(None, None)]), None),
            None
        );
    }

    #[test]
    fn empty_config_is_valid() {
        let config: ManualConfig = toml::from_str("").unwrap();
        assert!(config.jdk.is_none());
        assert!(config.maven.is_none());
        assert!(config.modules.is_empty());
    }

    #[test]
    fn maven_section_paths_are_relative_to_the_root() {
        let dir = std::env::temp_dir().join(format!("ja-manual-maven-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        assert_eq!(configured_maven_setup(&dir), None);
        std::fs::write(
            dir.join(CONFIG_FILE_NAME),
            r#"
            [maven]
            settings = "build/settings.xml"
            local_repository = "${user.home}/m2"
            "#,
        )
        .unwrap();
        assert_eq!(
            configured_maven_setup(&dir),
            Some(MavenSetup {
                settings: Some(dir.join("build/settings.xml")),
                local_repository: Some(PathBuf::from("${user.home}/m2")),
            })
        );
        let absolute = if cfg!(windows) {
            r"C:\abs\repo"
        } else {
            "/abs/repo"
        };
        std::fs::write(
            dir.join(CONFIG_FILE_NAME),
            format!("[maven]\nlocal_repository = '{absolute}'\n"),
        )
        .unwrap();
        assert_eq!(
            configured_maven_setup(&dir),
            Some(MavenSetup {
                settings: None,
                local_repository: Some(PathBuf::from(absolute)),
            })
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn merge_graph_renumbers_modules_and_dedups_libraries() {
        let lib = |jar: &str| LibraryData {
            name: jar.to_owned(),
            jar: PathBuf::from(jar),
            sources: None,
        };
        let module = |root: &str, dependencies: Vec<Dependency>| ModuleData {
            name: root.to_owned(),
            root: PathBuf::from(root),
            source_roots: Vec::new(),
            language_level: None,
            api_release: None,
            test_language_level: None,
            preview: false,
            dependencies,
            output_dirs: Vec::new(),
            encoding: None,
            transitive_dependencies: false,
        };
        let dep = |target| Dependency {
            target,
            scope: Scope::Compile,
        };

        let mut first = ProjectGraph {
            modules: vec![module(
                "/a",
                vec![dep(DependencyTarget::Library(LibraryId(0)))],
            )],
            libraries: vec![lib("/m2/guava.jar")],
            jdk: None,
        };
        let second = ProjectGraph {
            modules: vec![
                module(
                    "/b/core",
                    vec![dep(DependencyTarget::Library(LibraryId(1)))],
                ),
                module(
                    "/b/app",
                    vec![
                        dep(DependencyTarget::Module(base_db::ModuleId(0))),
                        dep(DependencyTarget::Library(LibraryId(0))),
                    ],
                ),
            ],
            libraries: vec![lib("/m2/slf4j.jar"), lib("/m2/guava.jar")],
            jdk: None,
        };
        merge_graph(&mut first, second);

        assert_eq!(first.modules.len(), 3);
        assert_eq!(first.libraries.len(), 2, "guava 只保留一份");
        // /b/core 依赖 guava：合并后是 0 号库
        assert_eq!(
            first.modules[1].dependencies[0].target,
            DependencyTarget::Library(LibraryId(0))
        );
        // /b/app 依赖 /b/core（顺延为 1 号模块）和 slf4j（1 号库）
        assert_eq!(
            first.modules[2].dependencies[0].target,
            DependencyTarget::Module(base_db::ModuleId(1))
        );
        assert_eq!(
            first.modules[2].dependencies[1].target,
            DependencyTarget::Library(LibraryId(1))
        );
    }

    #[test]
    fn library_dependencies_become_module_dependencies_across_roots() {
        let module = |root: &str, dependencies: Vec<Dependency>| ModuleData {
            name: root.to_owned(),
            root: PathBuf::from(root),
            source_roots: Vec::new(),
            language_level: None,
            api_release: None,
            test_language_level: None,
            preview: false,
            dependencies,
            output_dirs: Vec::new(),
            encoding: None,
            transitive_dependencies: false,
        };
        let dep = |target| Dependency {
            target,
            scope: Scope::Compile,
        };
        let mut graph = ProjectGraph {
            modules: vec![
                module("/lib", Vec::new()),
                module(
                    "/app",
                    vec![
                        dep(DependencyTarget::Library(LibraryId(0))),
                        dep(DependencyTarget::Library(LibraryId(1))),
                    ],
                ),
            ],
            libraries: vec![
                LibraryData {
                    name: "com.acme:lib:1.0-SNAPSHOT".to_owned(),
                    jar: PathBuf::from("/m2/lib.jar"),
                    sources: None,
                },
                LibraryData {
                    name: "com.google:guava:33".to_owned(),
                    jar: PathBuf::from("/m2/guava.jar"),
                    sources: None,
                },
            ],
            jdk: None,
        };
        let coordinates = vec![(
            base_db::ModuleId(0),
            "com.acme".to_owned(),
            "lib".to_owned(),
        )];
        link_modules_by_coordinates(&mut graph, &coordinates, &[]);
        assert_eq!(
            graph.modules[1].dependencies[0].target,
            DependencyTarget::Module(base_db::ModuleId(0))
        );
        assert_eq!(
            graph.modules[1].dependencies[1].target,
            DependencyTarget::Library(LibraryId(1))
        );
    }

    fn module_deps(graph: &ProjectGraph, name: &str) -> Vec<String> {
        let module = graph.modules.iter().find(|m| m.name == name).unwrap();
        let mut deps: Vec<String> = module
            .dependencies
            .iter()
            .map(|dep| match dep.target {
                DependencyTarget::Module(id) => graph.module(id).name.clone(),
                DependencyTarget::ModuleTests(id) => format!("{}/tests", graph.module(id).name),
                DependencyTarget::Library(id) => graph.library(id).name.clone(),
            })
            .collect();
        deps.sort();
        deps
    }

    #[test]
    fn manual_modules_depend_on_listed_modules_transitively() {
        let dir = std::env::temp_dir().join(format!("ja-manual-deps-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        for module in ["base", "core", "app", "other"] {
            std::fs::create_dir_all(dir.join(module).join("src")).unwrap();
        }
        let config: ManualConfig = toml::from_str(
            r#"
            [[module]]
            name = "base"
            root = "base"
            sources = ["src"]
            dependencies = []

            [[module]]
            name = "core"
            root = "core"
            sources = ["src"]
            dependencies = ["base"]

            [[module]]
            name = "app"
            root = "app"
            sources = ["src"]
            dependencies = ["core"]

            [[module]]
            name = "other"
            root = "other"
            sources = ["src"]
            "#,
        )
        .unwrap();
        let mut messages = Vec::new();
        let graph = manual_graph(&dir, &config, &mut messages);
        assert!(messages.is_empty(), "{messages:?}");
        assert!(module_deps(&graph, "base").is_empty());
        // 模块依赖是传递的
        assert_eq!(module_deps(&graph, "app"), ["base", "core"]);
        // 没写 dependencies 的模块能看到所有其他模块
        assert_eq!(module_deps(&graph, "other"), ["app", "base", "core"]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn modules_link_across_roots_even_when_not_installed() {
        let dir = std::env::temp_dir().join(format!("ja-cross-root-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let write = |path: &str, text: String| {
            let path = dir.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        };
        let group = "ja.test.crossroot";
        let pom = |artifact: &str, body: &str| {
            format!(
                "<project><groupId>{group}</groupId><artifactId>{artifact}</artifactId>\
                 <version>1</version>{body}</project>"
            )
        };
        let dep = |artifact: &str| {
            format!(
                "<dependencies><dependency><groupId>{group}</groupId>\
                 <artifactId>{artifact}</artifactId><version>1</version>\
                 </dependency></dependencies>"
            )
        };
        // 根 a 依赖根 b 里的模块 lib（没有装进本地仓库），lib 又依赖同一个根里的 util
        write("a/pom.xml", pom("app", &dep("lib")));
        write(
            "b/pom.xml",
            pom(
                "parent",
                "<packaging>pom</packaging><modules><module>lib</module><module>util</module></modules>",
            ),
        );
        write("b/lib/pom.xml", pom("lib", &dep("util")));
        write("b/util/pom.xml", pom("util", ""));
        // 根 c 和它们无关
        write("c/pom.xml", pom("unrelated", ""));
        let options = LoadOptions {
            jdk_home: None,
            maven_use_cli: false,
            gradle_allow_run: false,
        };
        let loaded = load_projects(&[dir.join("a"), dir.join("b"), dir.join("c")], &options);
        let graph = &loaded.graph;
        assert_eq!(module_deps(graph, "app"), ["lib", "util"]);
        assert_eq!(module_deps(graph, "lib"), ["util"]);
        assert!(module_deps(graph, "unrelated").is_empty());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn discovers_nested_build_roots_without_reimporting_reactor_modules() {
        let dir = std::env::temp_dir().join(format!("ja-nested-roots-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let write = |path: &str, text: &str| {
            let path = dir.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        };
        let pom = |artifact: &str, body: &str| {
            format!("<project><groupId>ja.test.nested</groupId><artifactId>{artifact}</artifactId><version>1</version>{body}</project>")
        };
        write("a/pom.xml", &pom("app", "<dependencies><dependency><groupId>ja.test.nested</groupId><artifactId>lib</artifactId><version>1</version></dependency></dependencies>"));
        write(
            "b/pom.xml",
            &pom(
                "parent",
                "<packaging>pom</packaging><modules><module>lib</module></modules>",
            ),
        );
        write("b/lib/pom.xml", &pom("lib", ""));
        write("b/example/pom.xml", &pom("not-a-reactor-module", ""));
        write("worktrees/a/pom.xml", &pom("app", ""));
        for skipped in [
            "target",
            "build",
            "node_modules",
            ".git",
            ".hidden",
            "one/two/three/four/five",
        ] {
            write(&format!("{skipped}/pom.xml"), &pom("ignored", ""));
        }
        let options = LoadOptions {
            maven_use_cli: false,
            gradle_allow_run: false,
            ..LoadOptions::default()
        };
        let loaded = load_projects(std::slice::from_ref(&dir), &options);
        assert_eq!(loaded.kind, ProjectKind::Maven);
        let roots: Vec<_> = loaded
            .graph
            .modules
            .iter()
            .map(|m| m.root.clone())
            .collect();
        assert_eq!(
            roots,
            [
                dir.join("a"),
                dir.join("b"),
                dir.join("b/lib"),
                dir.join("worktrees/a")
            ]
        );
        assert_eq!(module_deps(&loaded.graph, "app"), ["lib"]);
        assert!(loaded.build_files.contains(&dir.join("b/lib/pom.xml")));

        write(CONFIG_FILE_NAME, "[maven]\n");
        assert_eq!(load_project(&dir, &options).kind, ProjectKind::Plain);
        write(CONFIG_FILE_NAME, "[[module]]\nname = 'manual'\n");
        let manual = load_projects(std::slice::from_ref(&dir), &options);
        assert_eq!(manual.kind, ProjectKind::Manual);
        assert_eq!(manual.graph.modules.len(), 1);
        assert_eq!(manual.graph.modules[0].name, "manual");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn poms_starting_with_a_byte_order_mark_import_as_maven() {
        // Windows 上的编辑器保存的 pom.xml 常以 UTF-8 BOM 开头（l0ng-ai/openidea#4928）
        let dir = std::env::temp_dir().join(format!("ja-pom-bom-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let write = |path: &str, text: String| {
            let path = dir.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, format!("\u{feff}{text}")).unwrap();
        };
        let group = "ja.test.bom";
        let pom = |artifact: &str, body: &str| {
            format!(
                "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
                 <project><groupId>{group}</groupId><artifactId>{artifact}</artifactId>\
                 <version>1</version>{body}</project>"
            )
        };
        write(
            "pom.xml",
            pom(
                "parent",
                "<packaging>pom</packaging><modules><module>app</module><module>lib</module></modules>",
            ),
        );
        write(
            "app/pom.xml",
            pom(
                "app",
                &format!(
                    "<dependencies><dependency><groupId>{group}</groupId>\
                     <artifactId>lib</artifactId><version>1</version>\
                     </dependency></dependencies>"
                ),
            ),
        );
        write("lib/pom.xml", pom("lib", ""));
        let options = LoadOptions {
            jdk_home: None,
            maven_use_cli: false,
            gradle_allow_run: false,
        };
        let loaded = load_project(&dir, &options);
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(loaded.kind, ProjectKind::Maven);
        assert_eq!(module_deps(&loaded.graph, "app"), ["lib"]);
        assert!(module_deps(&loaded.graph, "lib").is_empty());
    }

    #[test]
    fn gradle_modules_link_across_roots_by_coordinates() {
        let dir = std::env::temp_dir().join(format!("ja-gradle-cross-root-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let write = |path: &str, text: &str| {
            let path = dir.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        };
        write("orders/settings.gradle", "rootProject.name = 'orders'\n");
        write(
            "users/settings.gradle",
            "rootProject.name = 'users'\ninclude 'api', 'core'\n",
        );
        // orders 用到的 users:core 已经发布到仓库（Gradle 缓存里有 jar），users:api 没有发布
        let core_jar = "cache/files-2.1/ja.test.users/core/1.0/h/core-1.0.jar";
        let gson_jar = "cache/files-2.1/com.google.code.gson/gson/2.11.0/h/gson-2.11.0.jar";
        write(core_jar, "");
        write(gson_jar, "");
        let d = |path: &str| dir.join(path).display().to_string();
        let set = |name: &str, classpath: Vec<String>, unresolved: Vec<&str>| {
            serde_json::json!({"name": name, "srcDirs": [], "outputDirs": [], "classpath": classpath,
                               "unresolved": unresolved})
        };
        let orders = serde_json::json!([
            {"name": "orders", "group": "ja.test.orders", "dir": d("orders"), "buildDir": d("orders/build"),
             "sourceSets": [set("main", vec![d(core_jar)], vec!["ja.test.users:api"])]}
        ]);
        let users = serde_json::json!([
            {"name": "api", "group": "ja.test.users", "dir": d("users/api"), "buildDir": d("users/api/build"),
             "sourceSets": [set("main", vec![d(gson_jar)], vec![])]},
            {"name": "core", "group": "ja.test.users", "dir": d("users/core"), "buildDir": d("users/core/build"),
             "sourceSets": [set("main", vec![d("users/api/build/classes/java/main"), d(gson_jar)], vec![])]}
        ]);
        let mut caches = Vec::new();
        for (root, model) in [("orders", orders), ("users", users)] {
            let cache = gradle::cache_file(&dir.join(root)).expect("没有可用的缓存目录");
            std::fs::create_dir_all(cache.parent().unwrap()).unwrap();
            std::fs::write(&cache, model.to_string()).unwrap();
            caches.push(cache);
        }
        let options = LoadOptions {
            jdk_home: None,
            maven_use_cli: false,
            gradle_allow_run: false,
        };
        let loaded = load_projects(&[dir.join("orders"), dir.join("users")], &options);
        let discovered = load_project(&dir, &options);
        assert_eq!(discovered.kind, ProjectKind::Gradle);
        assert_eq!(
            module_deps(&discovered.graph, "orders"),
            module_deps(&loaded.graph, "orders")
        );
        assert_eq!(discovered.graph.modules.len(), loaded.graph.modules.len());
        for cache in caches {
            let _ = std::fs::remove_file(cache);
        }
        let _ = std::fs::remove_dir_all(&dir);
        let graph = &loaded.graph;
        assert_eq!(loaded.kind, ProjectKind::Gradle);
        // 已发布的 jar 换成模块；没发布的依赖补上模块；被链接模块的依赖传递过来
        assert_eq!(
            module_deps(graph, "orders"),
            ["api", "com.google.code.gson:gson:2.11.0", "core"]
        );
        assert_eq!(
            module_deps(graph, "core"),
            ["api", "com.google.code.gson:gson:2.11.0"]
        );
    }
}
