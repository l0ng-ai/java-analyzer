//! Maven 工程导入：直接解析 POM，在本地仓库里解析依赖。
//!
//! 实现的部分：父 POM 继承、属性插值、`dependencyManagement`、BOM import、scope、
//! exclusion、最近者优先的版本仲裁、profile（`activeByDefault`，以及按 JDK 版本、操作系统、
//! 属性取反、文件是否存在激活的）、多模块 reactor。
//!
//! 本地仓库缺的构件交给 `mvn` 下载（见 [`import`]）。
//!
//! 没有实现的部分（遇到时依赖会缺失，由调用方决定是否回退到 `mvn` 命令行）：
//! 版本区间的完整语义、命令行 `-P` / `-D` 激活的 profile、改变源码目录的插件。

use std::{
    cmp::Ordering,
    collections::VecDeque,
    path::{Path, PathBuf},
    sync::{Arc, LazyLock, Mutex},
    time::Instant,
};

use base_db::{
    Dependency, DependencyTarget, LibraryData, LibraryId, ModuleData, ModuleId, Scope, SourceRoot,
    SourceRootKind,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    jdk::parse_feature_version,
    maven_settings::{maven_command, resolved_setup, run_maven, ResolvedSetup},
    xml::{self, XmlNode},
};

#[derive(Default)]
pub struct MavenImport {
    pub modules: Vec<ModuleData>,
    pub libraries: Vec<LibraryData>,
    pub messages: Vec<String>,
    /// 本地仓库里找不到的依赖构件（多个工作区根合并时，可能是另一个根里的模块）
    pub unresolved: Vec<crate::UnresolvedDep>,
    /// maven-toolchains-plugin 要求的 JDK 版本（`<toolchains><jdk><version>`），多个模块取最高的
    pub toolchain_jdk: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Coord {
    group: String,
    artifact: String,
}

#[derive(Clone, Debug, Default)]
struct RawDep {
    group: String,
    artifact: String,
    version: Option<String>,
    scope: Option<String>,
    kind: Option<String>,
    classifier: Option<String>,
    /// 原文：可能写成属性（`<optional>${foo.optional}</optional>`），插值之后再判断
    optional: Option<String>,
    exclusions: Vec<Coord>,
    /// `system` scope 的 `<systemPath>`
    system_path: Option<String>,
}

impl RawDep {
    fn coord(&self) -> Coord {
        Coord {
            group: self.group.clone(),
            artifact: self.artifact.clone(),
        }
    }
}

#[derive(Clone, Debug, Default)]
struct RawParent {
    group: String,
    artifact: String,
    version: String,
    relative_path: Option<String>,
}

#[derive(Clone, Debug, Default)]
struct RawPom {
    parent: Option<RawParent>,
    group: Option<String>,
    artifact: String,
    version: Option<String>,
    properties: Vec<(String, String)>,
    modules: Vec<String>,
    deps: Vec<RawDep>,
    managed: Vec<RawDep>,
    source_dir: Option<String>,
    test_source_dir: Option<String>,
    /// `<build>` 里的 `directory`、`outputDirectory`、`testOutputDirectory`
    build_dir: Option<String>,
    output_dir: Option<String>,
    test_output_dir: Option<String>,
    compiler_level: Option<String>,
    /// maven-compiler-plugin 的 `<release>`
    compiler_release: Option<String>,
    /// 测试代码的 `<testRelease>`，没有时取 `<testSource>`
    compiler_test_level: Option<String>,
    /// maven-compiler-plugin 的 `<testRelease>`
    compiler_test_release: Option<String>,
    /// maven-compiler-plugin 开了预览特性（`<enablePreview>` 或 `--enable-preview`）
    compiler_preview: Option<bool>,
    /// maven-compiler-plugin 的 `<encoding>`
    compiler_encoding: Option<String>,
    /// maven-toolchains-plugin 的 `<toolchains><jdk><version>`（原文，可能是区间或属性）
    toolchain_jdk: Option<String>,
    /// `<repositories>` 里的远程仓库：(id, url)
    repositories: Vec<(String, String)>,
}

fn text(node: &XmlNode, name: &str) -> Option<String> {
    node.child_text(name).map(str::to_owned)
}

fn read_dep(node: &XmlNode) -> Option<RawDep> {
    Some(RawDep {
        group: text(node, "groupId")?,
        artifact: text(node, "artifactId")?,
        version: text(node, "version"),
        scope: text(node, "scope"),
        kind: text(node, "type"),
        classifier: text(node, "classifier"),
        optional: text(node, "optional"),
        system_path: text(node, "systemPath"),
        exclusions: node
            .child("exclusions")
            .map(|e| {
                e.children_named("exclusion")
                    .filter_map(|x| {
                        Some(Coord {
                            group: text(x, "groupId")?,
                            artifact: text(x, "artifactId")?,
                        })
                    })
                    .collect()
            })
            .unwrap_or_default(),
    })
}

/// 读取 `<project>` 或 `<profile>` 里通用的那几节。
fn read_common(node: &XmlNode, pom: &mut RawPom) {
    if let Some(properties) = node.child("properties") {
        for prop in &properties.children {
            pom.properties.push((prop.name.clone(), prop.text.clone()));
        }
    }
    if let Some(modules) = node.child("modules") {
        pom.modules
            .extend(modules.children_named("module").map(|m| m.text.clone()));
    }
    if let Some(deps) = node.child("dependencies") {
        pom.deps
            .extend(deps.children_named("dependency").filter_map(read_dep));
    }
    if let Some(deps) = node.path(&["dependencyManagement", "dependencies"]) {
        pom.managed
            .extend(deps.children_named("dependency").filter_map(read_dep));
    }
    if let Some(repositories) = node.child("repositories") {
        pom.repositories.extend(
            repositories
                .children_named("repository")
                .filter_map(|r| Some((text(r, "id")?, text(r, "url")?))),
        );
    }
    if let Some(build) = node.child("build") {
        if let Some(dir) = text(build, "sourceDirectory") {
            pom.source_dir = Some(dir);
        }
        if let Some(dir) = text(build, "testSourceDirectory") {
            pom.test_source_dir = Some(dir);
        }
        if let Some(dir) = text(build, "directory") {
            pom.build_dir = Some(dir);
        }
        if let Some(dir) = text(build, "outputDirectory") {
            pom.output_dir = Some(dir);
        }
        if let Some(dir) = text(build, "testOutputDirectory") {
            pom.test_output_dir = Some(dir);
        }
        let plugin_lists = [
            build.child("plugins"),
            build.path(&["pluginManagement", "plugins"]),
        ];
        for plugins in plugin_lists.into_iter().flatten() {
            for plugin in plugins.children_named("plugin") {
                match plugin.child_text("artifactId") {
                    Some("maven-compiler-plugin") => {}
                    Some("maven-toolchains-plugin") => {
                        if let Some(version) = toolchain_jdk_version(plugin) {
                            pom.toolchain_jdk = Some(version);
                        }
                        continue;
                    }
                    _ => continue,
                }
                if let Some(config) = plugin.child("configuration") {
                    let release = text(config, "release");
                    let level = release.clone().or_else(|| text(config, "source"));
                    if level.is_some() {
                        pom.compiler_level = level;
                    }
                    if release.is_some() {
                        pom.compiler_release = release;
                    }
                    let test_release = text(config, "testRelease");
                    let test_level = test_release.clone().or_else(|| text(config, "testSource"));
                    if test_level.is_some() {
                        pom.compiler_test_level = test_level;
                    }
                    if test_release.is_some() {
                        pom.compiler_test_release = test_release;
                    }
                    let enable_preview = config.child_text("enablePreview") == Some("true");
                    let preview_arg = config.child("compilerArgs").is_some_and(|args| {
                        args.children.iter().any(|a| a.text == "--enable-preview")
                    }) || config.child_text("compilerArgument")
                        == Some("--enable-preview");
                    if enable_preview || preview_arg {
                        pom.compiler_preview = Some(true);
                    }
                    if let Some(encoding) = text(config, "encoding") {
                        pom.compiler_encoding = Some(encoding);
                    }
                }
            }
        }
    }
}

/// maven-toolchains-plugin 配置里的 JDK 版本：插件级的 `<configuration>` 或某个 execution 的。
fn toolchain_jdk_version(plugin: &XmlNode) -> Option<String> {
    let executions = plugin
        .child("executions")
        .into_iter()
        .flat_map(|e| e.children_named("execution"))
        .filter_map(|e| e.child("configuration"));
    plugin
        .child("configuration")
        .into_iter()
        .chain(executions)
        .find_map(|config| text(config.path(&["toolchains", "jdk"])?, "version"))
}

/// `pom.xml` 的 `(groupId, artifactId)`；没写 groupId 时继承 parent 的。
pub(crate) fn pom_coordinates(path: &Path) -> Option<(String, String)> {
    let pom = read_raw_pom(path)?;
    let group = pom.group.or_else(|| pom.parent.map(|p| p.group))?;
    Some((group, pom.artifact))
}

fn read_raw_pom(path: &Path) -> Option<RawPom> {
    let content = std::fs::read_to_string(path).ok()?;
    let root = xml::parse(&content)?;
    if root.name != "project" {
        return None;
    }
    let mut pom = RawPom {
        group: text(&root, "groupId"),
        artifact: text(&root, "artifactId")?,
        version: text(&root, "version"),
        ..RawPom::default()
    };
    if let Some(parent) = root.child("parent") {
        pom.parent = Some(RawParent {
            group: text(parent, "groupId")?,
            artifact: text(parent, "artifactId")?,
            version: text(parent, "version").unwrap_or_default(),
            relative_path: parent.child("relativePath").map(|n| n.text.clone()),
        });
    }
    read_common(&root, &mut pom);
    if let Some(profiles) = root.child("profiles") {
        let dir = path.parent().unwrap_or(Path::new("."));
        let profiles: Vec<&XmlNode> = profiles.children_named("profile").collect();
        let triggered: Vec<&XmlNode> = profiles
            .iter()
            .copied()
            .filter(|profile| {
                profile
                    .child("activation")
                    .is_some_and(|activation| activation_matches(activation, dir))
            })
            .collect();
        // `activeByDefault` 的 profile 只在同一个 POM 里没有别的 profile 被条件激活时生效
        let active = if triggered.is_empty() {
            profiles
                .iter()
                .copied()
                .filter(|profile| {
                    profile
                        .path(&["activation", "activeByDefault"])
                        .is_some_and(|n| n.text == "true")
                })
                .collect()
        } else {
            triggered
        };
        for profile in active {
            read_common(profile, &mut pom);
        }
    }
    Some(pom)
}

thread_local! {
    /// 导入时用的 JDK 的特性版本号：`<activation><jdk>` 按它判断（Maven 按运行它的 JDK 判断）
    static ACTIVATION_JDK: std::cell::Cell<Option<u32>> = const { std::cell::Cell::new(None) };
}

/// profile 的激活条件是否满足：写了的条件都得满足（`jdk`、`os`、`property`、`file`）。
/// 只有 `activeByDefault` 时不算条件激活。
///
/// 导入时没有命令行参数和系统属性：`<property><name>x</name></property>` 不满足，
/// `<name>!x</name>` 满足；带 `<value>` 的只有 `!value` 形式满足。
fn activation_matches(activation: &XmlNode, dir: &Path) -> bool {
    let mut any = false;
    if let Some(jdk) = text(activation, "jdk") {
        any = true;
        let Some(version) = ACTIVATION_JDK.with(|v| v.get()) else {
            return false;
        };
        if !jdk_matches(jdk.trim(), version) {
            return false;
        }
    }
    if let Some(os) = activation.child("os") {
        any = true;
        let family = text(os, "family").or_else(|| text(os, "name"));
        if let Some(family) = family {
            let (negated, family) = match family.strip_prefix('!') {
                Some(rest) => (true, rest.to_ascii_lowercase()),
                None => (false, family.to_ascii_lowercase()),
            };
            let matches = match family.as_str() {
                "windows" => cfg!(windows),
                "mac" | "mac os x" => cfg!(target_os = "macos"),
                "unix" => cfg!(unix),
                "linux" => cfg!(target_os = "linux"),
                _ => false,
            };
            if matches == negated {
                return false;
            }
        }
    }
    if let Some(property) = activation.child("property") {
        any = true;
        let name = text(property, "name").unwrap_or_default();
        let matches = match text(property, "value") {
            Some(value) => value.starts_with('!'),
            None => name.starts_with('!'),
        };
        if !matches {
            return false;
        }
    }
    if let Some(file) = activation.child("file") {
        any = true;
        let expand = |p: String| {
            let dir_text = dir.to_string_lossy();
            let p = p
                .replace("${project.basedir}", &dir_text)
                .replace("${basedir}", &dir_text);
            dir.join(p)
        };
        if let Some(exists) = text(file, "exists") {
            if !expand(exists).exists() {
                return false;
            }
        }
        if let Some(missing) = text(file, "missing") {
            if expand(missing).exists() {
                return false;
            }
        }
    }
    any
}

/// `<jdk>` 的写法：前缀（`17`、`1.8`）、`!` 取反，或者区间（`[17,)`、`(,11]`、`[1.8,11)`）。
/// 只按特性版本号比较。
fn jdk_matches(spec: &str, version: u32) -> bool {
    if let Some(rest) = spec.strip_prefix('!') {
        return !jdk_matches(rest, version);
    }
    if spec.starts_with('[') || spec.starts_with('(') {
        let mut ranges = Vec::new();
        let mut start = 0;
        for (idx, c) in spec.char_indices() {
            if matches!(c, ']' | ')') {
                ranges.push(spec[start..=idx].trim().trim_start_matches(','));
                start = idx + 1;
            }
        }
        return ranges.into_iter().any(|range| {
            let range = range.trim();
            let lower_inclusive = range.starts_with('[');
            let upper_inclusive = range.ends_with(']');
            let inner = range.trim_matches(|c| matches!(c, '[' | ']' | '(' | ')'));
            let (lower, upper) = match inner.split_once(',') {
                Some((lower, upper)) => (lower.trim(), upper.trim()),
                // `[17]`：恰好是这个版本
                None => (inner.trim(), inner.trim()),
            };
            let lower_ok = match parse_feature_version(lower) {
                Some(lower) if lower_inclusive => version >= lower,
                Some(lower) => version > lower,
                None => true,
            };
            let upper_ok = match parse_feature_version(upper) {
                Some(upper) if upper_inclusive || !inner.contains(',') => version <= upper,
                Some(upper) => version < upper,
                None => true,
            };
            lower_ok && upper_ok
        });
    }
    parse_feature_version(spec) == Some(version)
}

#[derive(Clone, Debug, Default)]
struct Managed {
    version: Option<String>,
    scope: Option<String>,
    exclusions: Vec<Coord>,
    system_path: Option<String>,
}

type ManagedKey = (String, String, Option<String>);

/// 继承、插值之后的有效 POM。
#[derive(Clone, Debug, Default)]
struct Effective {
    group: String,
    artifact: String,
    version: String,
    dir: PathBuf,
    properties: FxHashMap<String, String>,
    deps: Vec<RawDep>,
    managed: FxHashMap<ManagedKey, Managed>,
    /// 继承链上没插值的 `<dependencies>`（祖先在前）和 `<dependencyManagement>`（自己在前）。
    /// Maven 先合并继承链、再用最终的属性插值：子模块覆盖的属性（`<logback.version>`）
    /// 对父 POM 里写的依赖和受管版本、以及父 POM 导入哪个版本的 BOM 都生效
    raw_deps: Vec<RawDep>,
    raw_managed: Vec<RawDep>,
    source_dir: Option<String>,
    test_source_dir: Option<String>,
    /// `<build>` 里的 `directory`、`outputDirectory`、`testOutputDirectory`
    build_dir: Option<String>,
    output_dir: Option<String>,
    test_output_dir: Option<String>,
    /// 继承链上没插值的编译器插件配置：`source`、`release`、`testSource`、`testRelease`。
    /// 和依赖一样，父 POM 里的 `${maven.compile.source}` 要用子模块覆盖后的属性来插值
    raw_level: Option<String>,
    raw_release: Option<String>,
    raw_test_level: Option<String>,
    raw_test_release: Option<String>,
    /// 继承链上没插值的编译器插件 `<encoding>`
    raw_encoding: Option<String>,
    level: Option<u32>,
    /// `--release`：限制 JDK API 的版本
    release: Option<u32>,
    /// 测试代码单独设置的语言级别（`testRelease` / `testSource`）
    test_level: Option<u32>,
    /// 测试代码的 `--release`
    test_release: Option<u32>,
    preview: bool,
    /// 源文件编码：编译器插件的 `<encoding>`，没有时取 `project.build.sourceEncoding`
    encoding: Option<String>,
    /// maven-toolchains-plugin 的 JDK 版本：没插值的原文和解析出的特性版本号
    raw_toolchain: Option<String>,
    toolchain: Option<u32>,
}

fn interpolate(value: &str, properties: &FxHashMap<String, String>) -> String {
    let mut current = value.to_owned();
    // 属性可以互相引用；限制轮数以防循环定义
    for _ in 0..10 {
        let Some(start) = current.find("${") else {
            break;
        };
        let Some(len) = current[start..].find('}') else {
            break;
        };
        let key = &current[start + 2..start + len];
        let Some(replacement) = properties.get(key) else {
            break;
        };
        current = format!(
            "{}{}{}",
            &current[..start],
            replacement,
            &current[start + len + 1..]
        );
    }
    current
}

fn interpolate_dep(dep: &RawDep, properties: &FxHashMap<String, String>) -> RawDep {
    let i = |s: &String| interpolate(s, properties);
    RawDep {
        group: i(&dep.group),
        artifact: i(&dep.artifact),
        version: dep.version.as_ref().map(i),
        scope: dep.scope.as_ref().map(i),
        kind: dep.kind.clone(),
        classifier: dep.classifier.as_ref().map(i),
        optional: dep.optional.as_ref().map(i),
        exclusions: dep.exclusions.clone(),
        system_path: dep.system_path.as_ref().map(i),
    }
}

/// 区间的一端：（版本，是否包含它）；`None` 是没有这一端（`(,1.0]`、`[1.0,)`）。
type RangeBound = Option<(String, bool)>;

/// 解析版本区间：`[1.0,2.0)`、`(,1.0]`、`[1.0]`、并集 `[1,2),(3,)`。不是区间时返回 `None`。
/// 并集只在 `],` / `),` 处分开，每段里的逗号是上下界的分隔。
fn parse_range(spec: &str) -> Option<Vec<(RangeBound, RangeBound)>> {
    let mut rest = spec.trim();
    if !rest.starts_with(['[', '(']) {
        return None;
    }
    let bound = |v: &str, inclusive: bool| {
        let v = v.trim();
        (!v.is_empty()).then(|| (v.to_owned(), inclusive))
    };
    let mut ranges = Vec::new();
    while !rest.is_empty() {
        let lower_inclusive = match rest.as_bytes()[0] {
            b'[' => true,
            b'(' => false,
            _ => return None,
        };
        let end = rest.find([']', ')'])?;
        let upper_inclusive = rest.as_bytes()[end] == b']';
        let inner = &rest[1..end];
        ranges.push(match inner.split_once(',') {
            Some((lower, upper)) => (bound(lower, lower_inclusive), bound(upper, upper_inclusive)),
            // `[1.0]`：恰好是这个版本
            None => {
                let pin = bound(inner, true)?;
                (Some(pin.clone()), Some(pin))
            }
        });
        rest = rest[end + 1..].trim_start();
        rest = rest.strip_prefix(',').unwrap_or(rest).trim_start();
    }
    Some(ranges)
}

fn in_range(version: &str, (lower, upper): &(RangeBound, RangeBound)) -> bool {
    let above = lower
        .as_ref()
        .is_none_or(|(v, inclusive)| match compare_versions(version, v) {
            Ordering::Greater => true,
            Ordering::Equal => *inclusive,
            Ordering::Less => false,
        });
    let below = upper
        .as_ref()
        .is_none_or(|(v, inclusive)| match compare_versions(version, v) {
            Ordering::Less => true,
            Ordering::Equal => *inclusive,
            Ordering::Greater => false,
        });
    above && below
}

enum VersionToken {
    /// 去掉前导零的数字
    Number(String),
    /// 小写的限定词
    Qualifier(String),
}

impl VersionToken {
    /// 等同于没有这一项的：`0`、`ga`、`final`、`release`
    fn is_null(&self) -> bool {
        match self {
            VersionToken::Number(n) => n.is_empty(),
            VersionToken::Qualifier(q) => qualifier_rank(q).0 == 5,
        }
    }
}

/// 限定词的顺序：alpha < beta < milestone < rc < snapshot < 正式版 < sp < 其它（按字母）。
fn qualifier_rank(qualifier: &str) -> (u8, &str) {
    match qualifier {
        "alpha" | "a" => (0, ""),
        "beta" | "b" => (1, ""),
        "milestone" | "m" => (2, ""),
        "rc" | "cr" => (3, ""),
        "snapshot" => (4, ""),
        "" | "ga" | "final" | "release" => (5, ""),
        "sp" => (6, ""),
        other => (7, other),
    }
}

/// 按 `.`、`-` 和数字/字母的交界切分；限定词前面和末尾等同于没有的项去掉（`1.0-rc` == `1-rc`，`1.0` == `1`）。
fn version_tokens(version: &str) -> Vec<VersionToken> {
    let mut tokens = Vec::new();
    let lower = version.to_ascii_lowercase();
    let push = |tokens: &mut Vec<VersionToken>, part: &str| {
        let token = if part.starts_with(|c: char| c.is_ascii_digit()) {
            VersionToken::Number(part.trim_start_matches('0').to_owned())
        } else {
            while tokens.last().is_some_and(VersionToken::is_null) {
                tokens.pop();
            }
            VersionToken::Qualifier(part.to_owned())
        };
        tokens.push(token);
    };
    for part in lower.split(['.', '-']) {
        let mut start = 0;
        let bytes = part.as_bytes();
        for i in 1..bytes.len() {
            if bytes[i].is_ascii_digit() != bytes[i - 1].is_ascii_digit() {
                push(&mut tokens, &part[start..i]);
                start = i;
            }
        }
        push(&mut tokens, &part[start..]);
    }
    while tokens.last().is_some_and(VersionToken::is_null) {
        tokens.pop();
    }
    tokens
}

/// 比较两个 Maven 版本号。
// shortcut: not full GenericVersionScheme (unknown-qualifier and padding edge cases); upgrade if a real project mis-orders
fn compare_versions(a: &str, b: &str) -> Ordering {
    use VersionToken::{Number, Qualifier};
    let (a, b) = (version_tokens(a), version_tokens(b));
    for i in 0..a.len().max(b.len()) {
        let ordering = match (a.get(i), b.get(i)) {
            (Some(Number(x)), Some(Number(y))) => x.len().cmp(&y.len()).then_with(|| x.cmp(y)),
            (Some(Number(_)), Some(Qualifier(_))) => Ordering::Greater,
            (Some(Qualifier(_)), Some(Number(_))) => Ordering::Less,
            (Some(Qualifier(x)), Some(Qualifier(y))) => qualifier_rank(x).cmp(&qualifier_rank(y)),
            // 短的一方缺的项当作 `0` / 正式版
            (Some(Number(x)), None) => (!x.is_empty()).cmp(&false),
            (None, Some(Number(y))) => false.cmp(&!y.is_empty()),
            (Some(Qualifier(x)), None) => qualifier_rank(x).cmp(&qualifier_rank("")),
            (None, Some(Qualifier(y))) => qualifier_rank("").cmp(&qualifier_rank(y)),
            (None, None) => Ordering::Equal,
        };
        if ordering != Ordering::Equal {
            return ordering;
        }
    }
    Ordering::Equal
}

fn parse_scope(scope: Option<&str>) -> Scope {
    match scope {
        Some("test") => Scope::Test,
        Some("provided") => Scope::Provided,
        Some("runtime") => Scope::Runtime,
        _ => Scope::Compile,
    }
}

/// 传递依赖的 scope 合成规则。返回 `None` 表示该传递依赖不进入 classpath。
pub(crate) fn combine_scope(parent: Scope, child: Scope) -> Option<Scope> {
    if matches!(child, Scope::Test | Scope::Provided) {
        return None;
    }
    Some(match (parent, child) {
        (Scope::Test, _) => Scope::Test,
        (Scope::Provided, _) => Scope::Provided,
        (Scope::Runtime, _) => Scope::Runtime,
        (Scope::Compile, Scope::Runtime) => Scope::Runtime,
        (Scope::Compile, _) => Scope::Compile,
    })
}

fn is_excluded(exclusions: &[Coord], coord: &Coord) -> bool {
    exclusions.iter().any(|e| {
        (e.group == "*" || e.group == coord.group)
            && (e.artifact == "*" || e.artifact == coord.artifact)
    })
}

/// 本地仓库里缺的构件，带上让 Maven 下载它所需的全部坐标。
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct MissingArtifact {
    group: String,
    artifact: String,
    version: String,
    /// 依赖的 `<type>`：`jar`、`test-jar`、`pom`……
    kind: String,
    classifier: Option<String>,
}

struct Resolver {
    repo: PathBuf,
    /// reactor 里的模块：坐标 → pom.xml 路径
    reactor: FxHashMap<Coord, PathBuf>,
    cache: FxHashMap<PathBuf, Option<Arc<Effective>>>,
    messages: Vec<String>,
    missing: FxHashSet<MissingArtifact>,
    /// 遇到缺件的次数（同一个构件重复算）：判断某个模块有没有缺件用
    missing_hits: usize,
}

impl Resolver {
    /// 依赖声明里的版本。区间（`[1.0,2.0)`）和 Maven 一样取落在区间里的最高版本，候选只看本地仓库里的
    /// 版本目录（不读 `maven-metadata*.xml`）：优先取目录里有依赖要用的文件 `{artifact}-{v}{suffix}`
    /// （见 `artifact_suffix`）的最高版本，避免离线或远程仓库不可达时因别的工程留下的纯 pom 目录顶掉已有构件；
    /// 区间里没有任何版本有构件文件时，退而取有 `.pom` 的最高版本（展开已安装的传递依赖并按缺件
    /// 交给 Maven 补下载）；只有 `*.lastUpdated` 的目录不算候选；一个都没有时原样返回区间，
    /// 交给 Maven 自己按区间下载。软性版本（`1.0`）原样返回。
    fn resolve_version(&self, group: &str, artifact: &str, spec: &str, suffix: &str) -> String {
        let Some(ranges) = parse_range(spec) else {
            return spec.to_owned();
        };
        if let [(Some((lower, true)), Some((upper, true)))] = ranges.as_slice() {
            if lower == upper {
                return lower.clone();
            }
        }
        let coord = Coord {
            group: group.to_owned(),
            artifact: artifact.to_owned(),
        };
        if self.reactor.contains_key(&coord) {
            // reactor 里的模块不看本地仓库，版本号也用不上：照旧取第一个界
            return ranges
                .first()
                .and_then(|(lower, upper)| lower.as_ref().or(upper.as_ref()))
                .map_or_else(|| spec.to_owned(), |(v, _)| v.clone());
        }
        let dir = self.repo.join(group.replace('.', "/")).join(artifact);
        let in_range_versions: Vec<String> = std::fs::read_dir(&dir)
            .into_iter()
            .flatten()
            .flatten()
            .filter_map(|entry| entry.file_name().into_string().ok())
            .filter(|v| ranges.iter().any(|range| in_range(v, range)))
            .collect();
        let highest_with = |ext: &str| {
            in_range_versions
                .iter()
                .filter(|v| dir.join(v).join(format!("{artifact}-{v}{ext}")).is_file())
                // `1.0` 和 `1.0.0` 相等时按字符串定下来，不受目录顺序影响
                .max_by(|a, b| compare_versions(a, b).then_with(|| a.cmp(b)))
                .cloned()
        };
        highest_with(suffix)
            .or_else(|| (suffix != ".pom").then(|| highest_with(".pom")).flatten())
            .unwrap_or_else(|| spec.to_owned())
    }

    fn artifact_dir(&self, group: &str, artifact: &str, version: &str) -> PathBuf {
        self.repo
            .join(group.replace('.', "/"))
            .join(artifact)
            .join(version)
    }

    fn repo_pom(&self, group: &str, artifact: &str, version: &str) -> PathBuf {
        self.artifact_dir(group, artifact, version)
            .join(format!("{artifact}-{version}.pom"))
    }

    fn pom_for(&self, coord: &Coord, version: &str) -> PathBuf {
        match self.reactor.get(coord) {
            Some(path) => path.clone(),
            None => self.repo_pom(&coord.group, &coord.artifact, version),
        }
    }

    fn effective(&mut self, pom_path: &Path, depth: u32) -> Option<Arc<Effective>> {
        if let Some(cached) = self.cache.get(pom_path) {
            return cached.clone();
        }
        // 先占位，遇到循环的父子关系时直接返回 None
        self.cache.insert(pom_path.to_path_buf(), None);
        let result = self.compute_effective(pom_path, depth).map(Arc::new);
        self.cache.insert(pom_path.to_path_buf(), result.clone());
        result
    }

    fn compute_effective(&mut self, pom_path: &Path, depth: u32) -> Option<Effective> {
        if depth > 32 {
            return None;
        }
        let raw = read_raw_pom(pom_path)?;
        let dir = pom_path.parent().unwrap_or(Path::new(".")).to_path_buf();

        let parent = raw.parent.as_ref().and_then(|p| {
            let relative = p.relative_path.as_deref().unwrap_or("../pom.xml");
            let mut local = dir.join(relative);
            if local.is_dir() {
                local = local.join("pom.xml");
            }
            let local_matches = !relative.is_empty()
                && local.is_file()
                && read_raw_pom(&local).is_some_and(|candidate| candidate.artifact == p.artifact);
            let path = if local_matches {
                local
            } else {
                self.repo_pom(&p.group, &p.artifact, &p.version)
            };
            let parent = self.effective(&path, depth + 1);
            if parent.is_none() && !local_matches && !path.is_file() {
                self.missing.insert(MissingArtifact {
                    group: p.group.clone(),
                    artifact: p.artifact.clone(),
                    version: p.version.clone(),
                    kind: "pom".to_owned(),
                    classifier: None,
                });
            }
            if parent.is_none() {
                self.messages.push(base_db::tr!(
                    "找不到父 POM {}:{}:{}（{} 需要它）",
                    "Parent POM {}:{}:{} not found (required by {})",
                    p.group,
                    p.artifact,
                    p.version,
                    pom_path.display()
                ));
            }
            parent
        });

        let mut eff = Effective {
            dir,
            artifact: raw.artifact.clone(),
            ..Effective::default()
        };
        if let Some(parent) = &parent {
            eff.properties = parent.properties.clone();
            eff.raw_deps = parent.raw_deps.clone();
            eff.raw_managed = parent.raw_managed.clone();
            eff.source_dir = parent.source_dir.clone();
            eff.test_source_dir = parent.test_source_dir.clone();
            eff.build_dir = parent.build_dir.clone();
            eff.output_dir = parent.output_dir.clone();
            eff.test_output_dir = parent.test_output_dir.clone();
            eff.raw_level = parent.raw_level.clone();
            eff.raw_release = parent.raw_release.clone();
            eff.raw_test_level = parent.raw_test_level.clone();
            eff.raw_test_release = parent.raw_test_release.clone();
            eff.raw_encoding = parent.raw_encoding.clone();
            eff.level = parent.level;
            eff.release = parent.release;
            eff.test_level = parent.test_level;
            eff.test_release = parent.test_release;
            eff.preview = parent.preview;
            eff.raw_toolchain = parent.raw_toolchain.clone();
            eff.toolchain = parent.toolchain;
        }
        eff.group = raw
            .group
            .clone()
            .or_else(|| raw.parent.as_ref().map(|p| p.group.clone()))
            .unwrap_or_default();
        eff.version = raw
            .version
            .clone()
            .or_else(|| raw.parent.as_ref().map(|p| p.version.clone()))
            .unwrap_or_default();

        for (key, value) in &raw.properties {
            eff.properties.insert(key.clone(), value.clone());
        }
        eff.version = interpolate(&eff.version, &eff.properties);
        eff.group = interpolate(&eff.group, &eff.properties);
        for prefix in ["project", "pom"] {
            eff.properties
                .insert(format!("{prefix}.groupId"), eff.group.clone());
            eff.properties
                .insert(format!("{prefix}.artifactId"), eff.artifact.clone());
            eff.properties
                .insert(format!("{prefix}.version"), eff.version.clone());
        }
        if let Some(p) = &raw.parent {
            eff.properties
                .insert("project.parent.version".into(), p.version.clone());
            eff.properties
                .insert("project.parent.groupId".into(), p.group.clone());
        }
        eff.properties.insert(
            "project.basedir".into(),
            eff.dir.to_string_lossy().into_owned(),
        );

        // 自己声明的 dependencyManagement 覆盖继承来的；BOM 只补缺（先导入的优先，子模块的在前）
        eff.raw_managed.splice(0..0, raw.managed.iter().cloned());
        let mut boms: Vec<RawDep> = Vec::new();
        for dep in &eff.raw_managed {
            let dep = interpolate_dep(dep, &eff.properties);
            if dep.kind.as_deref() == Some("pom") {
                if dep.scope.as_deref() == Some("import") {
                    boms.push(dep);
                }
                // 受管的 `<type>pom</type>` 只管同样是 pom 类型的依赖（Maven 的键里有 type）：
                // `kotlin-bom` 管理的 `kotlin-stdlib-common:pom` 不能改 jar 依赖的版本
                continue;
            }
            eff.managed
                .entry((
                    dep.group.clone(),
                    dep.artifact.clone(),
                    dep.classifier.clone(),
                ))
                .or_insert(Managed {
                    version: dep.version,
                    scope: dep.scope,
                    exclusions: dep.exclusions,
                    system_path: dep.system_path,
                });
        }
        for bom in boms {
            let Some(version) = bom
                .version
                .as_deref()
                .map(|v| self.resolve_version(&bom.group, &bom.artifact, v, ".pom"))
            else {
                continue;
            };
            let path = self.pom_for(&bom.coord(), &version);
            match self.effective(&path, depth + 1) {
                Some(imported) => {
                    for (key, managed) in &imported.managed {
                        eff.managed
                            .entry(key.clone())
                            .or_insert_with(|| managed.clone());
                    }
                }
                // 依赖库自己（或它的父 POM）导入的 BOM 只影响它没写版本号的那些传递依赖，
                // Maven 遇到这种缺件也只是跳过：不算缺件，免得为此去跑 `mvn`
                None if pom_path.starts_with(&self.repo) => {}
                None => self.note_missing(MissingArtifact {
                    group: bom.group.clone(),
                    artifact: bom.artifact.clone(),
                    version,
                    kind: "pom".to_owned(),
                    classifier: None,
                }),
            }
        }

        eff.raw_deps.extend(raw.deps.iter().cloned());
        eff.deps = eff
            .raw_deps
            .iter()
            .map(|dep| interpolate_dep(dep, &eff.properties))
            .collect();
        if let Some(dir) = &raw.source_dir {
            eff.source_dir = Some(interpolate(dir, &eff.properties));
        }
        if let Some(dir) = &raw.test_source_dir {
            eff.test_source_dir = Some(interpolate(dir, &eff.properties));
        }
        for (raw_dir, eff_dir) in [
            (&raw.build_dir, &mut eff.build_dir),
            (&raw.output_dir, &mut eff.output_dir),
            (&raw.test_output_dir, &mut eff.test_output_dir),
        ] {
            if let Some(dir) = raw_dir {
                *eff_dir = Some(interpolate(dir, &eff.properties));
            }
        }

        for (own, inherited) in [
            (&raw.compiler_level, &mut eff.raw_level),
            (&raw.compiler_release, &mut eff.raw_release),
            (&raw.compiler_test_level, &mut eff.raw_test_level),
            (&raw.compiler_test_release, &mut eff.raw_test_release),
            (&raw.compiler_encoding, &mut eff.raw_encoding),
            (&raw.toolchain_jdk, &mut eff.raw_toolchain),
        ] {
            if own.is_some() {
                inherited.clone_from(own);
            }
        }
        let level = eff
            .raw_level
            .as_deref()
            .map(|l| interpolate(l, &eff.properties))
            .or_else(|| eff.properties.get("maven.compiler.release").cloned())
            .or_else(|| eff.properties.get("maven.compiler.source").cloned())
            .or_else(|| eff.properties.get("java.version").cloned())
            .and_then(|l| parse_feature_version(&interpolate(&l, &eff.properties)));
        if level.is_some() {
            eff.level = level;
        }
        let release = eff
            .raw_release
            .as_deref()
            .map(|l| interpolate(l, &eff.properties))
            .or_else(|| eff.properties.get("maven.compiler.release").cloned())
            .and_then(|l| parse_feature_version(&interpolate(&l, &eff.properties)));
        if release.is_some() {
            eff.release = release;
        }
        let test_level = eff
            .raw_test_level
            .as_deref()
            .map(|l| interpolate(l, &eff.properties))
            .or_else(|| eff.properties.get("maven.compiler.testRelease").cloned())
            .or_else(|| eff.properties.get("maven.compiler.testSource").cloned())
            .and_then(|l| parse_feature_version(&interpolate(&l, &eff.properties)));
        if test_level.is_some() {
            eff.test_level = test_level;
        }
        let test_release = eff
            .raw_test_release
            .as_deref()
            .map(|l| interpolate(l, &eff.properties))
            .or_else(|| eff.properties.get("maven.compiler.testRelease").cloned())
            .and_then(|l| parse_feature_version(&interpolate(&l, &eff.properties)));
        if test_release.is_some() {
            eff.test_release = test_release;
        }
        // 区间（`[1.8,9)`、`[11,)`）取下界
        let toolchain = eff
            .raw_toolchain
            .as_deref()
            .and_then(|v| parse_feature_version(&interpolate(v, &eff.properties)));
        if toolchain.is_some() {
            eff.toolchain = toolchain;
        }
        let preview_property = eff
            .properties
            .get("maven.compiler.enablePreview")
            .is_some_and(|v| v == "true");
        if raw.compiler_preview == Some(true) || preview_property {
            eff.preview = true;
        }
        // 属性在继承链上合并过，子模块覆盖的值也算在内；插值不完的（引用了不知道的属性）当没设置
        eff.encoding = eff
            .raw_encoding
            .as_deref()
            .or_else(|| {
                eff.properties
                    .get("project.build.sourceEncoding")
                    .map(String::as_str)
            })
            .map(|e| interpolate(e, &eff.properties).trim().to_owned())
            .filter(|e| !e.is_empty() && !e.contains("${"));
        Some(eff)
    }

    fn note_missing(&mut self, missing: MissingArtifact) {
        self.missing_hits += 1;
        let key = format!(
            "{}:{}:{} ({})",
            missing.group,
            missing.artifact,
            missing.version,
            if missing.kind == "pom" { "pom" } else { "jar" }
        );
        if self.missing.insert(missing) {
            self.messages.push(base_db::tr!(
                "本地仓库里没有 {key}",
                "{key} is not in the local repository"
            ));
        }
    }

    /// 把 `coord` 的传递依赖按 `pending` 的 scope 和排除项放进队列。
    fn enqueue_transitives(
        &mut self,
        root: &Effective,
        coord: &Coord,
        version: &str,
        pending: &Pending,
        queue: &mut VecDeque<Pending>,
    ) {
        let pom_path = self.pom_for(coord, version);
        let Some(dep_pom) = self.effective(&pom_path, 0) else {
            return;
        };
        for transitive in &dep_pom.deps {
            if transitive.optional.as_deref().map(str::trim) == Some("true") {
                continue;
            }
            let t_coord = transitive.coord();
            if is_excluded(&pending.exclusions, &t_coord) {
                continue;
            }
            let key = (
                transitive.group.clone(),
                transitive.artifact.clone(),
                transitive.classifier.clone(),
            );
            let own_managed = dep_pom.managed.get(&key);
            let root_managed = root.managed.get(&key);
            let raw_scope = transitive
                .scope
                .as_deref()
                .or_else(|| own_managed.and_then(|m| m.scope.as_deref()));
            let child_scope = parse_scope(raw_scope);
            let Some(scope) = combine_scope(pending.scope, child_scope) else {
                continue;
            };
            // 根模块的 dependencyManagement 对传递依赖的版本同样生效
            let version = root_managed
                .and_then(|m| m.version.clone())
                .map(|v| interpolate(&v, &root.properties))
                .or_else(|| transitive.version.clone())
                .or_else(|| own_managed.and_then(|m| m.version.clone()))
                .map(|v| {
                    let v = interpolate(&v, &dep_pom.properties);
                    let suffix = artifact_suffix(transitive);
                    self.resolve_version(&transitive.group, &transitive.artifact, &v, &suffix)
                });
            let Some(version) = version else { continue };

            let mut exclusions = (*pending.exclusions).clone();
            exclusions.extend(transitive.exclusions.iter().cloned());
            // 依赖库自己的 dependencyManagement 里写的排除项也合进它的依赖声明（Maven 注入受管信息时
            // 一并带上）：`velocity-tools` 管理 `commons-digester3` 时排除了 `cglib`
            if let Some(managed) = own_managed {
                exclusions.extend(managed.exclusions.iter().cloned());
            }
            if let Some(managed) = root_managed {
                exclusions.extend(managed.exclusions.iter().cloned());
            }
            let system_path = system_path(
                raw_scope,
                transitive.system_path.as_deref(),
                own_managed,
                &dep_pom.properties,
            );
            queue.push_back(Pending {
                dep: transitive.clone(),
                version,
                scope,
                exclusions: Arc::new(exclusions),
                direct: false,
                system_path,
            });
        }
    }

    /// 解析一个模块的传递依赖闭包（广度优先，最近者优先）。
    fn resolve_dependencies(&mut self, root: &Effective) -> Vec<ResolvedDep> {
        let mut result: Vec<ResolvedDep> = Vec::new();
        let mut seen: FxHashMap<ManagedKey, Seen> = FxHashMap::default();
        let mut queue: VecDeque<Pending> = VecDeque::new();

        for dep in &root.deps {
            let key = (
                dep.group.clone(),
                dep.artifact.clone(),
                dep.classifier.clone(),
            );
            let managed = root.managed.get(&key);
            let Some(version) = dep
                .version
                .clone()
                .or_else(|| managed.and_then(|m| m.version.clone()))
                .map(|v| {
                    let v = interpolate(&v, &root.properties);
                    let suffix = artifact_suffix(dep);
                    self.resolve_version(&dep.group, &dep.artifact, &v, &suffix)
                })
            else {
                self.messages.push(base_db::tr!(
                    "{}:{} 没有版本号（{}）",
                    "{}:{} has no version ({})",
                    dep.group,
                    dep.artifact,
                    root.artifact
                ));
                continue;
            };
            let raw_scope = dep
                .scope
                .as_deref()
                .or_else(|| managed.and_then(|m| m.scope.as_deref()));
            let scope = parse_scope(raw_scope);
            let system_path = system_path(
                raw_scope,
                dep.system_path.as_deref(),
                managed,
                &root.properties,
            );
            let mut exclusions = dep.exclusions.clone();
            if let Some(managed) = managed {
                exclusions.extend(managed.exclusions.iter().cloned());
            }
            queue.push_back(Pending {
                dep: dep.clone(),
                version,
                scope,
                exclusions: Arc::new(exclusions),
                direct: true,
                system_path,
            });
        }

        while let Some(pending) = queue.pop_front() {
            let coord = pending.dep.coord();
            let kind = pending.dep.kind.as_deref().unwrap_or("jar");
            // `test-jar` 和同一模块的普通依赖是两个不同的构件
            let key = (
                coord.group.clone(),
                coord.artifact.clone(),
                pending
                    .dep
                    .classifier
                    .clone()
                    .or_else(|| (kind == "test-jar").then(|| "tests".to_owned())),
            );
            // 同一个构件经由多条路径到达：版本取最近的那条（先到先得），scope 取最宽的
            // （按 Maven 的顺序 compile > runtime > provided > test），模块直接声明的依赖除外：
            // 它的 scope 就是写的那个，不随传递依赖变宽。
            // 变宽时它的传递依赖也要按新的 scope 再走一遍，和 Maven 一样沿用胜出那条路径上的
            // 排除项：变宽的那条路径排除掉的依赖照样跟着变宽
            if let Some(seen) = seen.get_mut(&key) {
                if seen.direct || maven_scope_rank(pending.scope) <= maven_scope_rank(seen.scope) {
                    continue;
                }
                seen.scope = pending.scope;
                if let Some(index) = seen.index {
                    result[index].set_scope(pending.scope);
                }
                let version = match seen.index.and_then(|i| result.get(i)) {
                    Some(ResolvedDep::Library { version, .. }) => version.clone(),
                    _ => pending.version.clone(),
                };
                let winner = Pending {
                    exclusions: seen.exclusions.clone(),
                    ..pending
                };
                self.enqueue_transitives(root, &coord, &version, &winner, &mut queue);
                continue;
            }
            let index_before = result.len();

            if let Some(jar) = &pending.system_path {
                // `system` 依赖直接用磁盘上的 jar，不去本地仓库找，也不展开它的依赖
                if jar.is_file() {
                    result.push(ResolvedDep::Library {
                        name: format!("{}:{}:{}", coord.group, coord.artifact, pending.version),
                        jar: jar.clone(),
                        sources: None,
                        scope: pending.scope,
                        version: pending.version.clone(),
                    });
                }
                seen.insert(
                    key,
                    Seen {
                        index: (result.len() > index_before).then_some(index_before),
                        scope: pending.scope,
                        exclusions: pending.exclusions.clone(),
                        direct: pending.direct,
                    },
                );
                continue;
            } else if let Some(pom) = self.reactor.get(&coord).cloned() {
                // `<type>test-jar</type>` 和 `<classifier>tests</classifier>` 都是测试代码的 jar
                let test_jar =
                    kind == "test-jar" || pending.dep.classifier.as_deref() == Some("tests");
                result.push(ResolvedDep::Module {
                    pom,
                    scope: pending.scope,
                    test_jar,
                });
            } else if kind != "pom" {
                let dir = self.artifact_dir(&coord.group, &coord.artifact, &pending.version);
                let stem = format!("{}-{}", coord.artifact, pending.version);
                let suffix = artifact_suffix(&pending.dep);
                let file = dir.join(format!("{stem}{suffix}"));
                if file.is_file() {
                    if suffix.ends_with(".jar") {
                        let sources = dir.join(format!("{stem}-sources.jar"));
                        result.push(ResolvedDep::Library {
                            name: format!("{}:{}:{}", coord.group, coord.artifact, pending.version),
                            jar: file,
                            sources: sources.is_file().then_some(sources),
                            scope: pending.scope,
                            version: pending.version.clone(),
                        });
                    }
                } else {
                    self.note_missing(MissingArtifact {
                        group: coord.group.clone(),
                        artifact: coord.artifact.clone(),
                        version: pending.version.clone(),
                        kind: kind.to_owned(),
                        classifier: pending.dep.classifier.clone(),
                    });
                    result.push(ResolvedDep::Missing {
                        group: coord.group.clone(),
                        artifact: coord.artifact.clone(),
                        scope: pending.scope,
                    });
                }
            }

            seen.insert(
                key,
                Seen {
                    index: (result.len() > index_before).then_some(index_before),
                    scope: pending.scope,
                    exclusions: pending.exclusions.clone(),
                    direct: pending.direct,
                },
            );
            self.enqueue_transitives(root, &coord, &pending.version, &pending, &mut queue);
        }
        result
    }
}

/// 依赖在本地仓库里的文件名去掉 `{artifact}-{version}` 之后的部分：`.pom`、`.jar`、`-tests.jar`、`.war`、`.zip`……
/// 只有已知的非 jar 归档类型按类型名取扩展名，未知类型（如 `hk2-jar`、`bundle`）照旧按 `.jar` 查找。
fn artifact_suffix(dep: &RawDep) -> String {
    let kind = dep.kind.as_deref().unwrap_or("jar");
    let ext = match kind {
        "pom" => return ".pom".to_owned(),
        "war" | "ear" | "rar" | "zip" | "tar.gz" | "tgz" | "aar" => kind,
        _ => "jar",
    };
    match (&dep.classifier, kind) {
        (Some(c), _) => format!("-{c}.{ext}"),
        (None, "test-jar") => "-tests.jar".to_owned(),
        _ => format!(".{ext}"),
    }
}

struct Pending {
    dep: RawDep,
    version: String,
    scope: Scope,
    exclusions: Arc<Vec<Coord>>,
    /// 模块自己声明的依赖（不是传递来的）
    direct: bool,
    /// `system` scope 的依赖：`<systemPath>` 插值后的路径
    system_path: Option<PathBuf>,
}

/// `system` scope 依赖的 jar：取依赖声明或受管声明里的 `<systemPath>`。
fn system_path(
    raw_scope: Option<&str>,
    declared: Option<&str>,
    managed: Option<&Managed>,
    properties: &FxHashMap<String, String>,
) -> Option<PathBuf> {
    if raw_scope.map(|s| interpolate(s, properties)).as_deref() != Some("system") {
        return None;
    }
    let path = declared.or_else(|| managed.and_then(|m| m.system_path.as_deref()))?;
    Some(PathBuf::from(interpolate(path, properties)))
}

/// 解析时已经处理过的构件。
struct Seen {
    /// 它在结果里的下标（没有进结果的为 `None`）
    index: Option<usize>,
    /// 目前的 scope
    scope: Scope,
    /// 最先到达（也就是胜出）的那条路径上的排除项
    exclusions: Arc<Vec<Coord>>,
    /// 模块直接声明的依赖
    direct: bool,
}

enum ResolvedDep {
    Module {
        pom: PathBuf,
        scope: Scope,
        /// `<type>test-jar</type>`：依赖的是这个模块的测试代码
        test_jar: bool,
    },
    Library {
        name: String,
        jar: PathBuf,
        sources: Option<PathBuf>,
        scope: Scope,
        version: String,
    },
    /// 本地仓库里没有的 jar
    Missing {
        group: String,
        artifact: String,
        scope: Scope,
    },
}

impl ResolvedDep {
    fn set_scope(&mut self, new: Scope) {
        match self {
            ResolvedDep::Module { scope, .. }
            | ResolvedDep::Library { scope, .. }
            | ResolvedDep::Missing { scope, .. } => *scope = new,
        }
    }
}

/// scope 覆盖的范围由窄到宽：只在测试里可见 < 不参与编译主代码的运行期 / 容器提供 < 编译期。
pub(crate) fn scope_rank(scope: Scope) -> u8 {
    match scope {
        Scope::Test => 0,
        Scope::Runtime => 1,
        Scope::Provided => 2,
        Scope::Compile => 3,
    }
}

/// 同一个构件经由几条路径到达时 Maven 取哪个 scope：compile > runtime > provided > test。
/// 和 [`scope_rank`] 不同，runtime 排在 provided 前面：既是 runtime 又是 provided 的依赖
/// 在 Maven 里是 runtime 的，在运行时类路径上。
fn maven_scope_rank(scope: Scope) -> u8 {
    match scope {
        Scope::Test => 0,
        Scope::Provided => 1,
        Scope::Runtime => 2,
        Scope::Compile => 3,
    }
}

/// 收集 reactor 里所有模块的 pom.xml（根在前）。
fn collect_reactor(pom_path: &Path, out: &mut Vec<PathBuf>) {
    if out.iter().any(|p| p == pom_path) || out.len() > 2000 {
        return;
    }
    let Some(raw) = read_raw_pom(pom_path) else {
        return;
    };
    out.push(pom_path.to_path_buf());
    let dir = pom_path.parent().unwrap_or(Path::new("."));
    for module in &raw.modules {
        let mut path = dir.join(module);
        if path.is_dir() {
            path = path.join("pom.xml");
        }
        if path.is_file() {
            collect_reactor(&path, out);
        }
    }
}

fn source_roots(eff: &Effective) -> Vec<SourceRoot> {
    let resolve = |configured: &Option<String>, default: &str| {
        let path = PathBuf::from(configured.as_deref().unwrap_or(default));
        if path.is_absolute() {
            path
        } else {
            eff.dir.join(path)
        }
    };
    let mut roots = vec![
        SourceRoot {
            path: resolve(&eff.source_dir, "src/main/java"),
            kind: SourceRootKind::Main,
        },
        SourceRoot {
            path: resolve(&eff.test_source_dir, "src/test/java"),
            kind: SourceRootKind::Test,
        },
    ];
    // 注解处理器等生成的源码
    for generated in ["target/generated-sources", "target/generated-test-sources"] {
        if let Ok(entries) = std::fs::read_dir(eff.dir.join(generated)) {
            for entry in entries.flatten() {
                if entry.path().is_dir() {
                    roots.push(SourceRoot {
                        path: entry.path(),
                        kind: SourceRootKind::Generated,
                    });
                }
            }
        }
    }
    roots.retain(|root| root.path.is_dir());
    roots
}

/// 编译输出目录：默认 `target/classes` 和 `target/test-classes`，可被 `<build>` 里的配置覆盖。
fn output_dirs(eff: &Effective) -> Vec<SourceRoot> {
    let absolute = |path: String| {
        let path = PathBuf::from(path);
        if path.is_absolute() {
            path
        } else {
            eff.dir.join(path)
        }
    };
    let basedir = eff.dir.to_string_lossy().into_owned();
    let expand = |value: &str| {
        value
            .replace("${project.basedir}", &basedir)
            .replace("${basedir}", &basedir)
    };
    let build_dir = absolute(expand(eff.build_dir.as_deref().unwrap_or("target")));
    let build_dir_text = build_dir.to_string_lossy().into_owned();
    let resolve = |configured: &Option<String>, default: &str| match configured {
        Some(dir) => absolute(expand(dir).replace("${project.build.directory}", &build_dir_text)),
        None => build_dir.join(default),
    };
    vec![
        SourceRoot {
            path: resolve(&eff.output_dir, "classes"),
            kind: SourceRootKind::Main,
        },
        SourceRoot {
            path: resolve(&eff.test_output_dir, "test-classes"),
            kind: SourceRootKind::Test,
        },
    ]
}

/// reactor 级的 `mvn` 让每个模块把依赖列表写到这里（相对模块目录）。
const DEPENDENCY_LIST_FILE: &str = "target/java-analyzer-dependencies.txt";

/// `mvn dependency:list` 列出的一个依赖。
#[derive(Clone, Debug, PartialEq, Eq)]
struct ListedDependency {
    group: String,
    artifact: String,
    /// `jar`、`test-jar`、`pom`……
    kind: String,
    classifier: Option<String>,
    version: String,
    scope: Scope,
    /// 解析到的文件；Maven 没有给出时为 `None`
    file: Option<PathBuf>,
}

fn parse_list_scope(scope: &str) -> Option<Scope> {
    Some(match scope {
        "compile" => Scope::Compile,
        "provided" => Scope::Provided,
        // `system` 和 `compile` 一样进编译和运行类路径，只是 jar 由 `<systemPath>` 指定
        "system" => Scope::Compile,
        "runtime" => Scope::Runtime,
        "test" => Scope::Test,
        _ => return None,
    })
}

/// 解析 `dependency:list -DoutputAbsoluteArtifactFilename=true` 的输出：每行是
/// `group:artifact:type[:classifier]:version:scope:/abs/path`，后面可能跟着 ` (optional)` 和
/// ` -- module 名字`。路径里可以有冒号（Windows 的盘符）。
fn parse_dependency_list(text: &str) -> Vec<ListedDependency> {
    text.lines().filter_map(parse_listed_dependency).collect()
}

fn parse_listed_dependency(line: &str) -> Option<ListedDependency> {
    let mut line = line.trim();
    if let Some(at) = line.find(" -- module ") {
        line = &line[..at];
    }
    let line = line.strip_suffix(" (optional)").unwrap_or(line).trim_end();
    let parts: Vec<&str> = line.splitn(7, ':').collect();
    let (classifier, version, scope_at) =
        if parts.len() >= 5 && parse_list_scope(parts[4]).is_some() {
            (None, parts[3], 4)
        } else if parts.len() >= 6 && parse_list_scope(parts[5]).is_some() {
            (Some(parts[3]), parts[4], 5)
        } else {
            return None;
        };
    if parts[..scope_at]
        .iter()
        .any(|p| p.is_empty() || p.contains(' '))
    {
        return None;
    }
    let file = line
        .splitn(scope_at + 2, ':')
        .nth(scope_at + 1)
        .map(str::trim)
        .filter(|f| !f.is_empty() && *f != "null")
        .map(PathBuf::from);
    Some(ListedDependency {
        group: parts[0].to_owned(),
        artifact: parts[1].to_owned(),
        kind: parts[2].to_owned(),
        classifier: classifier.map(str::to_owned),
        version: version.to_owned(),
        scope: parse_list_scope(parts[scope_at])?,
        file,
    })
}

/// 在整个 reactor 上运行一次 Maven，让它自己解析各模块的依赖（会联网下载缺失的构件）。
/// 返回模块目录 → 依赖列表（已经是仲裁过的完整传递闭包）；Maven 没有给出结果的模块不在里面。
fn reactor_dependency_lists(
    root_pom: &Path,
    module_dirs: &[PathBuf],
    setup: &ResolvedSetup,
) -> FxHashMap<PathBuf, Vec<ListedDependency>> {
    for dir in module_dirs {
        let _ = std::fs::remove_file(dir.join(DEPENDENCY_LIST_FILE));
    }
    let root_dir = root_pom.parent().unwrap_or(Path::new("."));
    // 相对路径的输出文件按各模块的目录解析：一次调用给出每个模块的结果；
    // `-fae`：一个模块失败了也接着算其他模块
    run_maven(
        maven_command(root_dir, setup)
            .arg("-q")
            .arg("-B")
            .arg("-fae")
            .arg("-f")
            .arg(root_pom)
            .arg("dependency:list")
            .arg("-DoutputAbsoluteArtifactFilename=true")
            .arg("-DappendOutput=false")
            .arg(format!("-DoutputFile={DEPENDENCY_LIST_FILE}")),
        "本地仓库里还缺构件，让 Maven 解析各模块的依赖",
    );
    let mut result = FxHashMap::default();
    for dir in module_dirs {
        let file = dir.join(DEPENDENCY_LIST_FILE);
        let Ok(content) = std::fs::read_to_string(&file) else {
            continue;
        };
        let _ = std::fs::remove_file(&file);
        result.insert(dir.clone(), parse_dependency_list(&content));
    }
    result
}

/// 补下载缺件最多跑几轮：每轮只下载已知缺的构件本身，它们的 POM 到手后才知道下一层缺什么
const MAX_FETCH_ROUNDS: usize = 12;

/// 本进程里交给 Maven 下载过、却还是缺的构件，按 [`ResolvedSetup::key`] 分开。
/// 重新导入（改了 POM、配置变了 …）时不再为它们运行 Maven：下载不到的构件每次都下载不到，
/// 每次导入都跑一遍 Maven 只是白白多花几十秒。换了本地仓库或设置文件时重新尝试。
static FAILED_FETCHES: LazyLock<Mutex<FxHashSet<(String, MissingArtifact)>>> =
    LazyLock::new(Default::default);

/// 本进程里 reactor 级 `mvn` 解析出的依赖：键是（根 POM，设置），值是当时缺的构件和结果。
/// 缺的构件没变时直接复用，不再运行 Maven。
type DependencyLists = FxHashMap<PathBuf, Vec<ListedDependency>>;
type DependencyListCache = FxHashMap<(PathBuf, String), (Vec<MissingArtifact>, DependencyLists)>;
static DEPENDENCY_LIST_CACHE: LazyLock<Mutex<DependencyListCache>> =
    LazyLock::new(Default::default);

fn sorted_missing(missing: &FxHashSet<MissingArtifact>) -> Vec<MissingArtifact> {
    let mut list: Vec<MissingArtifact> = missing.iter().cloned().collect();
    list.sort_by(|a, b| {
        (&a.group, &a.artifact, &a.version, &a.kind, &a.classifier).cmp(&(
            &b.group,
            &b.artifact,
            &b.version,
            &b.kind,
            &b.classifier,
        ))
    });
    list
}

/// 导入以 `root_pom` 为根的 Maven 工程。
///
/// 本地仓库里构件齐全时不运行 Maven。`use_cli` 为真时，本地仓库缺的构件交给 `mvn` 下载后重新解析；
/// 还缺的话再在整个 reactor 上运行一次 `mvn` 解析依赖。
/// `jdk_version` 是导入时用的 JDK 的特性版本号，按 `<activation><jdk>` 激活 profile 时用。
pub fn import(root_pom: &Path, use_cli: bool, jdk_version: Option<u32>) -> Option<MavenImport> {
    import_with(root_pom, use_cli, jdk_version, &resolved_setup())
}

fn import_with(
    root_pom: &Path,
    use_cli: bool,
    jdk_version: Option<u32>,
    setup: &ResolvedSetup,
) -> Option<MavenImport> {
    ACTIVATION_JDK.with(|v| v.set(jdk_version));
    let start = Instant::now();
    let mut poms = Vec::new();
    collect_reactor(root_pom, &mut poms);
    if poms.is_empty() {
        return None;
    }
    let repo = &setup.repo;
    let (import, mut missing) = import_once(&poms, repo, None);
    tracing::info!(
        "Maven 工程 {}：{} 个模块，本地仓库 {}，静态解析用时 {} ms，缺 {} 个构件",
        root_pom.display(),
        poms.len(),
        repo.display(),
        start.elapsed().as_millis(),
        missing.len()
    );
    if missing.is_empty() {
        return Some(import);
    }
    if !use_cli {
        tracing::info!("maven.useCli 已关闭，不运行 Maven 下载缺件");
        return Some(import);
    }
    // 不能直接在模块目录里让 Maven 解析依赖：兄弟模块没有 install 到本地仓库时整个解析都会失败。
    // 这里的解析结果已经是 Maven 会选的那些版本，把缺的构件逐个交给 Maven 下载就行
    let key = setup.key();
    let mut requested: FxHashSet<MissingArtifact> = FAILED_FETCHES
        .lock()
        .map(|set| {
            set.iter()
                .filter(|(k, _)| *k == key)
                .map(|(_, m)| m.clone())
                .collect()
        })
        .unwrap_or_default();
    let repositories = reactor_repositories(&poms);
    let mut fetched_any = false;
    for _ in 0..MAX_FETCH_ROUNDS {
        let mut batch: Vec<MissingArtifact> = missing
            .iter()
            .filter(|m| !requested.contains(*m))
            .cloned()
            .collect();
        if batch.is_empty() {
            break;
        }
        batch.sort_by(|a, b| {
            (&a.group, &a.artifact, &a.version).cmp(&(&b.group, &b.artifact, &b.version))
        });
        tracing::info!(
            "让 Maven 下载 {} 个缺件，例如 {}:{}:{}",
            batch.len(),
            batch[0].group,
            batch[0].artifact,
            batch[0].version
        );
        fetch_artifacts(root_pom, &batch, &repositories, setup);
        fetched_any = true;
        requested.extend(batch);
        let (import, now_missing) = import_once(&poms, repo, None);
        if now_missing.is_empty() {
            tracing::info!(
                "Maven 工程 {} 导入完成，用时 {} ms",
                root_pom.display(),
                start.elapsed().as_millis()
            );
            return Some(import);
        }
        missing = now_missing;
    }
    if let Ok(mut set) = FAILED_FETCHES.lock() {
        for artifact in missing.iter().filter(|m| requested.contains(*m)) {
            set.insert((key.clone(), artifact.clone()));
        }
    }
    if !fetched_any {
        tracing::info!(
            "缺的 {} 个构件本次运行里已经让 Maven 下载过、没有下载到，不再为它们运行 Maven 下载",
            missing.len()
        );
    }

    let snapshot = sorted_missing(&missing);
    let cache_key = (root_pom.to_path_buf(), key);
    let cached = DEPENDENCY_LIST_CACHE.lock().ok().and_then(|cache| {
        cache
            .get(&cache_key)
            .filter(|(was_missing, _)| *was_missing == snapshot)
            .map(|(_, lists)| lists.clone())
    });
    let lists = match cached {
        Some(lists) => {
            tracing::info!("缺的构件和上次导入时一样，沿用上次 Maven 解析出的依赖");
            lists
        }
        None => {
            let module_dirs: Vec<PathBuf> = poms
                .iter()
                .map(|p| p.parent().unwrap_or(Path::new(".")).to_path_buf())
                .collect();
            let lists = reactor_dependency_lists(root_pom, &module_dirs, setup);
            if let Ok(mut cache) = DEPENDENCY_LIST_CACHE.lock() {
                cache.insert(cache_key, (snapshot, lists.clone()));
            }
            lists
        }
    };
    let (import, _) = import_once(&poms, repo, Some(&lists));
    tracing::info!(
        "Maven 工程 {} 导入完成，用时 {} ms",
        root_pom.display(),
        start.elapsed().as_millis()
    );
    Some(import)
}

/// reactor 里各个 POM 声明的远程仓库（去重）。
fn reactor_repositories(poms: &[PathBuf]) -> Vec<(String, String)> {
    let mut repositories: Vec<(String, String)> = Vec::new();
    for raw in poms.iter().filter_map(|p| read_raw_pom(p)) {
        for repository in raw.repositories {
            if !repositories.iter().any(|(id, _)| *id == repository.0) {
                repositories.push(repository);
            }
        }
    }
    repositories
}

fn xml_escape(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

/// 把缺件分成几组，每组里同一个构件（groupId、artifactId、type、classifier）只出现一次：
/// 同一个 POM 里重复声明的依赖 Maven 只保留最后一个，不同模块要的不同版本得分开下载。
fn fetch_groups(artifacts: &[MissingArtifact]) -> Vec<Vec<&MissingArtifact>> {
    let mut groups: Vec<Vec<&MissingArtifact>> = Vec::new();
    for artifact in artifacts {
        let same = |other: &&MissingArtifact| {
            other.group == artifact.group
                && other.artifact == artifact.artifact
                && other.kind == artifact.kind
                && other.classifier == artifact.classifier
        };
        match groups.iter_mut().find(|group| !group.iter().any(same)) {
            Some(group) => group.push(artifact),
            None => groups.push(vec![artifact]),
        }
    }
    groups
}

const POM_HEADER: &str = "<project xmlns=\"http://maven.apache.org/POM/4.0.0\">\n\
     <modelVersion>4.0.0</modelVersion>\n\
     <groupId>java-analyzer</groupId>\n";

/// 下载用的临时 POM：每个缺件是一个排除了全部传递依赖的直接依赖，
/// Maven 只下载它们本身（和解析它们时要读的 POM），版本不会被它自己的仲裁改掉。
fn fetch_pom(
    artifact_id: &str,
    artifacts: &[&MissingArtifact],
    repositories: &[(String, String)],
) -> String {
    let mut pom = format!(
        "{POM_HEADER}<artifactId>{artifact_id}</artifactId>\n\
         <version>1</version>\n\
         <packaging>pom</packaging>\n"
    );
    if !repositories.is_empty() {
        pom.push_str("<repositories>\n");
        for (id, url) in repositories {
            pom.push_str(&format!(
                "<repository><id>{}</id><url>{}</url></repository>\n",
                xml_escape(id),
                xml_escape(url)
            ));
        }
        pom.push_str("</repositories>\n");
    }
    pom.push_str("<dependencies>\n");
    for artifact in artifacts {
        pom.push_str(&format!(
            "<dependency><groupId>{}</groupId><artifactId>{}</artifactId><version>{}</version><type>{}</type>",
            xml_escape(&artifact.group),
            xml_escape(&artifact.artifact),
            xml_escape(&artifact.version),
            xml_escape(&artifact.kind)
        ));
        if let Some(classifier) = &artifact.classifier {
            pom.push_str(&format!(
                "<classifier>{}</classifier>",
                xml_escape(classifier)
            ));
        }
        pom.push_str(
            "<exclusions><exclusion><groupId>*</groupId><artifactId>*</artifactId></exclusion></exclusions></dependency>\n",
        );
    }
    pom.push_str("</dependencies>\n</project>\n");
    pom
}

/// 让 Maven 把 `artifacts` 下载进本地仓库。
fn fetch_artifacts(
    root_pom: &Path,
    artifacts: &[MissingArtifact],
    repositories: &[(String, String)],
    setup: &ResolvedSetup,
) {
    let root_dir = root_pom.parent().unwrap_or(Path::new("."));
    let dir = std::env::temp_dir().join(format!(
        "java-analyzer-fetch-{}-{}",
        std::process::id(),
        FETCH_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    let pom = dir.join("pom.xml");
    let groups = fetch_groups(artifacts);
    let written = if let [group] = groups.as_slice() {
        write_file(&pom, &fetch_pom("fetch", group, repositories))
    } else {
        // 分成几组时用一个聚合工程，一次 Maven 调用下载完
        let mut modules = String::new();
        let mut written = true;
        for (i, group) in groups.iter().enumerate() {
            let name = format!("fetch-{i}");
            modules.push_str(&format!("<module>{name}</module>"));
            written &= write_file(
                &dir.join(&name).join("pom.xml"),
                &fetch_pom(&name, group, repositories),
            );
        }
        written
            && write_file(
                &pom,
                &format!(
                    "{POM_HEADER}<artifactId>fetch</artifactId><version>1</version>\
                     <packaging>pom</packaging><modules>{modules}</modules></project>\n"
                ),
            )
    };
    if written {
        // 其中有下载不到的构件时 Maven 会报错，但能下载的那些已经放进了本地仓库；
        // `-fae`：一组失败了也接着下载其他组
        let reason = format!("本地仓库里缺 {} 个构件，让 Maven 下载", artifacts.len());
        run_maven(
            maven_command(root_dir, setup)
                .arg("-q")
                .arg("-B")
                .arg("-fae")
                .arg("-f")
                .arg(&pom)
                .arg("dependency:resolve"),
            &reason,
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

fn write_file(path: &Path, text: &str) -> bool {
    path.parent()
        .is_some_and(|dir| std::fs::create_dir_all(dir).is_ok())
        && std::fs::write(path, text).is_ok()
}

static FETCH_COUNTER: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

/// 静态解析一遍：本地仓库里有什么就用什么。`cli_lists` 是 Maven 解析出的各模块依赖
/// （模块目录 → 依赖列表），有缺件的模块改用它。
fn import_once(
    poms: &[PathBuf],
    repo: &Path,
    cli_lists: Option<&DependencyLists>,
) -> (MavenImport, FxHashSet<MissingArtifact>) {
    let mut resolver = Resolver {
        repo: repo.to_path_buf(),
        reactor: FxHashMap::default(),
        cache: FxHashMap::default(),
        messages: Vec::new(),
        missing: FxHashSet::default(),
        missing_hits: 0,
    };
    for pom in poms {
        if let Some(raw) = read_raw_pom(pom) {
            let group = raw
                .group
                .or_else(|| raw.parent.map(|p| p.group))
                .unwrap_or_default();
            resolver.reactor.insert(
                Coord {
                    group,
                    artifact: raw.artifact,
                },
                pom.clone(),
            );
        }
    }

    let module_index: FxHashMap<&Path, ModuleId> = poms
        .iter()
        .enumerate()
        .map(|(i, p)| (p.as_path(), ModuleId(i as u32)))
        .collect();

    // Eclipse 插件按符号名互相依赖：符号名（没有清单时用 artifactId）→ 模块
    let mut bundle_modules: FxHashMap<String, ModuleId> = FxHashMap::default();
    for (idx, pom) in poms.iter().enumerate() {
        let dir = pom.parent().unwrap_or(Path::new("."));
        let name = crate::eclipse::symbolic_name(dir)
            .or_else(|| read_raw_pom(pom).map(|raw| raw.artifact));
        if let Some(name) = name {
            bundle_modules.entry(name).or_insert(ModuleId(idx as u32));
        }
    }

    let mut import = MavenImport::default();
    let mut library_ids: FxHashMap<PathBuf, LibraryId> = FxHashMap::default();
    let mut add_library = |import: &mut MavenImport, name: String, jar: PathBuf, sources| {
        *library_ids.entry(jar.clone()).or_insert_with(|| {
            import.libraries.push(LibraryData { name, jar, sources });
            LibraryId((import.libraries.len() - 1) as u32)
        })
    };

    // 以 Require-Bundle 依赖了别的工作区插件的模块：插件之间的依赖没有展开传递依赖
    let mut bundle_users: Vec<ModuleId> = Vec::new();
    for pom in poms {
        let missing_before = resolver.missing_hits;
        let Some(eff) = resolver.effective(pom, 0) else {
            // 保持模块下标与 poms 对齐
            import.modules.push(ModuleData {
                name: pom.display().to_string(),
                root: pom.parent().unwrap_or(Path::new(".")).to_path_buf(),
                source_roots: Vec::new(),
                language_level: None,
                test_language_level: None,
                api_release: None,
                preview: false,
                dependencies: Vec::new(),
                output_dirs: Vec::new(),
                encoding: None,
                transitive_dependencies: false,
            });
            continue;
        };
        let mut dependencies = Vec::new();
        let resolved = resolver.resolve_dependencies(&eff);
        let module_missing = resolver.missing_hits > missing_before;
        let listed = cli_lists
            .filter(|_| module_missing)
            .map(|lists| lists.get(&eff.dir));
        if let Some(Some(listed)) = listed {
            // Maven 解析出的依赖是完整的、仲裁过的，代替静态解析的结果
            let this = module_index.get(pom.as_path()).copied();
            for dep in listed {
                let coord = Coord {
                    group: dep.group.clone(),
                    artifact: dep.artifact.clone(),
                };
                let target = if let Some(module_pom) = resolver.reactor.get(&coord) {
                    let Some(&id) = module_index.get(module_pom.as_path()) else {
                        continue;
                    };
                    if Some(id) == this {
                        continue;
                    }
                    if dep.kind == "test-jar" || dep.classifier.as_deref() == Some("tests") {
                        DependencyTarget::ModuleTests(id)
                    } else {
                        DependencyTarget::Module(id)
                    }
                } else {
                    let Some(jar) = dep.file.clone().filter(|f| f.is_file()) else {
                        continue;
                    };
                    let sources =
                        jar.with_file_name(format!("{}-{}-sources.jar", dep.artifact, dep.version));
                    let name = format!("{}:{}:{}", dep.group, dep.artifact, dep.version);
                    DependencyTarget::Library(add_library(
                        &mut import,
                        name,
                        jar,
                        sources.is_file().then_some(sources),
                    ))
                };
                match dependencies
                    .iter_mut()
                    .find(|d: &&mut Dependency| d.target == target)
                {
                    Some(existing) => {
                        if scope_rank(dep.scope) > scope_rank(existing.scope) {
                            existing.scope = dep.scope;
                        }
                    }
                    None => dependencies.push(Dependency {
                        target,
                        scope: dep.scope,
                    }),
                }
            }
        }
        if let Some(None) = listed {
            resolver.messages.push(base_db::tr!(
                "调用 mvn 解析 {} 的依赖失败",
                "Running mvn to resolve the dependencies of {} failed",
                eff.artifact
            ));
        }
        for dep in resolved
            .into_iter()
            .filter(|_| !matches!(listed, Some(Some(_))))
        {
            match dep {
                ResolvedDep::Module {
                    pom,
                    scope,
                    test_jar,
                } => {
                    if let Some(&id) = module_index.get(pom.as_path()) {
                        dependencies.push(Dependency {
                            target: if test_jar {
                                DependencyTarget::ModuleTests(id)
                            } else {
                                DependencyTarget::Module(id)
                            },
                            scope,
                        });
                    }
                }
                ResolvedDep::Library {
                    name,
                    jar,
                    sources,
                    scope,
                    ..
                } => {
                    let id = add_library(&mut import, name, jar, sources);
                    dependencies.push(Dependency {
                        target: DependencyTarget::Library(id),
                        scope,
                    });
                }
                ResolvedDep::Missing {
                    group,
                    artifact,
                    scope,
                } => import.unresolved.push(crate::UnresolvedDep {
                    module: ModuleId(import.modules.len() as u32),
                    group,
                    artifact,
                    scope,
                }),
            }
        }

        // Eclipse 插件（Tycho）的依赖写在 MANIFEST.MF 里
        let mut missing_bundles: Vec<String> = Vec::new();
        for bundle in crate::eclipse::required_bundles(&eff.dir) {
            let target = match bundle_modules.get(&bundle) {
                Some(&id) if Some(&id) == module_index.get(pom.as_path()) => None,
                Some(&id) => Some(DependencyTarget::Module(id)),
                None => crate::eclipse::p2_bundle_jar(&resolver.repo, &bundle).map(|jar| {
                    let name = jar
                        .file_stem()
                        .map(|n| n.to_string_lossy().into_owned())
                        .unwrap_or_else(|| bundle.clone());
                    DependencyTarget::Library(add_library(&mut import, name, jar, None))
                }),
            };
            match target {
                Some(target) => {
                    if matches!(target, DependencyTarget::Module(_)) {
                        bundle_users.push(ModuleId(import.modules.len() as u32));
                    }
                    if !dependencies.iter().any(|d: &Dependency| d.target == target) {
                        dependencies.push(Dependency {
                            target,
                            scope: Scope::Compile,
                        });
                    }
                }
                None if !bundle_modules.contains_key(&bundle) => missing_bundles.push(bundle),
                None => {}
            }
        }
        if !missing_bundles.is_empty() {
            resolver.messages.push(base_db::tr!(
                "{} 依赖的插件不在本地仓库的 p2 缓存里（先用 Tycho 构建一次）：{}",
                "Plug-ins required by {} are not in the local repository's p2 cache (build once with Tycho): {}",
                eff.artifact,
                missing_bundles.join(", ")
            ));
        }

        let mut roots = source_roots(&eff);
        for root in crate::eclipse::source_roots(&eff.dir) {
            if !roots.iter().any(|r| r.path == root.path) {
                roots.push(root);
            }
        }
        import.toolchain_jdk = import.toolchain_jdk.max(eff.toolchain);
        import.modules.push(ModuleData {
            name: eff.artifact.clone(),
            root: eff.dir.clone(),
            source_roots: roots,
            language_level: eff.level,
            test_language_level: eff.test_level,
            // JDK 的 API 整个工作区共用一份：测试代码用更高的 `--release` 编译时放宽到它
            api_release: match (eff.release, eff.test_release) {
                (Some(main), Some(test)) => Some(main.max(test)),
                (release, _) => release,
            },
            preview: eff.preview,
            dependencies,
            output_dirs: output_dirs(&eff),
            encoding: eff.encoding.clone(),
            transitive_dependencies: true,
        });
    }

    // 是否 `visibility:=reexport` 没有区分，宽松地按传递依赖处理
    bundle_users.dedup();
    crate::inherit_module_dependencies(&mut import.modules, &bundle_users);
    import.messages = resolver.messages;
    (import, resolver.missing)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interpolation() {
        let mut props = FxHashMap::default();
        props.insert("a".to_owned(), "1".to_owned());
        props.insert("b".to_owned(), "${a}.2".to_owned());
        assert_eq!(interpolate("v${b}-x", &props), "v1.2-x");
        assert_eq!(interpolate("${missing}", &props), "${missing}");
        assert_eq!(interpolate("plain", &props), "plain");
    }

    #[test]
    fn scopes() {
        assert_eq!(
            combine_scope(Scope::Compile, Scope::Compile),
            Some(Scope::Compile)
        );
        assert_eq!(
            combine_scope(Scope::Compile, Scope::Runtime),
            Some(Scope::Runtime)
        );
        assert_eq!(
            combine_scope(Scope::Test, Scope::Compile),
            Some(Scope::Test)
        );
        assert_eq!(combine_scope(Scope::Compile, Scope::Test), None);
        assert_eq!(combine_scope(Scope::Compile, Scope::Provided), None);
    }

    fn write(path: &Path, text: &str) {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }

    fn pom(group: &str, artifact: &str, deps: &str) -> String {
        format!(
            "<project><groupId>{group}</groupId><artifactId>{artifact}</artifactId>\
             <version>1</version><dependencies>{deps}</dependencies></project>"
        )
    }

    fn dep(artifact: &str, extra: &str) -> String {
        format!("<dependency><groupId>g</groupId><artifactId>{artifact}</artifactId><version>1</version>{extra}</dependency>")
    }

    /// 本地仓库里放一个构件：pom 和空 jar。
    fn install(repo: &Path, artifact: &str, deps: &str) {
        let dir = repo.join("g").join(artifact).join("1");
        write(
            &dir.join(format!("{artifact}-1.pom")),
            &pom("g", artifact, deps),
        );
        write(&dir.join(format!("{artifact}-1.jar")), "");
    }

    fn resolver(repo: PathBuf) -> Resolver {
        Resolver {
            repo,
            reactor: FxHashMap::default(),
            cache: FxHashMap::default(),
            messages: Vec::new(),
            missing: FxHashSet::default(),
            missing_hits: 0,
        }
    }

    fn temp_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("ja-maven-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    }

    #[test]
    fn jdk_activation_specs() {
        assert!(jdk_matches("[25,)", 25));
        assert!(!jdk_matches("[25,)", 21));
        assert!(jdk_matches("1.8", 8));
        assert!(jdk_matches("!1.8", 17));
        assert!(jdk_matches("(,1.8],[11,)", 8));
        assert!(jdk_matches("(,1.8],[11,)", 21));
        assert!(!jdk_matches("(,1.8],[11,)", 9));
        assert!(jdk_matches("[11,17)", 11));
        assert!(!jdk_matches("[11,17)", 17));
        assert!(jdk_matches("[17]", 17));
    }

    #[test]
    fn profiles_activated_by_conditions() {
        let dir = temp_dir("profiles");
        let pom_path = dir.join("pom.xml");
        let profile = |id: &str, activation: &str, version: &str| {
            format!(
                "<profile><id>{id}</id><activation>{activation}</activation>\
                 <properties><v>{version}</v></properties></profile>"
            )
        };
        let write_pom = |profiles: String| {
            write(
                &pom_path,
                &format!(
                    "<project><groupId>g</groupId><artifactId>a</artifactId><version>1</version>\
                     <properties><v>0</v></properties><profiles>{profiles}</profiles></project>"
                ),
            );
        };
        // 后读到的同名属性覆盖先前的（profile 里的覆盖工程本身的）
        let value = || {
            read_raw_pom(&pom_path)
                .unwrap()
                .properties
                .iter()
                .rev()
                .find(|(k, _)| k == "v")
                .map(|(_, v)| v.clone())
        };

        ACTIVATION_JDK.with(|v| v.set(Some(25)));
        write_pom(
            profile(
                "default",
                "<activeByDefault>true</activeByDefault>",
                "default",
            ) + &profile("new-jdk", "<jdk>[25,)</jdk>", "jdk25"),
        );
        // 别的 profile 被条件激活时 `activeByDefault` 的不生效
        assert_eq!(value().as_deref(), Some("jdk25"));

        write_pom(
            profile(
                "default",
                "<activeByDefault>true</activeByDefault>",
                "default",
            ) + &profile("old-jdk", "<jdk>1.8</jdk>", "jdk8"),
        );
        assert_eq!(value().as_deref(), Some("default"));

        write_pom(
            profile(
                "by-prop",
                "<property><name>release</name></property>",
                "release",
            ) + &profile(
                "not-prop",
                "<property><name>!skipDefault</name></property>",
                "neg",
            ),
        );
        assert_eq!(value().as_deref(), Some("neg"));

        write(&dir.join("marker.txt"), "");
        write_pom(profile(
            "file",
            "<file><exists>${basedir}/marker.txt</exists></file>",
            "file",
        ));
        assert_eq!(value().as_deref(), Some("file"));
        ACTIVATION_JDK.with(|v| v.set(None));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn widest_scope_wins_across_paths() {
        let dir = temp_dir("scope");
        let repo = dir.join("repo");
        install(&repo, "api", &dep("api-dep", ""));
        install(&repo, "api-dep", "");
        // 先经由 test scope 的依赖到达 api，再经由 compile scope 的依赖到达
        install(&repo, "simple", &dep("api", ""));
        install(&repo, "bridge", &dep("api", ""));
        let root_pom = dir.join("app/pom.xml");
        write(
            &root_pom,
            &pom(
                "g",
                "app",
                &(dep("simple", "<scope>test</scope>") + &dep("bridge", "")),
            ),
        );
        let mut resolver = resolver(repo);
        let eff = resolver.effective(&root_pom, 0).unwrap();
        let scopes: Vec<(String, Scope)> = resolver
            .resolve_dependencies(&eff)
            .into_iter()
            .filter_map(|dep| match dep {
                ResolvedDep::Library { name, scope, .. } => Some((name, scope)),
                ResolvedDep::Module { .. } | ResolvedDep::Missing { .. } => None,
            })
            .collect();
        let scope_of = |name: &str| {
            scopes
                .iter()
                .find(|(n, _)| n == &format!("g:{name}:1"))
                .map(|(_, s)| *s)
        };
        assert_eq!(scope_of("simple"), Some(Scope::Test));
        assert_eq!(scope_of("bridge"), Some(Scope::Compile));
        assert_eq!(scope_of("api"), Some(Scope::Compile));
        // 变宽后传递依赖也跟着变宽
        assert_eq!(scope_of("api-dep"), Some(Scope::Compile));
        assert_eq!(scopes.len(), 4);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// eladmin：`jakarta.xml.bind-api` 先经由 test scope 的 starter 到达，再经由一条排除了
    /// `jakarta.activation-api` 的 compile 路径到达而变宽。Maven 里胜出的是先到的那个节点，
    /// 它的依赖按它自己路径上的排除项展开：`activation-api` 跟着 `xml.bind-api` 变成 compile。
    #[test]
    fn widened_scope_keeps_the_exclusions_of_the_nearest_path() {
        let dir = temp_dir("widen-exclusions");
        let repo = dir.join("repo");
        install(&repo, "activation", "");
        install(&repo, "bind", &dep("activation", ""));
        install(&repo, "starter-test", &dep("bind", ""));
        install(
            &repo,
            "runtime",
            &dep(
                "bind",
                "<exclusions><exclusion><groupId>g</groupId>\
                 <artifactId>activation</artifactId></exclusion></exclusions>",
            ),
        );
        install(&repo, "druid", &dep("runtime", ""));
        let root_pom = dir.join("app/pom.xml");
        write(
            &root_pom,
            &pom(
                "g",
                "app",
                &(dep("starter-test", "<scope>test</scope>") + &dep("druid", "")),
            ),
        );
        let mut resolver = resolver(repo);
        let eff = resolver.effective(&root_pom, 0).unwrap();
        let scopes: Vec<(String, Scope)> = resolver
            .resolve_dependencies(&eff)
            .into_iter()
            .filter_map(|dep| match dep {
                ResolvedDep::Library { name, scope, .. } => Some((name, scope)),
                ResolvedDep::Module { .. } | ResolvedDep::Missing { .. } => None,
            })
            .collect();
        let scope_of = |name: &str| {
            scopes
                .iter()
                .find(|(n, _)| n == &format!("g:{name}:1"))
                .map(|(_, s)| *s)
        };
        assert_eq!(scope_of("bind"), Some(Scope::Compile));
        assert_eq!(scope_of("activation"), Some(Scope::Compile), "{scopes:?}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// pig：模块直接声明为 provided 的 `lombok`、`spring-webmvc` 经由 compile 的传递依赖也能到达，
    /// Maven 里仍然是 provided；`http-converter` 一条路径是 runtime、一条是 provided，取 runtime。
    #[test]
    fn direct_scope_is_kept_and_runtime_beats_provided() {
        let dir = temp_dir("direct-scope");
        let repo = dir.join("repo");
        install(&repo, "lombok", "");
        install(&repo, "converter", "");
        install(&repo, "screw", &dep("lombok", ""));
        install(&repo, "webmvc", &dep("converter", "<scope>runtime</scope>"));
        install(
            &repo,
            "restclient",
            &dep("converter", "<scope>runtime</scope>"),
        );
        install(&repo, "springdoc", &dep("webmvc", ""));
        install(&repo, "gateway", &dep("restclient", ""));
        let root_pom = dir.join("app/pom.xml");
        write(
            &root_pom,
            &pom(
                "g",
                "app",
                &(dep("gateway", "<scope>provided</scope>")
                    + &dep("screw", "")
                    + &dep("springdoc", "")
                    + &dep("lombok", "<scope>provided</scope>")),
            ),
        );
        let mut resolver = resolver(repo);
        let eff = resolver.effective(&root_pom, 0).unwrap();
        let scopes: Vec<(String, Scope)> = resolver
            .resolve_dependencies(&eff)
            .into_iter()
            .filter_map(|dep| match dep {
                ResolvedDep::Library { name, scope, .. } => Some((name, scope)),
                ResolvedDep::Module { .. } | ResolvedDep::Missing { .. } => None,
            })
            .collect();
        let scope_of = |name: &str| {
            scopes
                .iter()
                .find(|(n, _)| n == &format!("g:{name}:1"))
                .map(|(_, s)| *s)
        };
        assert_eq!(scope_of("lombok"), Some(Scope::Provided), "{scopes:?}");
        assert_eq!(scope_of("restclient"), Some(Scope::Provided));
        assert_eq!(scope_of("converter"), Some(Scope::Runtime), "{scopes:?}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn optional_written_as_property() {
        let dir = temp_dir("optional");
        let repo = dir.join("repo");
        install(&repo, "extra", "");
        install(&repo, "plain", "");
        // `<optional>${extra.optional}</optional>`：属性在库自己的 POM 里定义成 true
        let lib_dir = repo.join("g/lib/1");
        write(
            &lib_dir.join("lib-1.pom"),
            &format!(
                "<project><groupId>g</groupId><artifactId>lib</artifactId><version>1</version>\
                 <properties><extra.optional>true</extra.optional></properties>\
                 <dependencies>{}{}</dependencies></project>",
                dep("extra", "<optional>${extra.optional}</optional>"),
                dep("plain", ""),
            ),
        );
        write(&lib_dir.join("lib-1.jar"), "");
        let root_pom = dir.join("app/pom.xml");
        write(&root_pom, &pom("g", "app", &dep("lib", "")));
        let mut resolver = resolver(repo);
        let eff = resolver.effective(&root_pom, 0).unwrap();
        let names: Vec<String> = resolver
            .resolve_dependencies(&eff)
            .into_iter()
            .filter_map(|dep| match dep {
                ResolvedDep::Library { name, .. } => Some(name),
                ResolvedDep::Module { .. } | ResolvedDep::Missing { .. } => None,
            })
            .collect();
        assert_eq!(names, vec!["g:lib:1".to_owned(), "g:plain:1".to_owned()]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn system_scope_uses_the_system_path() {
        let dir = temp_dir("system-scope");
        let repo = dir.join("repo");
        write(&dir.join("lib/oshi-1.jar"), "");
        write(&dir.join("lib/jna-1.jar"), "");
        // 受管声明给出 `<systemPath>`，依赖本身只写坐标
        let root_pom = dir.join("app/pom.xml");
        write(
            &root_pom,
            &format!(
                "<project><groupId>g</groupId><artifactId>app</artifactId><version>1</version>\
                 <dependencyManagement><dependencies>{}</dependencies></dependencyManagement>\
                 <dependencies>{}{}{}</dependencies></project>",
                dep(
                    "jna",
                    "<scope>system</scope><systemPath>${project.basedir}/../lib/jna-1.jar</systemPath>"
                ),
                dep(
                    "oshi",
                    "<scope>system</scope><systemPath>${project.basedir}/../lib/oshi-1.jar</systemPath>"
                ),
                "<dependency><groupId>g</groupId><artifactId>jna</artifactId></dependency>",
                dep(
                    "absent",
                    "<scope>system</scope><systemPath>${basedir}/../lib/absent-1.jar</systemPath>"
                ),
            ),
        );
        let mut resolver = resolver(repo);
        let eff = resolver.effective(&root_pom, 0).unwrap();
        let libs: Vec<(String, PathBuf, Scope)> = resolver
            .resolve_dependencies(&eff)
            .into_iter()
            .filter_map(|dep| match dep {
                ResolvedDep::Library {
                    name, jar, scope, ..
                } => Some((name, jar, scope)),
                ResolvedDep::Module { .. } | ResolvedDep::Missing { .. } => None,
            })
            .collect();
        let app = dir.join("app");
        assert_eq!(
            libs,
            vec![
                (
                    "g:oshi:1".to_owned(),
                    app.join("../lib/oshi-1.jar"),
                    Scope::Compile
                ),
                (
                    "g:jna:1".to_owned(),
                    app.join("../lib/jna-1.jar"),
                    Scope::Compile
                ),
            ]
        );
        // 磁盘上没有的 system jar 不当作本地仓库缺的构件，不会为它跑 Maven
        assert!(resolver.missing.is_empty());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn child_properties_apply_to_inherited_management() {
        let dir = temp_dir("inherited-props");
        let repo = dir.join("repo");
        for version in ["1", "2"] {
            let lib_dir = repo.join(format!("g/log/{version}"));
            write(
                &lib_dir.join(format!("log-{version}.pom")),
                &format!("<project><groupId>g</groupId><artifactId>log</artifactId><version>{version}</version></project>"),
            );
            write(&lib_dir.join(format!("log-{version}.jar")), "");
        }
        // 父 POM（像 spring-boot-dependencies）用属性管理版本，子模块覆盖这个属性
        let parent_dir = repo.join("g/parent/1");
        write(
            &parent_dir.join("parent-1.pom"),
            "<project><groupId>g</groupId><artifactId>parent</artifactId><version>1</version>\
             <packaging>pom</packaging><properties><log.version>2</log.version></properties>\
             <dependencyManagement><dependencies><dependency><groupId>g</groupId>\
             <artifactId>log</artifactId><version>${log.version}</version></dependency>\
             </dependencies></dependencyManagement></project>",
        );
        let root_pom = dir.join("app/pom.xml");
        write(
            &root_pom,
            "<project><parent><groupId>g</groupId><artifactId>parent</artifactId><version>1</version>\
             <relativePath/></parent><artifactId>app</artifactId>\
             <properties><log.version>1</log.version></properties>\
             <dependencies><dependency><groupId>g</groupId><artifactId>log</artifactId></dependency>\
             </dependencies></project>",
        );
        let mut resolver = resolver(repo);
        let eff = resolver.effective(&root_pom, 0).unwrap();
        let names: Vec<String> = resolver
            .resolve_dependencies(&eff)
            .into_iter()
            .filter_map(|dep| match dep {
                ResolvedDep::Library { name, .. } => Some(name),
                ResolvedDep::Module { .. } | ResolvedDep::Missing { .. } => None,
            })
            .collect();
        assert_eq!(names, vec!["g:log:1".to_owned()]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn library_managed_exclusions() {
        let dir = temp_dir("managed-exclusions");
        let repo = dir.join("repo");
        install(&repo, "cglib", "");
        install(&repo, "digester", &dep("cglib", ""));
        // 库在自己的 dependencyManagement 里管理 digester 时排除了 cglib，依赖声明本身不写版本
        let tools_dir = repo.join("g/tools/1");
        write(
            &tools_dir.join("tools-1.pom"),
            "<project><groupId>g</groupId><artifactId>tools</artifactId><version>1</version>\
             <dependencyManagement><dependencies><dependency><groupId>g</groupId>\
             <artifactId>digester</artifactId><version>1</version><exclusions><exclusion>\
             <groupId>g</groupId><artifactId>cglib</artifactId></exclusion></exclusions>\
             </dependency></dependencies></dependencyManagement>\
             <dependencies><dependency><groupId>g</groupId><artifactId>digester</artifactId>\
             </dependency></dependencies></project>",
        );
        write(&tools_dir.join("tools-1.jar"), "");
        let root_pom = dir.join("app/pom.xml");
        write(&root_pom, &pom("g", "app", &dep("tools", "")));
        let mut resolver = resolver(repo);
        let eff = resolver.effective(&root_pom, 0).unwrap();
        let names: Vec<String> = resolver
            .resolve_dependencies(&eff)
            .into_iter()
            .filter_map(|dep| match dep {
                ResolvedDep::Library { name, .. } => Some(name),
                ResolvedDep::Module { .. } | ResolvedDep::Missing { .. } => None,
            })
            .collect();
        assert_eq!(
            names,
            vec!["g:tools:1".to_owned(), "g:digester:1".to_owned()]
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn compiler_preview_and_level() {
        let dir = temp_dir("preview");
        let plugin = |config: &str| {
            format!(
                "<project><groupId>g</groupId><artifactId>a</artifactId><version>1</version>\
                 <build><plugins><plugin><artifactId>maven-compiler-plugin</artifactId>\
                 <configuration>{config}</configuration></plugin></plugins></build></project>"
            )
        };
        let cases = [
            (
                "<release>25</release><enablePreview>true</enablePreview>",
                true,
            ),
            (
                "<release>25</release><compilerArgs><arg>--enable-preview</arg></compilerArgs>",
                true,
            ),
            ("<release>21</release>", false),
            ("<source>1.8</source><target>1.8</target>", false),
        ];
        for (idx, (config, preview)) in cases.into_iter().enumerate() {
            let pom_path = dir.join(format!("m{idx}/pom.xml"));
            write(&pom_path, &plugin(config));
            let mut resolver = resolver(dir.join("repo"));
            let eff = resolver.effective(&pom_path, 0).unwrap();
            assert_eq!(eff.preview, preview, "{config}");
            assert!(eff.level.is_some());
            // 只有 `<release>` 限制 JDK API；只写 `<source>` 时用 JDK 的全部 API
            assert_eq!(
                eff.release.is_some(),
                config.contains("<release>"),
                "{config}"
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn toolchains_plugin_jdk_version() {
        let dir = temp_dir("toolchains");
        // 父 POM 在 pluginManagement 里用属性写版本，子模块覆盖属性
        write(
            &dir.join("parent/pom.xml"),
            "<project><groupId>g</groupId><artifactId>parent</artifactId><version>1</version>\
             <packaging>pom</packaging><properties><jdk.version>17</jdk.version></properties>\
             <build><pluginManagement><plugins><plugin>\
             <artifactId>maven-toolchains-plugin</artifactId><configuration><toolchains>\
             <jdk><version>${jdk.version}</version><vendor>temurin</vendor></jdk>\
             </toolchains></configuration></plugin></plugins></pluginManagement></build></project>",
        );
        write(
            &dir.join("child/pom.xml"),
            "<project><parent><groupId>g</groupId><artifactId>parent</artifactId><version>1</version>\
             <relativePath>../parent/pom.xml</relativePath></parent><artifactId>child</artifactId>\
             <properties><jdk.version>1.8</jdk.version></properties></project>",
        );
        // 写在 execution 里，版本是区间：取下界
        write(
            &dir.join("range/pom.xml"),
            "<project><groupId>g</groupId><artifactId>range</artifactId><version>1</version>\
             <build><plugins><plugin><artifactId>maven-toolchains-plugin</artifactId>\
             <executions><execution><goals><goal>toolchain</goal></goals><configuration>\
             <toolchains><jdk><version>[11,)</version></jdk></toolchains>\
             </configuration></execution></executions></plugin></plugins></build></project>",
        );
        let mut resolver = resolver(dir.join("repo"));
        let toolchain = |resolver: &mut Resolver, name: &str| {
            let pom = dir.join(format!("{name}/pom.xml"));
            resolver.effective(&pom, 0).unwrap().toolchain
        };
        assert_eq!(toolchain(&mut resolver, "parent"), Some(17));
        assert_eq!(toolchain(&mut resolver, "child"), Some(8));
        assert_eq!(toolchain(&mut resolver, "range"), Some(11));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_release_and_source() {
        let dir = temp_dir("test-release");
        // 父 POM 用属性分别设置主代码和测试代码的级别，子模块覆盖主代码的
        write(
            &dir.join("parent/pom.xml"),
            "<project><groupId>g</groupId><artifactId>parent</artifactId><version>1</version>\
             <packaging>pom</packaging><properties><java.release>17</java.release>\
             <java.test.release>17</java.test.release>\
             <maven.compiler.release>${java.release}</maven.compiler.release>\
             <maven.compiler.testRelease>${java.test.release}</maven.compiler.testRelease>\
             </properties></project>",
        );
        write(
            &dir.join("child/pom.xml"),
            "<project><parent><groupId>g</groupId><artifactId>parent</artifactId><version>1</version>\
             <relativePath>../parent/pom.xml</relativePath></parent><artifactId>child</artifactId>\
             <properties><java.release>11</java.release></properties></project>",
        );
        // 插件配置里直接写 `<testSource>`
        write(
            &dir.join("plugin/pom.xml"),
            "<project><groupId>g</groupId><artifactId>plugin</artifactId><version>1</version>\
             <build><plugins><plugin><artifactId>maven-compiler-plugin</artifactId>\
             <configuration><source>1.8</source><testSource>21</testSource></configuration>\
             </plugin></plugins></build></project>",
        );
        let mut resolver = resolver(dir.join("repo"));
        let child = resolver.effective(&dir.join("child/pom.xml"), 0).unwrap();
        assert_eq!(
            (
                child.level,
                child.release,
                child.test_level,
                child.test_release
            ),
            (Some(11), Some(11), Some(17), Some(17))
        );
        let plugin = resolver.effective(&dir.join("plugin/pom.xml"), 0).unwrap();
        assert_eq!(
            (
                plugin.level,
                plugin.release,
                plugin.test_level,
                plugin.test_release
            ),
            (Some(8), None, Some(21), None)
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn source_encoding_is_inherited() {
        let dir = temp_dir("encoding");
        write(
            &dir.join("parent/pom.xml"),
            "<project><groupId>g</groupId><artifactId>parent</artifactId><version>1</version>\
             <packaging>pom</packaging><properties><charset>UTF-8</charset>\
             <project.build.sourceEncoding>${charset}</project.build.sourceEncoding>\
             </properties></project>",
        );
        let child = |name: &str, extra: &str| {
            write(
                &dir.join(format!("{name}/pom.xml")),
                &format!(
                    "<project><parent><groupId>g</groupId><artifactId>parent</artifactId>\
                     <version>1</version><relativePath>../parent/pom.xml</relativePath></parent>\
                     <artifactId>{name}</artifactId>{extra}</project>"
                ),
            );
            dir.join(format!("{name}/pom.xml"))
        };
        let inherits = child("inherits", "");
        // 子模块覆盖父 POM 里引用的属性
        let overrides = child(
            "overrides",
            "<properties><charset>GBK</charset></properties>",
        );
        // 编译器插件的 `<encoding>` 优先
        let plugin = child(
            "plugin",
            "<build><plugins><plugin><artifactId>maven-compiler-plugin</artifactId>\
             <configuration><encoding>ISO-8859-1</encoding></configuration></plugin></plugins>\
             </build>",
        );
        write(
            &dir.join("none/pom.xml"),
            "<project><groupId>g</groupId><artifactId>none</artifactId><version>1</version>\
             </project>",
        );
        let mut resolver = resolver(dir.join("repo"));
        let encoding = |resolver: &mut Resolver, pom: &Path| {
            resolver.effective(pom, 0).unwrap().encoding.clone()
        };
        assert_eq!(encoding(&mut resolver, &inherits).as_deref(), Some("UTF-8"));
        assert_eq!(encoding(&mut resolver, &overrides).as_deref(), Some("GBK"));
        assert_eq!(
            encoding(&mut resolver, &plugin).as_deref(),
            Some("ISO-8859-1")
        );
        assert_eq!(encoding(&mut resolver, &dir.join("none/pom.xml")), None);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn parent_compiler_config_uses_child_properties() {
        let dir = temp_dir("compile-source");
        // 父 POM 的插件配置引用属性，子模块覆盖这个属性
        write(
            &dir.join("parent/pom.xml"),
            "<project><groupId>g</groupId><artifactId>parent</artifactId><version>1</version>\
             <packaging>pom</packaging><properties><maven.compile.source>1.3</maven.compile.source>\
             </properties><build><pluginManagement><plugins><plugin>\
             <artifactId>maven-compiler-plugin</artifactId><configuration>\
             <source>${maven.compile.source}</source></configuration></plugin></plugins>\
             </pluginManagement></build></project>",
        );
        write(
            &dir.join("child/pom.xml"),
            "<project><parent><groupId>g</groupId><artifactId>parent</artifactId><version>1</version>\
             <relativePath>../parent/pom.xml</relativePath></parent><artifactId>child</artifactId>\
             <properties><maven.compile.source>1.6</maven.compile.source></properties></project>",
        );
        let mut resolver = resolver(dir.join("repo"));
        let parent = resolver.effective(&dir.join("parent/pom.xml"), 0).unwrap();
        assert_eq!(parent.level, Some(3));
        let child = resolver.effective(&dir.join("child/pom.xml"), 0).unwrap();
        assert_eq!(child.level, Some(6));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn output_directories() {
        let dir = temp_dir("output");
        let pom = |build: &str| {
            format!(
                "<project><groupId>g</groupId><artifactId>a</artifactId><version>1</version>\
                 <properties><out>gen</out></properties><build>{build}</build></project>"
            )
        };
        let cases = [
            ("", "target/classes", "target/test-classes"),
            (
                "<directory>${project.basedir}/out</directory>",
                "out/classes",
                "out/test-classes",
            ),
            (
                "<outputDirectory>${project.build.directory}/main</outputDirectory>\
                 <testOutputDirectory>${out}/test</testOutputDirectory>",
                "target/main",
                "gen/test",
            ),
        ];
        for (idx, (build, main, test)) in cases.into_iter().enumerate() {
            let module = dir.join(format!("m{idx}"));
            write(&module.join("pom.xml"), &pom(build));
            let mut resolver = resolver(dir.join("repo"));
            let eff = resolver.effective(&module.join("pom.xml"), 0).unwrap();
            let dirs = output_dirs(&eff);
            assert_eq!(
                dirs.iter()
                    .map(|d| (d.path.clone(), d.kind))
                    .collect::<Vec<_>>(),
                [
                    (module.join(main), SourceRootKind::Main),
                    (module.join(test), SourceRootKind::Test)
                ],
                "{build}"
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn missing_artifacts_are_downloadable() {
        let dir = temp_dir("fetch");
        let app_pom = dir.join("app/pom.xml");
        write(
            &app_pom,
            "<project><parent><groupId>g</groupId><artifactId>parent</artifactId>\
             <version>2</version></parent><artifactId>app</artifactId>\
             <repositories><repository><id>corp</id><url>https://repo.example/m2?a&amp;b</url></repository></repositories>\
             <dependencies>\
             <dependency><groupId>g</groupId><artifactId>lib</artifactId><version>1</version><classifier>jdk8</classifier></dependency>\
             <dependency><groupId>g</groupId><artifactId>fixtures</artifactId><version>1</version><type>test-jar</type></dependency>\
             </dependencies></project>",
        );
        let mut resolver = resolver(dir.join("repo"));
        let eff = resolver.effective(&app_pom, 0).unwrap();
        resolver.resolve_dependencies(&eff);
        let missing =
            |artifact: &str, version: &str, kind: &str, classifier: Option<&str>| MissingArtifact {
                group: "g".into(),
                artifact: artifact.into(),
                version: version.into(),
                kind: kind.into(),
                classifier: classifier.map(Into::into),
            };
        let mut found: Vec<MissingArtifact> = resolver.missing.iter().cloned().collect();
        found.sort_by(|a, b| a.artifact.cmp(&b.artifact));
        assert_eq!(
            found,
            vec![
                missing("fixtures", "1", "test-jar", None),
                missing("lib", "1", "jar", Some("jdk8")),
                missing("parent", "2", "pom", None),
            ]
        );

        let repositories = reactor_repositories(std::slice::from_ref(&app_pom));
        assert_eq!(
            repositories,
            vec![("corp".to_owned(), "https://repo.example/m2?a&b".to_owned())]
        );
        let groups = fetch_groups(&found);
        assert_eq!(groups.len(), 1);
        let pom = fetch_pom("fetch", &groups[0], &repositories);
        assert!(pom.contains("<url>https://repo.example/m2?a&amp;b</url>"));
        assert!(pom.contains(
            "<artifactId>lib</artifactId><version>1</version><type>jar</type><classifier>jdk8</classifier>"
        ));
        assert!(pom.contains("<artifactId>parent</artifactId><version>2</version><type>pom</type>"));
        assert_eq!(pom.matches("<artifactId>*</artifactId>").count(), 3);
        assert!(xml::parse(&pom).is_some());

        // 同一个构件的两个版本分到两组
        found.push(missing("lib", "2", "jar", Some("jdk8")));
        found.push(missing("lib", "3", "jar", None));
        let groups = fetch_groups(&found);
        let versions: Vec<Vec<&str>> = groups
            .iter()
            .map(|g| g.iter().map(|a| a.version.as_str()).collect())
            .collect();
        assert_eq!(versions, vec![vec!["1", "1", "2", "3"], vec!["2"]]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn reactor_test_jar_dependency() {
        let dir = temp_dir("testjar");
        let core_pom = dir.join("core/pom.xml");
        write(&core_pom, &pom("g", "core", ""));
        let app_pom = dir.join("app/pom.xml");
        write(
            &app_pom,
            &pom(
                "g",
                "app",
                &(dep("core", "") + &dep("core", "<type>test-jar</type>")),
            ),
        );
        let mut resolver = resolver(dir.join("repo"));
        resolver.reactor.insert(
            Coord {
                group: "g".into(),
                artifact: "core".into(),
            },
            core_pom.clone(),
        );
        let eff = resolver.effective(&app_pom, 0).unwrap();
        let modules: Vec<bool> = resolver
            .resolve_dependencies(&eff)
            .into_iter()
            .filter_map(|dep| match dep {
                ResolvedDep::Module { pom, test_jar, .. } if pom == core_pom => Some(test_jar),
                _ => None,
            })
            .collect();
        assert_eq!(modules, vec![false, true]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn reactor_tests_classifier_dependency() {
        let dir = temp_dir("testsclassifier");
        let kit_pom = dir.join("kit/pom.xml");
        write(&kit_pom, &pom("g", "kit", ""));
        let app_pom = dir.join("app/pom.xml");
        write(
            &app_pom,
            &pom(
                "g",
                "app",
                &dep("kit", "<classifier>tests</classifier><scope>test</scope>"),
            ),
        );
        let mut resolver = resolver(dir.join("repo"));
        resolver.reactor.insert(
            Coord {
                group: "g".into(),
                artifact: "kit".into(),
            },
            kit_pom.clone(),
        );
        let eff = resolver.effective(&app_pom, 0).unwrap();
        let deps = resolver.resolve_dependencies(&eff);
        // `<classifier>tests</classifier>` 和 `<type>test-jar</type>` 一样是测试代码的 jar
        assert!(matches!(
            deps.as_slice(),
            [ResolvedDep::Module {
                test_jar: true,
                scope: Scope::Test,
                ..
            }]
        ));
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 两个模块的 reactor：`app` 依赖 `core` 和 `deps` 里的构件。
    fn reactor(dir: &Path, deps: &str) -> PathBuf {
        let root = dir.join("pom.xml");
        write(
            &root,
            "<project><groupId>g</groupId><artifactId>root</artifactId><version>1</version>\
             <packaging>pom</packaging><modules><module>core</module><module>app</module></modules></project>",
        );
        write(&dir.join("core/pom.xml"), &pom("g", "core", ""));
        write(
            &dir.join("app/pom.xml"),
            &pom("g", "app", &(dep("core", "") + deps)),
        );
        root
    }

    fn maven_runs() -> usize {
        crate::maven_settings::MAVEN_RUNS.with(|runs| runs.get())
    }

    /// 依赖模块的 optional 依赖和依赖模块时排除掉的依赖不在运行时类路径上
    /// （mall-search 排除 mall-mbg 带来的 redis；pig 的公共模块把 webflux 声明成 optional）。
    #[test]
    fn runtime_class_path_keeps_exclusions_and_optional_dependencies_of_modules() {
        let dir = temp_dir("module-exclusions");
        let repo = dir.join("repo");
        for lib in ["kept", "excluded", "opt"] {
            install(&repo, lib, "");
        }
        write(
            &dir.join("pom.xml"),
            "<project><groupId>g</groupId><artifactId>parent</artifactId><version>1</version>\
             <packaging>pom</packaging><modules><module>core</module><module>app</module>\
             </modules></project>",
        );
        write(
            &dir.join("core/pom.xml"),
            &pom(
                "g",
                "core",
                &(dep("kept", "")
                    + &dep("excluded", "")
                    + &dep("opt", "<optional>true</optional>")),
            ),
        );
        write(
            &dir.join("app/pom.xml"),
            &pom(
                "g",
                "app",
                &dep(
                    "core",
                    "<exclusions><exclusion><groupId>g</groupId>\
                     <artifactId>excluded</artifactId></exclusion></exclusions>",
                ),
            ),
        );
        for module in ["app", "core"] {
            std::fs::create_dir_all(dir.join(module).join("target/classes")).unwrap();
        }
        let setup = ResolvedSetup {
            repo: repo.clone(),
            settings: None,
        };
        let import = import_with(&dir.join("pom.xml"), false, None, &setup).unwrap();
        let graph = base_db::ProjectGraph {
            modules: import.modules,
            libraries: import.libraries,
            jdk: None,
        };
        let id = |name: &str| {
            ModuleId(graph.modules.iter().position(|m| m.name == name).unwrap() as u32)
        };
        // `<模块>/target/classes` 和 `g/<库>/1/<库>-1.jar` 都取倒数第三级的名字
        let names = |module: &str| -> Vec<String> {
            crate::runtime_class_path(&graph, id(module), false)
                .entries
                .iter()
                .map(|p| {
                    let parent = p.parent().unwrap().parent().unwrap();
                    parent.file_name().unwrap().to_string_lossy().into_owned()
                })
                .collect()
        };
        assert_eq!(names("app"), ["app", "core", "kept"]);
        assert_eq!(names("core"), ["core", "kept", "excluded", "opt"]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn no_maven_run_when_local_repository_has_everything() {
        let dir = temp_dir("complete");
        let repo = dir.join("repo");
        install(&repo, "lib", &dep("transitive", ""));
        install(&repo, "transitive", "");
        let root = reactor(&dir, &dep("lib", ""));
        let setup = ResolvedSetup {
            repo: repo.clone(),
            settings: None,
        };
        let before = maven_runs();
        let import = import_with(&root, true, None, &setup).unwrap();
        assert_eq!(maven_runs(), before);
        let names: Vec<&str> = import.libraries.iter().map(|l| l.name.as_str()).collect();
        assert_eq!(names, vec!["g:lib:1", "g:transitive:1"]);
        assert!(import.unresolved.is_empty());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn failed_downloads_are_not_retried_on_reimport() {
        let dir = temp_dir("retry");
        let repo = dir.join("repo");
        install(&repo, "lib", "");
        let root = reactor(&dir, &(dep("lib", "") + &dep("absent", "")));
        let setup = ResolvedSetup {
            repo: repo.clone(),
            settings: None,
        };
        // 第一次：一次下载缺件，一次 reactor 级的 classpath，不是每个模块一次
        let before = maven_runs();
        let import = import_with(&root, true, None, &setup).unwrap();
        assert_eq!(maven_runs(), before + 2);
        assert_eq!(import.unresolved.len(), 1);
        // 重新导入：缺的还是同一个构件，不再运行 Maven
        let before = maven_runs();
        let import = import_with(&root, true, None, &setup).unwrap();
        assert_eq!(maven_runs(), before);
        assert_eq!(import.unresolved.len(), 1);
        // 不让用 CLI 时也不运行
        import_with(&root, false, None, &setup).unwrap();
        assert_eq!(maven_runs(), before);
        // 换了设置文件：重新尝试
        let other = ResolvedSetup {
            repo,
            settings: Some(dir.join("settings.xml")),
        };
        import_with(&root, true, None, &other).unwrap();
        assert_eq!(maven_runs(), before + 2);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn parses_dependency_list_output() {
        let output = "\n\
The following files have been resolved:\n\
   org.slf4j:slf4j-api:jar:2.0.9:compile:/repo/org/slf4j/slf4j-api/2.0.9/slf4j-api-2.0.9.jar -- module org.slf4j\n\
   g:core:test-jar:tests:1:test:/work/core/target/test-classes\n\
   javax.servlet:servlet-api:jar:2.5:provided:C:\\m2\\javax\\servlet\\servlet-api-2.5.jar (optional)\n\
   com.sun:tools:jar:1.8:system:null\n\
   g:native:jar:linux-x86_64:3:runtime:/repo/g/native/3/native-3-linux-x86_64.jar (optional) -- module native [auto]\n\
   none\n";
        let listed = parse_dependency_list(output);
        let summary: Vec<(String, Option<&str>, Scope, Option<PathBuf>)> = listed
            .iter()
            .map(|d| {
                (
                    format!("{}:{}:{}:{}", d.group, d.artifact, d.kind, d.version),
                    d.classifier.as_deref(),
                    d.scope,
                    d.file.clone(),
                )
            })
            .collect();
        assert_eq!(
            summary,
            vec![
                (
                    "org.slf4j:slf4j-api:jar:2.0.9".to_owned(),
                    None,
                    Scope::Compile,
                    Some(PathBuf::from(
                        "/repo/org/slf4j/slf4j-api/2.0.9/slf4j-api-2.0.9.jar"
                    ))
                ),
                (
                    "g:core:test-jar:1".to_owned(),
                    Some("tests"),
                    Scope::Test,
                    Some(PathBuf::from("/work/core/target/test-classes"))
                ),
                (
                    "javax.servlet:servlet-api:jar:2.5".to_owned(),
                    None,
                    Scope::Provided,
                    Some(PathBuf::from(r"C:\m2\javax\servlet\servlet-api-2.5.jar"))
                ),
                (
                    "com.sun:tools:jar:1.8".to_owned(),
                    None,
                    Scope::Compile,
                    None
                ),
                (
                    "g:native:jar:3".to_owned(),
                    Some("linux-x86_64"),
                    Scope::Runtime,
                    Some(PathBuf::from("/repo/g/native/3/native-3-linux-x86_64.jar"))
                ),
            ]
        );
    }

    #[test]
    fn dependency_list_from_maven_replaces_static_resolution() {
        let dir = temp_dir("listed");
        let repo = dir.join("repo");
        install(&repo, "lib", "");
        let root = reactor(&dir, &(dep("lib", "") + &dep("absent", "")));
        let poms = {
            let mut poms = Vec::new();
            collect_reactor(&root, &mut poms);
            poms
        };
        let jar = |artifact: &str, version: &str| {
            let path = repo
                .join("g")
                .join(artifact)
                .join(version)
                .join(format!("{artifact}-{version}.jar"));
            write(&path, "");
            path
        };
        let lib2 = jar("lib", "2");
        // 静态解析在本地仓库里找不到它，Maven 却解析到了别处的文件
        let absent = dir.join("elsewhere/absent-1.jar");
        write(&absent, "");
        let servlet = jar("servlet", "1");
        let junit = jar("junit", "4");
        let installed_core = jar("core", "1");
        let line = |coords: &str, path: &Path| format!("   {coords}:{}\n", path.display());
        let listing = line("g:core:jar:1:compile", &installed_core)
            + &line("g:lib:jar:2:compile", &lib2)
            + &line("g:absent:jar:1:runtime", &absent)
            + &line("g:servlet:jar:1:provided", &servlet)
            + &line("g:junit:jar:4:test", &junit)
            + &line(
                "g:core:test-jar:tests:1:test",
                &dir.join("core/target/test-classes"),
            );
        let mut lists = DependencyLists::default();
        lists.insert(dir.join("app"), parse_dependency_list(&listing));

        let (import, _) = import_once(&poms, &repo, Some(&lists));
        let app = import.modules.iter().find(|m| m.name == "app").unwrap();
        let core = ModuleId(
            import
                .modules
                .iter()
                .position(|m| m.name == "core")
                .unwrap() as u32,
        );
        let deps: Vec<(String, Scope)> = app
            .dependencies
            .iter()
            .map(|d| {
                let target = match d.target {
                    DependencyTarget::Library(id) => import.libraries[id.0 as usize].name.clone(),
                    DependencyTarget::Module(id) if id == core => "module core".to_owned(),
                    DependencyTarget::ModuleTests(id) if id == core => "tests of core".to_owned(),
                    other => format!("{other:?}"),
                };
                (target, d.scope)
            })
            .collect();
        assert_eq!(
            deps,
            vec![
                ("module core".to_owned(), Scope::Compile),
                ("g:lib:2".to_owned(), Scope::Compile),
                ("g:absent:1".to_owned(), Scope::Runtime),
                ("g:servlet:1".to_owned(), Scope::Provided),
                ("g:junit:4".to_owned(), Scope::Test),
                ("tests of core".to_owned(), Scope::Test),
            ]
        );
        // 没有缺件的模块不受影响
        assert!(import
            .modules
            .iter()
            .find(|m| m.name == "core")
            .unwrap()
            .dependencies
            .is_empty());
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 本地仓库里放 `g:{artifact}:{version}` 的 pom 和空 jar。
    fn install_version(repo: &Path, artifact: &str, version: &str, body: &str) {
        let dir = repo.join("g").join(artifact).join(version);
        write(
            &dir.join(format!("{artifact}-{version}.pom")),
            &format!(
                "<project><groupId>g</groupId><artifactId>{artifact}</artifactId>\
                 <version>{version}</version>{body}</project>"
            ),
        );
        write(&dir.join(format!("{artifact}-{version}.jar")), "");
    }

    /// 解析一个模块（`body` 是 `<project>` 里的内容）：返回 classpath 上的库（`g:a:v`）和解析器。
    fn resolve_root(dir: &Path, repo: PathBuf, body: &str) -> (Vec<String>, Resolver) {
        let root_pom = dir.join("app/pom.xml");
        write(
            &root_pom,
            &format!(
                "<project><groupId>g</groupId><artifactId>app</artifactId>\
                 <version>1</version>{body}</project>"
            ),
        );
        let mut resolver = resolver(repo);
        let eff = resolver.effective(&root_pom, 0).unwrap();
        let libs = resolver
            .resolve_dependencies(&eff)
            .into_iter()
            .filter_map(|dep| match dep {
                ResolvedDep::Library { name, jar, .. } => {
                    assert!(jar.is_file());
                    Some(name)
                }
                _ => None,
            })
            .collect();
        (libs, resolver)
    }

    fn lib_dep(version: &str) -> String {
        format!(
            "<dependencies><dependency><groupId>g</groupId><artifactId>lib</artifactId>\
             <version>{version}</version></dependency></dependencies>"
        )
    }

    /// 区间取本地仓库里落在区间内的最高版本，不是下界。
    #[test]
    fn version_range_picks_highest_installed_version() {
        let dir = temp_dir("range-highest");
        let repo = dir.join("repo");
        for v in ["0.9", "1.0", "1.1"] {
            install_version(&repo, "lib", v, "");
        }
        let libs = |spec: &str| resolve_root(&dir, repo.clone(), &lib_dep(spec)).0;
        assert_eq!(libs("[1.0,2.0)"), ["g:lib:1.1"]);
        assert_eq!(libs("[1.0,1.1)"), ["g:lib:1.0"]);
        assert_eq!(libs("(,1.0]"), ["g:lib:1.0"]);
        // 硬性的单个版本和软性版本都不看仓库里有没有更高的
        assert_eq!(libs("[1.0]"), ["g:lib:1.0"]);
        assert_eq!(libs("1.0"), ["g:lib:1.0"]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 下载失败只留下 `*.lastUpdated` 的版本目录不是候选，即使它是区间里最高的
    /// （guava 经由 equinox.preferences 依赖 `org.osgi.service.prefs:[1.1.0,1.2.0)` 时就有这样的目录）。
    #[test]
    fn version_range_skips_versions_without_artifacts() {
        let dir = temp_dir("range-osgi");
        let repo = dir.join("repo");
        let lib = repo.join("g/lib");
        write(&lib.join("1.1.9/lib-1.1.9.jar.lastUpdated"), "");
        write(&lib.join("1.1.9/lib-1.1.9.pom.lastUpdated"), "");
        install_version(&repo, "lib", "1.1.1", "");
        install_version(&repo, "lib", "1.1.2", "");
        // 和 guava 一样经由传递依赖到达
        install_version(&repo, "mid", "1", &lib_dep("[1.1.0,1.2.0)"));
        let (libs, resolver) = resolve_root(
            &dir,
            repo,
            "<dependencies><dependency><groupId>g</groupId><artifactId>mid</artifactId>\
             <version>1</version></dependency></dependencies>",
        );
        assert_eq!(libs, ["g:mid:1", "g:lib:1.1.2"]);
        assert!(resolver.messages.is_empty(), "{:?}", resolver.messages);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 候选版本得有依赖要用的那个文件：只有 pom 的 3.8.2 不能顶掉有 jar 的 3.8.1；
    /// test-jar 依赖要的是 `-tests.jar`。
    #[test]
    fn version_range_requires_the_dependency_file() {
        let dir = temp_dir("range-pom-only");
        let repo = dir.join("repo");
        install_version(&repo, "lib", "3.8.1", "");
        install_version(&repo, "lib", "3.8.2", "");
        std::fs::remove_file(repo.join("g/lib/3.8.2/lib-3.8.2.jar")).unwrap();
        write(&repo.join("g/lib/3.8.1/lib-3.8.1-tests.jar"), "");
        let (libs, resolver) = resolve_root(&dir, repo.clone(), &lib_dep("[3.8.1,3.8.3)"));
        assert_eq!(libs, ["g:lib:3.8.1"]);
        assert!(resolver.missing.is_empty(), "{:?}", resolver.missing);
        assert!(resolver.messages.is_empty(), "{:?}", resolver.messages);
        install_version(&repo, "lib", "3.8.2", "");
        let (libs, resolver) = resolve_root(
            &dir,
            repo,
            "<dependencies><dependency><groupId>g</groupId><artifactId>lib</artifactId>\
             <version>[3.8.1,3.8.3)</version><type>test-jar</type></dependency></dependencies>",
        );
        assert_eq!(libs, ["g:lib:3.8.1"]);
        assert!(resolver.missing.is_empty(), "{:?}", resolver.missing);
        assert!(resolver.messages.is_empty(), "{:?}", resolver.messages);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 1.0 有 pom 和 jar，1.1 只有 pom（别的工程留下的）：区间 `[1.0,2.0)` 选已有 jar 的 1.0，
    /// 不选只有 pom 的 1.1，不报缺件。
    #[test]
    fn version_range_skips_pom_only_higher_version() {
        let dir = temp_dir("range-pom-only-1-1");
        let repo = dir.join("repo");
        install_version(&repo, "lib", "1.0", "");
        install_version(&repo, "lib", "1.1", "");
        std::fs::remove_file(repo.join("g/lib/1.1/lib-1.1.jar")).unwrap();
        let (libs, resolver) = resolve_root(&dir, repo, &lib_dep("[1.0,2.0)"));
        assert_eq!(libs, ["g:lib:1.0"]);
        assert!(resolver.missing.is_empty(), "{:?}", resolver.missing);
        assert!(resolver.messages.is_empty(), "{:?}", resolver.messages);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 区间也用在 zip 这类不是 jar 的依赖上：候选按 `.zip` 判断，只有 pom 的更高版本不算；
    /// 选中 1.2 后不报缺件，照样读它的 pom、展开传递依赖。
    #[test]
    fn version_range_on_non_jar_type() {
        let dir = temp_dir("range-zip");
        let repo = dir.join("repo");
        install_version(&repo, "lib", "1.0", "");
        install_version(&repo, "dist", "1.2", &lib_dep("1.0"));
        std::fs::remove_file(repo.join("g/dist/1.2/dist-1.2.jar")).unwrap();
        write(&repo.join("g/dist/1.2/dist-1.2.zip"), "");
        install_version(&repo, "dist", "1.3", "");
        std::fs::remove_file(repo.join("g/dist/1.3/dist-1.3.jar")).unwrap();
        let (libs, resolver) = resolve_root(
            &dir,
            repo,
            "<dependencies><dependency><groupId>g</groupId><artifactId>dist</artifactId>\
             <version>[1.0,2.0)</version><type>zip</type></dependency></dependencies>",
        );
        assert_eq!(libs, ["g:lib:1.0"]);
        assert!(resolver.missing.is_empty(), "{:?}", resolver.missing);
        assert!(resolver.messages.is_empty(), "{:?}", resolver.messages);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 区间里没有任何版本有 jar、但有已安装的 pom 时，退而选中最高版本的 pom：
    /// 展开它已安装的传递依赖，同时仍把缺的 jar 报给 Maven 补下载。
    #[test]
    fn version_range_pom_only_fallback_expands_transitives() {
        let dir = temp_dir("range-pom-only-transitives");
        let repo = dir.join("repo");
        install_version(&repo, "child", "1.0", "");
        install_version(
            &repo,
            "lib",
            "1.0",
            "<dependencies><dependency><groupId>g</groupId><artifactId>child</artifactId>\
             <version>1.0</version></dependency></dependencies>",
        );
        std::fs::remove_file(repo.join("g/lib/1.0/lib-1.0.jar")).unwrap();
        let (libs, resolver) = resolve_root(&dir, repo, &lib_dep("[1.0,2.0)"));
        assert_eq!(libs, ["g:child:1.0"]);
        let missing: Vec<_> = resolver
            .missing
            .iter()
            .map(|m| format!("{}:{}:{}", m.artifact, m.version, m.kind))
            .collect();
        assert_eq!(missing, ["lib:1.0:jar"]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 自定义打包类型（如 `hk2-jar`）在本地仓库里仍然是 `.jar`，固定版本不能被误报缺件。
    #[test]
    fn custom_jar_type_resolves_jar() {
        let dir = temp_dir("custom-hk2-jar");
        let repo = dir.join("repo");
        install_version(&repo, "custom", "1.0", "");
        let (libs, resolver) = resolve_root(
            &dir,
            repo,
            "<dependencies><dependency><groupId>g</groupId><artifactId>custom</artifactId>\
             <version>1.0</version><type>hk2-jar</type></dependency></dependencies>",
        );
        assert_eq!(libs, ["g:custom:1.0"]);
        assert!(resolver.missing.is_empty(), "{:?}", resolver.missing);
        assert!(resolver.messages.is_empty(), "{:?}", resolver.messages);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 同时声明 `java-source` 和普通 jar 时，不论先后顺序，都保留正常的二进制 jar。
    #[test]
    fn java_source_type_does_not_shadow_jar() {
        let dir = temp_dir("java-source-order");
        let repo = dir.join("repo");
        install_version(&repo, "lib", "1.0", "");
        write(&repo.join("g/lib/1.0/lib-1.0-sources.jar"), "");
        let src_dep = "<dependency><groupId>g</groupId><artifactId>lib</artifactId>\
                       <version>1.0</version><type>java-source</type></dependency>";
        let jar_dep = "<dependency><groupId>g</groupId><artifactId>lib</artifactId>\
                       <version>1.0</version></dependency>";
        let expected_jar = repo.join("g/lib/1.0/lib-1.0.jar");
        for deps in [format!("{src_dep}{jar_dep}"), format!("{jar_dep}{src_dep}")] {
            let root_pom = dir.join("app/pom.xml");
            write(
                &root_pom,
                &format!(
                    "<project><groupId>g</groupId><artifactId>app</artifactId>\
                     <version>1</version><dependencies>{deps}</dependencies></project>"
                ),
            );
            let mut r = resolver(repo.clone());
            let eff = r.effective(&root_pom, 0).unwrap();
            let jars: Vec<PathBuf> = r
                .resolve_dependencies(&eff)
                .into_iter()
                .filter_map(|dep| match dep {
                    ResolvedDep::Library { jar, .. } => Some(jar),
                    _ => None,
                })
                .collect();
            assert_eq!(jars, std::slice::from_ref(&expected_jar));
            assert!(r.missing.is_empty(), "{:?}", r.missing);
            assert!(r.messages.is_empty(), "{:?}", r.messages);
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 区间的并集：每一段都要看，取所有段里的最高版本。
    #[test]
    fn version_range_union() {
        let dir = temp_dir("range-union");
        let repo = dir.join("repo");
        install_version(&repo, "lib", "2", "");
        install_version(&repo, "lib", "2.5", "");
        let (libs, _) = resolve_root(&dir, repo, &lib_dep("[1,2),(2,3)"));
        assert_eq!(libs, ["g:lib:2.5"]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 区间里一个版本都没有：原样报缺件，交给 Maven 自己按区间下载，不退回下界。
    #[test]
    fn unsatisfied_version_range_stays_missing() {
        let dir = temp_dir("range-missing");
        let repo = dir.join("repo");
        install_version(&repo, "lib", "1.0", "");
        let (libs, resolver) = resolve_root(&dir, repo, &lib_dep("(1.0,2.0)"));
        assert!(libs.is_empty(), "{libs:?}");
        let missing: Vec<&str> = resolver
            .missing
            .iter()
            .map(|m| m.version.as_str())
            .collect();
        assert_eq!(missing, ["(1.0,2.0)"]);
        assert!(
            resolver
                .messages
                .iter()
                .any(|m| m.contains("g:lib:(1.0,2.0)")),
            "{:?}",
            resolver.messages
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// 导入 BOM 时版本写成区间：导入区间内最高的那个 BOM。
    #[test]
    fn bom_import_with_version_range() {
        let dir = temp_dir("range-bom");
        let repo = dir.join("repo");
        for v in ["1.0", "1.1"] {
            install_version(&repo, "lib", v, "");
            install_version(
                &repo,
                "bom",
                v,
                &format!(
                    "<packaging>pom</packaging><dependencyManagement><dependencies>\
                     <dependency><groupId>g</groupId><artifactId>lib</artifactId>\
                     <version>{v}</version></dependency></dependencies></dependencyManagement>"
                ),
            );
            // BOM 只有 pom，没有 jar
            std::fs::remove_file(repo.join(format!("g/bom/{v}/bom-{v}.jar"))).unwrap();
        }
        let (libs, resolver) = resolve_root(
            &dir,
            repo,
            "<dependencyManagement><dependencies><dependency><groupId>g</groupId>\
             <artifactId>bom</artifactId><version>[1.0,2.0)</version><type>pom</type>\
             <scope>import</scope></dependency></dependencies></dependencyManagement>\
             <dependencies><dependency><groupId>g</groupId><artifactId>lib</artifactId>\
             </dependency></dependencies>",
        );
        assert_eq!(libs, ["g:lib:1.1"]);
        assert!(resolver.messages.is_empty(), "{:?}", resolver.messages);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn version_ranges_and_exclusions() {
        use std::cmp::Ordering::{Equal, Less};
        assert_eq!(compare_versions("1.9", "1.10"), Less);
        assert_eq!(compare_versions("1.0", "1.0.0"), Equal);
        assert_eq!(compare_versions("1.0-rc1", "1.0"), Less);
        assert_eq!(compare_versions("1.0-SNAPSHOT", "1.0"), Less);
        assert_eq!(compare_versions("1.0-alpha", "1.0-beta-2"), Less);
        assert_eq!(compare_versions("1.0-rc", "1.0-snapshot"), Less);
        assert_eq!(compare_versions("1.0", "1.0-sp1"), Less);
        assert_eq!(compare_versions("1.0-rc", "1-rc"), Equal);
        assert_eq!(
            compare_versions("1.0.1", "1.0-rc"),
            std::cmp::Ordering::Greater
        );
        let bound = |v: &str, inclusive| Some((v.to_owned(), inclusive));
        assert_eq!(parse_range("1.2.3"), None);
        assert_eq!(
            parse_range("[1.2,2.0)"),
            Some(vec![(bound("1.2", true), bound("2.0", false))])
        );
        assert_eq!(
            parse_range("(,1.0]"),
            Some(vec![(None, bound("1.0", true))])
        );
        assert_eq!(
            parse_range("[1.0,)"),
            Some(vec![(bound("1.0", true), None)])
        );
        assert_eq!(
            parse_range("[1.0]"),
            Some(vec![(bound("1.0", true), bound("1.0", true))])
        );
        assert_eq!(
            parse_range("[1,2), (2,3)"),
            Some(vec![
                (bound("1", true), bound("2", false)),
                (bound("2", false), bound("3", false))
            ])
        );
        let ex = vec![Coord {
            group: "g".into(),
            artifact: "*".into(),
        }];
        assert!(is_excluded(
            &ex,
            &Coord {
                group: "g".into(),
                artifact: "a".into()
            }
        ));
        assert!(!is_excluded(
            &ex,
            &Coord {
                group: "h".into(),
                artifact: "a".into()
            }
        ));
    }
}
