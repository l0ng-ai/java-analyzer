//! Gradle 工程导入。
//!
//! Gradle 的构建脚本是可执行代码，无法静态解析。这里用 `--init-script` 注入一段脚本，
//! 在配置阶段结束时把每个子工程的 source set、编译 classpath 和语言级别写成 JSON。
//! 结果按"构建文件内容的哈希"缓存：构建文件没变时启动不需要调用 Gradle。

use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
    path::{Path, PathBuf},
    process::Command,
};

use base_db::{
    Dependency, DependencyTarget, LibraryData, LibraryId, ModuleData, ModuleId, Scope, SourceRoot,
    SourceRootKind,
};
use rustc_hash::FxHashMap;
use serde::Deserialize;

const INIT_SCRIPT: &str = r#"
// 由 java-analyzer 注入：导出工程模型，不执行任何构建任务。
// 每个子工程注册一个自己的任务，classpath 在任务执行时解析：Gradle 不允许在别的工程
// （或构建级的回调）里解析一个工程的配置。每个工程写一个 JSON 文件到输出目录。
// 组合构建（includeBuild）里的每个构建和 buildSrc 也会执行这个脚本：根构建的汇总任务依赖
// 被包含构建的汇总任务；buildSrc 的模型在它的 jar 任务（每次构建都会执行）之后导出。
import org.gradle.api.artifacts.component.ModuleComponentIdentifier
import org.gradle.api.artifacts.component.ModuleComponentSelector
import org.gradle.api.artifacts.result.UnresolvedDependencyResult

def javaAnalyzerOutput = new File(System.getProperty('javaAnalyzer.output'))
// 被包含的构建和 buildSrc 的文件名带上构建的路径，排在根构建的工程后面
def javaAnalyzerBuildPath = { g ->
    def names = []
    def current = g
    while (current.parent != null) {
        names.add(0, current.rootProject.name)
        current = current.parent
    }
    names
}
allprojects { p ->
    p.afterEvaluate {
        def sourceSets = p.extensions.findByName('sourceSets')
        def androidExtension = p.extensions.findByName('android')
        // AGP Android projects expose no top-level `sourceSets` (their sources live under
        // the `android` extension), so the vanilla check below would skip the whole module.
        // Keep such projects: the model task has a dedicated AGP branch that reads the
        // boot classpath (android.jar) and the variants' compile classpaths.
        if (sourceSets == null && androidExtension == null) {
            return
        }
        def javaExtension = p.extensions.findByName('java')
        def compileTasks = p.tasks.withType(JavaCompile)
        def projectName = p.name
        def projectDir = p.projectDir.absolutePath
        def buildDir = p.layout.buildDirectory.get().asFile.absolutePath
        def buildPath = javaAnalyzerBuildPath(p.gradle)
        def isBuildSrc = p.gradle.parent != null && p.rootProject.name == 'buildSrc'
            && p.rootProject.projectDir.name == 'buildSrc'
        def localName = p.path == ':' ? 'root' : p.path.substring(1).replace(':', '.')
        def fileName = (buildPath.isEmpty() ? '' : '~' + buildPath.join('~') + '~') + localName + '.json'
        def model = p.tasks.register('javaAnalyzerModel') {
            doLast {
                def sets = []

                // ---- Android (AGP) projects ----
                // AGP has no top-level Java sourceSets, so iterate the Android variants and
                // take the boot classpath (android.jar) plus each variant's javac classpath.
                // This is done here in doLast because AGP populates bootClasspath/variants
                // only once the configuration phase is fully over (afterEvaluate is too early).
                if (androidExtension != null) {
                    def boot = []
                    try { boot = (androidExtension.bootClasspath ?: []).collect { it.absolutePath } } catch (Throwable ignored) {}
                    def srcDirsAll = [] as LinkedHashSet
                    def cpAll = [] as LinkedHashSet
                    def variants = []
                    try { variants = androidExtension.applicationVariants ?: [] } catch (Throwable ignored) {}
                    if (variants.isEmpty()) {
                        try { variants = androidExtension.libraryVariants ?: [] } catch (Throwable ignored) {}
                    }
                    variants.each { v ->
                        try {
                            def jc = v.javaCompileProvider.get()
                            jc.classpath.files.each { cpAll << it.absolutePath }
                            // javac source is a FilteredFileTree; get its srcDirs via the variant's
                            // sourceSets instead, which is stable across AGP versions.
                            v.sourceSets.each { sset ->
                                sset.java.srcDirs.each { srcDirsAll << it.absolutePath }
                            }
                        } catch (Throwable ignored) {
                        }
                    }
                    // Fallback source dirs from the well-known AGP layout when variant sourceSets
                    // did not yield anything.
                    if (srcDirsAll.isEmpty()) {
                        ['src/main/java', 'src/main/kotlin'].each { rel ->
                            def d = new File(p.projectDir, rel)
                            if (d.isDirectory()) srcDirsAll << d.absolutePath
                        }
                    }
                    def agpCp = []
                    boot.each { agpCp << it }
                    cpAll.each { agpCp << it }
                    sets << [
                        name       : 'main',
                        srcDirs    : srcDirsAll.toList(),
                        classpath  : agpCp,
                        outputDirs : [],
                        coordinates: [:],
                        unresolved : [],
                    ]
                }

                sourceSets.each { ss ->
                    def classpath = []
                    def coordinates = [:]
                    def unresolved = []
                    def configuration = p.configurations.findByName(ss.compileClasspathConfigurationName)
                    // 宽松解析：解析不到的依赖（可能是另一个工作区根里的模块）不影响其余的 classpath
                    def lenientFiles = []
                    try {
                        if (configuration != null && configuration.canBeResolved) {
                            configuration.incoming.artifactView { lenient = true }.artifacts.each { a ->
                                def path = a.file.absolutePath
                                lenientFiles << path
                                def id = a.id.componentIdentifier
                                if (id instanceof ModuleComponentIdentifier) {
                                    coordinates[path] = "${id.group}:${id.module}:${id.version}".toString()
                                }
                            }
                            configuration.incoming.resolutionResult.allDependencies.each { d ->
                                if (d instanceof UnresolvedDependencyResult && d.requested instanceof ModuleComponentSelector) {
                                    def coordinate = "${d.requested.group}:${d.requested.module}".toString()
                                    if (!unresolved.contains(coordinate)) {
                                        unresolved << coordinate
                                    }
                                }
                            }
                        }
                    } catch (Throwable ignored) {
                    }
                    try {
                        ss.compileClasspath.files.each { classpath << it.absolutePath }
                    } catch (Throwable ignored) {
                        classpath = lenientFiles
                    }
                    sets << [
                        name       : ss.name,
                        srcDirs    : ss.java.srcDirs.collect { it.absolutePath },
                        classpath  : classpath,
                        outputDirs : ss.output.classesDirs.files.collect { it.absolutePath },
                        coordinates: coordinates,
                        unresolved : unresolved,
                    ]
                }
                def level = null
                try {
                    level = javaExtension?.sourceCompatibility?.majorVersion
                } catch (Throwable ignored) {
                }
                // AGP projects have no `java` extension; fall back to the compile tasks' release
                // (set by compileOptions/JavaVersion) or a sane default for modern Android.
                if (level == null && androidExtension != null) {
                    try {
                        compileTasks.each { task ->
                            def r = task.options.release.getOrNull()
                            if (r != null) { level = r.toString() }
                        }
                    } catch (Throwable ignored) {
                    }
                }
                def preview = false
                def release = null
                def encoding = null
                try {
                    compileTasks.each { task ->
                        if (task.options.compilerArgs.contains('--enable-preview')) {
                            preview = true
                        }
                        // compileJava 的编码优先，没设置时取别的编译任务的
                        try {
                            def e = task.options.encoding
                            if (e instanceof org.gradle.api.provider.Provider) {
                                e = e.getOrNull()
                            }
                            e = e?.toString()
                            if (e != null && (encoding == null || task.name == 'compileJava')) {
                                encoding = e
                            }
                        } catch (Throwable ignored) {
                        }
                        def r = task.options.release.getOrNull()
                        if (r != null && (release == null || r > release)) {
                            release = r
                        }
                    }
                } catch (Throwable ignored) {
                }
                javaAnalyzerOutput.mkdirs()
                new File(javaAnalyzerOutput, fileName).text = groovy.json.JsonOutput.toJson([
                    name         : projectName,
                    group        : p.group?.toString() ?: '',
                    dir          : projectDir,
                    buildDir     : buildDir,
                    build        : buildPath.join(':'),
                    buildSrc     : isBuildSrc,
                    languageLevel: level,
                    preview      : preview,
                    release      : release,
                    encoding     : encoding,
                    sourceSets   : sets,
                ])
            }
        }
        if (isBuildSrc) {
            p.tasks.matching { it.name == 'jar' }.configureEach { finalizedBy model }
        }
    }
}
// 每个构建的根工程上的汇总任务：本构建所有工程的导出任务，加上被包含构建的汇总任务
rootProject { root ->
    root.tasks.register('javaAnalyzerModels') {
        dependsOn root.provider {
            root.allprojects.collect { it.tasks.findByName('javaAnalyzerModel') }.findAll { it != null }
        }
        root.gradle.includedBuilds.each { included ->
            dependsOn included.task(':javaAnalyzerModels')
        }
    }
}
"#;

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct GradleSourceSet {
    name: String,
    #[serde(default)]
    src_dirs: Vec<PathBuf>,
    #[serde(default)]
    classpath: Vec<PathBuf>,
    #[serde(default)]
    output_dirs: Vec<PathBuf>,
    /// classpath 里来自仓库的构件 → `group:name:version`
    #[serde(default)]
    coordinates: FxHashMap<PathBuf, String>,
    /// 解析不到的依赖（`group:name`）：可能是另一个工作区根里的模块
    #[serde(default)]
    unresolved: Vec<String>,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct GradleProject {
    name: String,
    /// `project.group`，没有设置时为空
    #[serde(default)]
    group: String,
    dir: PathBuf,
    build_dir: PathBuf,
    #[serde(default)]
    language_level: Option<String>,
    #[serde(default)]
    preview: bool,
    /// `JavaCompile.options.release`
    #[serde(default)]
    release: Option<u32>,
    /// `JavaCompile.options.encoding`，`compileJava` 的优先
    #[serde(default)]
    encoding: Option<String>,
    #[serde(default)]
    source_sets: Vec<GradleSourceSet>,
    /// buildSrc 构建里的工程：它的类只给构建脚本用
    #[serde(default)]
    build_src: bool,
}

#[derive(Default)]
pub struct GradleImport {
    pub modules: Vec<ModuleData>,
    pub libraries: Vec<LibraryData>,
    pub messages: Vec<String>,
    /// 各模块的 `group` 和 `name`（没有 group 的不算），跨工作区根链接时用
    pub coordinates: Vec<(ModuleId, String, String)>,
    /// 解析不到的依赖
    pub unresolved: Vec<crate::UnresolvedDep>,
}

const BUILD_FILE_NAMES: &[&str] = &[
    "settings.gradle",
    "settings.gradle.kts",
    "build.gradle",
    "build.gradle.kts",
    "gradle.properties",
];

pub fn is_gradle_root(dir: &Path) -> bool {
    [
        "settings.gradle",
        "settings.gradle.kts",
        "build.gradle",
        "build.gradle.kts",
    ]
    .iter()
    .any(|name| dir.join(name).is_file())
}

/// `settings.gradle(.kts)` 里 `includeBuild("../lib")` / `includeBuild '../lib'` 引入的构建目录。
/// 只认字面量路径；用来监视被包含构建的构建文件。
pub fn included_builds(root: &Path) -> Vec<PathBuf> {
    let mut res = Vec::new();
    for name in ["settings.gradle", "settings.gradle.kts"] {
        let Ok(text) = std::fs::read_to_string(root.join(name)) else {
            continue;
        };
        let mut rest = text.as_str();
        while let Some(idx) = rest.find("includeBuild") {
            rest = &rest[idx + "includeBuild".len()..];
            // 关键字后面紧跟的第一个字符串字面量
            let arg = rest.trim_start().trim_start_matches('(').trim_start();
            let Some(quote) = arg.chars().next().filter(|c| *c == '"' || *c == '\'') else {
                continue;
            };
            let Some(end) = arg[1..].find(quote) else {
                continue;
            };
            let Ok(dir) = crate::canonicalize(&root.join(&arg[1..1 + end])) else {
                continue;
            };
            if dir.is_dir() && !res.contains(&dir) {
                res.push(dir);
            }
        }
    }
    res
}

/// 所有可能影响工程模型的构建文件（根目录和两层以内的子目录，外加版本目录和被包含构建的构建文件）。
pub fn build_files(root: &Path) -> Vec<PathBuf> {
    let mut out = own_build_files(root);
    let canonical_root = crate::canonicalize(root).unwrap_or_else(|_| root.to_path_buf());
    for included in included_builds(root) {
        // 在根目录里面的已经算过了
        if !included.starts_with(&canonical_root) {
            out.extend(own_build_files(&included));
        }
    }
    out.sort();
    out.dedup();
    out
}

fn own_build_files(root: &Path) -> Vec<PathBuf> {
    fn visit(dir: &Path, depth: u32, out: &mut Vec<PathBuf>) {
        for name in BUILD_FILE_NAMES {
            let path = dir.join(name);
            if path.is_file() {
                out.push(path);
            }
        }
        if depth == 0 {
            return;
        }
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if path.is_dir() && !name.starts_with('.') && name != "build" && name != "node_modules"
            {
                visit(&path, depth - 1, out);
            }
        }
    }
    let mut out = Vec::new();
    visit(root, 2, &mut out);
    let catalog = root.join("gradle/libs.versions.toml");
    if catalog.is_file() {
        out.push(catalog);
    }
    let wrapper = root.join("gradle/wrapper/gradle-wrapper.properties");
    if wrapper.is_file() {
        out.push(wrapper);
    }
    out.sort();
    out
}

fn cache_key(root: &Path) -> u64 {
    let mut hasher = DefaultHasher::new();
    root.hash(&mut hasher);
    INIT_SCRIPT.hash(&mut hasher);
    EXPORT_ARGS.hash(&mut hasher);
    CONFIGURE_ALL.hash(&mut hasher);
    for file in build_files(root) {
        file.hash(&mut hasher);
        if let Ok(content) = std::fs::read(&file) {
            content.hash(&mut hasher);
        }
    }
    hasher.finish()
}

fn cache_dir() -> Option<PathBuf> {
    Some(dirs::cache_dir()?.join("java-analyzer").join("gradle"))
}

/// 运行 Gradle 导出模型，返回 JSON 文本（各工程的模型组成的数组）。
fn run_gradle(root: &Path) -> Result<String, String> {
    let tmp = std::env::temp_dir();
    let pid = std::process::id();
    let script = tmp.join(format!("java-analyzer-init-{pid}.gradle"));
    let output = tmp.join(format!("java-analyzer-model-{pid}"));
    let _ = std::fs::remove_dir_all(&output);
    std::fs::write(&script, INIT_SCRIPT).map_err(|e| {
        base_db::tr!(
            "写入 init script 失败: {e}",
            "Failed to write the init script: {e}"
        )
    })?;

    let wrapper = root.join(if cfg!(windows) {
        "gradlew.bat"
    } else {
        "gradlew"
    });
    let program = if wrapper.is_file() {
        wrapper
    } else {
        PathBuf::from("gradle")
    };
    let result = export(&program, root, &script, &output, &[CONFIGURE_ALL])
        .or_else(|_| export(&program, root, &script, &output, &[]));
    let _ = std::fs::remove_file(&script);
    result
}

/// 运行一次导出（等 wrapper 锁时重试），读出模型。
fn export(
    program: &Path,
    root: &Path,
    script: &Path,
    output: &Path,
    extra: &[&str],
) -> Result<String, String> {
    let mut attempt = 1;
    let result = loop {
        let result = run_export(program, root, script, output, extra);
        match &result {
            Ok(out)
                if !out.status.success()
                    && attempt < WRAPPER_LOCK_ATTEMPTS
                    && waited_for_wrapper_lock(&String::from_utf8_lossy(&out.stderr)) =>
            {
                attempt += 1;
            }
            _ => break result,
        }
    };

    let result = result.map_err(|e| {
        base_db::tr!(
            "无法启动 {}: {e}",
            "Failed to start {}: {e}",
            program.display()
        )
    })?;
    if !result.status.success() {
        let _ = std::fs::remove_dir_all(output);
        let stderr = String::from_utf8_lossy(&result.stderr);
        let tail: Vec<&str> = stderr.lines().rev().take(15).collect();
        let tail: Vec<&str> = tail.into_iter().rev().collect();
        return Err(base_db::tr!(
            "Gradle 导入失败:\n{}",
            "Gradle import failed:\n{}",
            tail.join("\n")
        ));
    }
    let json = read_model_dir(output).map_err(|e| {
        base_db::tr!(
            "读取导出的模型失败: {e}",
            "Failed to read the exported model: {e}"
        )
    });
    let _ = std::fs::remove_dir_all(output);
    json
}

/// 另一个进程（IDE 的构建同步、终端里的 `./gradlew`）正在下载同一个 wrapper 发行包时，
/// wrapper 等独占锁 120 秒后放弃。首次下载慢时这只说明要再等，不是导入失败。
const WRAPPER_LOCK_ATTEMPTS: u32 = 5;

fn waited_for_wrapper_lock(stderr: &str) -> bool {
    stderr.contains("waiting for exclusive access to file") && stderr.contains("org.gradle.wrapper")
}

/// 导出时固定传给 Gradle 的参数，也参与缓存键：参数变了，旧参数导出的模型要作废。
const EXPORT_ARGS: &[&str] = &[
    // 导出任务在执行时读工程模型，和配置缓存不兼容；旧版本 Gradle 不认识的系统属性会被忽略
    "-Dorg.gradle.configuration-cache=false",
    "-Dorg.gradle.unsafe.configuration-cache=false",
    "-q",
    "--console=plain",
    ":javaAnalyzerModels",
];

/// 导出任务要读每个工程的模型；按需配置会让子工程不被配置，它们的 afterEvaluate 注册不会执行。
/// 但按需配置也会跳过配置时就出错的子工程，关掉后整个导出失败；这时按工程自己的设置再导出一次，
/// 缓存实际用到的模型（修好坏子工程会改变构建文件，缓存键随之变化，下次会重新尝试完整导出）。
const CONFIGURE_ALL: &str = "-Dorg.gradle.configureondemand=false";

fn run_export(
    program: &Path,
    root: &Path,
    script: &Path,
    output: &Path,
    extra: &[&str],
) -> std::io::Result<std::process::Output> {
    let _ = std::fs::remove_dir_all(output);
    Command::new(program)
        .current_dir(root)
        .arg("--init-script")
        .arg(script)
        .arg(format!("-DjavaAnalyzer.output={}", output.display()))
        .args(extra)
        .args(EXPORT_ARGS)
        .output()
}

/// 输出目录里每个工程一个 JSON 对象，按文件名排序后拼成一个数组。
fn read_model_dir(dir: &Path) -> std::io::Result<String> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)?
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
        .collect();
    files.sort();
    let mut parts = Vec::with_capacity(files.len());
    for file in files {
        parts.push(std::fs::read_to_string(file)?);
    }
    Ok(format!("[{}]", parts.join(",")))
}

/// Gradle 缓存里与 jar 相邻的 sources jar：
/// `files-2.1/<group>/<name>/<version>/<hash>/<name>-<version>.jar`，sources 在另一个 hash 目录下。
fn find_sources_jar(jar: &Path) -> Option<PathBuf> {
    let stem = jar.file_stem()?.to_string_lossy().into_owned();
    let version_dir = jar.parent()?.parent()?;
    let wanted = format!("{stem}-sources.jar");
    for hash_dir in std::fs::read_dir(version_dir).ok()?.flatten() {
        let candidate = hash_dir.path().join(&wanted);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

/// Gradle 缓存里的 jar 的坐标：`files-2.1/<group>/<name>/<version>/<hash>/<file>.jar`。
fn cache_coordinates(jar: &Path) -> Option<String> {
    let mut parts = jar.iter().rev().skip(2).take(3);
    let version = parts.next()?.to_str()?;
    let name = parts.next()?.to_str()?;
    let group = parts.next()?.to_str()?;
    let in_cache = jar.iter().rev().nth(5).is_some_and(|p| p == "files-2.1");
    in_cache.then(|| format!("{group}:{name}:{version}"))
}

enum TestOutput {
    No,
    Yes,
    Maybe,
}

/// classpath 里指向工程 `project` 产物的条目是不是它的测试代码：测试类源码集（名字里带 test，
/// 包括 testFixtures）的输出目录是；名字里带 test 的 jar 可能是。
fn test_output(project: &GradleProject, entry: &Path) -> TestOutput {
    let test_set = |set: &GradleSourceSet| set.name.to_lowercase().contains("test");
    if let Some(set) = project
        .source_sets
        .iter()
        .find(|set| set.output_dirs.iter().any(|d| d == entry))
    {
        return if test_set(set) {
            TestOutput::Yes
        } else {
            TestOutput::No
        };
    }
    let test_jar = entry.extension().is_some_and(|ext| ext == "jar")
        && entry
            .file_stem()
            .is_some_and(|stem| stem.to_string_lossy().to_lowercase().contains("test"));
    if test_jar {
        TestOutput::Maybe
    } else {
        TestOutput::No
    }
}

fn convert(projects: Vec<GradleProject>) -> GradleImport {
    let mut import = GradleImport::default();
    let mut library_ids: FxHashMap<PathBuf, LibraryId> = FxHashMap::default();

    // 先排好模块下标，classpath 里指向别的子工程产物的条目要转成模块依赖
    let project_ids: Vec<ModuleId> = (0..projects.len()).map(|i| ModuleId(i as u32)).collect();
    let owner_of = |path: &Path| -> Option<ModuleId> {
        projects
            .iter()
            .zip(&project_ids)
            .find(|(p, _)| path.starts_with(&p.build_dir))
            .map(|(_, id)| *id)
    };

    for (idx, project) in projects.iter().enumerate() {
        let mut source_roots = Vec::new();
        let mut output_dirs: Vec<SourceRoot> = Vec::new();
        let mut dependencies: Vec<Dependency> = Vec::new();

        for set in &project.source_sets {
            let is_test = set.name.to_lowercase().contains("test");
            let kind = if is_test {
                SourceRootKind::Test
            } else {
                SourceRootKind::Main
            };
            for dir in &set.output_dirs {
                if !output_dirs.iter().any(|d| &d.path == dir) {
                    output_dirs.push(SourceRoot {
                        path: dir.clone(),
                        kind,
                    });
                }
            }
            for dir in &set.src_dirs {
                if dir.is_dir() {
                    let generated = dir.starts_with(&project.build_dir);
                    source_roots.push(SourceRoot {
                        path: dir.clone(),
                        kind: if generated {
                            SourceRootKind::Generated
                        } else {
                            kind
                        },
                    });
                }
            }
            let scope = if is_test { Scope::Test } else { Scope::Compile };
            for entry in &set.classpath {
                // 本工程自己的输出目录（test 依赖 main）不算依赖
                if set.output_dirs.contains(entry) || entry.starts_with(&project.build_dir) {
                    continue;
                }
                let targets: Vec<DependencyTarget> = match owner_of(entry) {
                    Some(module) if module == project_ids[idx] => continue,
                    Some(module) => match test_output(&projects[module.0 as usize], entry) {
                        TestOutput::No => vec![DependencyTarget::Module(module)],
                        TestOutput::Yes => vec![DependencyTarget::ModuleTests(module)],
                        // 名字里带 test 的 jar 分不清是测试代码还是主代码，两样都算
                        TestOutput::Maybe => vec![
                            DependencyTarget::Module(module),
                            DependencyTarget::ModuleTests(module),
                        ],
                    },
                    None => {
                        if !entry.is_file() {
                            continue;
                        }
                        let id = *library_ids.entry(entry.clone()).or_insert_with(|| {
                            // 有坐标的构件按 `group:name:version` 命名，和 Maven 导入的一致
                            let name = set
                                .coordinates
                                .get(entry)
                                .cloned()
                                .or_else(|| cache_coordinates(entry))
                                .unwrap_or_else(|| {
                                    entry
                                        .file_name()
                                        .map(|n| n.to_string_lossy().into_owned())
                                        .unwrap_or_default()
                                });
                            import.libraries.push(LibraryData {
                                name,
                                jar: entry.clone(),
                                sources: find_sources_jar(entry),
                            });
                            LibraryId((import.libraries.len() - 1) as u32)
                        });
                        vec![DependencyTarget::Library(id)]
                    }
                };
                for target in targets {
                    // 同一个依赖同时出现在 main 和 test 里时保留 Compile
                    match dependencies.iter_mut().find(|d| d.target == target) {
                        Some(existing) => {
                            if scope == Scope::Compile {
                                existing.scope = Scope::Compile;
                            }
                        }
                        None => dependencies.push(Dependency { target, scope }),
                    }
                }
            }
            for coordinate in &set.unresolved {
                let Some((group, artifact)) = coordinate.split_once(':') else {
                    continue;
                };
                let module = project_ids[idx];
                match import
                    .unresolved
                    .iter_mut()
                    .find(|d| d.module == module && d.group == group && d.artifact == artifact)
                {
                    Some(existing) => {
                        if scope == Scope::Compile {
                            existing.scope = Scope::Compile;
                        }
                    }
                    None => import.unresolved.push(crate::UnresolvedDep {
                        module,
                        group: group.to_owned(),
                        artifact: artifact.to_owned(),
                        scope,
                    }),
                }
            }
        }

        // 注解处理器生成的源码目录
        for generated in [
            "generated/sources/annotationProcessor/java/main",
            "generated/sources/annotationProcessor/java/test",
        ] {
            let dir = project.build_dir.join(generated);
            if dir.is_dir() && !source_roots.iter().any(|r| r.path == dir) {
                source_roots.push(SourceRoot {
                    path: dir,
                    kind: SourceRootKind::Generated,
                });
            }
        }

        if !project.group.is_empty() && !project.build_src {
            import.coordinates.push((
                project_ids[idx],
                project.group.clone(),
                project.name.clone(),
            ));
        }
        import.modules.push(ModuleData {
            name: project.name.clone(),
            root: project.dir.clone(),
            source_roots,
            language_level: project
                .language_level
                .as_deref()
                .and_then(crate::jdk::parse_feature_version),
            api_release: project.release,
            test_language_level: None,
            preview: project.preview,
            dependencies,
            output_dirs,
            encoding: project.encoding.clone().filter(|e| !e.trim().is_empty()),
            transitive_dependencies: false,
        });
    }
    import
}

/// `root` 处的 Gradle 工程当前对应的缓存文件。构建文件的内容变了，路径也会变。
/// 也用于测试：预先写入导出的模型，就能在不运行 Gradle 的情况下导入。
pub fn cache_file(root: &Path) -> Option<PathBuf> {
    cache_dir().map(|dir| dir.join(format!("{:016x}.json", cache_key(root))))
}

/// 导入 Gradle 工程。`allow_run` 为假时只使用缓存，不调用 Gradle。
pub fn import(root: &Path, allow_run: bool) -> Option<GradleImport> {
    let cache_file = cache_file(root);

    let cached = cache_file
        .as_ref()
        .and_then(|path| std::fs::read_to_string(path).ok());
    let (json, from_cache) = match cached {
        Some(json) => (json, true),
        None if allow_run => match run_gradle(root) {
            Ok(json) => (json, false),
            Err(message) => {
                return Some(GradleImport {
                    messages: vec![message],
                    ..GradleImport::default()
                })
            }
        },
        None => return None,
    };

    let projects: Vec<GradleProject> = match serde_json::from_str(&json) {
        Ok(projects) => projects,
        Err(err) => {
            if let Some(path) = &cache_file {
                let _ = std::fs::remove_file(path);
            }
            return Some(GradleImport {
                messages: vec![base_db::tr!(
                    "无法解析 Gradle 导出的模型: {err}",
                    "Cannot parse the model exported by Gradle: {err}"
                )],
                ..GradleImport::default()
            });
        }
    };

    if !from_cache {
        if let Some(path) = &cache_file {
            if let Some(dir) = path.parent() {
                let _ = std::fs::create_dir_all(dir);
            }
            let _ = std::fs::write(path, &json);
        }
    }
    Some(convert(projects))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wrapper_lock_timeout_is_recognised() {
        let stderr = "Exception in thread \"main\" java.lang.RuntimeException: Timeout of 120000 reached waiting for exclusive access to file: /home/u/.gradle/wrapper/dists/gradle-9.9.1-bin/x/gradle-9.9.1-bin.zip\n\tat org.gradle.internal.file.locking.ExclusiveFileAccessManager.access(SourceFile:3)\n\tat org.gradle.wrapper.Install.createDist(SourceFile:21)\n";
        assert!(waited_for_wrapper_lock(stderr));
        assert!(!waited_for_wrapper_lock("FAILURE: Build failed with an exception.\n* What went wrong:\nCould not resolve all dependencies"));
    }

    #[test]
    fn export_disables_configure_on_demand() {
        assert_eq!(CONFIGURE_ALL, "-Dorg.gradle.configureondemand=false");
    }

    /// 按需配置原本跳过的坏子工程会让关掉按需配置的导出失败，这时退回按工程自己的设置导出
    #[cfg(unix)]
    #[test]
    fn failed_export_retries_with_configure_on_demand() {
        use std::os::unix::fs::PermissionsExt;
        let root = std::env::temp_dir().join(format!("ja-gradle-fallback-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).unwrap();
        let gradlew = root.join("gradlew");
        std::fs::write(
            &gradlew,
            r#"#!/bin/sh
for a in "$@"; do
  case "$a" in
    -Dorg.gradle.configureondemand=false) echo "boom" >&2; exit 1;;
    -DjavaAnalyzer.output=*) out="${a#-DjavaAnalyzer.output=}";;
  esac
done
mkdir -p "$out" && echo '{"path":":"}' > "$out/root.json"
"#,
        )
        .unwrap();
        std::fs::set_permissions(&gradlew, std::fs::Permissions::from_mode(0o755)).unwrap();
        let json = run_gradle(&root);
        std::fs::remove_dir_all(&root).unwrap();
        assert_eq!(
            json.unwrap().replace(char::is_whitespace, ""),
            r#"[{"path":":"}]"#
        );
    }

    #[test]
    fn model_files_are_joined_into_one_array() {
        let dir = std::env::temp_dir().join(format!("ja-gradle-model-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("core.json"),
            r#"{"name":"core","dir":"/p/core","buildDir":"/p/core/build"}"#,
        )
        .unwrap();
        std::fs::write(
            dir.join("app.json"),
            r#"{"name":"app","dir":"/p/app","buildDir":"/p/app/build"}"#,
        )
        .unwrap();
        std::fs::write(dir.join("ignored.txt"), "x").unwrap();
        let json = read_model_dir(&dir).unwrap();
        let _ = std::fs::remove_dir_all(&dir);
        let projects: Vec<GradleProject> = serde_json::from_str(&json).unwrap();
        let names: Vec<&str> = projects.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(names, vec!["app", "core"]);
    }

    #[test]
    fn converts_exported_model() {
        let json = r#"[
            {"name":"app","dir":"/w/app","buildDir":"/w/app/build","languageLevel":"17",
             "encoding":"UTF-8",
             "sourceSets":[{"name":"main","srcDirs":["/w/app/src/main/java"],
                            "classpath":["/w/lib/build/libs/lib.jar"],"outputDirs":[]}]},
            {"name":"lib","dir":"/w/lib","buildDir":"/w/lib/build","languageLevel":null,"sourceSets":[]}
        ]"#;
        let projects: Vec<GradleProject> = serde_json::from_str(json).unwrap();
        let import = convert(projects);
        assert_eq!(import.modules.len(), 2);
        assert_eq!(import.modules[0].language_level, Some(17));
        assert_eq!(import.modules[0].encoding.as_deref(), Some("UTF-8"));
        assert_eq!(import.modules[1].encoding, None);
        assert_eq!(
            import.modules[0].dependencies,
            vec![Dependency {
                target: DependencyTarget::Module(ModuleId(1)),
                scope: Scope::Compile
            }]
        );
        assert!(import.libraries.is_empty());
    }

    #[test]
    fn test_outputs_of_other_projects_are_module_tests() {
        let json = r#"[
            {"name":"app","dir":"/w/app","buildDir":"/w/app/build","sourceSets":[
                {"name":"main","srcDirs":[],"classpath":["/w/core/build/classes/java/main"],
                 "outputDirs":["/w/app/build/classes/java/main"]},
                {"name":"test","srcDirs":[],"classpath":[
                    "/w/app/build/classes/java/main",
                    "/w/core/build/classes/java/main",
                    "/w/core/build/classes/java/testFixtures",
                    "/w/kit/build/libs/kit-test-utils.jar"],
                 "outputDirs":["/w/app/build/classes/java/test"]}]},
            {"name":"core","dir":"/w/core","buildDir":"/w/core/build","sourceSets":[
                {"name":"main","srcDirs":[],"classpath":[],"outputDirs":["/w/core/build/classes/java/main"]},
                {"name":"testFixtures","srcDirs":[],"classpath":[],
                 "outputDirs":["/w/core/build/classes/java/testFixtures"]}]},
            {"name":"kit","dir":"/w/kit","buildDir":"/w/kit/build","sourceSets":[]}
        ]"#;
        let projects: Vec<GradleProject> = serde_json::from_str(json).unwrap();
        let import = convert(projects);
        let dep = |target, scope| Dependency { target, scope };
        assert_eq!(
            import.modules[0].dependencies,
            vec![
                dep(DependencyTarget::Module(ModuleId(1)), Scope::Compile),
                dep(DependencyTarget::ModuleTests(ModuleId(1)), Scope::Test),
                // 名字里带 test 的 jar 分不清，主代码和测试代码都算
                dep(DependencyTarget::Module(ModuleId(2)), Scope::Test),
                dep(DependencyTarget::ModuleTests(ModuleId(2)), Scope::Test),
            ]
        );
    }

    /// 组合构建里的模块：运行 / 测试类路径跨构建取依赖模块的输出目录和 jar。
    #[test]
    fn runtime_class_path_across_included_builds() {
        let dir = std::env::temp_dir().join(format!("ja-gradle-runtime-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let touch = |relative: &str| crate::runtime::tests::touch(&dir, relative);
        let app_main = touch("app/build/classes/java/main/");
        let app_test = touch("app/build/classes/java/test/");
        let common = touch("platform/common/build/classes/java/main/");
        let testkit = touch("platform/testkit/build/classes/java/main/");
        let gson = touch("cache/gson-2.11.0.jar");
        let guava = touch("cache/guava-33.0.jar");
        let junit = touch("cache/junit-5.10.jar");
        let json = serde_json::json!([
            {"name": "app", "dir": dir.join("app"), "buildDir": dir.join("app/build"), "sourceSets": [
                {"name": "main", "outputDirs": [app_main], "classpath": [common, gson]},
                {"name": "test", "outputDirs": [app_test], "classpath": [app_main, testkit, common, gson, junit]}]},
            {"name": "common", "dir": dir.join("platform/common"), "buildDir": dir.join("platform/common/build"),
             "sourceSets": [{"name": "main", "outputDirs": [common], "classpath": [guava]}]},
            {"name": "testkit", "dir": dir.join("platform/testkit"), "buildDir": dir.join("platform/testkit/build"),
             "sourceSets": [{"name": "main", "outputDirs": [testkit], "classpath": [common]}]}
        ]);
        let import = convert(serde_json::from_value(json).unwrap());
        let graph = base_db::ProjectGraph {
            modules: import.modules,
            libraries: import.libraries,
            jdk: None,
        };
        let runtime = crate::runtime_class_path(&graph, ModuleId(0), false);
        assert_eq!(runtime.output_dirs, std::slice::from_ref(&app_main));
        assert_eq!(
            runtime.entries,
            [
                app_main.clone(),
                common.clone(),
                gson.clone(),
                guava.clone()
            ]
        );
        let test = crate::runtime_class_path(&graph, ModuleId(0), true);
        assert_eq!(test.output_dirs, [app_test.clone(), app_main.clone()]);
        assert_eq!(
            test.entries,
            [
                app_test,
                app_main,
                common.clone(),
                gson,
                testkit,
                junit,
                guava.clone()
            ]
        );
        // 被包含的构建里的模块自己的类路径
        assert_eq!(
            crate::runtime_class_path(&graph, ModuleId(1), false).entries,
            [common, guava]
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn reads_composite_build_model() {
        let dir = std::env::temp_dir().join(format!("ja-gradle-composite-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let gson = dir.join(
            "caches/modules-2/files-2.1/com.google.code.gson/gson/2.11.0/abc/gson-2.11.0.jar",
        );
        let local = dir.join("app/libs/local.jar");
        for jar in [&gson, &local] {
            std::fs::create_dir_all(jar.parent().unwrap()).unwrap();
            std::fs::write(jar, "").unwrap();
        }
        let d = |path: &str| dir.join(path).display().to_string();
        // 根构建 app，被包含的构建 platform（common、testkit），以及 buildSrc
        let json = serde_json::json!([
            {"name": "app", "group": "", "dir": d("app"), "buildDir": d("app/build"), "sourceSets": [
                {"name": "main", "srcDirs": [], "outputDirs": [d("app/build/classes/java/main")],
                 "classpath": [d("platform/common/build/classes/java/main"), gson, local],
                 "coordinates": {gson.display().to_string(): "com.google.code.gson:gson:2.11.0"},
                 "unresolved": ["com.acme.users:api"]},
                {"name": "test", "srcDirs": [], "outputDirs": [d("app/build/classes/java/test")],
                 "classpath": [d("app/build/classes/java/main"), d("platform/testkit/build/classes/java/main"),
                               d("platform/common/build/classes/java/main")],
                 "unresolved": ["com.acme.users:api", "com.acme.users:testkit"]}]},
            {"name": "common", "group": "com.acme.platform", "dir": d("platform/common"),
             "buildDir": d("platform/common/build"), "sourceSets": [
                {"name": "main", "srcDirs": [], "classpath": [gson],
                 "outputDirs": [d("platform/common/build/classes/java/main")]}]},
            {"name": "testkit", "group": "com.acme.platform", "dir": d("platform/testkit"),
             "buildDir": d("platform/testkit/build"), "sourceSets": [
                {"name": "main", "srcDirs": [], "classpath": [d("platform/common/build/classes/java/main")],
                 "outputDirs": [d("platform/testkit/build/classes/java/main")]}]},
            {"name": "buildSrc", "group": "com.acme", "dir": d("app/buildSrc"), "buildDir": d("app/buildSrc/build"),
             "buildSrc": true, "sourceSets": []}
        ]);
        let projects: Vec<GradleProject> = serde_json::from_value(json).unwrap();
        let import = convert(projects);
        let _ = std::fs::remove_dir_all(&dir);
        let dep = |target, scope| Dependency { target, scope };
        assert_eq!(
            import.modules[0].dependencies,
            vec![
                dep(DependencyTarget::Module(ModuleId(1)), Scope::Compile),
                dep(DependencyTarget::Library(LibraryId(0)), Scope::Compile),
                dep(DependencyTarget::Library(LibraryId(1)), Scope::Compile),
                dep(DependencyTarget::Module(ModuleId(2)), Scope::Test),
            ]
        );
        // 有坐标的构件按坐标命名（Gradle 缓存里的路径也能认出坐标），其余按文件名
        let names: Vec<&str> = import.libraries.iter().map(|l| l.name.as_str()).collect();
        assert_eq!(names, ["com.google.code.gson:gson:2.11.0", "local.jar"]);
        assert_eq!(
            cache_coordinates(&gson).as_deref(),
            Some("com.google.code.gson:gson:2.11.0")
        );
        // 没有 group 的工程和 buildSrc 不参与按坐标链接
        assert_eq!(
            import.coordinates,
            vec![
                (
                    ModuleId(1),
                    "com.acme.platform".to_owned(),
                    "common".to_owned()
                ),
                (
                    ModuleId(2),
                    "com.acme.platform".to_owned(),
                    "testkit".to_owned()
                ),
            ]
        );
        // 解析不到的依赖：main 和 test 都有的算 Compile
        let unresolved: Vec<(String, Scope)> = import
            .unresolved
            .iter()
            .map(|d| (format!("{}:{}", d.group, d.artifact), d.scope))
            .collect();
        assert_eq!(
            unresolved,
            [
                ("com.acme.users:api".to_owned(), Scope::Compile),
                ("com.acme.users:testkit".to_owned(), Scope::Test),
            ]
        );
    }

    #[test]
    fn included_builds_are_watched() {
        let dir = std::env::temp_dir().join(format!("ja-gradle-include-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        for sub in ["app", "platform", "tools/gen"] {
            std::fs::create_dir_all(dir.join(sub)).unwrap();
        }
        std::fs::write(
            dir.join("app/settings.gradle"),
            "rootProject.name = 'app'\nincludeBuild '../platform'\nincludeBuild(\"../tools/gen\") { }\nincludeBuild '../missing'\n",
        )
        .unwrap();
        std::fs::write(dir.join("platform/settings.gradle.kts"), "").unwrap();
        std::fs::write(dir.join("tools/gen/build.gradle"), "").unwrap();
        let app = dir.join("app");
        let real = |path: &str| crate::canonicalize(&dir.join(path)).unwrap();
        assert_eq!(
            included_builds(&app),
            vec![real("platform"), real("tools/gen")]
        );
        let files = build_files(&app);
        assert!(
            files.contains(&real("platform/settings.gradle.kts")),
            "{files:?}"
        );
        assert!(files.contains(&real("tools/gen/build.gradle")), "{files:?}");
        let _ = std::fs::remove_dir_all(&dir);
    }
}
