//! Maven 的 `settings.xml`：本地仓库位置和镜像；以及运行 `mvn` 的方式。
//!
//! 和 Maven 一样有两级配置：用户级 `~/.m2/settings.xml`（或显式指定的设置文件，相当于
//! `mvn -s`）优先，其次是安装目录下的 `conf/settings.xml`（`MAVEN_HOME` / `M2_HOME`，
//! 或者 `PATH` 上 `mvn` 所在的安装）。

use std::{
    ffi::OsString,
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Stdio},
    sync::RwLock,
};

use serde::Deserialize;

use crate::xml;

/// 显式指定的 Maven 设置：编辑器配置里的 `maven.settings` / `maven.localRepository`，
/// 或者 `java-analyzer.toml` 的 `[maven]` 节。
#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
#[serde(default)]
pub struct MavenSetup {
    /// 代替 `~/.m2/settings.xml` 的用户级 `settings.xml`（相当于 `mvn -s`）
    pub settings: Option<PathBuf>,
    /// 本地仓库的目录（相当于 `-Dmaven.repo.local`），优先于一切自动发现
    pub local_repository: Option<PathBuf>,
}

impl MavenSetup {
    /// 自己没写的项用 `fallback` 的。
    fn or(&self, fallback: &MavenSetup) -> MavenSetup {
        MavenSetup {
            settings: self.settings.clone().or_else(|| fallback.settings.clone()),
            local_repository: self
                .local_repository
                .clone()
                .or_else(|| fallback.local_repository.clone()),
        }
    }
}

/// 编辑器配置里的设置。
static CLIENT_SETUP: RwLock<MavenSetup> = RwLock::new(MavenSetup {
    settings: None,
    local_repository: None,
});
/// 工作区里 `java-analyzer.toml` 的 `[maven]`，优先于编辑器配置。
static PROJECT_SETUP: RwLock<MavenSetup> = RwLock::new(MavenSetup {
    settings: None,
    local_repository: None,
});

/// 设置编辑器配置里指定的 Maven 设置文件和本地仓库位置。
pub fn set_client_setup(setup: MavenSetup) {
    if let Ok(mut slot) = CLIENT_SETUP.write() {
        *slot = setup;
    }
}

/// 设置 `java-analyzer.toml` 里指定的 Maven 设置（路径已经是绝对的）。
pub(crate) fn set_project_setup(setup: MavenSetup) {
    if let Ok(mut slot) = PROJECT_SETUP.write() {
        *slot = setup;
    }
}

fn explicit_setup() -> MavenSetup {
    let project = PROJECT_SETUP.read().map(|s| s.clone()).unwrap_or_default();
    let client = CLIENT_SETUP.read().map(|s| s.clone()).unwrap_or_default();
    project.or(&client)
}

/// 自动发现时要看的环境：用户目录、Maven 安装目录、`MAVEN_OPTS`。
struct Environment {
    home: PathBuf,
    install: Option<PathBuf>,
    maven_opts: Option<String>,
}

impl Environment {
    fn current() -> Environment {
        Environment {
            home: dirs::home_dir().unwrap_or_default(),
            install: maven_installation(),
            maven_opts: std::env::var("MAVEN_OPTS").ok(),
        }
    }

    /// 显式给出的路径里也可以用 `${user.home}`、`${env.NAME}`。
    fn expand(&self, path: &Path) -> PathBuf {
        PathBuf::from(interpolate(
            &path.to_string_lossy(),
            &self.home,
            self.install.as_deref(),
        ))
    }
}

/// 解析后的 Maven 设置：本地仓库和用户级 `settings.xml`。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedSetup {
    pub repo: PathBuf,
    /// 显式指定、而且存在的设置文件；要用 `-s` 传给 `mvn`
    pub settings: Option<PathBuf>,
}

impl ResolvedSetup {
    /// 运行 `mvn` 时加的参数：用同一份设置、下载进同一个本地仓库，下载到的构件才能被读到。
    pub fn cli_args(&self) -> Vec<OsString> {
        let mut args = Vec::new();
        if let Some(settings) = &self.settings {
            args.push(OsString::from("-s"));
            args.push(settings.clone().into_os_string());
        }
        let mut repo = OsString::from("-Dmaven.repo.local=");
        repo.push(&self.repo);
        args.push(repo);
        args
    }

    /// 区分不同设置的键：`mvn` 下载失败的记录按它分开。
    pub fn key(&self) -> String {
        format!(
            "{}|{}",
            self.repo.display(),
            self.settings
                .as_deref()
                .map(|s| s.display().to_string())
                .unwrap_or_default()
        )
    }
}

/// 当前生效的 Maven 设置（见 [`local_repository`]）。
pub(crate) fn resolved_setup() -> ResolvedSetup {
    resolve(&explicit_setup(), &Environment::current())
}

/// Maven 本地仓库的位置。依次看：显式指定的本地仓库（`java-analyzer.toml`，其次编辑器配置）、
/// `MAVEN_OPTS` 里的 `-Dmaven.repo.local`、用户级 `settings.xml`（显式指定的设置文件，
/// 没有时是 `~/.m2/settings.xml`）的 `localRepository`、安装目录 `conf/settings.xml` 的
/// `localRepository`，都没有时是 `~/.m2/repository`。
pub fn local_repository() -> PathBuf {
    resolved_setup().repo
}

fn resolve(explicit: &MavenSetup, env: &Environment) -> ResolvedSetup {
    let settings = explicit.settings.as_deref().map(|s| env.expand(s));
    let settings = match settings {
        Some(path) if path.is_file() => Some(path),
        Some(path) => {
            tracing::warn!("指定的 Maven 设置文件不存在：{}", path.display());
            None
        }
        None => None,
    };
    let repo = match &explicit.local_repository {
        Some(repo) => env.expand(repo),
        None => {
            let from_opts = env
                .maven_opts
                .as_deref()
                .and_then(repo_local_from_opts)
                .map(|raw| interpolate(&raw, &env.home, env.install.as_deref()));
            from_opts
                .or_else(|| {
                    settings_files(&env.home, settings.as_deref(), env.install.as_deref())
                        .iter()
                        .find_map(|path| {
                            let raw = local_repository_in(&std::fs::read_to_string(path).ok()?)?;
                            let install = maven_home_of(path).or(env.install.clone());
                            Some(interpolate(&raw, &env.home, install.as_deref()))
                        })
                })
                .map(PathBuf::from)
                .unwrap_or_else(|| env.home.join(".m2/repository"))
        }
    };
    ResolvedSetup { repo, settings }
}

/// 所有存在的 `settings.xml`，用户级在前。
pub(crate) fn existing_settings_files() -> Vec<PathBuf> {
    let env = Environment::current();
    let settings = resolve(&explicit_setup(), &env).settings;
    settings_files(&env.home, settings.as_deref(), env.install.as_deref())
}

/// `user_settings` 是显式指定的设置文件，代替 `~/.m2/settings.xml`。
fn settings_files(
    home: &Path,
    user_settings: Option<&Path>,
    install: Option<&Path>,
) -> Vec<PathBuf> {
    let mut files = vec![user_settings
        .map(Path::to_path_buf)
        .unwrap_or_else(|| home.join(".m2/settings.xml"))];
    if let Some(install) = install {
        let global = install.join("conf/settings.xml");
        if !files.contains(&global) {
            files.push(global);
        }
    }
    files.retain(|f| f.is_file());
    files
}

/// 设置文件在某个 Maven 安装的 `conf/` 下时，那个安装目录就是其中 `${maven.home}` 的值。
fn maven_home_of(settings: &Path) -> Option<PathBuf> {
    let conf = settings.parent()?;
    (conf.file_name()? == "conf")
        .then(|| conf.parent().map(Path::to_path_buf))
        .flatten()
}

/// 在 `dir` 里运行 Maven：优先用上层目录里的 Maven Wrapper，带上 [`ResolvedSetup::cli_args`]。
pub(crate) fn maven_command(dir: &Path, setup: &ResolvedSetup) -> Command {
    let (wrapper_name, mvn) = if cfg!(windows) {
        // Windows 上 `Command` 只会补 `.exe`：批处理文件得写全名
        ("mvnw.cmd", "mvn.cmd")
    } else {
        ("mvnw", "mvn")
    };
    let wrapper = dir
        .ancestors()
        .map(|d| d.join(wrapper_name))
        .find(|p| p.is_file());
    let mut command = Command::new(wrapper.unwrap_or_else(|| PathBuf::from(mvn)));
    // 语言服务器的 stdin / stdout 是 LSP 通道：子进程不能继承，Maven 的输出（尤其是失败时的
    // `[ERROR]`）写进 stdout 会把协议流弄坏，读 stdin 会吞掉客户端的消息
    command
        .current_dir(dir)
        .args(setup.cli_args())
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    command
}

#[cfg(test)]
thread_local! {
    /// 单元测试里不真的运行 Maven，只记下当前线程想运行几次
    pub(crate) static MAVEN_RUNS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// 运行 Maven 并记日志：为什么运行、用了多久、结果。启动不了时返回 `None`。
pub(crate) fn run_maven(command: &mut Command, reason: &str) -> Option<ExitStatus> {
    #[cfg(test)]
    {
        let _ = (command, reason);
        MAVEN_RUNS.with(|runs| runs.set(runs.get() + 1));
        None
    }
    #[cfg(not(test))]
    run_maven_now(command, reason)
}

#[cfg(not(test))]
fn run_maven_now(command: &mut Command, reason: &str) -> Option<ExitStatus> {
    let line = std::iter::once(command.get_program())
        .chain(command.get_args())
        .map(|arg| arg.to_string_lossy())
        .collect::<Vec<_>>()
        .join(" ");
    let dir = command
        .get_current_dir()
        .map(|d| d.display().to_string())
        .unwrap_or_default();
    let start = std::time::Instant::now();
    let result = command.status();
    let ms = start.elapsed().as_millis();
    match &result {
        Ok(status) if status.success() => {
            tracing::info!("mvn（{reason}）用时 {ms} ms：{line}（在 {dir}）")
        }
        Ok(status) => {
            tracing::warn!("mvn（{reason}）用时 {ms} ms，失败（{status}）：{line}（在 {dir}）")
        }
        Err(err) => tracing::warn!("无法运行 mvn（{reason}）：{err}：{line}（在 {dir}）"),
    }
    result.ok()
}

fn local_repository_in(settings: &str) -> Option<String> {
    let root = xml::parse(settings)?;
    let text = root.child_text("localRepository")?.trim().to_owned();
    (!text.is_empty()).then_some(text)
}

/// `MAVEN_OPTS` 里的 `-Dmaven.repo.local=...`。
fn repo_local_from_opts(opts: &str) -> Option<String> {
    opts.split_whitespace().find_map(|arg| {
        let value = arg.strip_prefix("-Dmaven.repo.local=")?;
        let value = value.trim_matches('"');
        (!value.is_empty()).then(|| value.to_owned())
    })
}

/// 展开 `${user.home}`、`${maven.home}` 和 `${env.NAME}`；不认识的占位符原样保留。
fn interpolate(raw: &str, home: &Path, install: Option<&Path>) -> String {
    let mut out = String::new();
    let mut rest = raw;
    while let Some(start) = rest.find("${") {
        out.push_str(&rest[..start]);
        let after = &rest[start + 2..];
        let Some(end) = after.find('}') else {
            out.push_str(&rest[start..]);
            return out;
        };
        let name = &after[..end];
        let value = match name {
            "user.home" => Some(home.to_string_lossy().into_owned()),
            "maven.home" => install.map(|p| p.to_string_lossy().into_owned()),
            _ => name
                .strip_prefix("env.")
                .and_then(|var| std::env::var(var).ok()),
        };
        match value {
            Some(value) => out.push_str(&value),
            None => out.push_str(&rest[start..start + 2 + end + 1]),
        }
        rest = &after[end + 1..];
    }
    out.push_str(rest);
    out
}

/// Maven 的安装目录（下面有 `conf/settings.xml` 的那一层）。
fn maven_installation() -> Option<PathBuf> {
    for var in ["MAVEN_HOME", "M2_HOME"] {
        if let Some(dir) = std::env::var_os(var).map(PathBuf::from) {
            if dir.join("conf/settings.xml").is_file() {
                return Some(dir);
            }
        }
    }
    let path = std::env::var_os("PATH")?;
    let names: &[&str] = if cfg!(windows) {
        &["mvn.cmd", "mvn.bat", "mvn"]
    } else {
        &["mvn"]
    };
    std::env::split_paths(&path).find_map(|dir| {
        let exe = names.iter().map(|n| dir.join(n)).find(|p| p.is_file())?;
        installation_of(&exe)
    })
}

/// 由 `mvn` 可执行文件推出安装目录：跟随符号链接后取 `bin` 的上一级；
/// Homebrew 的 `bin/mvn` 是个包装脚本，真正的安装在旁边的 `libexec` 里。
fn installation_of(exe: &Path) -> Option<PathBuf> {
    let real = std::fs::canonicalize(exe).unwrap_or_else(|_| exe.to_path_buf());
    let base = real.parent()?.parent()?;
    [base.to_path_buf(), base.join("libexec")]
        .into_iter()
        .find(|dir| dir.join("conf/settings.xml").is_file())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_local_repository_element() {
        let settings = r#"<?xml version="1.0"?>
<settings xmlns="http://maven.apache.org/SETTINGS/1.0.0">
  <!-- <localRepository>/commented/out</localRepository> -->
  <localRepository>
    D:\repo\maven
  </localRepository>
</settings>"#;
        assert_eq!(
            local_repository_in(settings).as_deref(),
            Some(r"D:\repo\maven")
        );
        assert_eq!(local_repository_in("<settings></settings>"), None);
        // Windows 上保存的 settings.xml 可能以 UTF-8 BOM 开头
        assert_eq!(
            local_repository_in(
                "\u{feff}<settings><localRepository>/data/m2</localRepository></settings>"
            )
            .as_deref(),
            Some("/data/m2")
        );
    }

    #[test]
    fn repo_local_from_maven_opts() {
        assert_eq!(
            repo_local_from_opts("-Xmx1g -Dmaven.repo.local=/data/m2 -B").as_deref(),
            Some("/data/m2")
        );
        assert_eq!(repo_local_from_opts("-Xmx1g"), None);
    }

    #[test]
    fn interpolates_known_placeholders() {
        let home = Path::new("/home/u");
        let install = Path::new("/opt/maven");
        assert_eq!(
            interpolate("${user.home}/.m2/custom", home, Some(install)),
            "/home/u/.m2/custom"
        );
        assert_eq!(
            interpolate("${maven.home}/repo", home, Some(install)),
            "/opt/maven/repo"
        );
        assert_eq!(interpolate("${unknown}/x", home, None), "${unknown}/x");
    }

    #[test]
    fn global_settings_are_read_after_user_settings() {
        let dir = std::env::temp_dir().join(format!("ja-maven-settings-{}", std::process::id()));
        let home = dir.join("home");
        let install = dir.join("maven");
        std::fs::create_dir_all(install.join("conf")).unwrap();
        std::fs::create_dir_all(install.join("bin")).unwrap();
        std::fs::write(install.join("bin/mvn"), "").unwrap();
        std::fs::write(
            install.join("conf/settings.xml"),
            "<settings><localRepository>/global/repo</localRepository></settings>",
        )
        .unwrap();

        // 只有全局配置
        let files = settings_files(&home, None, Some(&install));
        assert_eq!(files, vec![install.join("conf/settings.xml")]);
        assert_eq!(
            installation_of(&install.join("bin/mvn")),
            Some(std::fs::canonicalize(&install).unwrap())
        );

        // 用户配置优先
        std::fs::create_dir_all(home.join(".m2")).unwrap();
        std::fs::write(home.join(".m2/settings.xml"), "<settings></settings>").unwrap();
        let files = settings_files(&home, None, Some(&install));
        assert_eq!(files[0], home.join(".m2/settings.xml"));
        // 用户配置里没有 localRepository 时落到全局的
        let found = files
            .iter()
            .find_map(|f| local_repository_in(&std::fs::read_to_string(f).unwrap()));
        assert_eq!(found.as_deref(), Some("/global/repo"));
        let _ = std::fs::remove_dir_all(&dir);
    }

    fn env(home: &Path, install: Option<&Path>, maven_opts: Option<&str>) -> Environment {
        Environment {
            home: home.to_path_buf(),
            install: install.map(Path::to_path_buf),
            maven_opts: maven_opts.map(str::to_owned),
        }
    }

    #[test]
    fn explicit_settings_file_replaces_user_settings() {
        let dir = std::env::temp_dir().join(format!("ja-maven-explicit-{}", std::process::id()));
        let home = dir.join("home");
        // PATH 上的 Maven 安装和 ~/.m2 都没有 localRepository，真正的仓库写在另一个安装的配置里
        let path_install = dir.join("apache-maven-3.9.6");
        let other_install = dir.join("apache-maven-3.8.4");
        std::fs::create_dir_all(home.join(".m2")).unwrap();
        std::fs::create_dir_all(path_install.join("conf")).unwrap();
        std::fs::create_dir_all(other_install.join("conf")).unwrap();
        std::fs::write(home.join(".m2/settings.xml"), "<settings/>").unwrap();
        std::fs::write(path_install.join("conf/settings.xml"), "<settings/>").unwrap();
        let other_settings = other_install.join("conf/settings.xml");
        std::fs::write(
            &other_settings,
            "<settings><localRepository>${maven.home}/repository</localRepository></settings>",
        )
        .unwrap();
        let env = env(&home, Some(&path_install), None);

        // 什么都没指定：落到 ~/.m2/repository
        let auto = resolve(&MavenSetup::default(), &env);
        assert_eq!(auto.repo, home.join(".m2/repository"));
        assert_eq!(auto.settings, None);

        // 指定设置文件：读它的 localRepository，`${maven.home}` 是它所在的安装
        let explicit = MavenSetup {
            settings: Some(other_settings.clone()),
            local_repository: None,
        };
        let resolved = resolve(&explicit, &env);
        assert_eq!(resolved.repo, other_install.join("repository"));
        assert_eq!(resolved.settings.as_deref(), Some(other_settings.as_path()));
        let mut repo_arg = OsString::from("-Dmaven.repo.local=");
        // 和上面的 `repo` 是同一个路径；Windows 上插值出来的 `/` 原样保留
        repo_arg.push(&resolved.repo);
        assert_eq!(
            resolved.cli_args(),
            vec![
                OsString::from("-s"),
                other_settings.clone().into_os_string(),
                repo_arg
            ]
        );

        // MAVEN_OPTS 的 -Dmaven.repo.local 和 Maven 一样优先于设置文件
        let with_opts = resolve(
            &explicit,
            &self::env(
                &home,
                Some(&path_install),
                Some("-Dmaven.repo.local=/opts/repo"),
            ),
        );
        assert_eq!(with_opts.repo, PathBuf::from("/opts/repo"));

        // 显式指定的本地仓库优先于一切
        let both = MavenSetup {
            settings: Some(other_settings.clone()),
            local_repository: Some(PathBuf::from("${user.home}/repo")),
        };
        let resolved = resolve(&both, &env);
        assert_eq!(resolved.repo, home.join("repo"));
        assert_eq!(resolved.settings.as_deref(), Some(other_settings.as_path()));

        // 不存在的设置文件不传给 mvn，仓库照常自动发现
        let missing = MavenSetup {
            settings: Some(dir.join("nope.xml")),
            local_repository: None,
        };
        let resolved = resolve(&missing, &env);
        assert_eq!(resolved.settings, None);
        assert_eq!(resolved.repo, home.join(".m2/repository"));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn project_setup_overrides_client_setup_per_field() {
        let project = MavenSetup {
            settings: None,
            local_repository: Some(PathBuf::from("/project/repo")),
        };
        let client = MavenSetup {
            settings: Some(PathBuf::from("/client/settings.xml")),
            local_repository: Some(PathBuf::from("/client/repo")),
        };
        assert_eq!(
            project.or(&client),
            MavenSetup {
                settings: Some(PathBuf::from("/client/settings.xml")),
                local_repository: Some(PathBuf::from("/project/repo")),
            }
        );
    }
}
