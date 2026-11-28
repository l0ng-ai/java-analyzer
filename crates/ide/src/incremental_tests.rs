//! 增量计算的失效范围：编辑之后哪些查询会重新执行。
//!
//! 打字时最常见的是在方法体里编辑。这里锁住的约定：方法体内的编辑只让这个体重新推断，
//! 同一文件的其它体（哪怕位置挪动了）、别的文件的推断和诊断都直接复用。

use std::sync::Arc;

use base_db::{salsa::Setter, SourceFile};
use ide_db::{record_executions, QueryExecutions, RootDatabase};
use ide_diagnostics::{DiagnosticCode, DiagnosticsConfig};
use test_fixture::{fixture, Fixture};

use crate::highlight;

const MAIN: &str = r#"
//- /p/Main.java
package p;

public class Main {
    public static final int LIMIT = 10;

    int first(int a) {
        int x = a + 1;
        return x;
    }

    int second() {
        String s = "abc";
        return s.length() + missing;
    }

    int third() {
        return first(LIMIT);
    }
}
//- /p/Other.java
package p;

class Other {
    int use(Main m) {
        if (Main.LIMIT > 5) {
            return m.third();
        }
        return 0;
    }
}
"#;

fn source(fx: &Fixture, path: &str) -> SourceFile {
    fx.file_by_path(path).source
}

/// 把 `file` 里第一处 `from` 换成 `to`。
fn replace(db: &mut RootDatabase, file: SourceFile, from: &str, to: &str) {
    let text = file.text(db).to_string();
    assert!(text.contains(from), "文件里没有 {from:?}");
    let new: Arc<str> = Arc::from(text.replacen(from, to, 1));
    file.set_text(db).to(new);
}

fn diagnostics_of(db: &RootDatabase, file: SourceFile) -> (Vec<String>, QueryExecutions) {
    let (diags, executions) = record_executions(db, || {
        ide_diagnostics::diagnostics(db, file, &DiagnosticsConfig::default())
    });
    let text = file.text(db);
    let rendered = diags
        .iter()
        .filter(|d| d.code != DiagnosticCode::UnusedImport)
        .map(|d| format!("{:?} {}", d.code, &text[d.range]))
        .collect();
    (rendered, executions)
}

fn warm(fx: &Fixture) {
    for file in [source(fx, "/p/Main.java"), source(fx, "/p/Other.java")] {
        ide_diagnostics::diagnostics(&fx.db, file, &DiagnosticsConfig::default());
        highlight::highlight(&fx.db, file, None);
    }
}

#[test]
fn body_edit_reinfers_only_that_body() {
    let mut fx = fixture(MAIN);
    warm(&fx);
    let main = source(&fx, "/p/Main.java");
    let (before, _) = diagnostics_of(&fx.db, main);

    // 在第一个方法体里插入一条语句：后面两个方法整体挪了位置
    replace(
        &mut fx.db,
        main,
        "int x = a + 1;",
        "int y = 0; int x = a + 1;",
    );

    let (after, executions) = diagnostics_of(&fx.db, main);
    assert_eq!(executions.count("infer_tracked"), 1, "{executions:?}");
    // 签名级的摘要没变：类的签名、类索引都不重新计算
    assert_eq!(executions.count("class_data_tracked"), 0, "{executions:?}");
    assert_eq!(executions.count("source_class_index"), 0, "{executions:?}");
    // 挪了位置的方法里的诊断换算到新位置上，内容不变
    assert!(
        after.contains(&"UnresolvedName missing".to_owned()),
        "{after:?}"
    );
    assert_eq!(
        before.iter().filter(|d| d.contains("missing")).count(),
        after.iter().filter(|d| d.contains("missing")).count()
    );

    // 依赖它的文件（用到了它的常量和方法）的诊断直接复用
    let other = source(&fx, "/p/Other.java");
    let (_, executions) = diagnostics_of(&fx.db, other);
    assert_eq!(executions.count("default_diagnostics"), 0, "{executions:?}");
    assert_eq!(executions.count("infer_tracked"), 0, "{executions:?}");
}

/// 方法体都够大，各自单独缓存检查结果（很小的体和体之外的部分一起检查）。
fn large_bodies() -> String {
    // 每个方法里加一段注释，让体足够大
    let pad = "        // 这段注释只是为了让方法体足够大，单独缓存它的检查结果。\n".repeat(8);
    format!(
        r#"
//- /p/Main.java
package p;

public class Main {{
    public static final int LIMIT = 10;

    int first(int a) {{
{pad}        int x = a + 1;
        int total = 0;
        for (int i = 0; i < LIMIT; i++) {{
            total += i * x;
        }}
        return total + x;
    }}

    int second() {{
{pad}        String s = "abc";
        int total = 0;
        for (int i = 0; i < LIMIT; i++) {{
            total += s.length();
        }}
        return total + missing;
    }}

    int third() {{
{pad}        int total = 0;
        for (int i = 0; i < LIMIT; i++) {{
            total += first(i);
        }}
        return total;
    }}
}}
"#
    )
}

#[test]
fn body_edit_rechecks_only_that_body() {
    let mut fx = fixture(&large_bodies());
    let main = source(&fx, "/p/Main.java");
    ide_diagnostics::diagnostics(&fx.db, main, &DiagnosticsConfig::default());
    let whole = |db: &RootDatabase| {
        ide_diagnostics::whole_file_diagnostics(db, main, &DiagnosticsConfig::default())
    };

    // 在第一个方法体里插入一条语句：后面两个方法整体挪了位置
    replace(
        &mut fx.db,
        main,
        "int x = a + 1;",
        "int y = 0; int x = a + 1;",
    );
    let (diags, executions) = record_executions(&fx.db, || {
        ide_diagnostics::diagnostics(&fx.db, main, &DiagnosticsConfig::default())
    });
    // 按体缓存的检查只在被编辑的体上重新执行，挪了位置的体直接复用
    assert_eq!(executions.count("body_full"), 1, "{executions:?}");
    assert_eq!(executions.count("body_basic"), 0, "{executions:?}");
    // 拼起来的结果和整个文件一起检查的完全相同
    assert_eq!(diags, whole(&fx.db));
    let text = main.text(&fx.db);
    assert!(
        diags
            .iter()
            .any(|d| d.code == DiagnosticCode::UnusedLocal && &text[d.range] == "y"),
        "{diags:?}"
    );
    assert!(
        diags
            .iter()
            .any(|d| d.code == DiagnosticCode::UnresolvedName && &text[d.range] == "missing"),
        "{diags:?}"
    );

    // 打字途中语句写了一半（文件有语法错误）：接着在同一个体里打字，也只重新检查这个体
    replace(&mut fx.db, main, "int y = 0;", "int y = ");
    ide_diagnostics::diagnostics(&fx.db, main, &DiagnosticsConfig::default());
    replace(&mut fx.db, main, "int y = ", "int y = a");
    let (diags, executions) = record_executions(&fx.db, || {
        ide_diagnostics::diagnostics(&fx.db, main, &DiagnosticsConfig::default())
    });
    assert_eq!(executions.count("body_basic"), 1, "{executions:?}");
    assert_eq!(executions.count("body_full"), 0, "{executions:?}");
    assert_eq!(diags, whole(&fx.db));
    replace(&mut fx.db, main, "int y = a", "int y = 0;");

    // 加了一个方法（类的签名变了，各个体都要重新检查）：结果同样和整个文件一起检查的相同
    replace(
        &mut fx.db,
        main,
        "        return total;\n    }\n",
        "        return total;\n    }\n\n    void added() { int z; }\n",
    );
    let diags = ide_diagnostics::diagnostics(&fx.db, main, &DiagnosticsConfig::default());
    assert_eq!(diags, whole(&fx.db));
}

#[test]
fn shifted_bodies_keep_their_results_at_new_positions() {
    let mut fx = fixture(MAIN);
    warm(&fx);
    let main = source(&fx, "/p/Main.java");
    let highlights = |db: &RootDatabase| {
        let text = main.text(db).to_string();
        highlight::highlight(db, main, None)
            .into_iter()
            .map(|h| format!("{} {:?}", &text[h.range], h.tag))
            .collect::<Vec<_>>()
    };
    let before = highlights(&fx.db);

    replace(&mut fx.db, main, "return x;", "return  x;");
    let (after, executions) = record_executions(&fx.db, || highlights(&fx.db));
    assert_eq!(executions.count("infer_tracked"), 1, "{executions:?}");
    assert_eq!(before, after);

    // 再改回去：只有被编辑的那个体重新推断
    replace(&mut fx.db, main, "return  x;", "return x;");
    let (_, executions) = record_executions(&fx.db, || highlights(&fx.db));
    assert!(executions.count("infer_tracked") <= 1, "{executions:?}");
}

#[test]
fn signature_edit_reinfers_dependents() {
    let mut fx = fixture(MAIN);
    warm(&fx);
    let main = source(&fx, "/p/Main.java");
    // 改了方法签名：用到它的别的文件要重新检查，并报出实参不匹配
    replace(&mut fx.db, main, "int third()", "int third(int k)");
    let other = source(&fx, "/p/Other.java");
    let (diags, executions) = diagnostics_of(&fx.db, other);
    assert!(executions.count("infer_tracked") >= 1, "{executions:?}");
    assert!(
        diags.iter().any(|d| d.starts_with("ArgumentMismatch")),
        "{diags:?}"
    );
}

/// 四个够大的体（各自单独缓存检查结果）：`third` 调用 `first`，`fourth` 读字段 `count`，
/// `second` 两个都不用。
fn members_and_users() -> String {
    let pad = "        // 这段注释只是为了让方法体足够大，单独缓存它的检查结果。\n".repeat(8);
    format!(
        r#"
//- /p/Main.java
package p;

import java.util.List;

public class Main {{
    private int count = 0;

    int first(int a) {{
{pad}        return a + 1;
    }}

    int second(List<String> names) {{
{pad}        int total = 0;
        for (String name : names) {{
            total += name.length();
        }}
        return total;
    }}

    int third() {{
{pad}        return first(2) * 3;
    }}

    int fourth() {{
{pad}        return count * 2;
    }}
}}
"#
    )
}

/// 签名级的编辑之后，没用到被改动的成员的体既不重新推断，也不重新检查。
#[test]
fn signature_edit_reinfers_only_users() {
    let mut fx = fixture(&members_and_users());
    let main = source(&fx, "/p/Main.java");
    let config = DiagnosticsConfig::default();
    let check = |db: &RootDatabase| {
        let (diags, executions) =
            record_executions(db, || ide_diagnostics::diagnostics(db, main, &config));
        // 按体缓存拼起来的结果和整个文件一起检查的完全相同
        assert_eq!(
            diags,
            ide_diagnostics::whole_file_diagnostics(db, main, &config)
        );
        executions
    };
    check(&fx.db);

    // 给 `first` 加一个形参：`first` 自己和调用它的 `third` 重新推断，`second`、`fourth` 不动
    replace(
        &mut fx.db,
        main,
        "int first(int a)",
        "int first(int a, int b)",
    );
    let executions = check(&fx.db);
    assert_eq!(executions.count("infer_tracked"), 2, "{executions:?}");
    assert_eq!(executions.count("body_full"), 2, "{executions:?}");

    // 改字段的类型：只有读它的 `fourth`（和字段自己的初值）重新推断
    replace(&mut fx.db, main, "private int count", "private long count");
    let executions = check(&fx.db);
    assert_eq!(executions.count("infer_tracked"), 2, "{executions:?}");
    assert_eq!(executions.count("body_full"), 1, "{executions:?}");
}

const LOMBOK: &str = r#"
//- /a/A.java
package a;

@lombok.Getter
@lombok.Setter
class A {
    private String name;
}
//- /a/sub/S.java
package a.sub;

@lombok.Getter
class S {
    private String name;
}
//- /b/B.java
package b;

@lombok.Getter
class B {
    private String name;
}
"#;

const ROOT_CONFIG: &str = "lombok.accessors.prefix += m\nlombok.accessors.chain = true\n";
const SUB_CONFIG: &str = "config.stopBubbling = true\nlombok.accessors.prefix += _\n";

/// 换掉全部资源文件：`(目录, 文件名, 文本)`。
fn set_resources(db: &mut RootDatabase, files: &[(&str, &str, &str)]) {
    let resources = files
        .iter()
        .enumerate()
        .map(|(idx, (dir, name, text))| base_db::ResourceFile {
            file_id: base_db::FileId(1000 + idx as u32),
            name: (*name).into(),
            dir: (*dir).into(),
            module: None,
            text: Arc::from(*text),
        })
        .collect();
    base_db::workspace(db)
        .set_resources(db)
        .to(Arc::new(resources));
}

/// 文件里第一个类的方法名（不含构造器，排序）。
fn method_names(db: &RootDatabase, file: SourceFile) -> Vec<String> {
    let tree = hir::item_tree(db, file);
    let mut names: Vec<String> = tree.classes[0]
        .methods
        .iter()
        .filter(|m| !m.is_constructor)
        .map(|m| m.name.to_string())
        .collect();
    names.sort();
    names
}

#[test]
fn lombok_config_applies_per_directory() {
    let mut fx = fixture(LOMBOK);
    let (a, s, b) = (
        source(&fx, "/a/A.java"),
        source(&fx, "/a/sub/S.java"),
        source(&fx, "/b/B.java"),
    );
    let a_config = "clear lombok.accessors.prefix\nlombok.accessors.fluent = true\n";
    set_resources(
        &mut fx.db,
        &[
            ("", "lombok.config", ROOT_CONFIG),
            ("/a", "lombok.config", a_config),
            ("/a/sub", "lombok.config", SUB_CONFIG),
            ("/a", "application.yml", "server:\n  port: 1\n"),
        ],
    );
    // 里层的覆盖外层的（`clear` 清掉外层加的前缀）；`stopBubbling` 之后外层的不再生效
    assert_eq!(method_names(&fx.db, a), ["name", "name"]);
    assert_eq!(method_names(&fx.db, s), Vec::<String>::new());
    assert_eq!(method_names(&fx.db, b), Vec::<String>::new());

    // 只改 `/a` 下的配置：`/b`、`/a/sub` 的条目树不重新计算
    let a_config = "clear lombok.accessors.prefix\n";
    set_resources(
        &mut fx.db,
        &[
            ("", "lombok.config", ROOT_CONFIG),
            ("/a", "lombok.config", a_config),
            ("/a/sub", "lombok.config", SUB_CONFIG),
            ("/a", "application.yml", "server:\n  port: 1\n"),
        ],
    );
    let (names, executions) =
        record_executions(&fx.db, || [a, s, b].map(|file| method_names(&fx.db, file)));
    assert_eq!(names[0], ["getName", "setName"]);
    assert_eq!(executions.count("item_tree_and_map"), 1, "{executions:?}");

    // 改别的资源文件（Spring 配置）：各目录的配置和条目树都不重新计算
    set_resources(
        &mut fx.db,
        &[
            ("", "lombok.config", ROOT_CONFIG),
            ("/a", "lombok.config", a_config),
            ("/a/sub", "lombok.config", SUB_CONFIG),
            ("/a", "application.yml", "server:\n  port: 2\n"),
        ],
    );
    let (_, executions) =
        record_executions(&fx.db, || [a, s, b].map(|file| method_names(&fx.db, file)));
    assert_eq!(executions.count("item_tree_and_map"), 0, "{executions:?}");
    assert_eq!(
        executions.count("lombok_config_tracked"),
        0,
        "{executions:?}"
    );
}

/// 同一个二进制名在两个文件里都有声明：符号索引按文件建立（不读全局的类索引），检索到的
/// 类和成员仍然指向各自文件里的那一份。
#[test]
fn symbol_index_keeps_duplicate_classes_apart() {
    let fx = fixture(
        r#"
//- /a/p/Dup.java
package p;

public class Dup {
    int alpha;
}
//- /b/p/Dup.java
package p;

public class Dup {
    int beta;
}
"#,
    );
    let file_of = |def: &hir::Definition| match def {
        hir::Definition::Class(class) => hir::class_source_file(&fx.db, *class),
        hir::Definition::Field(field) => hir::class_source_file(&fx.db, field.class),
        _ => None,
    };
    let search = |query: &str| ide_db::symbol_index::search_symbols(&fx.db, query, 10, false);

    let classes: Vec<_> = search("Dup")
        .iter()
        .filter_map(|symbol| file_of(&symbol.entry.def))
        .collect();
    assert_eq!(
        classes,
        [source(&fx, "/a/p/Dup.java"), source(&fx, "/b/p/Dup.java")]
    );
    for (field, path) in [("alpha", "/a/p/Dup.java"), ("beta", "/b/p/Dup.java")] {
        let found = search(field);
        assert_eq!(file_of(&found[0].entry.def), Some(source(&fx, path)));
    }
}

/// 同名的类有多份时，外层类跟着**声明它的那个文件**走，而不是按名字全局取主副本。
///
/// `Dup$Inner` 只在第二份里声明，所以它是自己的主副本（`is_copy()` 为假）；但它的外层类
/// `Dup` 有两份，全局查会拿到第一份——那里没有 `Inner` 的外层成员，裸调 `m()` 就解析不到。
#[test]
fn nested_class_resolves_outer_members_from_its_own_file() {
    let fx = fixture(
        r#"
//- /a/p/Dup.java
package p;

public class Dup {
    void only() {}
}
//- /b/p/Dup.java
package p;

public class Dup {
    static String m() { return "t"; }
    static final String C = "c";

    public static class Inner {
        void run() {
            System.out.println(m() + C);
        }
    }
}
"#,
    );
    let file = source(&fx, "/b/p/Dup.java");
    // diagnostics_of 用 Debug 格式渲染代码，所以这里匹配 DiagnosticCode 的名字
    let (messages, _) = diagnostics_of(&fx.db, file);
    let unresolved: Vec<&String> = messages
        .iter()
        .filter(|m| m.starts_with("UnresolvedMethod") || m.starts_with("UnresolvedName"))
        .collect();
    assert!(
        unresolved.is_empty(),
        "外层类的成员应当解析得到: {unresolved:?}"
    );
}

/// 取消以 panic 展开穿过 `direct_supers`。工作线程常驻，展开后它的线程局部栈里不能留下这个类，
/// 否则这个线程之后再查它的父类型都得到空：类型层次里看不到父类。
#[test]
fn cancelled_query_leaves_no_stale_supers_on_the_thread() {
    use std::{panic::AssertUnwindSafe, sync::mpsc, thread};

    use base_db::salsa::Cancelled;

    let mut fx = fixture(
        r#"
//- /p/Base.java
package p;
class Base {}
//- /p/Child.java
package p;
class Chi$0ld extends Base {}
"#,
    );
    let base = source(&fx, "/p/Base.java");
    let child_id = hir::lookup_class(&fx.db, "p/Child").unwrap();
    let (_, file_id, offset) = fx.position();
    let items =
        crate::hierarchy::prepare_type_hierarchy(&fx.db, crate::FilePosition { file_id, offset })
            .unwrap();
    let key = items[0].key.clone().unwrap();
    let supertypes = move |db: &RootDatabase| -> Vec<String> {
        crate::hierarchy::supertypes(db, &key)
            .into_iter()
            .map(|n| n.name.to_string())
            .collect()
    };

    let (db_tx, db_rx) = mpsc::channel::<RootDatabase>();
    let (done_tx, done_rx) = mpsc::channel();
    let worker = thread::spawn(move || {
        let db = db_rx.recv().unwrap();
        // 循环里唯一的取消检查点在 `direct_supers` 压栈之后，所以取消一定在它出栈前展开
        let cancelled = Cancelled::catch(AssertUnwindSafe(|| loop {
            hir::direct_supers(&db, child_id);
        }));
        assert!(cancelled.is_err());
        drop(db);
        let db = db_rx.recv().unwrap();
        done_tx.send(supertypes(&db)).unwrap();
    });

    db_tx.send(fx.db.clone()).unwrap();
    // 写入会取消工作线程上的查询，并等它的快照释放
    replace(&mut fx.db, base, "class Base {", "class Base { int x;");
    db_tx.send(fx.db.clone()).unwrap();
    let on_worker = done_rx.recv().unwrap();
    worker.join().unwrap();

    assert_eq!(on_worker, ["Base"]);
}
