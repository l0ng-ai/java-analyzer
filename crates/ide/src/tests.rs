use syntax::TextRange;
use test_fixture::{fixture, fixture_with_level, Fixture};

use crate::{
    hierarchy, highlight, hover, navigation, references, signature_help, structure, FilePosition,
    HlTag, NavFile, SymbolKind,
};

fn position(fx: &Fixture) -> FilePosition {
    let (_, file_id, offset) = fx.position();
    FilePosition { file_id, offset }
}

fn slice<'a>(fx: &'a Fixture, file: &NavFile, range: TextRange) -> &'a str {
    let NavFile::Source(file_id) = file else {
        panic!("目标不在源码里")
    };
    let source = base_db::source_file(&fx.db, *file_id).unwrap();
    let text: &str = source.text(&fx.db);
    &text[usize::from(range.start())..usize::from(range.end())]
}

#[test]
fn goto_definition_of_local_field_and_method() {
    let fx = fixture(
        r#"
class Main {
    int count;
    int next() { return count + 1; }
    void f() {
        int local = ne$0xt();
    }
}
"#,
    );
    let result = navigation::goto_definition(&fx.db, position(&fx)).unwrap();
    assert_eq!(result.info.len(), 1);
    let nav = &result.info[0];
    assert_eq!(nav.kind, SymbolKind::Method);
    assert_eq!(slice(&fx, &nav.file, nav.focus_range), "next");
    assert!(slice(&fx, &nav.file, nav.full_range).starts_with("int next()"));
}

#[test]
fn goto_definition_across_files() {
    let fx = fixture(
        r#"
//- /a/Foo.java
package a;
public class Foo { public void bar() {} }
//- /b/Main.java
package b;
import a.Foo;
class Main {
    void f(Foo foo) { foo.ba$0r(); }
}
"#,
    );
    let result = navigation::goto_definition(&fx.db, position(&fx)).unwrap();
    let nav = &result.info[0];
    assert_eq!(
        nav.file,
        NavFile::Source(fx.file_by_path("/a/Foo.java").file_id)
    );
    assert_eq!(nav.container.as_deref(), Some("a.Foo"));
}

#[test]
fn goto_type_definition_of_variable() {
    let fx = fixture(
        r#"
class Foo {}
class Main {
    void f() {
        Foo foo = new Foo();
        fo$0o.toString();
    }
}
"#,
    );
    let result = navigation::goto_type_definition(&fx.db, position(&fx)).unwrap();
    assert_eq!(result.info[0].name, "Foo");
    assert_eq!(result.info[0].kind, SymbolKind::Class);
}

#[test]
fn goto_implementation_of_interface_method() {
    let fx = fixture(
        r#"
interface Shape { double ar$0ea(); }
class Circle implements Shape { public double area() { return 1; } }
class Square implements Shape { public double area() { return 2; } }
"#,
    );
    let result = navigation::goto_implementation(&fx.db, position(&fx)).unwrap();
    let mut containers: Vec<_> = result
        .info
        .iter()
        .filter_map(|nav| nav.container.clone())
        .collect();
    containers.sort();
    assert_eq!(containers, ["Circle", "Square"]);
}

#[test]
fn goto_implementation_of_methods_that_cannot_be_overridden() {
    for (source, expected) in [
        ("class A { final void f$0() {} }\nclass B extends A {}\n", 0),
        (
            "class A { static void f$0() {} }\nclass B extends A { static void f() {} }\n",
            0,
        ),
        ("final class A { void f$0() {} }\n", 0),
        (
            "class A { void f$0() {} }\nclass B extends A { void f() {} }\n",
            1,
        ),
    ] {
        let fx = fixture(source);
        let result = navigation::goto_implementation(&fx.db, position(&fx)).unwrap();
        assert_eq!(result.info.len(), expected, "{source}");
    }
}

#[test]
fn references_include_other_files_and_writes() {
    let fx = fixture(
        r#"
//- /a/Counter.java
package a;
public class Counter {
    public int val$0ue;
    void inc() { value++; }
}
//- /a/User.java
package a;
class User {
    int read(Counter c) { return c.value; }
}
"#,
    );
    let refs = references::find_all_refs(&fx.db, position(&fx), true).unwrap();
    assert_eq!(refs.len(), 3, "声明 + 两处引用: {refs:?}");
    assert_eq!(refs.iter().filter(|r| r.is_declaration).count(), 1);
    assert_eq!(refs.iter().filter(|r| r.is_write).count(), 1);
    let user = fx.file_by_path("/a/User.java").file_id;
    assert!(refs.iter().any(|r| r.file_id == user));
}

#[test]
fn highlight_related_stays_in_file() {
    let fx = fixture(
        r#"
class Main {
    void f() {
        int x$0 = 1;
        x = x + 1;
    }
}
"#,
    );
    let highlights = references::highlight_related(&fx.db, position(&fx)).unwrap();
    assert_eq!(highlights.len(), 3);
    assert_eq!(highlights.iter().filter(|h| h.is_write).count(), 2);
}

#[test]
fn hover_shows_signature_and_docs() {
    let fx = fixture(
        r#"
class Main {
    /**
     * Adds two numbers.
     * @param a first
     * @return the sum
     */
    static int add(int a, int b) { return a + b; }
    void f() { ad$0d(1, 2); }
}
"#,
    );
    let result = hover::hover(&fx.db, position(&fx)).unwrap();
    assert_eq!(result.info.signature, "static int add(int a, int b)");
    assert_eq!(result.info.container.as_deref(), Some("Main"));
    let docs = result.info.docs.as_deref().unwrap();
    assert!(docs.starts_with("Adds two numbers."), "{docs}");
    assert!(docs.contains("`a` — first"), "{docs}");
    assert!(result
        .info
        .to_markdown()
        .contains("```java\nstatic int add(int a, int b)\n```"));
}

#[test]
fn hover_inherits_docs_from_overridden_method() {
    let fx = fixture(
        r#"
interface Shape {
    /** The area. */
    double area();
}
class Circle implements Shape {
    public double ar$0ea() { return 1; }
}
"#,
    );
    let result = hover::hover(&fx.db, position(&fx)).unwrap();
    assert_eq!(result.info.docs.as_deref(), Some("The area."));
}

#[test]
fn signature_help_tracks_active_parameter() {
    let fx = fixture(
        r#"
class Main {
    void f(String s) {
        s.substring(1, $0);
    }
}
"#,
    );
    let help = signature_help::signature_help(&fx.db, position(&fx)).unwrap();
    assert_eq!(help.signatures.len(), 2);
    assert_eq!(help.active_parameter, Some(1));
    let active = &help.signatures[help.active_signature];
    assert_eq!(
        active.label,
        "String substring(int beginIndex, int endIndex)"
    );
    let (start, end) = active.params[1];
    assert_eq!(&active.label[start as usize..end as usize], "int endIndex");
}

#[test]
fn type_hierarchy_supers_and_subs() {
    let fx = fixture(
        r#"
interface Shape {}
class Cir$0cle implements Shape {}
class Dot extends Circle {}
"#,
    );
    let items = hierarchy::prepare_type_hierarchy(&fx.db, position(&fx)).unwrap();
    let key = items[0].key.clone().unwrap();
    let supers: Vec<_> = hierarchy::supertypes(&fx.db, &key)
        .into_iter()
        .map(|n| n.name.to_string())
        .collect();
    assert!(supers.contains(&"Shape".to_owned()), "{supers:?}");
    assert!(supers.contains(&"Object".to_owned()), "{supers:?}");
    let subs: Vec<_> = hierarchy::subtypes(&fx.db, &key)
        .into_iter()
        .map(|n| n.name.to_string())
        .collect();
    assert_eq!(subs, ["Dot"]);
}

#[test]
fn type_hierarchy_lists_local_and_anonymous_subtypes() {
    let fx = fixture(
        r#"
interface Sha$0pe {}
enum Kind implements Shape { ROUND { }, FLAT }
class Main {
    Shape a() { return new Shape() { }; }
    Shape b() {
        class Local implements Shape {}
        return new Local();
    }
}
"#,
    );
    let items = hierarchy::prepare_type_hierarchy(&fx.db, position(&fx)).unwrap();
    let key = items[0].key.clone().unwrap();
    let mut subs: Vec<_> = hierarchy::subtypes(&fx.db, &key)
        .into_iter()
        .map(|n| n.name.to_string())
        .collect();
    subs.sort();
    assert_eq!(subs, ["Kind", "Local", "new Shape() {…}"]);
    // 枚举常量的类体是枚举的子类
    let fx = fixture("enum Ki$0nd { ROUND { }, FLAT }");
    let kind = hierarchy::prepare_type_hierarchy(&fx.db, position(&fx)).unwrap();
    let subs: Vec<_> = hierarchy::subtypes(&fx.db, kind[0].key.as_ref().unwrap())
        .into_iter()
        .map(|n| n.name.to_string())
        .collect();
    assert_eq!(subs, ["ROUND {…}"]);
}

#[test]
fn call_hierarchy_incoming_and_outgoing() {
    let fx = fixture(
        r#"
class Main {
    void leaf() {}
    void mid$0dle() { leaf(); leaf(); }
    void top() { middle(); }
}
"#,
    );
    let items = hierarchy::prepare_call_hierarchy(&fx.db, position(&fx)).unwrap();
    let key = items[0].key.clone().unwrap();

    let incoming = hierarchy::incoming_calls(&fx.db, &key);
    assert_eq!(incoming.len(), 1);
    assert_eq!(incoming[0].target.name, "top");

    let outgoing = hierarchy::outgoing_calls(&fx.db, &key);
    assert_eq!(outgoing.len(), 1);
    assert_eq!(outgoing[0].target.name, "leaf");
    assert_eq!(outgoing[0].ranges.len(), 2);
}

#[test]
fn file_structure_is_nested() {
    let fx = fixture(
        r#"
class Outer {
    int a, b;
    Outer() {}
    void run(int n) {}
    enum Kind { X, Y }
}
"#,
    );
    let cu = base_db::parse(&fx.db, fx.file().source).tree();
    let nodes = structure::file_structure(&cu);
    assert_eq!(nodes.len(), 1);
    let names: Vec<&str> = nodes[0].children.iter().map(|n| n.name.as_str()).collect();
    assert_eq!(names, ["a", "b", "Outer", "run", "Kind"]);
    let run = &nodes[0].children[3];
    assert_eq!(run.detail.as_deref(), Some("(int n): void"));
    let kind = &nodes[0].children[4];
    assert_eq!(kind.kind, SymbolKind::Enum);
    assert_eq!(kind.children.len(), 2);
}

#[test]
fn folding_regions_from_comments() {
    let fx = fixture(
        "class Main {\n    //region helpers\n    void a() {}\n    // <editor-fold desc=\"more\">\n    void b() {}\n    // </editor-fold>\n    //endregion\n}\n",
    );
    let root = base_db::parse(&fx.db, fx.file().source).syntax_node();
    let text = root.text().to_string();
    let folds = structure::folding_ranges(&root);
    let regions: Vec<&str> = folds
        .iter()
        .filter(|f| f.kind == crate::FoldKind::Region)
        .map(|f| &text[usize::from(f.range.start())..usize::from(f.range.end())])
        .collect();
    assert!(
        regions
            .iter()
            .any(|r| r.starts_with("//region helpers") && r.ends_with("//endregion")),
        "{regions:?}"
    );
    assert!(
        regions
            .iter()
            .any(|r| r.starts_with("// <editor-fold") && r.ends_with("// </editor-fold>")),
        "{regions:?}"
    );
}

#[test]
fn document_links_in_comments_and_strings() {
    let fx = fixture(
        "/** See <a href=\"https://docs.oracle.com/javase/specs/\">JLS</a>. */\nclass Main {\n    // (details: https://example.org/a_(b)/c).\n    String u = \"http://localhost:8080/api?x=1\";\n    int https = 1; // not a link: https://\n}\n",
    );
    let root = base_db::parse(&fx.db, fx.file().source).syntax_node();
    let text = root.text().to_string();
    let links = structure::document_links(&root);
    let targets: Vec<&str> = links.iter().map(|(_, url)| url.as_str()).collect();
    assert_eq!(
        targets,
        [
            "https://docs.oracle.com/javase/specs/",
            "https://example.org/a_(b)/c",
            "http://localhost:8080/api?x=1",
        ]
    );
    for (range, url) in &links {
        assert_eq!(
            &text[usize::from(range.start())..usize::from(range.end())],
            url
        );
    }
}

#[test]
fn folding_and_matching_brace() {
    let fx = fixture("import a.B;\nimport a.C;\n\nclass Main {\n    void f() {\n    }\n}\n");
    let root = base_db::parse(&fx.db, fx.file().source).syntax_node();
    let folds = structure::folding_ranges(&root);
    assert!(folds.iter().any(|f| f.kind == crate::FoldKind::Imports));
    assert_eq!(
        folds
            .iter()
            .filter(|f| f.kind == crate::FoldKind::Region)
            .count(),
        2
    );

    let text = root.text().to_string();
    let open = text.find('{').unwrap() as u32;
    let close = text.rfind('}').unwrap() as u32;
    assert_eq!(
        structure::matching_brace(&root, open.into()),
        Some(close.into())
    );
    assert_eq!(
        structure::matching_brace(&root, close.into()),
        Some(open.into())
    );
}

#[test]
fn semantic_highlight_distinguishes_symbols() {
    let fx = fixture(
        r#"
class Main {
    static final int LIMIT = 1;
    void f(int param) {
        int local = param + LIMIT;
    }
}
"#,
    );
    let file = fx.file().source;
    let text: &str = file.text(&fx.db);
    let ranges = highlight::highlight(&fx.db, file, None);
    let tag_of = |needle: &str, nth: usize| {
        let (start, _) = text.match_indices(needle).nth(nth).unwrap();
        ranges
            .iter()
            .find(|hl| usize::from(hl.range.start()) == start)
            .unwrap_or_else(|| panic!("`{needle}` 没有被高亮"))
    };
    assert_eq!(tag_of("Main", 0).tag, HlTag::Symbol(SymbolKind::Class));
    assert_eq!(tag_of("param", 1).tag, HlTag::Symbol(SymbolKind::Param));
    assert_eq!(tag_of("local", 0).tag, HlTag::Symbol(SymbolKind::Local));
    let limit = tag_of("LIMIT", 1);
    assert_eq!(limit.tag, HlTag::Symbol(SymbolKind::Field));
    assert!(limit.mods.contains(crate::HlMods::STATIC));
    assert!(limit.mods.contains(crate::HlMods::READONLY));
    assert!(!limit.mods.contains(crate::HlMods::DECLARATION));
}

// ---------------------------------------------------------------------------
// 修改代码
// ---------------------------------------------------------------------------

/// 把修改应用到 fixture 的文件上，返回 `路径 → 新文本`。
fn apply_change(fx: &Fixture, change: &crate::SourceChange) -> Vec<(String, String)> {
    let mut res = Vec::new();
    for (file_id, edits) in &change.edits {
        let file = fx
            .files
            .iter()
            .find(|f| f.file_id == *file_id)
            .expect("修改了 fixture 之外的文件");
        let mut text = file.source.text(&fx.db).to_string();
        for edit in edits.iter().rev() {
            text.replace_range(
                usize::from(edit.range.start())..usize::from(edit.range.end()),
                &edit.new_text,
            );
        }
        res.push((file.path.clone(), text));
    }
    res.sort();
    res
}

fn assist(fx: &Fixture, id: &str) -> Option<String> {
    let (_, file_id, offset) = fx.position();
    let range = crate::FileRange {
        file_id,
        range: TextRange::empty(offset),
    };
    let found = crate::assists::assists(&fx.db, range)
        .into_iter()
        .find(|a| a.id == id)?;
    Some(apply_change(fx, &found.change).remove(0).1)
}

#[test]
fn rename_local_variable() {
    let fx = fixture("class Main {\n    int f() {\n        int co$0unt = 1;\n        count++;\n        return count;\n    }\n}\n");
    let change = crate::rename::rename(&fx.db, position(&fx), "total").unwrap();
    let text = &apply_change(&fx, &change)[0].1;
    assert_eq!(text, "class Main {\n    int f() {\n        int total = 1;\n        total++;\n        return total;\n    }\n}\n");
}

#[test]
fn rename_method_updates_overrides_and_callers() {
    let fx = fixture(
        r#"
//- /Shape.java
interface Shape { double ar$0ea(); }
//- /Circle.java
class Circle implements Shape { public double area() { return 1; } }
//- /Main.java
class Main { double f(Shape s, Circle c) { return s.area() + c.area(); } }
"#,
    );
    let change = crate::rename::rename(&fx.db, position(&fx), "size").unwrap();
    let files = apply_change(&fx, &change);
    assert_eq!(files.len(), 3);
    assert!(
        files.iter().all(|(_, text)| !text.contains("area")),
        "{files:?}"
    );
    assert!(files[0].1.contains("public double size()"));
    assert!(files[1].1.contains("s.size() + c.size()"));
}

#[test]
fn rename_class_renames_constructor_and_file() {
    let fx = fixture(
        r#"
//- /Point.java
public class Poi$0nt {
    Point() {}
    static Point origin() { return new Point(); }
}
"#,
    );
    let change = crate::rename::rename(&fx.db, position(&fx), "Vec2").unwrap();
    let text = &apply_change(&fx, &change)[0].1;
    assert!(!text.contains("Point"), "{text}");
    assert!(
        text.contains("Vec2() {}") && text.contains("new Vec2()"),
        "{text}"
    );
    assert_eq!(
        change.file_renames,
        [(fx.file().file_id, "Vec2.java".to_owned())]
    );
}

#[test]
fn rename_rejects_conflicts_and_bad_names() {
    let fx = fixture(
        "class Main {\n    void f() {\n        int a$0 = 1;\n        int b = 2;\n    }\n}\n",
    );
    assert!(crate::rename::rename(&fx.db, position(&fx), "b").is_err());
    assert!(crate::rename::rename(&fx.db, position(&fx), "class").is_err());
    assert!(crate::rename::rename(&fx.db, position(&fx), "1x").is_err());
    assert!(crate::rename::rename(&fx.db, position(&fx), "c").is_ok());

    // 标准库（这里是 minicore）里的符号不在 fixture 的可改范围内，但它是源码，
    // 所以换成覆写关系来验证"不能改库里的方法"的那条路径不会误伤普通方法
    let fx = fixture("class Main { String na$0me() { return \"\"; } }");
    assert!(crate::rename::rename(&fx.db, position(&fx), "title").is_ok());
}

#[test]
fn assist_add_import_for_unresolved_type() {
    let fx = fixture("package app;\n\nclass Main {\n    Array$0List<String> xs;\n}\n");
    let text = assist(&fx, "add_import").expect("应当提供导入");
    assert!(
        text.starts_with("package app;\n\nimport java.util.ArrayList;\n"),
        "{text}"
    );
}

#[test]
fn assist_organize_imports() {
    let fx = fixture(
        "import java.util.Map;\nimport java.util.List;\nimport static java.lang.Math.max;\nimport java.util.List;\nimport java.util.Set;\n\nclass Ma$0in {\n    List<String> xs;\n    Map<String, String> m;\n    int f() { return max(1, 2); }\n}\n",
    );
    let text = assist(&fx, "organize_imports").expect("import 需要整理");
    assert!(
        text.starts_with(
            "import java.util.List;\nimport java.util.Map;\n\nimport static java.lang.Math.max;\n\nclass Main"
        ),
        "{text}"
    );
}

#[test]
fn assist_generate_constructor_and_accessors() {
    let fx = fixture("class Point {\n    private final int x;\n    private int y;\n    $0\n}\n");
    let text = assist(&fx, "generate_constructor").unwrap();
    assert!(
        text.contains(
            "    public Point(int x, int y) {\n        this.x = x;\n        this.y = y;\n    }\n}"
        ),
        "{text}"
    );

    let text = assist(&fx, "generate_getters_setters").unwrap();
    assert!(
        text.contains("    public int getX() {\n        return x;\n    }\n"),
        "{text}"
    );
    assert!(text.contains("public void setY(int y) {"), "{text}");
    assert!(!text.contains("setX"), "final 字段没有 setter: {text}");
}

#[test]
fn assist_equals_hash_code_follows_language_level() {
    let source = "class Point {\n    int x;\n    String name;\n    int[] data;\n    $0\n}\n";

    // Java 6 没有 `java.util.Objects`：手写判空和经典的 31 * result 哈希
    let fx = fixture_with_level(source, 6);
    let text = assist(&fx, "generate_equals_hash_code").unwrap();
    assert!(!text.contains("java.util.Objects"), "{text}");
    assert!(text.contains("x == that.x"), "{text}");
    assert!(
        text.contains("(name == null ? that.name == null : name.equals(that.name))"),
        "{text}"
    );
    assert!(
        text.contains("java.util.Arrays.equals(data, that.data)"),
        "{text}"
    );
    assert!(text.contains("        int result = x;\n"), "{text}");
    assert!(
        text.contains("        result = 31 * result + (name != null ? name.hashCode() : 0);\n"),
        "{text}"
    );
    assert!(
        text.contains("        result = 31 * result + java.util.Arrays.hashCode(data);\n"),
        "{text}"
    );
    assert!(text.contains("        return result;\n"), "{text}");

    // Java 7 起用 `Objects`
    let fx = fixture_with_level(source, 8);
    let text = assist(&fx, "generate_equals_hash_code").unwrap();
    assert!(
        text.contains("java.util.Objects.equals(name, that.name)"),
        "{text}"
    );
    assert!(
        text.contains("return java.util.Objects.hash(x, name, data);"),
        "{text}"
    );
    assert!(!text.contains("31 * result"), "{text}");
}

#[test]
fn assist_implement_methods_and_add_override() {
    let fx = fixture(
        "interface Shape { double area(); String name(); }\nclass Circle imp$0lements Shape {\n    public String name() { return \"c\"; }\n}\n",
    );
    let text = assist(&fx, "implement_methods").unwrap();
    assert!(
        text.contains("    @Override\n    public double area() {\n        return 0;\n    }\n"),
        "{text}"
    );
    assert_eq!(
        text.matches("name()").count(),
        2,
        "已实现的方法不重复生成: {text}"
    );

    let fx = fixture(
        "interface Shape { String name(); }\nclass Circle implements Shape {\n    public String na$0me() { return \"c\"; }\n}\n",
    );
    let text = assist(&fx, "add_override").unwrap();
    assert!(
        text.contains("    @Override\n    public String name()"),
        "{text}"
    );
}

#[test]
fn assist_extract_variable() {
    let source = "class Main {\n    int f(int a, int b) {\n        return a * b + 1;\n    }\n}\n";
    let fx = fixture(source);
    let start = source.find("a * b").unwrap() as u32;
    let range = crate::FileRange {
        file_id: fx.file().file_id,
        range: TextRange::new(start.into(), (start + 5).into()),
    };
    let found = crate::assists::assists(&fx.db, range)
        .into_iter()
        .find(|a| a.id == "extract_variable")
        .expect("选中的表达式可以提取");
    let text = &apply_change(&fx, &found.change)[0].1;
    assert!(
        text.contains("        int extracted = a * b;\n        return extracted + 1;\n"),
        "{text}"
    );
}

#[test]
fn inlay_hints_for_var_and_literal_arguments() {
    let fx = fixture(
        r#"
class Main {
    static int clamp(int value, int limit) { return value; }
    void f(String s) {
        var trimmed = s.trim();
        var fresh = new StringBuilder();
        int x = clamp(5, -1);
        int y = clamp(x, x);
    }
}
"#,
    );
    let file = fx.file().source;
    let text: &str = file.text(&fx.db);
    let hints = crate::inlay_hints::inlay_hints(&fx.db, file, None);
    let rendered: Vec<(String, &str)> = hints
        .iter()
        .map(|hint| {
            let offset = usize::from(hint.offset);
            let before = text[..offset]
                .rsplit(|c: char| !c.is_alphanumeric())
                .next()
                .unwrap_or("");
            (before.to_owned(), hint.label.as_str())
        })
        .collect();
    assert_eq!(
        rendered,
        [
            ("trimmed".to_owned(), ": String"),
            (String::new(), "value:"),
            (String::new(), "limit:"),
        ],
        "`new` 的类型显而易见、变量实参不需要提示"
    );
}

/// 选中 `needle` 后取指定的代码操作并应用。
fn assist_on_selection(source: &str, needle: &str, id: &str) -> Option<String> {
    let fx = fixture(source);
    let start = source.find(needle).expect("fixture 里没有要选中的文本") as u32;
    let range = crate::FileRange {
        file_id: fx.file().file_id,
        range: TextRange::new(start.into(), (start + needle.len() as u32).into()),
    };
    let found = crate::assists::assists(&fx.db, range)
        .into_iter()
        .find(|a| a.id == id)?;
    Some(apply_change(&fx, &found.change).remove(0).1)
}

#[test]
fn assist_inline_variable() {
    let fx = fixture(
        "class Main {\n    int f(int a, int b) {\n        int su$0m = a + b;\n        return sum * sum;\n    }\n}\n",
    );
    let text = assist(&fx, "inline_variable").unwrap();
    assert_eq!(
        text,
        "class Main {\n    int f(int a, int b) {\n        return (a + b) * (a + b);\n    }\n}\n"
    );

    // 被重新赋值的变量不能内联
    let fx = fixture(
        "class Main {\n    int f(int a) {\n        int x$0 = a;\n        x = x + 1;\n        return x;\n    }\n}\n",
    );
    assert!(assist(&fx, "inline_variable").is_none());
}

#[test]
fn assist_inline_variable_keeps_side_effects_once() {
    // 有副作用的初值用了两次、或者用在条件分支里：不能内联
    for body in [
        "int val$0ue = next();\n        return value + value;",
        "int val$0ue = next();\n        return flag ? value : 0;",
        "int val$0ue = next();\n        return flag && value > 0 ? 1 : 0;",
        "int val$0ue = next();\n        while (flag) { use(value); }\n        return 0;",
        "int val$0ue = next();\n        Runnable r = () -> use(value);\n        return 0;",
    ] {
        let fx = fixture(&format!(
            "class Main {{\n    boolean flag;\n    int next() {{ return 1; }}\n    void use(int v) {{}}\n    int f() {{\n        {body}\n    }}\n}}\n"
        ));
        assert!(assist(&fx, "inline_variable").is_none(), "{body}");
    }

    // 只用一次、无条件求值：可以
    let fx = fixture(
        "class Main {\n    int next() { return 1; }\n    int f() {\n        int val$0ue = next();\n        return value + 1;\n    }\n}\n",
    );
    let text = assist(&fx, "inline_variable").unwrap();
    assert!(text.contains("return next() + 1;"), "{text}");
}

#[test]
fn assist_extract_method_from_statements() {
    let source = "class Main {\n    int f(int a, int b) {\n        int sum = a + b;\n        int twice = sum * 2;\n        return twice + a;\n    }\n}\n";
    let text = assist_on_selection(
        source,
        "int sum = a + b;\n        int twice = sum * 2;",
        "extract_method",
    )
    .expect("两条语句可以提取");
    assert_eq!(
        text,
        "class Main {\n    int f(int a, int b) {\n        int twice = extracted(a, b);\n        return twice + a;\n    }\n\n    private int extracted(int a, int b) {\n        int sum = a + b;\n        int twice = sum * 2;\n        return twice;\n    }\n}\n"
    );
}

#[test]
fn assist_extract_method_rejects_escaping_control_flow() {
    let source = "class Main {\n    int f(int a) {\n        if (a > 0) return 1;\n        return 2;\n    }\n}\n";
    assert!(assist_on_selection(source, "if (a > 0) return 1;", "extract_method").is_none());

    // 两个都要带出去的值
    let source = "class Main {\n    int f(int a) {\n        int x = a;\n        int y = a;\n        return x + y;\n    }\n}\n";
    assert!(
        assist_on_selection(source, "int x = a;\n        int y = a;", "extract_method").is_none()
    );
}

#[test]
fn assist_extract_method_from_expression_in_static_method() {
    let source =
        "class Main {\n    static int f(int a, int b) {\n        return a * b + 1;\n    }\n}\n";
    let text = assist_on_selection(source, "a * b", "extract_method").unwrap();
    assert!(text.contains("return extracted(a, b) + 1;"), "{text}");
    assert!(
        text.contains(
            "    private static int extracted(int a, int b) {\n        return a * b;\n    }"
        ),
        "{text}"
    );
}

#[test]
fn assist_extract_constant() {
    let source = "class Main {\n    int f(int a) {\n        return a * 1024;\n    }\n}\n";
    let text = assist_on_selection(source, "1024", "extract_constant").unwrap();
    assert!(text.contains("return a * EXTRACTED;"), "{text}");
    assert!(
        text.contains("    private static final int EXTRACTED = 1024;\n}"),
        "{text}"
    );
    assert!(assist_on_selection(source, "a * 1024", "extract_constant").is_none());
}

#[test]
fn assist_remove_unused_parameter() {
    let fx = fixture(
        r#"
//- /Util.java
class Util {
    static int twice(int value, int unu$0sed) { return value * 2; }
}
//- /Main.java
class Main { int f() { return Util.twice(1, 2) + Util.twice(3, 4); } }
"#,
    );
    let (_, file_id, offset) = fx.position();
    let range = crate::FileRange {
        file_id,
        range: TextRange::empty(offset),
    };
    let found = crate::assists::assists(&fx.db, range)
        .into_iter()
        .find(|a| a.id == "remove_unused_parameter")
        .expect("未使用的形参可以删除");
    let files = apply_change(&fx, &found.change);
    assert!(
        files
            .iter()
            .any(|(_, t)| t.contains("static int twice(int value) {")),
        "{files:?}"
    );
    assert!(
        files
            .iter()
            .any(|(_, t)| t.contains("Util.twice(1) + Util.twice(3)")),
        "{files:?}"
    );
}

#[test]
fn assist_invert_if() {
    let fx = fixture(
        "class Main {\n    int f(int a) {\n        i$0f (a == 0) {\n            return 1;\n        } else {\n            return 2;\n        }\n    }\n}\n",
    );
    let text = assist(&fx, "invert_if").unwrap();
    assert!(
        text.contains("if (a != 0) {\n            return 2;\n        } else {\n            return 1;\n        }"),
        "{text}"
    );
}

#[test]
fn code_lens_counts_references_and_implementations() {
    let fx = fixture(
        r#"
//- /Shape.java
interface Shape { double area(); }
//- /Circle.java
class Circle implements Shape { public double area() { return 1; } }
//- /Main.java
class Main { double f(Shape s) { return s.area() + s.area(); } }
"#,
    );
    let shape = fx.file_by_path("/Shape.java");
    let lenses = crate::code_lens::code_lenses(&fx.db, shape.source);
    // 接口：引用 + 实现；抽象方法：引用 + 实现
    assert_eq!(lenses.len(), 4, "{lenses:?}");

    let text: &str = shape.source.text(&fx.db);
    let count = |name: &str, kind| {
        let lens = lenses
            .iter()
            .find(|l| {
                l.kind == kind
                    && &text[usize::from(l.range.start())..usize::from(l.range.end())] == name
            })
            .unwrap();
        let position = FilePosition {
            file_id: shape.file_id,
            offset: lens.range.start(),
        };
        crate::code_lens::code_lens_count(&fx.db, position, kind)
    };
    assert_eq!(count("area", crate::CodeLensKind::References), 2);
    assert_eq!(count("area", crate::CodeLensKind::Implementations), 1);
    assert_eq!(count("Shape", crate::CodeLensKind::Implementations), 1);
}

#[test]
fn assist_inline_method() {
    let fx = fixture(
        "class Main {\n    private int sq$0uare(int n) {\n        return n * n;\n    }\n\n    int f(int a) {\n        return square(a + 1) + square(2);\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(
        text.contains("return ((a + 1) * (a + 1)) + (2 * 2);"),
        "{text}"
    );
    assert!(!text.contains("square"), "{text}");

    // 可以被覆写的方法、实参有副作用的调用都不内联
    let fx = fixture("class Main {\n    int tw$0ice(int n) { return n + n; }\n    int f() { return twice(1); }\n}\n");
    assert!(assist(&fx, "inline_method").is_none());
    let fx = fixture(
        "class Main {\n    private int tw$0ice(int n) { return n + n; }\n    int g() { return 1; }\n    int f() { return twice(g()); }\n}\n",
    );
    assert!(assist(&fx, "inline_method").is_none());
}

#[test]
fn inline_method_qualifies_fields_shadowed_at_call_site() {
    let fx = fixture(
        "class InlineField {\n    static String name = \"field\";\n    private static String fet$0ch() { return name; }\n\n    public static void main(String[] args) {\n        String name = \"local\";\n        System.out.println(fetch());\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(
        text.contains("System.out.println(InlineField.name);"),
        "{text}"
    );

    let fx = fixture(
        "class Main {\n    int count;\n    private int cur$0rent() { return count + 1; }\n\n    int f(int count) {\n        return current() * count;\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(text.contains("return (this.count + 1) * count;"), "{text}");

    // 没有遮蔽时保持原样
    let fx = fixture(
        "class Main {\n    int count;\n    private int cur$0rent() { return count; }\n\n    int f(int other) {\n        return current() + other;\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(text.contains("return count + other;"), "{text}");
}

#[test]
fn inline_method_casts_arguments_to_keep_overload() {
    let fx = fixture(
        "class InlineOverload {\n    static String render(Object n) { return \"Object\"; }\n    static String render(String n) { return \"String\"; }\n    private static String wr$0ap(Object n) { return render(n); }\n\n    public static void main(String[] args) {\n        System.out.println(wrap(\"x\"));\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(
        text.contains("System.out.println(render((Object) \"x\"));"),
        "{text}"
    );

    // 基本类型拓宽之后再运算：不转换就会按 int 溢出
    let fx = fixture(
        "class Main {\n    private static long sq$0uare(long n) { return n * n; }\n\n    long f(int a) {\n        return square(a);\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(text.contains("return ((long) a) * ((long) a);"), "{text}");

    // 类型相同不加转换
    let fx = fixture(
        "class Main {\n    static String render(Object n) { return \"Object\"; }\n    private static String wr$0ap(Object n) { return render(n); }\n\n    String f(Object o) {\n        return wrap(o);\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(text.contains("return render(o);"), "{text}");

    // 方法自己的类型形参在调用处写不出来：不提供
    let fx = fixture(
        "class Main {\n    static String render(Object n) { return \"Object\"; }\n    static String render(String n) { return \"String\"; }\n    private static <T> String wr$0ap(T n) { return render(n); }\n\n    String f() {\n        return wrap(\"x\");\n    }\n}\n",
    );
    assert!(assist(&fx, "inline_method").is_none());
}

#[test]
fn inline_method_casts_result_to_return_type() {
    // 方法体表达式的类型和返回类型不同：按返回类型转换，调用的值才按原来的类型参与重载和运算
    let fx = fixture(
        "class Main {\n    static String render(Object n) { return \"Object\"; }\n    static String render(String n) { return \"String\"; }\n    private static Object g$0et() { return \"x\"; }\n\n    String f() {\n        return render(get());\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(text.contains("return render((Object) \"x\");"), "{text}");

    let fx = fixture(
        "class Main {\n    private static int co$0de() { return 'a'; }\n\n    void f() {\n        System.out.println(code());\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(text.contains("System.out.println((int) 'a');"), "{text}");

    let fx = fixture(
        "class Main {\n    private static int i$0d(int x) { return x; }\n\n    void f() {\n        System.out.println(id('a'));\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(text.contains("System.out.println((int) 'a');"), "{text}");

    let fx = fixture(
        "class Main {\n    private static long b$0ig() { return 100000; }\n\n    long f() {\n        return big() * 100000;\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(text.contains("return ((long) 100000) * 100000;"), "{text}");

    let fx = fixture(
        "class Main {\n    static String render(Object n) { return \"Object\"; }\n    static String render(String n) { return \"String\"; }\n    private static String n$0ame() { return \"x\"; }\n\n    String f() {\n        return render(name());\n    }\n}\n",
    );
    let text = assist(&fx, "inline_method").unwrap();
    assert!(text.contains("return render(\"x\");"), "{text}");
}

#[test]
fn move_class_updates_package_and_imports() {
    let fx = fixture(
        r#"
//- /app/util/Strings.java
package app.util;

public class Strings {
    static String pad(String s) { return Helper.trim(s); }
}
//- /app/util/Helper.java
package app.util;

public class Helper {
    static String trim(String s) { return Strings.pad(s); }
}
//- /app/Main.java
package app;

import app.util.Strings;

class Main { String f() { return Strings.pad(""); } }
"#,
    );
    let moved = fx.file_by_path("/app/util/Strings.java");
    let change = crate::move_class::move_to_package(&fx.db, moved.file_id, "app.text");
    let files = apply_change(&fx, &change);
    let text_of = |path: &str| {
        &files
            .iter()
            .find(|(p, _)| p == path)
            .unwrap_or_else(|| panic!("{path} 没有被修改"))
            .1
    };

    let strings = text_of("/app/util/Strings.java");
    assert!(strings.starts_with("package app.text;\n"), "{strings}");
    assert!(
        strings.contains("import app.util.Helper;"),
        "原包里的类需要 import: {strings}"
    );

    assert!(text_of("/app/Main.java").contains("import app.text.Strings;"));
    assert!(
        text_of("/app/util/Helper.java").contains("import app.text.Strings;"),
        "原来同包的使用者要补 import"
    );

    // 包没变就没有修改
    assert!(crate::move_class::move_to_package(&fx.db, moved.file_id, "app.util").is_empty());
}

#[test]
fn moving_a_package_keeps_classes_moved_together_unimported() {
    let fx = fixture(
        r#"
//- /app/util/Strings.java
package app.util;

public class Strings {
    static String pad(String s) { return Helper.trim(s) + Other.x(); }
}
//- /app/util/Helper.java
package app.util;

public class Helper {
    static String trim(String s) { return Strings.pad(s); }
}
//- /app/util/Other.java
package app.util;

public class Other {
    static String x() { return Strings.pad(""); }
}
//- /app/Main.java
package app;

import app.util.Strings;
import app.util.Helper;

class Main { String f() { return Strings.pad("") + Helper.trim(""); } }
"#,
    );
    // Strings 和 Helper 一起移到 app.text，Other 留在原包
    let moves = vec![
        (
            fx.file_by_path("/app/util/Strings.java").file_id,
            "app.text".to_owned(),
        ),
        (
            fx.file_by_path("/app/util/Helper.java").file_id,
            "app.text".to_owned(),
        ),
    ];
    let change = crate::move_class::move_files(&fx.db, &moves);
    let files = apply_change(&fx, &change);
    let text_of = |path: &str| {
        &files
            .iter()
            .find(|(p, _)| p == path)
            .unwrap_or_else(|| panic!("{path} 没有被修改"))
            .1
    };
    let strings = text_of("/app/util/Strings.java");
    assert!(strings.starts_with("package app.text;\n"), "{strings}");
    assert!(
        !strings.contains("import app.util.Helper;"),
        "一起移动的类不需要 import: {strings}"
    );
    assert!(!strings.contains("import app.text.Helper;"), "{strings}");
    assert!(
        strings.contains("import app.util.Other;"),
        "留在原包的类要 import: {strings}"
    );
    let helper = text_of("/app/util/Helper.java");
    assert!(!helper.contains("import app.text.Strings;"), "{helper}");
    assert!(text_of("/app/util/Other.java").contains("import app.text.Strings;"));
    let main = text_of("/app/Main.java");
    assert!(
        main.contains("import app.text.Strings;") && main.contains("import app.text.Helper;"),
        "{main}"
    );
}

#[test]
fn test_jar_dependency_exposes_test_classes_to_main_code() {
    use base_db::{
        salsa::Setter, workspace, Dependency, DependencyTarget, FileEntry, FileKind, ModuleData,
        ModuleId, ProjectGraph, Scope, SourceRootKind,
    };
    use std::{path::PathBuf, sync::Arc};

    let visible = |target: Option<DependencyTarget>| {
        let mut fx = fixture(
            r#"
//- /core/src/test/java/core/Fixtures.java
package core;
public class Fixtures {}
//- /app/src/main/java/app/Main.java
package app;
class Main {}
"#,
        );
        let ws = workspace(&fx.db);
        let mut files = (**ws.files(&fx.db)).clone();
        for (module, root, path) in [
            (
                0,
                SourceRootKind::Test,
                "/core/src/test/java/core/Fixtures.java",
            ),
            (1, SourceRootKind::Main, "/app/src/main/java/app/Main.java"),
        ] {
            let file = fx.file_by_path(path);
            files.insert(
                file.file_id,
                FileEntry {
                    source: file.source,
                    kind: FileKind::Workspace {
                        module: Some(ModuleId(module)),
                        root,
                    },
                },
            );
        }
        let module = |name: &str, dependencies| ModuleData {
            name: name.to_owned(),
            root: PathBuf::from(format!("/{name}")),
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
        let project = ProjectGraph {
            modules: vec![
                module("core", Vec::new()),
                module(
                    "app",
                    target
                        .map(|target| Dependency {
                            target,
                            scope: Scope::Compile,
                        })
                        .into_iter()
                        .collect(),
                ),
            ],
            ..ProjectGraph::default()
        };
        ws.set_files(&mut fx.db).to(Arc::new(files));
        ws.set_project(&mut fx.db).to(Arc::new(project));
        let class = hir::lookup_class(&fx.db, "core/Fixtures").unwrap();
        let main = fx.file_by_path("/app/src/main/java/app/Main.java").source;
        hir::is_visible_from(&fx.db, Some(main), class)
    };
    assert!(visible(Some(DependencyTarget::ModuleTests(ModuleId(0)))));
    assert!(!visible(Some(DependencyTarget::Module(ModuleId(0)))));
    assert!(!visible(None));
}

#[test]
fn test_sources_use_their_own_language_level() {
    use base_db::{
        salsa::Setter, workspace, FileEntry, FileKind, ModuleData, ModuleId, ProjectGraph,
        SourceRootKind,
    };
    use std::{path::PathBuf, sync::Arc};

    let mut fx = fixture(
        r#"
//- /core/src/main/java/core/Point.java
package core;
record Point(int x, int y) {}
//- /core/src/test/java/core/PointTest.java
package core;
record Pair(int a, int b) {}
"#,
    );
    let ws = workspace(&fx.db);
    let mut files = (**ws.files(&fx.db)).clone();
    for (root, path) in [
        (SourceRootKind::Main, "/core/src/main/java/core/Point.java"),
        (
            SourceRootKind::Test,
            "/core/src/test/java/core/PointTest.java",
        ),
    ] {
        let file = fx.file_by_path(path);
        files.insert(
            file.file_id,
            FileEntry {
                source: file.source,
                kind: FileKind::Workspace {
                    module: Some(ModuleId(0)),
                    root,
                },
            },
        );
    }
    let project = ProjectGraph {
        modules: vec![ModuleData {
            name: "core".to_owned(),
            root: PathBuf::from("/core"),
            source_roots: Vec::new(),
            language_level: Some(11),
            api_release: Some(17),
            test_language_level: Some(17),
            preview: false,
            dependencies: Vec::new(),
            output_dirs: Vec::new(),
            encoding: None,
            transitive_dependencies: false,
        }],
        ..ProjectGraph::default()
    };
    ws.set_files(&mut fx.db).to(Arc::new(files));
    ws.set_project(&mut fx.db).to(Arc::new(project));

    let errors = |path: &str| -> Vec<String> {
        let file = fx.file_by_path(path).source;
        ide_diagnostics::diagnostics(&fx.db, file, &ide_diagnostics::DiagnosticsConfig::default())
            .into_iter()
            .filter(|d| d.severity == ide_diagnostics::Severity::Error)
            .map(|d| d.message)
            .collect()
    };
    let main = errors("/core/src/main/java/core/Point.java");
    assert!(
        main.iter().any(|m| m.contains("16")),
        "主代码按 11 检查: {main:?}"
    );
    let test = errors("/core/src/test/java/core/PointTest.java");
    assert!(test.is_empty(), "测试代码按 17 检查: {test:?}");
}

#[test]
fn anonymous_to_lambda_needs_java_8() {
    let source = r#"
class Main {
    void f() {
        Runnable r = new Run$0nable() {
            public void run() {
                System.out.println("x");
            }
        };
    }
}
"#;
    let fx = fixture_with_level(source, 7);
    assert_eq!(assist(&fx, "anonymous_to_lambda"), None);

    let fx = fixture_with_level(source, 8);
    let text = assist(&fx, "anonymous_to_lambda").expect("Java 8 可以改成 lambda");
    assert!(text.contains("Runnable r = () ->"), "{text}");
}

#[test]
fn switch_to_arrow_needs_java_14() {
    let source = r#"
class Main {
    void f(int n) {
        sw$0itch (n) {
            case 1:
                System.out.println("one");
                break;
            default:
                System.out.println("other");
        }
    }
}
"#;
    let fx = fixture_with_level(source, 11);
    assert_eq!(assist(&fx, "switch_to_arrow"), None);

    let fx = fixture_with_level(source, 17);
    let text = assist(&fx, "switch_to_arrow").expect("Java 14 起可以改成 `->`");
    assert!(
        text.contains("case 1 -> System.out.println(\"one\");"),
        "{text}"
    );
}

#[test]
fn fix_all_applies_behavior_preserving_fixes_only() {
    let fx = fixture(
        r#"
//- /app/Main.java
package app;

class Main {
    void f(String s, int[] a) {
        int b[] = a;
        String t = s.toString();
        new RuntimeException("x");
        System.out.println(b.length + t);
    }
}
"#,
    );
    let file_id = fx.files[0].file_id;
    let fix = crate::assists::fix_all(&fx.db, file_id).expect("应当有可修的问题");
    assert_eq!(fix.kind, crate::AssistKind::FixAll);
    let text = apply_change(&fx, &fix.change).remove(0).1;
    assert!(text.contains("int[] b = a;"), "{text}");
    assert!(text.contains("String t = s;"), "{text}");
    // 会改变行为的修复（补上 throw）不在其中
    assert!(
        text.contains("        new RuntimeException(\"x\");"),
        "{text}"
    );
}

#[test]
fn same_name_classes_in_different_modules_are_distinct() {
    use base_db::{
        salsa::Setter, workspace, FileEntry, FileKind, ModuleData, ModuleId, ProjectGraph,
        SourceRootKind,
    };
    use std::{path::PathBuf, sync::Arc};

    let mut fx = fixture(
        r#"
//- /alpha/src/main/java/com/acme/Config.java
package com.acme;
public class Config { public int alphaPort; public static class Inner {} }
//- /alpha/src/main/java/com/acme/App.java
package com.acme;
class App {}
//- /beta/src/main/java/com/acme/Config.java
package com.acme;
public class Config { public String betaHost; public static class Inner {} }
//- /beta/src/main/java/com/acme/App.java
package com.acme;
class App {}
"#,
    );
    let ws = workspace(&fx.db);
    let mut files = (**ws.files(&fx.db)).clone();
    for (module, path) in [
        (0, "/alpha/src/main/java/com/acme/Config.java"),
        (0, "/alpha/src/main/java/com/acme/App.java"),
        (1, "/beta/src/main/java/com/acme/Config.java"),
        (1, "/beta/src/main/java/com/acme/App.java"),
    ] {
        let file = fx.file_by_path(path);
        files.insert(
            file.file_id,
            FileEntry {
                source: file.source,
                kind: FileKind::Workspace {
                    module: Some(ModuleId(module)),
                    root: SourceRootKind::Main,
                },
            },
        );
    }
    let module = |name: &str| ModuleData {
        name: name.to_owned(),
        root: PathBuf::from(format!("/{name}")),
        source_roots: Vec::new(),
        language_level: None,
        api_release: None,
        test_language_level: None,
        preview: false,
        dependencies: Vec::new(),
        output_dirs: Vec::new(),
        encoding: None,
        transitive_dependencies: false,
    };
    let project = ProjectGraph {
        modules: vec![module("alpha"), module("beta")],
        ..ProjectGraph::default()
    };
    ws.set_files(&mut fx.db).to(Arc::new(files));
    ws.set_project(&mut fx.db).to(Arc::new(project));

    let db = &fx.db;
    let file = |path: &str| fx.file_by_path(path).source;
    let resolve = |path: &str| hir::lookup_class_from(db, Some(file(path)), "com/acme/Config");
    let alpha = resolve("/alpha/src/main/java/com/acme/App.java").unwrap();
    let beta = resolve("/beta/src/main/java/com/acme/App.java").unwrap();
    assert_ne!(alpha, beta);
    assert_eq!(alpha.binary_name(db), beta.binary_name(db));
    assert_eq!(hir::class_copies(db, "com/acme/Config").len(), 2);
    let fields = |class| {
        hir::class_data(db, class)
            .unwrap()
            .fields
            .iter()
            .map(|f| f.name.to_string())
            .collect::<Vec<_>>()
    };
    assert_eq!(fields(alpha), ["alphaPort"]);
    assert_eq!(fields(beta), ["betaHost"]);
    // 成员类型和外层类跟着所在的那一份走
    let inner = hir::nested_class(db, beta, "Inner").unwrap();
    assert_eq!(hir::outer_class(db, inner), Some(beta));
    assert_ne!(Some(inner), hir::nested_class(db, alpha, "Inner"));
    // 协议数据里的类标识能还原成同一份
    assert_eq!(hir::class_by_key(db, &beta.key(db)), Some(beta));
    assert_eq!(hir::class_by_key(db, &alpha.key(db)), Some(alpha));
    // 声明节点对应的类是所在文件里的那一份
    let beta_file = file("/beta/src/main/java/com/acme/Config.java");
    assert_eq!(hir::class_in_file(db, beta_file, "com/acme/Config"), beta);
    // 不看上下文的全局查找取主副本
    assert_eq!(hir::lookup_class(db, "com/acme/Config"), Some(alpha));
}

#[test]
fn copies_of_a_class_are_compatible_across_modules() {
    // `jakarta.servlet.http.HttpServletRequest` 既在 `jakarta.servlet-api` 里，又在
    // `tomcat-embed-core` 里：别的模块的签名里用的是另一份，javac 只按名字认类
    use base_db::{
        salsa::Setter, workspace, Dependency, DependencyTarget, FileEntry, FileKind, ModuleData,
        ModuleId, ProjectGraph, Scope, SourceRootKind,
    };
    use std::{path::PathBuf, sync::Arc};

    let mut fx = fixture(
        r#"
//- /tomcat/src/main/java/web/Request.java
package web;
public interface Request { String uri(); }
//- /tomcat/src/main/java/web/Failure.java
package web;
public class Failure extends Exception {}
//- /spring/src/main/java/spring/Holder.java
package spring;
import web.Request;
public class Holder {
    public static Request current() { return null; }
    public static void handle(Request request) {}
    public void init() throws web.Failure {}
    public static boolean hold(Box<Request> box) { return true; }
    public static Box<Request> box() { return null; }
}
//- /spring/src/main/java/spring/Box.java
package spring;
public class Box<T> {}
//- /api/src/main/java/web/Request.java
package web;
public interface Request { String uri(); }
//- /api/src/main/java/web/Failure.java
package web;
public class Failure extends Exception {}
//- /app/src/main/java/app/Main.java
package app;
import web.Failure;
import web.Request;
class Main extends spring.Holder {
    Request get() { return spring.Holder.current(); }
    void pass(Request request) { spring.Holder.handle(request); }
    @Override
    public void init() throws Failure { super.init(); }
    // 类型实参里的副本也是同一个类型
    boolean holdIt(spring.Box<Request> box) { return spring.Holder.hold(box); }
    spring.Box<Request> boxIt() { return spring.Holder.box(); }
}
"#,
    );
    let ws = workspace(&fx.db);
    let mut files = (**ws.files(&fx.db)).clone();
    for (module, path) in [
        (0, "/tomcat/src/main/java/web/Request.java"),
        (0, "/tomcat/src/main/java/web/Failure.java"),
        (1, "/spring/src/main/java/spring/Holder.java"),
        (1, "/spring/src/main/java/spring/Box.java"),
        (2, "/api/src/main/java/web/Request.java"),
        (2, "/api/src/main/java/web/Failure.java"),
        (3, "/app/src/main/java/app/Main.java"),
    ] {
        let file = fx.file_by_path(path);
        files.insert(
            file.file_id,
            FileEntry {
                source: file.source,
                kind: FileKind::Workspace {
                    module: Some(ModuleId(module)),
                    root: SourceRootKind::Main,
                },
            },
        );
    }
    let module = |name: &str, deps: &[u32]| ModuleData {
        name: name.to_owned(),
        root: PathBuf::from(format!("/{name}")),
        source_roots: Vec::new(),
        language_level: None,
        api_release: None,
        test_language_level: None,
        preview: false,
        dependencies: deps
            .iter()
            .map(|&m| Dependency {
                target: DependencyTarget::Module(ModuleId(m)),
                scope: Scope::Compile,
            })
            .collect(),
        output_dirs: Vec::new(),
        encoding: None,
        transitive_dependencies: false,
    };
    let project = ProjectGraph {
        modules: vec![
            module("tomcat", &[]),
            module("spring", &[0]),
            module("api", &[]),
            // app 看到的是 api 里的那一份，spring 的签名里是 tomcat 里的那一份
            module("app", &[2, 1]),
        ],
        ..ProjectGraph::default()
    };
    ws.set_files(&mut fx.db).to(Arc::new(files));
    ws.set_project(&mut fx.db).to(Arc::new(project));

    let main = fx.file_by_path("/app/src/main/java/app/Main.java").source;
    let errors: Vec<String> =
        ide_diagnostics::diagnostics(&fx.db, main, &ide_diagnostics::DiagnosticsConfig::default())
            .into_iter()
            .filter(|d| d.severity == ide_diagnostics::Severity::Error)
            .map(|d| d.message)
            .collect();
    assert!(errors.is_empty(), "{errors:?}");
}

fn goto_in_annotation(marker: &str) -> (String, SymbolKind) {
    let fx = fixture(&format!(
        r#"
//- /m/MediaType.java
package m;
public class MediaType {{
    public static final String TEXT_PLAIN = "text/plain";
    public static class Nested {{ public static final int N = 1; }}
}}
//- /m/Mode.java
package m;
public enum Mode {{ FAST, SLOW }}
//- /m/Produces.java
package m;
public @interface Produces {{ String[] value() default "*/*"; Mode mode() default Mode.FAST; int n() default 0; }}
//- /b/Main.java
package b;
import m.MediaType;
import m.Mode;
import m.Produces;
import static m.MediaType.TEXT_PLAIN;
{marker}
"#
    ));
    let result = navigation::goto_definition(&fx.db, position(&fx)).expect("没有跳转目标");
    let nav = &result.info[0];
    (slice(&fx, &nav.file, nav.focus_range).to_string(), nav.kind)
}

#[test]
fn goto_definition_in_annotation_values() {
    let cases = [
        (
            "class Main { @Produces(MediaType.TEXT_PL$0AIN) String hello() { return \"\"; } }",
            "TEXT_PLAIN",
            SymbolKind::Field,
        ),
        (
            "class Main { @Produces(Media$0Type.TEXT_PLAIN) String hello() { return \"\"; } }",
            "MediaType",
            SymbolKind::Class,
        ),
        (
            "@Produces(m.MediaType.TEXT_PL$0AIN) class Main {}",
            "TEXT_PLAIN",
            SymbolKind::Field,
        ),
        (
            "@Produces(TEXT_PL$0AIN) class Main {}",
            "TEXT_PLAIN",
            SymbolKind::Field,
        ),
        (
            "@Produces(value = {MediaType.TEXT_PL$0AIN}, mode = Mode.SLOW) class Main {}",
            "TEXT_PLAIN",
            SymbolKind::Field,
        ),
        (
            "@Produces(mode = Mode.SL$0OW) class Main {}",
            "SLOW",
            SymbolKind::EnumConstant,
        ),
        (
            "@Produces(n = MediaType.Nested.$0N) class Main {}",
            "N",
            SymbolKind::Field,
        ),
        (
            "class Main { static final String LOCAL = \"x\"; @Produces(LOC$0AL) void f() {} }",
            "LOCAL",
            SymbolKind::Field,
        ),
    ];
    for (source, name, kind) in cases {
        assert_eq!(
            goto_in_annotation(source),
            (name.to_string(), kind),
            "{source}"
        );
    }
}
