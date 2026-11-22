//! 无损语法树（基于 rowan）与类型化 AST。
//!
//! - [`SyntaxNode`] / [`SyntaxToken`]：保留全部空白和注释的具体语法树，树的文本恒等于源码。
//! - [`ast`]：在语法树之上的零成本类型化视图。
//! - [`Parse`]：解析结果，内部只持有 `GreenNode`（`Send + Sync`），可以安全地放进查询缓存。

pub mod algo;
pub mod ast;
mod build;
mod ptr;

use std::{marker::PhantomData, sync::Arc};

pub use parser::{SyntaxKind, T};
pub use rowan::{
    Direction, GreenNode, GreenToken, NodeOrToken, TextRange, TextSize, TokenAtOffset, WalkEvent,
};
pub use smol_str::SmolStr;

pub use crate::{
    ast::AstNode,
    ptr::{AstPtr, SyntaxNodePtr},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum JavaLanguage {}

impl rowan::Language for JavaLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> SyntaxKind {
        SyntaxKind::from_u16(raw.0)
    }

    fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}

pub type SyntaxNode = rowan::SyntaxNode<JavaLanguage>;
pub type SyntaxToken = rowan::SyntaxToken<JavaLanguage>;
pub type SyntaxElement = rowan::SyntaxElement<JavaLanguage>;
pub type SyntaxNodeChildren = rowan::SyntaxNodeChildren<JavaLanguage>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SyntaxError {
    pub message: String,
    pub range: TextRange,
}

/// 一次解析的结果：语法树 + 语法错误。
pub struct Parse<T> {
    green: GreenNode,
    errors: Arc<[SyntaxError]>,
    _ty: PhantomData<fn() -> T>,
}

impl<T> Clone for Parse<T> {
    fn clone(&self) -> Self {
        Parse {
            green: self.green.clone(),
            errors: self.errors.clone(),
            _ty: PhantomData,
        }
    }
}

impl<T> PartialEq for Parse<T> {
    fn eq(&self, other: &Self) -> bool {
        green_eq(&self.green, &other.green) && self.errors == other.errors
    }
}

/// 两棵绿树的内容是否相同。和 `GreenNode` 自带的比较等价，但遇到同一个子树（增量重解析后
/// 没变的部分是共享的）直接认为相等，不再逐层往下比。
pub fn green_eq(a: &rowan::GreenNodeData, b: &rowan::GreenNodeData) -> bool {
    if std::ptr::eq(a, b) {
        return true;
    }
    if a.kind() != b.kind()
        || a.text_len() != b.text_len()
        || a.children().len() != b.children().len()
    {
        return false;
    }
    a.children().zip(b.children()).all(|pair| match pair {
        (NodeOrToken::Node(x), NodeOrToken::Node(y)) => green_eq(x, y),
        (NodeOrToken::Token(x), NodeOrToken::Token(y)) => x == y,
        _ => false,
    })
}

impl<T> Eq for Parse<T> {}

impl<T> std::fmt::Debug for Parse<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Parse")
            .field("errors", &self.errors.len())
            .finish_non_exhaustive()
    }
}

impl<T> Parse<T> {
    pub fn syntax_node(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }

    pub fn errors(&self) -> &[SyntaxError] {
        &self.errors
    }

    pub fn green(&self) -> &GreenNode {
        &self.green
    }
}

impl<T: AstNode> Parse<T> {
    pub fn tree(&self) -> T {
        T::cast(self.syntax_node()).expect("根节点种类与 Parse 的类型参数不符")
    }
}

impl ast::CompilationUnit {
    pub fn parse(text: &str) -> Parse<ast::CompilationUnit> {
        let (green, errors) = build::build_tree(text);
        Parse {
            green,
            errors: errors.into(),
            _ty: PhantomData,
        }
    }
}

impl Parse<ast::CompilationUnit> {
    /// 块级增量重解析：旧文本的 `edit` 范围被替换后得到 `new_text`，
    /// 如果这次编辑完全落在某个方法体（或初始化块）的花括号之内，就只重新解析那个块。
    ///
    /// 返回 `None` 表示不适用，调用方应整文件重新解析。返回的结果与整文件解析等价。
    pub fn reparse(&self, edit: TextRange, new_text: &str) -> Option<Parse<ast::CompilationUnit>> {
        let root = self.syntax_node();
        let old_len = root.text_range().end();
        if edit.end() > old_len {
            return None;
        }
        let new_len = TextSize::of(new_text);
        // 被替换进来的文本长度 = 新长度 - (旧长度 - 被删掉的长度)
        let inserted = new_len.checked_sub(old_len.checked_sub(edit.len())?)?;

        let covering = match root.covering_element(edit) {
            NodeOrToken::Node(node) => node,
            NodeOrToken::Token(token) => token.parent()?,
        };
        let block = covering.ancestors().find(|node| {
            node.kind() == SyntaxKind::BLOCK
                && node.parent().is_some_and(|parent| {
                    matches!(
                        parent.kind(),
                        SyntaxKind::METHOD_DECL
                            | SyntaxKind::CONSTRUCTOR_DECL
                            | SyntaxKind::INITIALIZER_BLOCK
                    )
                })
                // 编辑必须严格在两个花括号之间
                && node.text_range().start() < edit.start()
                && edit.end() < node.text_range().end()
        })?;
        // 块必须以自己的右花括号结束：缺了右花括号时（末尾的 `}` 属于里层的块），
        // "此处应为 `}`" 报在块后面的 token 上，分不清它在新文本里还该不该有
        let closed = block
            .last_child_or_token()
            .and_then(NodeOrToken::into_token)
            .is_some_and(|token| token.kind() == SyntaxKind::R_CURLY);
        if !closed {
            return None;
        }
        let old_range = block.text_range();
        let new_end = old_range.end() - edit.len() + inserted;
        let new_range = TextRange::new(old_range.start(), new_end);
        let fragment =
            new_text.get(usize::from(new_range.start())..usize::from(new_range.end()))?;

        // 贴在块边界上的旧错误分不清属于块内还是块外：保守起见不做增量。
        // 块外的解析器报错时会标在"下一个 token"上，所以从左花括号开始的错误
        // （不管长度）也可能是块外报的。
        let ambiguous = self.errors.iter().any(|err| {
            err.range.start() == old_range.start()
                || (err.range.is_empty() && err.range.start() == old_range.end())
        });
        if ambiguous {
            return None;
        }

        let (green, block_errors) = build::build_block(fragment)?;
        let new_root = block.replace_with(green);

        let mut errors: Vec<SyntaxError> = Vec::with_capacity(self.errors.len());
        for err in self.errors.iter() {
            if err.range.end() <= old_range.start() {
                errors.push(err.clone());
            } else if err.range.start() >= old_range.end() {
                // 块之后的错误整体平移
                let start = err.range.start() - edit.len() + inserted;
                errors.push(SyntaxError {
                    message: err.message.clone(),
                    range: TextRange::at(start, err.range.len()),
                });
            } else if !old_range.contains_range(err.range) {
                // 跨越块边界的错误：无法可靠地保留
                return None;
            }
        }
        errors.extend(block_errors.into_iter().map(|err| SyntaxError {
            message: err.message,
            range: err.range + old_range.start(),
        }));
        errors.sort_by_key(|e| (e.range.start(), e.range.end()));
        Some(Parse {
            green: new_root,
            errors: errors.into(),
            _ty: PhantomData,
        })
    }
}

/// 两份文本之间的最小单处编辑：返回旧文本里被替换的范围。文本相同时返回 `None`。
pub fn diff_range(old: &str, new: &str) -> Option<TextRange> {
    if old == new {
        return None;
    }
    let mut prefix = old
        .bytes()
        .zip(new.bytes())
        .take_while(|(a, b)| a == b)
        .count();
    while !old.is_char_boundary(prefix) || !new.is_char_boundary(prefix) {
        prefix -= 1;
    }
    let max_suffix = old.len().min(new.len()) - prefix;
    let mut suffix = old
        .bytes()
        .rev()
        .zip(new.bytes().rev())
        .take(max_suffix)
        .take_while(|(a, b)| a == b)
        .count();
    while !old.is_char_boundary(old.len() - suffix) || !new.is_char_boundary(new.len() - suffix) {
        suffix -= 1;
    }
    Some(TextRange::new(
        TextSize::from(prefix as u32),
        TextSize::from((old.len() - suffix) as u32),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{AstNode, CompilationUnit};

    fn check_ok(text: &str) -> SyntaxNode {
        let parse = CompilationUnit::parse(text);
        let node = parse.syntax_node();
        assert_eq!(node.text().to_string(), text, "语法树必须无损");
        assert!(
            parse.errors().is_empty(),
            "不应有语法错误: {:#?}\n{:#?}",
            parse.errors(),
            node
        );
        node
    }

    fn check_lossless(text: &str) {
        let parse = CompilationUnit::parse(text);
        assert_eq!(parse.syntax_node().text().to_string(), text);
    }

    #[test]
    fn empty_file() {
        check_ok("");
        check_ok("  // only a comment\n");
    }

    #[test]
    fn class_with_members() {
        let node = check_ok(
            r#"
package a.b;

import java.util.List;
import static java.util.Collections.*;

/** Doc. */
@Deprecated
public final class Foo<T extends Comparable<T>> extends Base<T> implements Runnable, java.io.Serializable {
    private static final int X = 1, Y[] = {1, 2};
    protected List<? extends T> items = new java.util.ArrayList<>();

    static { System.out.println("init"); }

    public Foo(int x) throws Exception { this.x = x; }

    @Override
    public <R> R map(java.util.function.Function<? super T, ? extends R> f, int... rest) {
        return f.apply(null);
    }

    abstract void run();

    enum Color { RED, GREEN(1) { void f() {} }, BLUE; Color() {} Color(int x) {} }

    record Point(int x, int y) implements Comparable<Point> {
        Point { if (x < 0) throw new IllegalArgumentException(); }
        public int compareTo(Point o) { return 0; }
    }

    @interface Ann { String value() default "x"; int[] nums() default {1, 2}; }

    sealed interface Shape permits Circle, Square {}
    non-sealed class Circle implements Shape {}
}
"#,
        );
        let cu = CompilationUnit::cast(node).unwrap();
        assert_eq!(
            cu.package()
                .and_then(|p| p.name())
                .map(|n| n.text())
                .as_deref(),
            Some("a.b")
        );
        assert_eq!(cu.imports().count(), 2);
        let class = cu.type_decls().next().unwrap();
        assert_eq!(class.name().unwrap().text(), "Foo");
        assert!(class.doc_comment().is_some());
    }

    #[test]
    fn statements_and_expressions() {
        check_ok(
            r#"
class A {
    void f(Object o, int[] arr, java.util.List<String> list) throws Exception {
        int a = 1, b = a + 2 * 3 - (4 >> 1) >>> 2;
        final var c = (long) a;
        String s = (String) o;
        Runnable r = () -> {};
        java.util.function.Function<Integer, Integer> g = x -> x + 1;
        java.util.function.BiFunction<Integer, Integer, Integer> h = (x, y) -> x + y;
        java.util.function.Supplier<java.util.List<String>> sup = java.util.ArrayList<String>::new;
        Class<?> k = int[].class;
        if (o instanceof String str && !str.isEmpty()) { a++; } else if (a < b) --a; else a = b > 1 ? 2 : 3;
        for (int i = 0, j = 1; i < 10; i++, j--) { continue; }
        for (final String it : list) { break; }
        outer: while (true) { do { break outer; } while (a >= b); }
        try (var in = open(); other) { foo(); } catch (IllegalStateException | IllegalArgumentException e) { throw e; } finally { }
        switch (a) { case 1: case 2: foo(); break; default: bar(); }
        int v = switch (o) {
            case Integer i when i > 0 -> i;
            case Point(int x, var y) -> x;
            case null, default -> { yield 0; }
        };
        synchronized (this) { assert a > 0 : "msg"; }
        a <<= 2; a >>= 1; a >>>= 1; arr[0] += 1;
        Object n = new Outer.Inner<String>(1, "a") { int z; };
        int[][] m = new int[3][], q = {{1}, {2, 3}};
        this.<String>generic("x").field.method();
        list.stream().map(String::length).forEach(System.out::println);
        class Local {}
        ;
    }
}
"#,
        );
    }

    /// 正在输入、少了 `}` 的方法体不会吞掉后面的成员。
    #[test]
    fn unclosed_block_stops_at_member_declarations() {
        let text = r#"
class A {
    void broken(java.util.List<String> names) {
        for (String n : names) {
            n.length();
        names.clear();
    }

    int afterBroken() { return 1; }

    @Override
    public String toString() { return ""; }

    static { }

    <T> T generic(T t) { return t; }

    void viaSwitch(int k) {
        switch (k) {
            case 1:
                k++;

    java.util.Map<String, Integer> lookup(String key) { return null; }

    void lastOne() {
        record P(int a) {}
        int y = switch (1) { default -> { yield count(2); } };
        final int x = 1;
        synchronized (this) { }
        int[] arr = new int[x];
        String s;
    }
}
"#;
        let parse = CompilationUnit::parse(text);
        assert!(!parse.errors().is_empty());
        let root = parse.syntax_node();
        let class = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::CLASS_BODY)
            .unwrap();
        let members: Vec<String> = class
            .children()
            .filter(|n| {
                matches!(
                    n.kind(),
                    SyntaxKind::METHOD_DECL | SyntaxKind::INITIALIZER_BLOCK
                )
            })
            .map(|n| {
                n.children()
                    .find(|c| c.kind() == SyntaxKind::NAME)
                    .map_or_else(|| "<init>".to_owned(), |c| c.text().to_string())
            })
            .collect();
        assert_eq!(
            members,
            [
                "broken",
                "afterBroken",
                "toString",
                "<init>",
                "generic",
                "viaSwitch",
                "lookup",
                "lastOne"
            ],
            "{root:#?}"
        );
    }

    #[test]
    fn module_info() {
        check_ok(
            "open module a.b { requires transitive java.base; requires static x.y; exports a.b to c, d; opens a.b; uses a.S; provides a.S with a.Impl, a.Impl2; }",
        );
    }

    #[test]
    fn module_info_directives() {
        let node = check_ok(
            "module a.b { requires transitive java.base; requires x.y; exports a.b to c, d; opens a.c; }",
        );
        let cu = CompilationUnit::cast(node).unwrap();
        let body = cu.module().unwrap().body().unwrap();
        let requires: Vec<(String, bool)> = body
            .requires()
            .map(|r| (r.name().unwrap().text(), r.is_transitive()))
            .collect();
        assert_eq!(
            requires,
            vec![("java.base".to_owned(), true), ("x.y".to_owned(), false)]
        );
        let exports = body.exports().next().unwrap();
        assert_eq!(exports.name().unwrap().text(), "a.b");
        let targets: Vec<String> = exports.targets().map(|t| t.text()).collect();
        assert_eq!(targets, vec!["c", "d"]);
        assert_eq!(body.opens().next().unwrap().name().unwrap().text(), "a.c");
    }

    #[test]
    fn module_imports() {
        let node = check_ok(
            "import module java.base;\nimport module.foo.Bar;\nimport module;\nimport static module.Util.*;\nclass A {}",
        );
        let cu = CompilationUnit::cast(node).unwrap();
        let imports: Vec<(bool, String)> = cu
            .imports()
            .map(|i| (i.is_module(), i.name().unwrap().text()))
            .collect();
        assert_eq!(
            imports,
            vec![
                (true, "java.base".to_owned()),
                (false, "module.foo.Bar".to_owned()),
                (false, "module".to_owned()),
                (false, "module.Util".to_owned()),
            ]
        );
    }

    #[test]
    fn incomplete_code_is_lossless_and_keeps_shape() {
        let text = "class A { void f() { foo. } void g() { new Bar( } int }";
        check_lossless(text);
        let parse = CompilationUnit::parse(text);
        assert!(!parse.errors().is_empty());
        let has_field_access = parse
            .syntax_node()
            .descendants()
            .any(|n| n.kind() == SyntaxKind::FIELD_ACCESS);
        assert!(has_field_access, "`foo.` 应当解析为缺成员名的 FIELD_ACCESS");
    }

    #[test]
    fn garbage_never_panics() {
        for text in [
            "}}}} ((( ]]] ;;; @ @ @",
            "class",
            "class A { void f( { } }",
            "import ; package ; class A extends { }",
            "class A { int x = ; void f() { if ( } }",
            "\"unterminated\nclass A {}",
            "class A { void f() { switch (x) { case -> ; default } } }",
            "a -> -> b",
        ] {
            check_lossless(text);
        }
    }
    /// 把 `old` 改成 `new`：增量结果必须与整文件解析完全一致。
    fn check_reparse(old: &str, new: &str, expect_incremental: bool) {
        let old_parse = CompilationUnit::parse(old);
        let full = CompilationUnit::parse(new);
        let edit = diff_range(old, new).expect("文本应当不同");
        match old_parse.reparse(edit, new) {
            Some(incremental) => {
                assert!(expect_incremental, "不应走增量路径: {old:?} -> {new:?}");
                assert_eq!(incremental.syntax_node().text().to_string(), new);
                assert_eq!(
                    format!("{:#?}", incremental.syntax_node()),
                    format!("{:#?}", full.syntax_node())
                );
                assert_eq!(incremental.errors(), full.errors());
            }
            None => assert!(!expect_incremental, "应当走增量路径: {old:?} -> {new:?}"),
        }
    }

    #[test]
    fn reparse_inside_method_body() {
        let old = "class A {\n  void f() { int x = 1; }\n  void g() { foo(; }\n}\n";
        // 方法体内的插入、删除、替换
        check_reparse(
            old,
            "class A {\n  void f() { int x = 12; }\n  void g() { foo(; }\n}\n",
            true,
        );
        check_reparse(
            old,
            "class A {\n  void f() { int x; }\n  void g() { foo(; }\n}\n",
            true,
        );
        check_reparse(
            old,
            "class A {\n  void f() { if (a) { b(); } }\n  void g() { foo(; }\n}\n",
            true,
        );
        // 改动带来新的语法错误，后面方法里原有的错误要跟着平移
        check_reparse(
            old,
            "class A {\n  void f() { int x = ; }\n  void g() { foo(; }\n}\n",
            true,
        );
        // 修掉块里原有的错误
        check_reparse(
            old,
            "class A {\n  void f() { int x = 1; }\n  void g() { foo(); }\n}\n",
            true,
        );
    }

    #[test]
    fn reparse_falls_back_when_structure_changes() {
        let old = "class A {\n  void f() { int x = 1; }\n}\n";
        // 花括号不再配对
        check_reparse(old, "class A {\n  void f() { int x = 1; } }\n}\n", false);
        check_reparse(old, "class A {\n  void f() { { int x = 1; }\n}\n", false);
        // 未闭合的注释吞掉了右花括号
        check_reparse(old, "class A {\n  void f() { /* int x = 1; }\n}\n", false);
        // 改动在方法体之外
        check_reparse(old, "class A {\n  void ff() { int x = 1; }\n}\n", false);
        check_reparse(old, "class B {\n  void f() { int x = 1; }\n}\n", false);
    }

    /// 模糊测试找到的输入：增量与整文件解析给出的错误必须完全一致。
    #[test]
    fn reparse_fuzz_regressions() {
        for (old, new) in [
            (
                "\u{1}\0\0\0clm({u[}tm{if2u[t",
                "\u{1}\0\0\0clm({u$[}tm{if2u[t",
            ),
            // 构造器的块缺了自己的右花括号（末尾的 `}` 属于里层的块），插入的 `}` 把它补上了
            (
                "0xz{.o?{o?x.?.??}<o}<?hc.}xd<?h",
                "0xz{.o?{o?x.?.?c.}xd<?}<o}<?hc.}xd<?h",
            ),
        ] {
            let old_parse = CompilationUnit::parse(old);
            let edit = diff_range(old, new).unwrap();
            if let Some(incremental) = old_parse.reparse(edit, new) {
                let full = CompilationUnit::parse(new);
                assert_eq!(incremental.green(), full.green());
                assert_eq!(incremental.errors(), full.errors(), "{old:?} -> {new:?}");
            }
        }
    }

    /// JLS 3.3：`\uXXXX` 在分词之前翻译。三份文件 javac 都能编译，
    /// 因此不应该有任何语法错误（报告见 issue：此前分别报 5 个、约 10 个语法
    /// 错误和一个 Cannot resolve symbol）。
    #[test]
    fn unicode_escapes_translate_before_lexing() {
        // 1. token 之间的转义：`\u0020` 就是空格
        let text = "class UnicodeSpace {\n    int\\u0020x = 1;\n    int y = 2;\n}\n";
        let parse = CompilationUnit::parse(text);
        assert_eq!(parse.syntax_node().text().to_string(), text);
        assert!(parse.errors().is_empty(), "{:#?}", parse.errors());

        // 2. 转义拼出注释起点：整行在 javac 眼里是注释
        let text = "class UnicodeCommentStart {\n\\u002f\\u002f javac sees a comment\n    int y = 2;\n}\n";
        let parse = CompilationUnit::parse(text);
        assert_eq!(parse.syntax_node().text().to_string(), text);
        assert!(parse.errors().is_empty(), "{:#?}", parse.errors());

        // 3. 注释里的 `\u000A` 是行终止符：后面的 `int x = 1;` 是真代码
        let text = "class UnicodeNewlineCode {\n    int use() {\n        // \\u000A int x = 1;\n        return x;\n    }\n}\n";
        let parse = CompilationUnit::parse(text);
        assert_eq!(parse.syntax_node().text().to_string(), text);
        assert!(parse.errors().is_empty(), "{:#?}", parse.errors());
        let declared = parse
            .syntax_node()
            .descendants()
            .filter_map(ast::VariableDeclarator::cast)
            .any(|d| d.name().is_some_and(|n| n.text() == "x"));
        assert!(declared, "注释里的转义换行之后应当出现 `int x = 1;` 声明");
    }

    #[test]
    fn diff_range_finds_minimal_edit() {
        assert_eq!(diff_range("abc", "abc"), None);
        assert_eq!(
            diff_range("abcd", "abXd"),
            Some(TextRange::new(2.into(), 3.into()))
        );
        assert_eq!(
            diff_range("ab", "aXb"),
            Some(TextRange::new(1.into(), 1.into()))
        );
        assert_eq!(
            diff_range("aXb", "ab"),
            Some(TextRange::new(1.into(), 2.into()))
        );
        // 重复字符：前后缀不能重叠
        assert_eq!(
            diff_range("aa", "aaa"),
            Some(TextRange::new(2.into(), 2.into()))
        );
        // 多字节字符不会被切开
        let range = diff_range("x = \"中\";", "x = \"丰\";").unwrap();
        assert!("x = \"中\";".is_char_boundary(usize::from(range.start())));
        assert!("x = \"中\";".is_char_boundary(usize::from(range.end())));
    }
    fn test_data(dir: &str) -> Vec<(std::path::PathBuf, String)> {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("test_data")
            .join(dir);
        let mut files: Vec<_> = std::fs::read_dir(&dir)
            .unwrap_or_else(|err| panic!("{}: {err}", dir.display()))
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "java"))
            .collect();
        files.sort();
        assert!(!files.is_empty(), "{} 下没有测试文件", dir.display());
        files
            .into_iter()
            .map(|path| (path.clone(), std::fs::read_to_string(path).unwrap()))
            .collect()
    }

    /// `test_data/ok` 下的文件是合法的 Java：必须无损且没有任何语法错误。
    #[test]
    fn corpus_ok_files_parse_cleanly() {
        for (path, text) in test_data("ok") {
            let parse = CompilationUnit::parse(&text);
            assert_eq!(
                parse.syntax_node().text().to_string(),
                text,
                "{}",
                path.display()
            );
            let errors: Vec<String> = parse
                .errors()
                .iter()
                .map(|err| {
                    let line = text[..usize::from(err.range.start())].matches('\n').count() + 1;
                    format!("第 {line} 行: {}", err.message)
                })
                .collect();
            assert!(
                errors.is_empty(),
                "{}:\n{}",
                path.display(),
                errors.join("\n")
            );
            // 合法代码里不应出现 ERROR 节点
            assert!(
                parse
                    .syntax_node()
                    .descendants()
                    .all(|n| n.kind() != SyntaxKind::ERROR),
                "{}",
                path.display()
            );
        }
    }

    /// `test_data/err` 下的文件是残缺的：必须无损、报出错误，并且错误范围都落在文件之内。
    #[test]
    fn corpus_err_files_recover() {
        for (path, text) in test_data("err") {
            let parse = CompilationUnit::parse(&text);
            let root = parse.syntax_node();
            assert_eq!(root.text().to_string(), text, "{}", path.display());
            assert!(!parse.errors().is_empty(), "{}", path.display());
            for err in parse.errors() {
                assert!(root.text_range().contains_range(err.range), "{err:?}");
            }
            // 错误恢复之后，文件末尾那个完好的字段仍然被识别出来
            let recovered = root
                .descendants()
                .filter_map(ast::VariableDeclarator::cast)
                .any(|d| d.name().is_some_and(|n| n.text() == "ok"));
            assert!(recovered, "{}: 没有恢复出 `int ok = 1;`", path.display());
        }
    }

    /// 在语料文件的每个方法体里做一次编辑：增量结果必须与整文件解析一致。
    #[test]
    fn corpus_incremental_reparse_matches_full_parse() {
        for (path, text) in test_data("ok") {
            let old_parse = CompilationUnit::parse(&text);
            let blocks: Vec<TextRange> = old_parse
                .syntax_node()
                .descendants()
                .filter(|n| {
                    n.kind() == SyntaxKind::BLOCK
                        && n.parent()
                            .is_some_and(|p| p.kind() == SyntaxKind::METHOD_DECL)
                })
                .map(|n| n.text_range())
                .collect();
            for block in blocks {
                // 在左花括号后面插入一条语句
                let at = usize::from(block.start()) + 1;
                let mut new_text = text.clone();
                new_text.insert_str(at, " int __inserted = 0; ");
                let edit = diff_range(&text, &new_text).unwrap();
                let incremental = old_parse
                    .reparse(edit, &new_text)
                    .unwrap_or_else(|| panic!("{}: 方法体内的编辑应当走增量路径", path.display()));
                let full = CompilationUnit::parse(&new_text);
                assert_eq!(incremental.green(), full.green(), "{}", path.display());
                assert_eq!(incremental.errors(), full.errors(), "{}", path.display());
            }
        }
    }
}
