//! 文档注释里的引用：`{@link Foo#bar(int)}`、`{@linkplain}`、`{@value}`、`@see`、
//! `@throws` / `@exception` 的类型，以及 `@param` 的形参名和类型参数（`@param <T>`）。
//!
//! 引用按被注释的声明所在的作用域解析：类型名走 import 和成员类型，`#member` 不写类型时
//! 在被注释的类（成员的注释里是它所在的类）、它的父类型和外层类里找。

use base_db::{Db, SourceFile};
use hir::{all_supers, class_data, method_sig, ClassId, Definition, FieldId, MethodId, Semantics};
use syntax::{
    ast::{self, AstNode},
    SyntaxKind, SyntaxNode, SyntaxToken, TextRange, TextSize,
};

use crate::search::{refers_to, Reference, ReferenceKind};

/// 文档注释里一个名字指向的东西。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DocTarget {
    /// 类型路径的前若干段（`java.util.Map.Entry` 里的 `Map` 是 `["java", "util", "Map"]`）
    Type(Vec<String>),
    /// `Type#name` / `#name(params)`
    Member {
        ty: Vec<String>,
        name: String,
        params: Option<Vec<String>>,
    },
    /// `@param name`
    Param(String),
    /// `@param <T>`
    TypeParam(String),
}

/// 文档注释里的一个名字（范围是文件里的绝对位置）。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocSegment {
    pub range: TextRange,
    pub target: DocTarget,
}

/// 文档注释里的全部引用名字。
pub fn doc_segments(token: &SyntaxToken) -> Vec<DocSegment> {
    let base = token.text_range().start();
    parse_segments(token.text())
        .into_iter()
        .map(|(start, len, target)| DocSegment {
            range: TextRange::at(
                base + TextSize::from(start as u32),
                TextSize::from(len as u32),
            ),
            target,
        })
        .collect()
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '$'
}

/// `(起点, 长度, 目标)`，位置相对注释文本。
fn parse_segments(text: &str) -> Vec<(usize, usize, DocTarget)> {
    let mut res = Vec::new();
    let bytes = text.as_bytes();
    let mut i = 0;
    while let Some(at) = text[i..].find('@').map(|p| p + i) {
        i = at + 1;
        let tag_end = text[i..]
            .find(|c: char| !c.is_ascii_alphabetic())
            .map_or(text.len(), |p| p + i);
        let tag = &text[i..tag_end];
        let inline = at > 0 && bytes[at - 1] == b'{';
        let block = !inline && at_line_start(text, at);
        let kind = match (tag, inline, block) {
            ("link" | "linkplain" | "value", true, _) => Some(TagKind::Reference),
            ("see", _, true) => Some(TagKind::Reference),
            ("throws" | "exception", _, true) => Some(TagKind::Type),
            ("param", _, true) => Some(TagKind::Param),
            _ => None,
        };
        let Some(kind) = kind else {
            continue;
        };
        // 标签名之后至少一个空白，再到引用本身
        let rest = &text[tag_end..];
        let trimmed = rest.trim_start_matches([' ', '\t']);
        if trimmed.len() == rest.len() && !rest.is_empty() {
            continue;
        }
        let start = tag_end + (rest.len() - trimmed.len());
        i = start;
        match kind {
            TagKind::Param => parse_param(text, start, &mut res),
            TagKind::Type | TagKind::Reference => {
                let end = reference_end(text, start);
                if end > start {
                    parse_reference(
                        text,
                        start,
                        end,
                        matches!(kind, TagKind::Reference),
                        &mut res,
                    );
                    i = end;
                }
            }
        }
    }
    res
}

#[derive(Clone, Copy)]
enum TagKind {
    Reference,
    Type,
    Param,
}

/// `@` 前面这一行只有空白和 `*`（或者注释开头的 `/**`）。
fn at_line_start(text: &str, at: usize) -> bool {
    let line_start = text[..at].rfind('\n').map_or(0, |p| p + 1);
    let prefix = &text[line_start..at];
    let prefix = prefix.strip_prefix("/**").unwrap_or(prefix);
    prefix.chars().all(|c| c.is_whitespace() || c == '*')
}

/// 引用在哪里结束：空白或 `}`，括号里的空白不算。
fn reference_end(text: &str, start: usize) -> usize {
    let mut depth = 0;
    for (offset, c) in text[start..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    return start + offset + 1;
                }
            }
            '\n' | '\r' => return start + offset,
            '}' if depth == 0 => return start + offset,
            c if c.is_whitespace() && depth == 0 => return start + offset,
            _ => {}
        }
    }
    text.len()
}

fn parse_param(text: &str, start: usize, out: &mut Vec<(usize, usize, DocTarget)>) {
    let rest = &text[start..];
    if let Some(inner) = rest.strip_prefix('<') {
        let len = inner
            .find(|c: char| !is_ident_char(c))
            .unwrap_or(inner.len());
        if len > 0 && inner[len..].starts_with('>') {
            out.push((
                start + 1,
                len,
                DocTarget::TypeParam(inner[..len].to_owned()),
            ));
        }
        return;
    }
    let len = rest.find(|c: char| !is_ident_char(c)).unwrap_or(rest.len());
    if len > 0 {
        out.push((start, len, DocTarget::Param(rest[..len].to_owned())));
    }
}

/// 一条类型路径（`a.b.C`）的各段：`(起点, 长度, 到这一段为止的路径)`。
fn path_segments(text: &str, start: usize, end: usize) -> Vec<(usize, usize, Vec<String>)> {
    let mut res = Vec::new();
    let mut path = Vec::new();
    let mut seg_start = start;
    for part in text[start..end].split('.') {
        let len = part.len();
        if len == 0 || !part.chars().all(is_ident_char) {
            return res;
        }
        path.push(part.to_owned());
        res.push((seg_start, len, path.clone()));
        seg_start += len + 1;
    }
    res
}

fn parse_reference(
    text: &str,
    start: usize,
    end: usize,
    allow_member: bool,
    out: &mut Vec<(usize, usize, DocTarget)>,
) {
    let reference = &text[start..end];
    // `@see "书名"`、`@see <a href=…>`
    if reference.starts_with(['"', '<']) {
        return;
    }
    // 模块前缀 `java.base/java.util.List`
    let paren = reference.find('(').unwrap_or(reference.len());
    let hash = reference[..paren].find('#');
    let type_end_rel = hash.unwrap_or(paren);
    let module_end = reference[..type_end_rel].find('/').map_or(0, |p| p + 1);
    let type_start = start + module_end;
    let type_end = start + type_end_rel;
    let mut type_path = Vec::new();
    if type_end > type_start {
        for (s, len, path) in path_segments(text, type_start, type_end) {
            type_path = path.clone();
            out.push((s, len, DocTarget::Type(path)));
        }
        if type_path.is_empty() {
            return;
        }
    }
    let Some(hash) = hash.filter(|_| allow_member) else {
        return;
    };
    let name_start = start + hash + 1;
    let name_end = start + paren;
    let name = &text[name_start..name_end];
    if name.is_empty() || !name.chars().all(is_ident_char) {
        return;
    }
    let params = (paren < reference.len()).then(|| {
        let inner_start = start + paren + 1;
        let inner_end = end.saturating_sub(1).max(inner_start);
        let inner = &text[inner_start..inner_end];
        let mut params = Vec::new();
        let mut offset = inner_start;
        for part in inner.split(',') {
            let leading = part.len() - part.trim_start().len();
            let word = part
                .trim_start()
                .split(|c: char| c.is_whitespace())
                .next()
                .unwrap_or("");
            let ty = word.trim_end_matches("...").trim_end_matches("[]");
            let ty = ty.trim_end_matches("[]");
            if !ty.is_empty() {
                let ty_start = offset + leading;
                for (s, len, path) in path_segments(text, ty_start, ty_start + ty.len()) {
                    out.push((s, len, DocTarget::Type(path)));
                }
                params.push(normalize_param(word));
            }
            offset += part.len() + 1;
        }
        params
    });
    out.push((
        name_start,
        name.len(),
        DocTarget::Member {
            ty: type_path,
            name: name.to_owned(),
            params,
        },
    ));
}

/// 文档里写的形参类型去掉限定名，`...` 当数组：`java.lang.String...` → `String[]`。
fn normalize_param(word: &str) -> String {
    let (base, varargs) = match word.strip_suffix("...") {
        Some(base) => (base, true),
        None => (word, false),
    };
    let simple = base.rsplit('.').next().unwrap_or(base);
    if varargs {
        format!("{simple}[]")
    } else {
        simple.to_owned()
    }
}

/// 文档注释所注释的声明：类型、方法、构造器、字段、枚举常量、记录。
pub fn documented_decl(token: &SyntaxToken) -> Option<SyntaxNode> {
    token.parent()
}

/// 解析文档注释里的名字时取作用域的节点。类的注释按类体里的作用域解析：
/// 类自己的成员类型和类型参数都看得见，`#member` 指的是它自己的成员。
pub fn doc_scope_node(token: &SyntaxToken) -> Option<SyntaxNode> {
    let decl = documented_decl(token)?;
    Some(if ast::TypeDecl::can_cast(decl.kind()) {
        decl.children()
            .find(|c| c.kind() == SyntaxKind::CLASS_BODY)
            .unwrap_or(decl)
    } else {
        decl
    })
}

/// 文档里引用方法时形参类型的写法：擦除后的类型，不带包名（嵌套类带外层类名），
/// 例如 `Map.Entry[]`、`int`、`Object`（类型参数擦除到上界）。
pub fn doc_param_type(db: &dyn Db, ty: &hir::Ty) -> String {
    match ty.erasure(db) {
        hir::Ty::Array(element) => format!("{}[]", doc_param_type(db, &element)),
        hir::Ty::Class(class, _) => {
            let name = class.binary_name(db);
            let simple = name.rsplit('/').next().unwrap_or(&name);
            simple.replace('$', ".")
        }
        other => other.display(db),
    }
}

/// 解析文档注释里的一个名字。
pub fn resolve_segment(
    db: &dyn Db,
    file: SourceFile,
    token: &SyntaxToken,
    target: &DocTarget,
) -> Option<Definition> {
    let sema = Semantics::new(db);
    let decl = documented_decl(token)?;
    let scope = sema.type_scope(file, &doc_scope_node(token)?);
    let resolve_type = |path: &[String]| -> Option<Definition> {
        match hir::resolve_type_path(db, &scope, path)? {
            hir::TypeNs::Class(class) => Some(Definition::Class(class)),
            hir::TypeNs::TypeParam(param) => Some(Definition::TypeParam(param)),
        }
    };
    match target {
        DocTarget::Type(path) => resolve_type(path),
        DocTarget::Member { ty, name, params } => {
            let classes: Vec<ClassId> = if ty.is_empty() {
                // 被注释的类自己（成员的注释里是它所在的类），再往外层类找
                let mut res = Vec::new();
                let mut class = scope.class;
                while let Some(c) = class {
                    res.push(c);
                    class = hir::outer_class(db, c);
                }
                res
            } else {
                match resolve_type(ty)? {
                    Definition::Class(class) => vec![class],
                    _ => return None,
                }
            };
            classes
                .into_iter()
                .find_map(|class| find_member(db, class, name, params.as_deref()))
        }
        DocTarget::Param(name) | DocTarget::TypeParam(name) => {
            let type_param = matches!(target, DocTarget::TypeParam(_));
            let list_kinds: &[SyntaxKind] = if type_param {
                &[SyntaxKind::TYPE_PARAM_LIST]
            } else {
                &[SyntaxKind::PARAM_LIST]
            };
            let decl_name = decl
                .children()
                .filter(|child| list_kinds.contains(&child.kind()))
                .flat_map(|list| list.descendants().filter_map(ast::Name::cast))
                .find(|n| n.text() == name.as_str())?;
            sema.classify_name(file, &decl_name)
        }
    }
}

/// `class` 及其父类型里名为 `name` 的成员。`params` 给出时找方法（含构造器），按形参的
/// 简单类型名匹配，对不上时退回到个数相同的、再退回到同名的第一个。
fn find_member(
    db: &dyn Db,
    class: ClassId,
    name: &str,
    params: Option<&[String]>,
) -> Option<Definition> {
    let mut classes = vec![class];
    classes.extend(all_supers(db, class).iter().copied());
    for c in classes {
        let Some(data) = class_data(db, c) else {
            continue;
        };
        if params.is_none() {
            if let Some((idx, _)) = data.field_named(name) {
                return Some(Definition::Field(FieldId { class: c, idx }));
            }
        }
        let candidates: Vec<MethodId> = if data.name == name {
            data.constructors()
                .map(|(idx, _)| MethodId { class: c, idx })
                .collect()
        } else {
            data.methods_named(name)
                .map(|(idx, _)| MethodId { class: c, idx })
                .collect()
        };
        if candidates.is_empty() {
            continue;
        }
        let Some(params) = params else {
            return candidates.first().map(|m| Definition::Method(*m));
        };
        let matches_exactly = |method: &MethodId| {
            let sig = method_sig(db, *method);
            sig.params.len() == params.len()
                && sig.params.iter().zip(params).all(|(ty, written)| {
                    let shown = ty.erasure(db).display(db);
                    let simple = strip_generics(&shown);
                    simple == *written || matches!(ty, hir::Ty::TypeParam(_))
                })
        };
        let found = candidates
            .iter()
            .find(|m| matches_exactly(m))
            .or_else(|| {
                candidates
                    .iter()
                    .find(|m| method_sig(db, **m).params.len() == params.len())
            })
            .or(candidates.first());
        return found.map(|m| Definition::Method(*m));
    }
    None
}

/// `java.util.List<String>[]` → `List[]`
fn strip_generics(shown: &str) -> String {
    let mut res = String::new();
    let mut depth = 0;
    for c in shown.chars() {
        match c {
            '<' => depth += 1,
            '>' => depth -= 1,
            _ if depth == 0 => res.push(c),
            _ => {}
        }
    }
    let dims = res.matches("[]").count();
    let base = res.trim_end_matches("[]");
    let simple = base.rsplit(['.', '$']).next().unwrap_or(base);
    format!("{simple}{}", "[]".repeat(dims))
}

/// 光标在文档注释里的一个引用名字上时，它的范围和解析结果。
pub fn definition_at(
    db: &dyn Db,
    file: SourceFile,
    root: &SyntaxNode,
    offset: TextSize,
) -> Option<(TextRange, Definition)> {
    let token = root
        .token_at_offset(offset)
        .find(|t| t.kind() == SyntaxKind::DOC_COMMENT)?;
    let segment = doc_segments(&token)
        .into_iter()
        .find(|s| s.range.contains_inclusive(offset))?;
    let def = resolve_segment(db, file, &token, &segment.target)?;
    Some((segment.range, def))
}

/// 光标是否在文档注释里（在注释里时代码里的名字查找不适用）。
pub fn in_doc_comment(root: &SyntaxNode, offset: TextSize) -> bool {
    root.token_at_offset(offset).any(|t| {
        let range = t.text_range();
        t.kind() == SyntaxKind::DOC_COMMENT && range.start() < offset && offset < range.end()
    })
}

/// 文件的文档注释里对 `def` 的引用。
pub fn doc_references_in_file(
    db: &dyn Db,
    file: SourceFile,
    def: &Definition,
    name: &str,
) -> Vec<Reference> {
    let text = file.text(db);
    if name.is_empty() || !text.contains(name) || !text.contains("/**") {
        return Vec::new();
    }
    let root = base_db::parse(db, file).syntax_node();
    let file_id = file.file_id(db);
    let mut res = Vec::new();
    let mut current: Option<(SyntaxToken, Vec<DocSegment>)> = None;
    for (offset, _) in text.match_indices(name) {
        let offset = TextSize::from(offset as u32);
        let Some(token) = root
            .token_at_offset(offset)
            .find(|t| t.kind() == SyntaxKind::DOC_COMMENT)
        else {
            continue;
        };
        if current.as_ref().is_none_or(|(t, _)| *t != token) {
            let segments = doc_segments(&token);
            current = Some((token.clone(), segments));
        }
        let Some((_, segments)) = &current else {
            continue;
        };
        let range = TextRange::at(offset, TextSize::from(name.len() as u32));
        let Some(segment) = segments.iter().find(|s| s.range == range) else {
            continue;
        };
        let Some(found) = resolve_segment(db, file, &token, &segment.target) else {
            continue;
        };
        if refers_to(db, &found, def) {
            res.push(Reference {
                file_id,
                range,
                kind: ReferenceKind::Read,
            });
        }
    }
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(text: &str) -> Vec<(String, DocTarget)> {
        parse_segments(text)
            .into_iter()
            .map(|(s, len, target)| (text[s..s + len].to_owned(), target))
            .collect()
    }

    #[test]
    fn parses_links_and_tags() {
        let text = "/**\n * See {@link java.util.List#get(int) get} and {@link #run}.\n * @param <T> the type\n * @param count how many\n * @throws IllegalStateException when\n * @see Map.Entry#getKey()\n * @see \"Book\"\n * mail me @param not a tag\n */";
        let got = names(text);
        let shown: Vec<&str> = got.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(
            shown,
            [
                "java",
                "util",
                "List",
                "int",
                "get",
                "run",
                "T",
                "count",
                "IllegalStateException",
                "Map",
                "Entry",
                "getKey"
            ]
        );
        assert_eq!(
            got[4].1,
            DocTarget::Member {
                ty: vec!["java".into(), "util".into(), "List".into()],
                name: "get".into(),
                params: Some(vec!["int".into()]),
            }
        );
        assert_eq!(
            got[5].1,
            DocTarget::Member {
                ty: vec![],
                name: "run".into(),
                params: None,
            }
        );
        assert_eq!(got[6].1, DocTarget::TypeParam("T".into()));
        assert_eq!(got[7].1, DocTarget::Param("count".into()));
    }

    #[test]
    fn varargs_and_spaces_in_params() {
        let got = names("/** {@link #m(String[], java.lang.Object... rest)} */");
        let member = got.last().unwrap();
        assert_eq!(
            member.1,
            DocTarget::Member {
                ty: vec![],
                name: "m".into(),
                params: Some(vec!["String[]".into(), "Object[]".into()]),
            }
        );
        assert_eq!(
            strip_generics("java.util.List<java.lang.String>[]"),
            "List[]"
        );
        assert_eq!(normalize_param("java.lang.Object..."), "Object[]");
    }
}
