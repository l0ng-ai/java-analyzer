//! Spring 配置：`application*.properties` / `.yml` 里的配置项，以及 Java 代码里引用它们的地方
//! （`@Value("${key:default}")`、`environment.getProperty("key")`）。
//!
//! 配置项按 Spring 的宽松绑定比较：忽略大小写、`-` 和 `_`（`app.max-size` 等同于 `app.maxSize`）。

use base_db::{workspace, Db, FileId, ModuleId, ResourceFile};
use syntax::{
    ast::{self, AstNode},
    SyntaxKind, SyntaxToken, TextRange, TextSize,
};

/// 配置文件里的一项。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConfigProperty {
    /// 展开后的完整键：`spring.datasource.url`、`app.servers[0]`
    pub key: String,
    pub value: String,
    pub file_id: FileId,
    /// 配置文件名，如 `application-dev.yml`
    pub file_name: smol_str::SmolStr,
    /// 键在文件里的范围（YAML 里是最后一段）
    pub key_range: TextRange,
}

/// 宽松绑定下的规范形式。
pub fn canonical(key: &str) -> String {
    key.chars()
        .filter(|c| *c != '-' && *c != '_')
        .flat_map(char::to_lowercase)
        .collect()
}

/// 资源文件名是不是配置文件（而不是配置元数据之类的其他资源）。
pub fn is_config_name(name: &str) -> bool {
    [".properties", ".yml", ".yaml"]
        .iter()
        .any(|ext| name.ends_with(ext))
}

/// 一个模块能看到的配置文件：它自己的、它依赖的模块的，以及不属于任何模块的。
/// `module` 为 `None` 时全部可见。
pub fn visible_resources(db: &dyn Db, module: Option<ModuleId>) -> Vec<ResourceFile> {
    let ws = workspace(db);
    // 资源文件里还有 `lombok.config` 等，只要 Spring 的配置文件
    let resources: Vec<&ResourceFile> = ws
        .resources(db)
        .iter()
        .filter(|r| is_config_name(&r.name))
        .collect();
    let Some(module) = module else {
        return resources.into_iter().cloned().collect();
    };
    let project = ws.project(db);
    let mut visible = vec![module];
    if let Some(data) = project.modules.get(module.0 as usize) {
        for dependency in &data.dependencies {
            match dependency.target {
                base_db::DependencyTarget::Module(id)
                | base_db::DependencyTarget::ModuleTests(id) => visible.push(id),
                base_db::DependencyTarget::Library(_) => {}
            }
        }
    }
    resources
        .into_iter()
        .filter(|r| r.module.is_none_or(|m| visible.contains(&m)))
        .cloned()
        .collect()
}

/// 模块能看到的全部配置项。
pub fn config_properties(db: &dyn Db, module: Option<ModuleId>) -> Vec<ConfigProperty> {
    let mut out = Vec::new();
    for resource in visible_resources(db, module) {
        parse_resource(&resource, &mut out);
    }
    out
}

pub fn parse_resource(resource: &ResourceFile, out: &mut Vec<ConfigProperty>) {
    let mut push = |key: String, value: String, range: TextRange| {
        out.push(ConfigProperty {
            key,
            value,
            file_id: resource.file_id,
            file_name: resource.name.clone(),
            key_range: range,
        })
    };
    if resource.name.ends_with(".properties") {
        parse_properties(&resource.text, &mut push);
    } else {
        parse_yaml(&resource.text, &mut push);
    }
}

fn range(start: usize, end: usize) -> TextRange {
    TextRange::new(TextSize::from(start as u32), TextSize::from(end as u32))
}

/// `.properties` 的一行以续行符结尾：行尾有奇数个 `\`（`\\` 是转义的反斜杠本身）。
fn continues_line(line: &str) -> bool {
    (line.len() - line.trim_end_matches('\\').len()) % 2 == 1
}

/// `.properties`：`key=value`、`key: value`、`key value`，`#` / `!` 开头是注解，
/// 行尾的 `\` 表示续行。
pub fn parse_properties(text: &str, push: &mut impl FnMut(String, String, TextRange)) {
    let mut offset = 0;
    let mut lines = text.split_inclusive('\n').peekable();
    while let Some(raw) = lines.next() {
        let line_start = offset;
        offset += raw.len();
        let line = raw.trim_end_matches(['\n', '\r']);
        let indent = line.len() - line.trim_start().len();
        let content = &line[indent..];
        if content.is_empty() || content.starts_with('#') || content.starts_with('!') {
            continue;
        }
        // 键在第一个没有转义的 `=`、`:` 或空白处结束
        let bytes = content.as_bytes();
        let mut end = 0;
        while end < bytes.len() {
            match bytes[end] {
                b'\\' => end += 2,
                b'=' | b':' | b' ' | b'\t' => break,
                _ => end += 1,
            }
        }
        let end = end.min(bytes.len());
        let key = content[..end].replace('\\', "");
        let mut value = content[end..]
            .trim_start_matches([' ', '\t'])
            .trim_start_matches(['=', ':'])
            .trim_start()
            .to_owned();
        // 续行
        while continues_line(&value) {
            value.pop();
            match lines.next() {
                Some(next) => {
                    offset += next.len();
                    value.push_str(next.trim());
                }
                None => break,
            }
        }
        if key.is_empty() {
            continue;
        }
        let start = line_start + indent;
        push(key, value, range(start, start + end));
    }
}

/// YAML 的常见子集：按缩进嵌套的映射、`- ` 列表项（展开成 `key[0]`）、`---` 分隔的多个文档、
/// `|` / `>` 块标量。锚点、流式写法（`{a: 1}`）不展开。
pub fn parse_yaml(text: &str, push: &mut impl FnMut(String, String, TextRange)) {
    parse_yaml_impl(text, false, push)
}

/// YAML 里所有的键（含只有子键、没有值的外层键），以及各自的范围。
pub fn yaml_keys(text: &str) -> Vec<(String, TextRange)> {
    let mut out = Vec::new();
    parse_yaml_impl(text, true, &mut |key, _, range| out.push((key, range)));
    out
}

/// `parents`：外层键（值为空、下面是嵌套映射）也报告，值为空串。
fn parse_yaml_impl(text: &str, parents: bool, push: &mut impl FnMut(String, String, TextRange)) {
    // (缩进, 键)
    let mut stack: Vec<(usize, String)> = Vec::new();
    // 每个父键下已经出现的列表项个数
    let mut list_counts: Vec<(String, usize)> = Vec::new();
    let mut block_indent: Option<usize> = None;
    let mut offset = 0;
    for raw in text.split_inclusive('\n') {
        let line_start = offset;
        offset += raw.len();
        let line = raw.trim_end_matches(['\n', '\r']);
        let indent = line.len() - line.trim_start().len();
        let content = line[indent..].trim_end();
        if let Some(block) = block_indent {
            if content.is_empty() || indent > block {
                continue;
            }
            block_indent = None;
        }
        if content.is_empty() || content.starts_with('#') {
            continue;
        }
        if content == "---" || content == "..." {
            stack.clear();
            list_counts.clear();
            continue;
        }
        while stack.last().is_some_and(|(i, _)| *i >= indent) {
            stack.pop();
        }
        let parent = stack.last().map(|(_, k)| k.clone()).unwrap_or_default();

        let (mut key_start, mut entry) = (line_start + indent, content);
        let mut prefix = parent.clone();
        let mut item_indent = indent;
        if let Some(rest) =
            content
                .strip_prefix("- ")
                .or(if content == "-" { Some("") } else { None })
        {
            // 列表项：`parent[i]`
            let idx = match list_counts.iter_mut().find(|(k, _)| *k == parent) {
                Some((_, n)) => {
                    *n += 1;
                    *n - 1
                }
                None => {
                    list_counts.push((parent.clone(), 1));
                    0
                }
            };
            prefix = format!("{parent}[{idx}]");
            let skipped = content.len() - rest.trim_start().len();
            key_start += skipped;
            item_indent = indent + skipped;
            entry = rest.trim_start();
            match split_yaml_entry(entry) {
                Some(_) => {
                    // `- name: x`：后面同缩进的行属于这一项
                    stack.push((indent, prefix.clone()));
                }
                None => {
                    if !entry.is_empty() {
                        let value = yaml_scalar(entry);
                        push(prefix, value, range(key_start, key_start + entry.len()));
                    } else {
                        stack.push((indent, prefix));
                    }
                    continue;
                }
            }
        }
        let Some((key, value)) = split_yaml_entry(entry) else {
            continue;
        };
        let full = if prefix.is_empty() {
            key.to_owned()
        } else {
            format!("{prefix}.{key}")
        };
        let key_offset = entry.find(key).unwrap_or(0);
        let key_range = range(key_start + key_offset, key_start + key_offset + key.len());
        let value = yaml_value_text(value.trim());
        if value.is_empty() {
            if parents {
                push(full.clone(), String::new(), key_range);
            }
            stack.push((item_indent, full));
        } else if value.starts_with('|') || value.starts_with('>') {
            block_indent = Some(item_indent);
            push(full, String::new(), key_range);
        } else {
            push(full, yaml_scalar(value), key_range);
        }
    }
}

/// `key: value` 拆成键和值；键可以带引号。不是映射项时返回 `None`。
fn split_yaml_entry(entry: &str) -> Option<(&str, &str)> {
    let (key, value) = if let Some(rest) = entry.strip_prefix(['"', '\'']) {
        let quote = entry.as_bytes()[0] as char;
        let close = rest.find(quote)?;
        let after = rest[close + 1..].trim_start().strip_prefix(':')?;
        (&rest[..close], after)
    } else {
        // `: ` 或行尾的 `:` 才是分隔符（`http://x` 里的不是）
        let idx = entry
            .match_indices(':')
            .find(|(i, _)| entry[i + 1..].is_empty() || entry[i + 1..].starts_with([' ', '\t']))?
            .0;
        (entry[..idx].trim_end(), &entry[idx + 1..])
    };
    (!key.is_empty()).then_some((key, value))
}

/// 带引号的标量里收尾引号的位置：双引号里 `\` 转义下一个字符，单引号里 `''` 是一个引号。
fn yaml_closing_quote(value: &str) -> Option<usize> {
    let bytes = value.as_bytes();
    let quote = *bytes.first().filter(|b| matches!(b, b'"' | b'\''))?;
    let mut i = 1;
    while i < bytes.len() {
        match bytes[i] {
            b'\\' if quote == b'"' => i += 2,
            b'\'' if quote == b'\'' && bytes.get(i + 1) == Some(&b'\'') => i += 2,
            b if b == quote => return Some(i),
            _ => i += 1,
        }
    }
    None
}

/// 值去掉行尾注释后的原文（`value` 已去掉前导空白）。引号里的 `#` 不是注释。
fn yaml_value_text(value: &str) -> &str {
    if let Some(close) = yaml_closing_quote(value) {
        return &value[..=close];
    }
    let comment = value
        .match_indices('#')
        .find(|(i, _)| *i == 0 || value[..*i].ends_with([' ', '\t']))
        .map_or(value.len(), |(i, _)| i);
    value[..comment].trim_end()
}

fn yaml_scalar(value: &str) -> String {
    let value = yaml_value_text(value.trim());
    if let Some(inner) = value.strip_prefix('\'').filter(|_| value.len() > 1) {
        if let Some(inner) = inner.strip_suffix('\'') {
            return inner.replace("''", "'");
        }
    }
    if let Some(inner) = value.strip_prefix('"').filter(|_| value.len() > 1) {
        if let Some(inner) = inner.strip_suffix('"') {
            let mut out = String::with_capacity(inner.len());
            let mut chars = inner.chars();
            while let Some(c) = chars.next() {
                if c != '\\' {
                    out.push(c);
                    continue;
                }
                match chars.next() {
                    Some('n') => out.push('\n'),
                    Some('t') => out.push('\t'),
                    Some(c @ ('"' | '\\' | '/' | ' ')) => out.push(c),
                    Some(c) => {
                        out.push('\\');
                        out.push(c);
                    }
                    None => out.push('\\'),
                }
            }
            return out;
        }
    }
    value.to_owned()
}

/// 字符串字面量里的一个 `${key}` / `${key:default}` 占位符。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Placeholder {
    pub key: String,
    /// 键在文件里的范围
    pub key_range: TextRange,
    pub has_default: bool,
}

/// 字面量（含引号的原文）里的占位符。`${` 后面还没写完（没有 `}`）的也算，键到字面量末尾为止。
pub fn placeholders(literal: &SyntaxToken) -> Vec<Placeholder> {
    let text = literal.text();
    let base = usize::from(literal.text_range().start());
    let mut out = Vec::new();
    let mut search = 0;
    while let Some(found) = text[search..].find("${") {
        let key_start = search + found + 2;
        // `\${...}`：Spring 的转义，原样保留，不是占位符。源码里的反斜杠写作 `\\`
        if text[..search + found].ends_with("\\\\") {
            search = key_start;
            continue;
        }
        let rest = &text[key_start..];
        let key_len = rest.find([':', '}', '"', '$', '\n']).unwrap_or(rest.len());
        let has_default = rest[key_len..].starts_with(':');
        let key = rest[..key_len].trim();
        out.push(Placeholder {
            key: key.to_owned(),
            key_range: range(base + key_start, base + key_start + key_len),
            has_default,
        });
        search = key_start + key_len;
    }
    out
}

/// 字符串字面量所在的配置引用：`@Value("...")` 的值（返回其中的占位符），
/// 或者 `xxx.getProperty("key")` 的第一个实参（整个字面量就是键）。
pub enum PropertyUse {
    /// `@Value`：里面的 `${...}`
    Value(Vec<Placeholder>),
    /// `getProperty("key")`：键的范围（引号里面）
    Lookup(Placeholder),
}

pub fn property_use(
    literal: &SyntaxToken,
    receiver_is_environment: impl Fn(&ast::Expr) -> bool,
) -> Option<PropertyUse> {
    if literal.kind() != SyntaxKind::STRING_LITERAL {
        return None;
    }
    let expr = literal.parent()?;
    let parent = expr.parent()?;
    // `@Value("...")` 或 `@Value(value = "...")`
    let annotation = ast::AnnotationArg::cast(parent.clone())
        .filter(|arg| arg.name_ref().is_none_or(|n| n.text() == "value"))
        .and_then(|arg| arg.syntax().parent()?.parent())
        .and_then(ast::Annotation::cast);
    if let Some(annotation) = annotation {
        let name = annotation.name()?.segments().last()?.to_string();
        if name != "Value" {
            return None;
        }
        return Some(PropertyUse::Value(placeholders(literal)));
    }
    // `env.getProperty("key", ...)`
    if parent.kind() == SyntaxKind::ARG_LIST && parent.children().next().as_ref() == Some(&expr) {
        let call = ast::MethodCall::cast(parent.parent()?)?;
        let name = call.name_ref()?.text();
        if !matches!(
            name.as_str(),
            "getProperty" | "getRequiredProperty" | "containsProperty"
        ) {
            return None;
        }
        if !call.receiver().is_some_and(|r| receiver_is_environment(&r)) {
            return None;
        }
        let text = literal.text();
        let inner = text.strip_prefix('"')?;
        let len = inner.strip_suffix('"').map_or(inner.len(), str::len);
        let start = usize::from(literal.text_range().start()) + 1;
        return Some(PropertyUse::Lookup(Placeholder {
            key: inner[..len].to_owned(),
            key_range: range(start, start + len),
            has_default: true,
        }));
    }
    None
}

/// 接收者的类型是 Spring 的 `Environment` / `PropertyResolver` 一族。
pub fn is_environment(
    db: &dyn Db,
    sema: &hir::Semantics<'_>,
    file: base_db::SourceFile,
    expr: &ast::Expr,
) -> bool {
    let Some(hir::Ty::Class(class, _)) = sema.type_of_expr(file, expr) else {
        return false;
    };
    let is_env = |c: hir::ClassId| {
        hir::class_data(db, c).is_some_and(|d| {
            d.name.ends_with("Environment") || d.name.ends_with("PropertyResolver")
        })
    };
    is_env(class) || hir::all_supers(db, class).iter().copied().any(is_env)
}

/// 光标处引用的配置项：占位符（或 `getProperty` 的键）以及文件所在的模块。
pub fn property_at(
    db: &dyn Db,
    file: base_db::SourceFile,
    offset: TextSize,
) -> Option<(Placeholder, Option<ModuleId>)> {
    let root = base_db::parse(db, file).syntax_node();
    let token = root
        .token_at_offset(offset)
        .find(|t| t.kind() == SyntaxKind::STRING_LITERAL)?;
    let sema = hir::Semantics::new(db);
    let found = match property_use(&token, |r| is_environment(db, &sema, file, r))? {
        PropertyUse::Value(list) => list
            .into_iter()
            .find(|p| p.key_range.contains_inclusive(offset))?,
        PropertyUse::Lookup(p) => p.key_range.contains_inclusive(offset).then_some(p)?,
    };
    let module = match base_db::file_entry(db, file.file_id(db))?.kind {
        base_db::FileKind::Workspace { module, .. } => module,
        base_db::FileKind::Library => return None,
    };
    Some((found, module))
}

/// 和 `key` 匹配的配置项（宽松绑定）。
pub fn matching_properties(
    db: &dyn Db,
    module: Option<ModuleId>,
    key: &str,
) -> Vec<ConfigProperty> {
    let wanted = canonical(key);
    config_properties(db, module)
        .into_iter()
        .filter(|p| canonical(&p.key) == wanted)
        .collect()
}

// ---------------------------------------------------------------------------
// 配置文件里的光标位置
// ---------------------------------------------------------------------------

/// 配置文件里光标所在的位置。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfigCursor {
    /// 在键上。`parent` 是 YAML 里外层映射的完整键（properties 文件里为空）；
    /// `range` 是整个键（YAML 里是这一段）的范围，`typed` 是光标前已经输入的部分，
    /// `has_separator` 表示键后面已经有 `=` / `:`，`indent` 是键所在的列。
    Key {
        parent: String,
        range: TextRange,
        typed: String,
        has_separator: bool,
        indent: usize,
    },
    /// 在值上：`key` 是完整键，`range` 是值的范围。
    Value { key: String, range: TextRange },
}

/// 光标所在行的范围（不含换行符）。
fn line_bounds(text: &str, offset: usize) -> (usize, usize) {
    let start = text[..offset].rfind('\n').map_or(0, |i| i + 1);
    let end = text[offset..].find('\n').map_or(text.len(), |i| offset + i);
    let end = if text[start..end].ends_with('\r') {
        end - 1
    } else {
        end
    };
    (start, end)
}

/// 配置文件 `name` 里 `offset` 处的光标位置。
pub fn config_cursor(name: &str, text: &str, offset: TextSize) -> Option<ConfigCursor> {
    let offset = usize::from(offset).min(text.len());
    if !text.is_char_boundary(offset) {
        return None;
    }
    if name.ends_with(".properties") {
        properties_cursor(text, offset)
    } else {
        yaml_cursor(text, offset)
    }
}

fn properties_cursor(text: &str, offset: usize) -> Option<ConfigCursor> {
    let (line_start, line_end) = line_bounds(text, offset);
    // 续行里是值的一部分
    if line_start > 0 {
        let (prev_start, prev_end) = line_bounds(text, line_start - 1);
        let prev = &text[prev_start..prev_end];
        if continues_line(prev) && !prev.trim_start().starts_with(['#', '!']) {
            return None;
        }
    }
    let line = &text[line_start..line_end];
    let indent = line.len() - line.trim_start().len();
    let content = &line[indent..];
    if content.starts_with(['#', '!']) {
        return None;
    }
    let key_start = line_start + indent;
    if offset < key_start {
        return None;
    }
    let bytes = content.as_bytes();
    let mut end = 0;
    while end < bytes.len() {
        match bytes[end] {
            b'\\' => end += 2,
            b'=' | b':' | b' ' | b'\t' => break,
            _ => end += 1,
        }
    }
    let key_end = key_start + end.min(bytes.len());
    if offset <= key_end {
        return Some(ConfigCursor::Key {
            parent: String::new(),
            range: range(key_start, key_end),
            typed: text[key_start..offset].to_owned(),
            has_separator: !text[key_end..line_end].trim().is_empty(),
            indent,
        });
    }
    let rest = text[key_end..line_end].trim_start_matches([' ', '\t']);
    let rest = rest.strip_prefix(['=', ':']).unwrap_or(rest);
    let rest = rest.trim_start_matches([' ', '\t']);
    let value_start = (line_end - rest.len()).min(offset);
    let value_end = (line_start + line.trim_end().len()).max(offset);
    Some(ConfigCursor::Value {
        key: text[key_start..key_end].replace('\\', ""),
        range: range(value_start, value_end),
    })
}

/// YAML 映射项的 `:` 分隔符在 `entry` 里的位置。
fn yaml_separator(entry: &str) -> Option<usize> {
    if let Some(rest) = entry.strip_prefix(['"', '\'']) {
        let quote = entry.as_bytes()[0] as char;
        let close = rest.find(quote)? + 1;
        let after = &entry[close + 1..];
        let colon = after.find(':')?;
        return after[..colon]
            .trim()
            .is_empty()
            .then_some(close + 1 + colon);
    }
    entry
        .match_indices(':')
        .find(|(i, _)| entry[i + 1..].is_empty() || entry[i + 1..].starts_with([' ', '\t']))
        .map(|(i, _)| i)
}

/// 把 `line_start..line_end` 这一行换成 `replacement` 后解析，返回从 `target` 起（允许差一个引号）
/// 的那一项的完整键。
fn yaml_key_with_line(
    text: &str,
    line_start: usize,
    line_end: usize,
    replacement: &str,
    target: usize,
) -> Option<String> {
    let mut patched = String::with_capacity(text.len() + replacement.len());
    patched.push_str(&text[..line_start]);
    patched.push_str(replacement);
    patched.push_str(&text[line_end..]);
    let mut found = None;
    parse_yaml(&patched, &mut |key, _, range| {
        let start = usize::from(range.start());
        if found.is_none() && (start == target || start == target + 1) {
            found = Some(key);
        }
    });
    found
}

/// 解析时临时代替光标所在的键，用来求出它的外层键。
const SENTINEL: &str = "__java_analyzer_cursor__";

fn yaml_cursor(text: &str, offset: usize) -> Option<ConfigCursor> {
    let (line_start, line_end) = line_bounds(text, offset);
    let line = &text[line_start..line_end];
    let indent = line.len() - line.trim_start().len();
    let content = line[indent..].trim_end();
    if content.starts_with('#') || content == "---" || content == "..." {
        return None;
    }
    // 列表项的 `- ` 前缀
    let item_prefix = match content.strip_prefix('-') {
        Some(rest) if rest.is_empty() || rest.starts_with([' ', '\t']) => {
            content.len() - rest.trim_start().len()
        }
        _ => 0,
    };
    let entry_col = indent + item_prefix;
    let entry_start = line_start + entry_col;
    let entry = &content[item_prefix..];
    let dash = if item_prefix > 0 {
        format!("{}- ", " ".repeat(indent))
    } else {
        " ".repeat(indent)
    };
    let parent_at = |col: usize, prefix: &str| {
        let replacement = format!("{prefix}{SENTINEL}: x");
        let key = yaml_key_with_line(text, line_start, line_end, &replacement, line_start + col)?;
        Some(match key.strip_suffix(SENTINEL) {
            Some(parent) => parent.trim_end_matches('.').to_owned(),
            None => String::new(),
        })
    };

    if content.is_empty() {
        // 空行：光标所在的列决定嵌套层次
        if !text[line_start..offset].chars().all(|c| c == ' ') {
            return None;
        }
        let col = offset - line_start;
        return Some(ConfigCursor::Key {
            parent: parent_at(col, &" ".repeat(col))?,
            range: range(offset, offset),
            typed: String::new(),
            has_separator: false,
            indent: col,
        });
    }
    if offset < entry_start {
        return None;
    }
    let separator = yaml_separator(entry);
    if let Some(sep) = separator.filter(|sep| offset > entry_start + sep) {
        // 值
        let replacement = format!("{dash}{}: x", &entry[..sep]);
        let key = yaml_key_with_line(text, line_start, line_end, &replacement, entry_start)?;
        let after = &entry[sep + 1..];
        let lead = after.len() - after.trim_start().len();
        let value = yaml_value_text(after.trim_start());
        let value_start = entry_start + sep + 1 + lead;
        let value_end = value_start + value.len();
        return Some(ConfigCursor::Value {
            key,
            range: range(value_start.min(offset), value_end.max(offset)),
        });
    }
    if item_prefix > 0 && separator.is_none() {
        // `- 值`：列表元素
        let replacement = format!("{dash}x");
        let key = yaml_key_with_line(text, line_start, line_end, &replacement, entry_start)?;
        return Some(ConfigCursor::Value {
            key,
            range: range(entry_start, (entry_start + entry.len()).max(offset)),
        });
    }
    let key_end = entry_start + separator.unwrap_or(entry.len());
    Some(ConfigCursor::Key {
        parent: parent_at(entry_col, &dash)?,
        range: range(entry_start, key_end.max(offset)),
        typed: text[entry_start..offset].to_owned(),
        has_separator: separator.is_some(),
        indent: entry_col,
    })
}

/// 配置文件里覆盖 `offset` 的键：完整键和键（YAML 里是这一段）的范围。
pub fn config_key_at(name: &str, text: &str, offset: TextSize) -> Option<(String, TextRange)> {
    if name.ends_with(".properties") {
        let mut found = None;
        parse_properties(text, &mut |key, _, range| {
            if found.is_none() && range.contains_inclusive(offset) {
                found = Some((key, range));
            }
        });
        found
    } else {
        yaml_keys(text)
            .into_iter()
            .find(|(_, range)| range.contains_inclusive(offset))
    }
}

/// YAML 文件的缩进单位：最小的非零缩进，默认两个空格。
pub fn yaml_indent_unit(text: &str) -> usize {
    text.lines()
        .filter(|l| !l.trim().is_empty() && !l.trim_start().starts_with('#'))
        .map(|l| l.len() - l.trim_start_matches(' ').len())
        .filter(|&n| n > 0)
        .min()
        .unwrap_or(2)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn collect(text: &str, yaml: bool) -> Vec<(String, String, String)> {
        let mut out = Vec::new();
        let mut push = |k: String, v: String, r: TextRange| {
            let span = text[usize::from(r.start())..usize::from(r.end())].to_owned();
            out.push((k, v, span));
        };
        if yaml {
            parse_yaml(text, &mut push);
        } else {
            parse_properties(text, &mut push);
        }
        out
    }

    #[test]
    fn properties() {
        let got = collect(
            "# comment\nserver.port=8080\napp.name : demo\napp.list a,\\\n  b\n\n! bang\nurl=http://x:1\n",
            false,
        );
        let keys: Vec<(&str, &str)> = got
            .iter()
            .map(|(k, v, _)| (k.as_str(), v.as_str()))
            .collect();
        assert_eq!(
            keys,
            vec![
                ("server.port", "8080"),
                ("app.name", "demo"),
                ("app.list", "a,b"),
                ("url", "http://x:1"),
            ]
        );
        assert_eq!(got[0].2, "server.port");
    }

    #[test]
    fn properties_escaped_trailing_backslash() {
        // 行尾偶数个 `\` 是转义的反斜杠，不续行；奇数个才续行
        let got = collect(
            "path=C:\\\\temp\\\\\nafter=works\nodd=a\\\\\\\n  b\nlast=1\n",
            false,
        );
        let keys: Vec<&str> = got.iter().map(|(k, _, _)| k.as_str()).collect();
        assert_eq!(keys, vec!["path", "after", "odd", "last"]);
        assert_eq!(got[2].1, "a\\\\b");

        let p = "application.properties";
        assert_eq!(
            key_parent(&cursor(p, "path=C:\\\\temp\\\\\naft|er=works\n")),
            ("", "aft")
        );
        assert!(config_cursor(p, "a=1\\\nb=2", TextSize::from(5)).is_none());
    }

    #[test]
    fn yaml() {
        let text = "server:\n  port: 8080 # web\nspring:\n  datasource:\n    url: \"jdbc:h2:mem\"\n  profiles:\n    active: dev\napp:\n  servers:\n    - a.example.com\n    - b.example.com\n  users:\n    - name: tom\n      role: admin\n  banner: |\n    hello\n    world\n  after: 1\n---\nother: 2\n";
        let got = collect(text, true);
        let keys: Vec<(&str, &str)> = got
            .iter()
            .map(|(k, v, _)| (k.as_str(), v.as_str()))
            .collect();
        assert_eq!(
            keys,
            vec![
                ("server.port", "8080"),
                ("spring.datasource.url", "jdbc:h2:mem"),
                ("spring.profiles.active", "dev"),
                ("app.servers[0]", "a.example.com"),
                ("app.servers[1]", "b.example.com"),
                ("app.users[0].name", "tom"),
                ("app.users[0].role", "admin"),
                ("app.banner", ""),
                ("app.after", "1"),
                ("other", "2"),
            ]
        );
        assert_eq!(got[0].2, "port");
        assert_eq!(got[5].2, "name");
    }

    #[test]
    fn yaml_quoted_hash() {
        // 引号里的 `#` 属于字符串，收尾引号后面的才是注释
        let text = "probe:\n  message: \"hello # world\" # comment\n  single: 'it''s # x' # c\n  escaped: \"a \\\" # b\" # c\n  plain: a#b # c\n  list:\n    - \"x # y\" # z\n  empty: # nothing here\n    child: 1\n";
        let got = collect(text, true);
        let keys: Vec<(&str, &str)> = got
            .iter()
            .map(|(k, v, _)| (k.as_str(), v.as_str()))
            .collect();
        assert_eq!(
            keys,
            vec![
                ("probe.message", "hello # world"),
                ("probe.single", "it's # x"),
                ("probe.escaped", "a \" # b"),
                ("probe.plain", "a#b"),
                ("probe.list[0]", "x # y"),
                ("probe.empty.child", "1"),
            ]
        );

        let y = "application.yml";
        let c = cursor(y, "probe:\n  message: \"hello # wo|rld\" # comment\n");
        let ConfigCursor::Value { range, .. } = c else {
            panic!("不是值: {c:?}");
        };
        assert_eq!(usize::from(range.start()), 18);
        assert_eq!(usize::from(range.end()), 33);
    }

    fn cursor(name: &str, text: &str) -> ConfigCursor {
        let offset = text.find('|').unwrap();
        let text = text.replace('|', "");
        config_cursor(name, &text, TextSize::from(offset as u32)).unwrap()
    }

    fn key_parent(c: &ConfigCursor) -> (&str, &str) {
        match c {
            ConfigCursor::Key { parent, typed, .. } => (parent, typed),
            other => panic!("不是键: {other:?}"),
        }
    }

    fn value_key(c: &ConfigCursor) -> &str {
        match c {
            ConfigCursor::Value { key, .. } => key,
            other => panic!("不是值: {other:?}"),
        }
    }

    #[test]
    fn properties_cursor() {
        let p = "application.properties";
        assert_eq!(
            key_parent(&cursor(p, "a=1\nserver.po|\n")),
            ("", "server.po")
        );
        assert_eq!(value_key(&cursor(p, "server.port=80|\n")), "server.port");
        assert_eq!(value_key(&cursor(p, "debug=|")), "debug");
        assert!(config_cursor(p, "# x", TextSize::from(2)).is_none());
    }

    #[test]
    fn yaml_cursor() {
        let y = "application.yml";
        assert_eq!(key_parent(&cursor(y, "serv|")), ("", "serv"));
        assert_eq!(
            key_parent(&cursor(y, "server:\n  port: 1\n  ser|\n")),
            ("server", "ser")
        );
        assert_eq!(
            key_parent(&cursor(y, "spring:\n  datasource:\n    |\n")),
            ("spring.datasource", "")
        );
        assert_eq!(key_parent(&cursor(y, "spring:\n  x: 1\n|\n")), ("", ""));
        assert_eq!(
            value_key(&cursor(y, "server:\n  shutdown: gr|\n")),
            "server.shutdown"
        );
        assert_eq!(
            value_key(&cursor(
                y,
                "spring:\n  profiles:\n    include:\n      - d|\n"
            )),
            "spring.profiles.include[0]"
        );
        assert_eq!(
            key_parent(&cursor(y, "app:\n  users:\n    - name: a\n      ro|\n")),
            ("app.users[0]", "ro")
        );
    }

    #[test]
    fn keys_at_offset() {
        let text = "spring:\n  datasource:\n    url: x\n";
        let (key, _) = config_key_at("a.yml", text, TextSize::from(12)).unwrap();
        assert_eq!(key, "spring.datasource");
        let (key, _) = config_key_at("a.yml", text, TextSize::from(27)).unwrap();
        assert_eq!(key, "spring.datasource.url");
        assert_eq!(yaml_indent_unit(text), 2);
    }

    #[test]
    fn relaxed_binding() {
        assert_eq!(canonical("app.max-size"), canonical("app.maxSize"));
        assert_eq!(
            canonical("APP_MAXSIZE"),
            canonical("app.max-size").replace('.', "")
        );
    }
}
