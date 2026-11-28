//! Javadoc 注释 → Markdown。
//!
//! 处理常见的行内标签（`{@code}`、`{@link}`、`{@literal}`、`{@value}`）、
//! 块标签（`@param`、`@return`、`@throws`、`@see`、`@since`、`@deprecated`）
//! 和一小部分 HTML（`<p>`、`<pre>`、`<code>`、`<b>`、`<i>`、`<li>` …）。

/// 去掉 `/** ... */` 和每行开头的 ` * `，返回纯内容。
fn strip_comment_markers(raw: &str) -> String {
    let body = raw.trim();
    let body = body.strip_prefix("/**").unwrap_or(body);
    let body = body.strip_suffix("*/").unwrap_or(body);
    let mut out = String::new();
    for line in body.lines() {
        let line = line.trim_start();
        let line = match line.strip_prefix('*') {
            Some(rest) => rest.strip_prefix(' ').unwrap_or(rest),
            None => line,
        };
        out.push_str(line.trim_end());
        out.push('\n');
    }
    out.trim().to_owned()
}

/// `Foo#bar(int)` → `Foo.bar(int)`；`#bar` → `bar`；带标签时取标签。
fn render_link_target(content: &str) -> String {
    let content = content.trim();
    // `{@link Target label}`：括号里的空格不算分隔
    let mut depth = 0i32;
    let mut split = None;
    for (i, c) in content.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            c if c.is_whitespace() && depth == 0 => {
                split = Some(i);
                break;
            }
            _ => {}
        }
    }
    let (target, label) = match split {
        Some(i) => (&content[..i], content[i..].trim()),
        None => (content, ""),
    };
    if !label.is_empty() {
        return label.to_owned();
    }
    target.trim_start_matches('#').replace('#', ".")
}

/// 把 `{@tag ...}` 形式的行内标签换成 Markdown。
fn render_inline_tags(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("{@") {
        out.push_str(&rest[..start]);
        let after = &rest[start + 2..];
        // 找到配对的右花括号（`{@code}` 里可以嵌套花括号）
        let mut depth = 1i32;
        let mut end = None;
        for (i, c) in after.char_indices() {
            match c {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(i);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(end) = end else {
            out.push_str(&rest[start..]);
            return out;
        };
        let inner = &after[..end];
        let (tag, content) = match inner.find(char::is_whitespace) {
            Some(i) => (&inner[..i], inner[i..].trim()),
            None => (inner, ""),
        };
        match tag {
            "code" | "literal" => {
                out.push('`');
                out.push_str(content);
                out.push('`');
            }
            "link" | "linkplain" | "value" => {
                out.push('`');
                out.push_str(&render_link_target(content));
                out.push('`');
            }
            "inheritDoc" => {}
            _ => out.push_str(content),
        }
        rest = &after[end + 1..];
    }
    out.push_str(rest);
    out
}

fn decode_html_entities(text: &str) -> String {
    text.replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"")
        .replace("&#39;", "'")
        .replace("&nbsp;", " ")
        .replace("&amp;", "&")
}

/// 把常见的 HTML 标签换成 Markdown，其余标签直接去掉。
fn render_html(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    let mut in_pre = false;
    while let Some(start) = rest.find('<') {
        let Some(len) = rest[start..].find('>') else {
            break;
        };
        let tag = &rest[start + 1..start + len];
        let name = tag
            .trim_start_matches('/')
            .split(|c: char| c.is_whitespace() || c == '/')
            .next()
            .unwrap_or("")
            .to_ascii_lowercase();
        let closing = tag.starts_with('/');
        // 不像标签的 `<`（例如 `a < b`、泛型）原样保留
        let looks_like_tag = !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric());
        if !looks_like_tag {
            out.push_str(&rest[..=start]);
            rest = &rest[start + 1..];
            continue;
        }
        out.push_str(&rest[..start]);
        let after_tag = &rest[start + len + 1..];
        match (name.as_str(), closing) {
            ("p", false) | ("br", _) => out.push_str("\n\n"),
            ("pre", false) => {
                in_pre = true;
                out.push_str("\n```java");
                if !after_tag.starts_with('\n') {
                    out.push('\n');
                }
            }
            ("pre", true) => {
                in_pre = false;
                if !out.ends_with('\n') {
                    out.push('\n');
                }
                out.push_str("```\n");
            }
            ("code" | "tt", _) if !in_pre => out.push('`'),
            ("b" | "strong", _) => out.push_str("**"),
            ("i" | "em", _) => out.push('*'),
            ("li", false) => out.push_str("\n- "),
            ("ul" | "ol", _) => out.push('\n'),
            ("h1" | "h2" | "h3" | "h4", false) => out.push_str("\n\n#### "),
            ("h1" | "h2" | "h3" | "h4", true) => out.push_str("\n\n"),
            _ => {}
        }
        rest = after_tag;
    }
    out.push_str(rest);
    decode_html_entities(&out)
}

/// 把一段 Javadoc 注释（含 `/** */`）转成 Markdown。
pub fn javadoc_to_markdown(raw: &str) -> String {
    let content = strip_comment_markers(raw);

    // 正文与块标签分开：块标签从行首的 `@` 开始
    let mut description = String::new();
    let mut tags: Vec<(String, String)> = Vec::new();
    for line in content.lines() {
        let trimmed = line.trim_start();
        let is_block_tag = trimmed.starts_with('@')
            && trimmed[1..]
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic());
        if is_block_tag {
            let (tag, rest) = match trimmed.find(char::is_whitespace) {
                Some(i) => (&trimmed[1..i], trimmed[i..].trim()),
                None => (&trimmed[1..], ""),
            };
            tags.push((tag.to_owned(), rest.to_owned()));
        } else if let Some((_, body)) = tags.last_mut() {
            body.push(' ');
            body.push_str(trimmed);
        } else {
            description.push_str(line);
            description.push('\n');
        }
    }

    let render = |text: &str| render_html(&render_inline_tags(text)).trim().to_owned();
    let mut out = render(&description);

    let section = |title: &str, tag_names: &[&str], named: bool, out: &mut String| {
        let items: Vec<&(String, String)> = tags
            .iter()
            .filter(|(tag, _)| tag_names.contains(&tag.as_str()))
            .collect();
        if items.is_empty() {
            return;
        }
        out.push_str("\n\n**");
        out.push_str(title);
        out.push_str("**\n");
        for (_, body) in items {
            if named {
                // 先取参数名 / 异常类型，避免 `<T>` 被当作 HTML 标签去掉。
                let body = body.trim();
                let (name, desc) = match body.find(char::is_whitespace) {
                    Some(i) => (&body[..i], &body[i..]),
                    None => (body, ""),
                };
                let desc = render(desc);
                if desc.is_empty() {
                    out.push_str(&format!("\n- `{name}`"));
                } else {
                    out.push_str(&format!("\n- `{name}` — {desc}"));
                }
            } else {
                out.push_str(&format!("\n- {}", render(body)));
            }
        }
    };
    section(
        base_db::trs!("参数", "Parameters"),
        &["param"],
        true,
        &mut out,
    );
    section(
        base_db::trs!("返回", "Returns"),
        &["return", "returns"],
        false,
        &mut out,
    );
    section(
        base_db::trs!("抛出", "Throws"),
        &["throws", "exception"],
        true,
        &mut out,
    );
    section(base_db::trs!("参见", "See also"), &["see"], false, &mut out);
    section(base_db::trs!("始于", "Since"), &["since"], false, &mut out);
    section(
        base_db::trs!("已弃用", "Deprecated"),
        &["deprecated"],
        false,
        &mut out,
    );
    out.trim().to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn converts_common_javadoc() {
        let doc = r#"/**
     * Returns the {@code n}-th element, see {@link List#get(int)}.
     * <p>
     * Example:
     * <pre>
     * list.get(0);
     * </pre>
     *
     * @param index the index, must be &gt;= 0
     * @return the element
     * @throws IndexOutOfBoundsException if out of range
     */"#;
        let md = javadoc_to_markdown(doc);
        assert!(
            md.starts_with("Returns the `n`-th element, see `List.get(int)`."),
            "{md}"
        );
        assert!(md.contains("```java\nlist.get(0);\n```"), "{md}");
        assert!(md.contains("- `index` — the index, must be >= 0"), "{md}");
        assert!(md.contains("**返回**"), "{md}");
        assert!(
            md.contains("- `IndexOutOfBoundsException` — if out of range"),
            "{md}"
        );
    }

    #[test]
    fn keeps_non_tag_angle_brackets() {
        let md = javadoc_to_markdown("/** a < b and List<String> */");
        assert!(md.contains("a < b"), "{md}");
    }

    #[test]
    fn link_with_label() {
        assert_eq!(render_link_target("Foo#bar(int, int) the bar"), "the bar");
        assert_eq!(render_link_target("#baz"), "baz");
    }
}
