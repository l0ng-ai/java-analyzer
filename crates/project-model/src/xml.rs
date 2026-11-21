//! 一个只为读 POM / settings.xml / Eclipse `.classpath` 而写的极简 XML 解析器。
//!
//! 支持：元素、文本、属性、自闭合标签、注释、CDATA、处理指令、DOCTYPE、
//! 五个预定义实体和数字字符引用。不支持命名空间处理和 DTD 实体——POM 用不到。

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct XmlNode {
    /// 去掉命名空间前缀的元素名
    pub name: String,
    /// 直接文本内容（已去除首尾空白）
    pub text: String,
    /// 属性（名字去掉命名空间前缀，值已解码实体）
    pub attrs: Vec<(String, String)>,
    pub children: Vec<XmlNode>,
}

impl XmlNode {
    pub fn child(&self, name: &str) -> Option<&XmlNode> {
        self.children.iter().find(|c| c.name == name)
    }

    pub fn children_named<'a>(&'a self, name: &'a str) -> impl Iterator<Item = &'a XmlNode> {
        self.children.iter().filter(move |c| c.name == name)
    }

    /// 子元素的文本；不存在或为空时返回 `None`。
    pub fn child_text(&self, name: &str) -> Option<&str> {
        self.child(name)
            .map(|c| c.text.as_str())
            .filter(|t| !t.is_empty())
    }

    pub fn attr(&self, name: &str) -> Option<&str> {
        self.attrs
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v.as_str())
    }

    /// 沿路径逐层取子元素。
    pub fn path(&self, path: &[&str]) -> Option<&XmlNode> {
        let mut node = self;
        for name in path {
            node = node.child(name)?;
        }
        Some(node)
    }
}

pub fn parse(input: &str) -> Option<XmlNode> {
    // Windows 上的编辑器常在 UTF-8 文件开头写 BOM（U+FEFF）；它不算空白，`trim_start` 去不掉
    let input = input.strip_prefix('\u{feff}').unwrap_or(input);
    let mut parser = Parser { s: input, pos: 0 };
    parser.skip_misc();
    let root = parser.element()?;
    Some(root)
}

struct Parser<'a> {
    s: &'a str,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn rest(&self) -> &'a str {
        &self.s[self.pos..]
    }

    fn skip_until(&mut self, end: &str) -> bool {
        match self.rest().find(end) {
            Some(i) => {
                self.pos += i + end.len();
                true
            }
            None => {
                self.pos = self.s.len();
                false
            }
        }
    }

    /// 跳过空白、注释、处理指令、DOCTYPE。
    fn skip_misc(&mut self) {
        loop {
            let rest = self.rest();
            let trimmed = rest.trim_start();
            self.pos += rest.len() - trimmed.len();
            if trimmed.starts_with("<!--") {
                self.skip_until("-->");
            } else if trimmed.starts_with("<?") {
                self.skip_until("?>");
            } else if trimmed.starts_with("<!DOCTYPE") {
                self.skip_until(">");
            } else {
                break;
            }
        }
    }

    fn element(&mut self) -> Option<XmlNode> {
        if !self.rest().starts_with('<') {
            return None;
        }
        self.pos += 1;
        let name_end = self
            .rest()
            .find(|c: char| c.is_whitespace() || c == '>' || c == '/')?;
        let raw_name = &self.rest()[..name_end];
        let name = raw_name.rsplit(':').next().unwrap_or(raw_name).to_owned();
        self.pos += name_end;

        // 属性：`名字 = "值"`，一直到标签结束（引号里的 `>` 不算）
        let mut self_closing = false;
        let mut attrs = Vec::new();
        let mut pending_name: Option<String> = None;
        loop {
            let c = self.rest().chars().next()?;
            match c {
                '"' | '\'' => {
                    self.pos += 1;
                    let end = self.rest().find(c)?;
                    if let Some(attr) = pending_name.take() {
                        let mut value = String::new();
                        decode_entities(&self.rest()[..end], &mut value);
                        attrs.push((attr, value));
                    }
                    self.pos += end + 1;
                }
                c if c.is_alphabetic() || c == '_' => {
                    let end = self
                        .rest()
                        .find(|c: char| c.is_whitespace() || matches!(c, '=' | '>' | '/'))?;
                    let raw = &self.rest()[..end];
                    pending_name = Some(raw.rsplit(':').next().unwrap_or(raw).to_owned());
                    self.pos += end;
                }
                '/' if self.rest().starts_with("/>") => {
                    self.pos += 2;
                    self_closing = true;
                    break;
                }
                '>' => {
                    self.pos += 1;
                    break;
                }
                _ => self.pos += c.len_utf8(),
            }
        }

        let mut node = XmlNode {
            name,
            attrs,
            ..XmlNode::default()
        };
        if self_closing {
            return Some(node);
        }

        let mut text = String::new();
        loop {
            let rest = self.rest();
            if rest.is_empty() {
                break;
            }
            if let Some(stripped) = rest.strip_prefix("<![CDATA[") {
                let end = stripped.find("]]>")?;
                text.push_str(&stripped[..end]);
                self.pos += "<![CDATA[".len() + end + 3;
            } else if rest.starts_with("<!--") {
                self.skip_until("-->");
            } else if rest.starts_with("<?") {
                self.skip_until("?>");
            } else if rest.starts_with("</") {
                self.skip_until(">");
                break;
            } else if rest.starts_with('<') {
                node.children.push(self.element()?);
            } else {
                let end = rest.find('<').unwrap_or(rest.len());
                decode_entities(&rest[..end], &mut text);
                self.pos += end;
            }
        }
        node.text = text.trim().to_owned();
        Some(node)
    }
}

fn decode_entities(raw: &str, out: &mut String) {
    let mut rest = raw;
    while let Some(amp) = rest.find('&') {
        out.push_str(&rest[..amp]);
        rest = &rest[amp..];
        let Some(semi) = rest.find(';') else { break };
        let entity = &rest[1..semi];
        let decoded = match entity {
            "lt" => Some('<'),
            "gt" => Some('>'),
            "amp" => Some('&'),
            "quot" => Some('"'),
            "apos" => Some('\''),
            _ => entity
                .strip_prefix("#x")
                .and_then(|hex| u32::from_str_radix(hex, 16).ok())
                .or_else(|| entity.strip_prefix('#').and_then(|dec| dec.parse().ok()))
                .and_then(char::from_u32),
        };
        match decoded {
            Some(c) => out.push(c),
            None => out.push_str(&rest[..=semi]),
        }
        rest = &rest[semi + 1..];
    }
    out.push_str(rest);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_pom_like_document() {
        let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<!-- comment -->
<project xmlns="http://maven.apache.org/POM/4.0.0" xsi:schemaLocation="a > b">
  <groupId>com.example</groupId>
  <artifactId>demo</artifactId>
  <properties>
    <java.version>17</java.version>
    <note><![CDATA[a < b]]> &amp; c &#65;</note>
  </properties>
  <dependencies>
    <dependency><groupId>g</groupId><artifactId>a</artifactId></dependency>
    <dependency><groupId>g2</groupId><artifactId>a2</artifactId><optional/></dependency>
  </dependencies>
</project>"#;
        let root = parse(xml).unwrap();
        assert_eq!(root.name, "project");
        assert_eq!(root.attr("schemaLocation"), Some("a > b"));
        assert_eq!(
            root.attr("xmlns"),
            Some("http://maven.apache.org/POM/4.0.0")
        );
        assert_eq!(root.child_text("groupId"), Some("com.example"));
        assert_eq!(
            root.path(&["properties", "java.version"]).unwrap().text,
            "17"
        );
        assert_eq!(
            root.path(&["properties", "note"]).unwrap().text,
            "a < b & c A"
        );
        let deps: Vec<_> = root
            .child("dependencies")
            .unwrap()
            .children_named("dependency")
            .collect();
        assert_eq!(deps.len(), 2);
        assert!(deps[1].child("optional").is_some());
    }

    #[test]
    fn leading_byte_order_mark_is_skipped() {
        let root = parse(
            "\u{feff}<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<project><artifactId>demo</artifactId></project>",
        )
        .unwrap();
        assert_eq!(root.name, "project");
        assert_eq!(root.child_text("artifactId"), Some("demo"));
        assert_eq!(parse("\u{feff}<project/>").unwrap().name, "project");
    }

    #[test]
    fn attributes() {
        let root = parse(
            r#"<classpath><classpathentry kind="src" path="src"/><e a='1 &amp; 2' b = "x"></e></classpath>"#,
        )
        .unwrap();
        assert_eq!(root.children[0].attr("kind"), Some("src"));
        assert_eq!(root.children[0].attr("path"), Some("src"));
        assert_eq!(root.children[1].attr("a"), Some("1 & 2"));
        assert_eq!(root.children[1].attr("b"), Some("x"));
    }

    #[test]
    fn malformed_input_does_not_panic() {
        for xml in [
            "",
            "<",
            "<a",
            "<a><b></a>",
            "<a attr='x",
            "text only",
            "<a>&bogus</a>",
        ] {
            let _ = parse(xml);
        }
    }
}
