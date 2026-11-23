//! 手写 lexer：把源码切成带长度的 token 序列（包含空白和注释）。
//!
//! 约定：
//! - `>` 永远单独成 token（`>=` 除外），`>>`、`>>>`、`>>=`、`>>>=` 由 parser 根据相邻关系拼接，
//!   这样泛型的闭合尖括号不需要特殊处理。
//! - 上下文关键字（`var`、`record`、`sealed` …）一律产出 `IDENT`。
//! - token 的 `len` 恒为**原始源码**里的字节数：JLS 3.3 的 `\uXXXX` 翻译只改变
//!   词法判断所用的逻辑字符序列，语法树读原文切片，保持无损。

use crate::SyntaxKind::{self, *};
use std::borrow::Cow;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: SyntaxKind,
    pub len: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexError {
    /// 出错 token 的起始字节偏移
    pub offset: u32,
    pub len: u32,
    pub message: &'static str,
}

pub fn tokenize(text: &str) -> (Vec<Token>, Vec<LexError>) {
    let mut lexer = Lexer {
        src: Source::new(text),
        pos: 0,
        raw_pos: 0,
        errors: Vec::new(),
    };
    let mut tokens = Vec::with_capacity(text.len() / 4);
    while lexer.pos < lexer.src.logical_len() {
        let raw_start = lexer.raw_pos;
        let kind = lexer.next_kind();
        debug_assert!(lexer.raw_pos > raw_start);
        tokens.push(Token {
            kind,
            len: (lexer.raw_pos - raw_start) as u32,
        });
    }
    (tokens, lexer.errors)
}

/// JLS 3.3 的 Unicode 转义翻译：源码里合格的 `\uXXXX`（前面紧挨着偶数个 `\`）
/// 在分词之前就替换成它表示的字符——代码、注释、字符串/字符字面量里都生效。
///
/// 记录每个逻辑字符在原文里的字节长度，token 才能映射回原文的无损切片。
struct Translated {
    /// 翻译后的逻辑字符
    chars: Vec<char>,
    /// 逻辑字符之前的原始字节偏移（前缀和，比 `chars` 多一项）
    offsets: Vec<u32>,
}

impl Translated {
    /// 原文里没有 `\u` 时返回 `None`：绝大多数文件走零开销的原文直读路径。
    fn new(text: &str) -> Option<Translated> {
        if !text.contains("\\u") {
            return None;
        }
        let mut chars = Vec::with_capacity(text.len() / 2);
        let mut raw = Vec::with_capacity(text.len() / 2);
        translate_into(text, &mut chars, &mut raw);
        let mut offsets = Vec::with_capacity(chars.len() + 1);
        offsets.push(0u32);
        for len in &raw {
            offsets.push(offsets.last().unwrap() + len);
        }
        Some(Translated { chars, offsets })
    }
}

/// 对一小段原文单独做同样的 JLS 3.3 翻译。
///
/// 只用于不含裸 `\` 的 token 文本（标识符里的转义已随翻译消耗掉，token 范围
/// 内转义前的反斜杠数只会是 0），单独翻译与全文翻译的结果一致。
pub(crate) fn translate_span(text: &str) -> String {
    let mut chars = Vec::new();
    let mut raw = Vec::new();
    translate_into(text, &mut chars, &mut raw);
    chars.into_iter().collect()
}

fn translate_into(text: &str, chars: &mut Vec<char>, raw: &mut Vec<u32>) {
    let bytes = text.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b'\\' {
            let run = i;
            while i < bytes.len() && bytes[i] == b'\\' {
                i += 1;
            }
            let n = i - run;
            // 只有串长为奇数（最后一个 `\` 前面有偶数个 `\`）且后面紧跟
            // 一个或多个 `u`（`\uu0041` 也合法）+ 4 个十六进制位时，最后一个 `\` 才开启一个合格的转义
            let hex_start = i + bytes[i..].iter().take_while(|&&b| b == b'u').count();
            let eligible = n % 2 == 1
                && hex_start > i
                && bytes
                    .get(hex_start..hex_start + 4)
                    .is_some_and(|hex| hex.iter().all(u8::is_ascii_hexdigit));
            if eligible {
                let hex = std::str::from_utf8(&bytes[hex_start..hex_start + 4]).unwrap();
                let code = u32::from_str_radix(hex, 16).unwrap();
                if let Some(ch) = char::from_u32(code) {
                    for _ in 0..n - 1 {
                        chars.push('\\');
                        raw.push(1);
                    }
                    chars.push(ch);
                    // 转义占的原始字节：`\`、所有的 `u` 和 4 个十六进制位
                    raw.push((hex_start + 4 - i + 1) as u32);
                    i = hex_start + 4;
                    continue;
                }
                // 代理区的码点单独成不了 `char`：保留原文。字符和字符串字面量里
                // （`'\uD800'`、`"\uD83D\uDE00"`）照旧按转义序列跳过，在代码位置则报错误字符。
            }
            for _ in 0..n {
                chars.push('\\');
                raw.push(1);
            }
        } else {
            let ch = text[i..].chars().next().unwrap();
            chars.push(ch);
            raw.push(ch.len_utf8() as u32);
            i += ch.len_utf8();
        }
    }
}

/// 词法判断所用的字符序列：绝大多数文件直接读原文，含 `\u` 的文件读翻译视图。
enum Source<'a> {
    Raw(&'a str),
    Translated(Translated),
}

impl<'a> Source<'a> {
    fn new(text: &'a str) -> Source<'a> {
        match Translated::new(text) {
            Some(t) => Source::Translated(t),
            None => Source::Raw(text),
        }
    }

    fn logical_len(&self) -> usize {
        match self {
            Source::Raw(text) => text.len(),
            Source::Translated(t) => t.chars.len(),
        }
    }

    fn peek(&self, pos: usize) -> Option<char> {
        match self {
            Source::Raw(text) => text[pos..].chars().next(),
            Source::Translated(t) => t.chars.get(pos).copied(),
        }
    }

    fn peek_nth(&self, pos: usize, n: usize) -> Option<char> {
        match self {
            Source::Raw(text) => text[pos..].chars().nth(n),
            Source::Translated(t) => t.chars.get(pos + n).copied(),
        }
    }

    /// 逻辑位置换算成原始字节偏移。
    fn raw_offset(&self, pos: usize) -> usize {
        match self {
            Source::Raw(_) => pos,
            Source::Translated(t) => t.offsets[pos] as usize,
        }
    }

    /// token 文本：关键字判断用翻译后的拼写。
    fn token_text(&self, start: usize, end: usize) -> Cow<'a, str> {
        match self {
            Source::Raw(text) => Cow::Borrowed(&text[start..end]),
            Source::Translated(t) => Cow::Owned(t.chars[start..end].iter().collect()),
        }
    }
}

struct Lexer<'a> {
    src: Source<'a>,
    /// 逻辑位置（Raw 模式即字节下标）
    pos: usize,
    /// 原始源码里的字节位置
    raw_pos: usize,
    errors: Vec<LexError>,
}

fn is_java_whitespace(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r' | '\x0C')
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c == '$' || c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c == '$' || c.is_alphanumeric()
}

impl Lexer<'_> {
    fn peek(&self) -> Option<char> {
        self.src.peek(self.pos)
    }

    fn peek_nth(&self, n: usize) -> Option<char> {
        self.src.peek_nth(self.pos, n)
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.src.peek(self.pos)?;
        match &self.src {
            Source::Raw(_) => {
                self.pos += c.len_utf8();
                self.raw_pos += c.len_utf8();
            }
            Source::Translated(t) => {
                self.raw_pos += t.offsets[self.pos + 1] as usize - t.offsets[self.pos] as usize;
                self.pos += 1;
            }
        }
        Some(c)
    }

    fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn eat_while(&mut self, pred: impl Fn(char) -> bool) {
        while let Some(c) = self.peek() {
            if !pred(c) {
                break;
            }
            self.bump();
        }
    }

    /// 跳过直到 `a` 后紧跟 `b`（含）；到结尾返回 false，位置停在末尾。
    fn skip_until_pair(&mut self, a: char, b: char) -> bool {
        loop {
            match self.peek() {
                None => return false,
                Some(c) if c == a => {
                    self.bump();
                    if self.eat(b) {
                        return true;
                    }
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
    }

    fn error(&mut self, start: usize, message: &'static str) {
        self.errors.push(LexError {
            offset: self.src.raw_offset(start) as u32,
            len: (self.raw_pos - self.src.raw_offset(start)) as u32,
            message,
        });
    }

    fn next_kind(&mut self) -> SyntaxKind {
        let start = self.pos;
        let c = match self.bump() {
            Some(c) => c,
            None => return EOF,
        };
        match c {
            c if is_java_whitespace(c) => {
                self.eat_while(is_java_whitespace);
                WHITESPACE
            }
            '/' => match self.peek() {
                Some('/') => {
                    self.eat_while(|c| c != '\n' && c != '\r');
                    LINE_COMMENT
                }
                Some('*') => {
                    self.bump();
                    let is_doc = self.peek() == Some('*') && self.peek_nth(1) != Some('/');
                    if !self.skip_until_pair('*', '/') {
                        self.error(start, "注释未闭合");
                    }
                    if is_doc {
                        DOC_COMMENT
                    } else {
                        BLOCK_COMMENT
                    }
                }
                Some('=') => {
                    self.bump();
                    SLASH_EQ
                }
                _ => SLASH,
            },
            '"' => {
                if self.peek() == Some('"') && self.peek_nth(1) == Some('"') {
                    self.bump();
                    self.bump();
                    self.text_block(start)
                } else {
                    self.quoted(start, '"', "字符串字面量未闭合");
                    STRING_LITERAL
                }
            }
            '\'' => {
                self.quoted(start, '\'', "字符字面量未闭合");
                CHAR_LITERAL
            }
            '0'..='9' => self.number(c),
            '.' => {
                if matches!(self.peek(), Some('0'..='9')) {
                    self.decimal_fraction_and_suffix()
                } else if self.peek() == Some('.') && self.peek_nth(1) == Some('.') {
                    self.bump();
                    self.bump();
                    ELLIPSIS
                } else {
                    DOT
                }
            }
            c if is_ident_start(c) => {
                self.eat_while(is_ident_continue);
                let spelling = self.src.token_text(start, self.pos);
                SyntaxKind::from_keyword(&spelling).unwrap_or(IDENT)
            }
            '(' => L_PAREN,
            ')' => R_PAREN,
            '{' => L_CURLY,
            '}' => R_CURLY,
            '[' => L_BRACK,
            ']' => R_BRACK,
            ';' => SEMICOLON,
            ',' => COMMA,
            '@' => AT,
            '?' => QUESTION,
            '~' => TILDE,
            ':' => {
                if self.eat(':') {
                    COLON_COLON
                } else {
                    COLON
                }
            }
            '=' => {
                if self.eat('=') {
                    EQ_EQ
                } else {
                    EQ
                }
            }
            '!' => {
                if self.eat('=') {
                    NEQ
                } else {
                    BANG
                }
            }
            '<' => {
                if self.eat('=') {
                    LT_EQ
                } else if self.eat('<') {
                    if self.eat('=') {
                        SHL_EQ
                    } else {
                        SHL
                    }
                } else {
                    LT
                }
            }
            '>' => {
                if self.eat('=') {
                    GT_EQ
                } else {
                    GT
                }
            }
            '+' => {
                if self.eat('+') {
                    PLUS_PLUS
                } else if self.eat('=') {
                    PLUS_EQ
                } else {
                    PLUS
                }
            }
            '-' => {
                if self.eat('-') {
                    MINUS_MINUS
                } else if self.eat('=') {
                    MINUS_EQ
                } else if self.eat('>') {
                    ARROW
                } else {
                    MINUS
                }
            }
            '*' => {
                if self.eat('=') {
                    STAR_EQ
                } else {
                    STAR
                }
            }
            '%' => {
                if self.eat('=') {
                    PERCENT_EQ
                } else {
                    PERCENT
                }
            }
            '^' => {
                if self.eat('=') {
                    CARET_EQ
                } else {
                    CARET
                }
            }
            '&' => {
                if self.eat('&') {
                    AMP_AMP
                } else if self.eat('=') {
                    AMP_EQ
                } else {
                    AMP
                }
            }
            '|' => {
                if self.eat('|') {
                    PIPE_PIPE
                } else if self.eat('=') {
                    PIPE_EQ
                } else {
                    PIPE
                }
            }
            _ => {
                self.error(start, "无法识别的字符");
                ERROR_TOKEN
            }
        }
    }

    /// 普通字符串 / 字符字面量：遇到行尾仍未闭合则报错并在行尾截断。
    /// javac 拒绝空字符字面量（`''`，包括 `'\u0027'` 翻译出来的形态）。
    fn quoted(&mut self, start: usize, quote: char, message: &'static str) {
        if quote == '\'' && self.peek() == Some('\'') {
            self.error(start, "空字符字面量");
            self.bump();
            return;
        }
        loop {
            match self.peek() {
                None | Some('\n') | Some('\r') => {
                    self.error(start, message);
                    return;
                }
                Some('\\') => {
                    self.bump();
                    if !matches!(self.peek(), None | Some('\n') | Some('\r')) {
                        self.bump();
                    }
                }
                Some(c) => {
                    self.bump();
                    if c == quote {
                        return;
                    }
                }
            }
        }
    }

    fn text_block(&mut self, start: usize) -> SyntaxKind {
        loop {
            match self.peek() {
                None => {
                    self.error(start, "文本块未闭合");
                    break;
                }
                Some('\\') => {
                    self.bump();
                    self.bump();
                }
                Some('"') if self.peek_nth(1) == Some('"') && self.peek_nth(2) == Some('"') => {
                    self.bump();
                    self.bump();
                    self.bump();
                    break;
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
        TEXT_BLOCK
    }

    fn number(&mut self, first: char) -> SyntaxKind {
        if first == '0' {
            match self.peek() {
                Some('x') | Some('X') => {
                    self.bump();
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                    let mut is_float = false;
                    if self.peek() == Some('.')
                        && matches!(self.peek_nth(1), Some(c) if c.is_ascii_hexdigit() || c == 'p' || c == 'P')
                    {
                        self.bump();
                        self.eat_while(|c| c.is_ascii_hexdigit() || c == '_');
                        is_float = true;
                    }
                    if matches!(self.peek(), Some('p') | Some('P')) {
                        self.bump();
                        if matches!(self.peek(), Some('+') | Some('-')) {
                            self.bump();
                        }
                        self.eat_while(|c| c.is_ascii_digit() || c == '_');
                        is_float = true;
                    }
                    return if is_float {
                        self.float_suffix()
                    } else {
                        self.int_suffix()
                    };
                }
                Some('b') | Some('B') => {
                    self.bump();
                    self.eat_while(|c| c == '0' || c == '1' || c == '_');
                    return self.int_suffix();
                }
                _ => {}
            }
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        // `1.5`、`1.`、`1.e3` 都是浮点数；`1.foo` / `1..` 不把点吃进来
        if self.peek() == Some('.') {
            let after = self.peek_nth(1);
            let is_fraction = match after {
                Some(c) if c.is_ascii_digit() => true,
                Some('e') | Some('E') | Some('f') | Some('F') | Some('d') | Some('D') => true,
                Some('.') => false,
                Some(c) if is_ident_start(c) => false,
                _ => true,
            };
            if is_fraction {
                self.bump();
                return self.decimal_fraction_and_suffix();
            }
        }
        if matches!(self.peek(), Some('e') | Some('E')) {
            self.exponent();
            return self.float_suffix();
        }
        match self.peek() {
            Some('f') | Some('F') => {
                self.bump();
                FLOAT_LITERAL
            }
            Some('d') | Some('D') => {
                self.bump();
                DOUBLE_LITERAL
            }
            _ => self.int_suffix(),
        }
    }

    /// 已经吃掉小数点，继续吃小数部分、指数和后缀。
    fn decimal_fraction_and_suffix(&mut self) -> SyntaxKind {
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
        if matches!(self.peek(), Some('e') | Some('E')) {
            self.exponent();
        }
        self.float_suffix()
    }

    fn exponent(&mut self) {
        self.bump();
        if matches!(self.peek(), Some('+') | Some('-')) {
            self.bump();
        }
        self.eat_while(|c| c.is_ascii_digit() || c == '_');
    }

    fn float_suffix(&mut self) -> SyntaxKind {
        match self.peek() {
            Some('f') | Some('F') => {
                self.bump();
                FLOAT_LITERAL
            }
            Some('d') | Some('D') => {
                self.bump();
                DOUBLE_LITERAL
            }
            _ => DOUBLE_LITERAL,
        }
    }

    fn int_suffix(&mut self) -> SyntaxKind {
        match self.peek() {
            Some('l') | Some('L') => {
                self.bump();
                LONG_LITERAL
            }
            _ => INT_LITERAL,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(text: &str) -> Vec<SyntaxKind> {
        let (tokens, _) = tokenize(text);
        tokens
            .into_iter()
            .map(|t| t.kind)
            .filter(|k| !k.is_trivia())
            .collect()
    }

    #[test]
    fn lengths_cover_whole_input() {
        let text = "class A { int x = 0x1F; String s = \"a\\\"b\"; /** doc */ // c\n }";
        let (tokens, errors) = tokenize(text);
        assert!(errors.is_empty());
        let total: u32 = tokens.iter().map(|t| t.len).sum();
        assert_eq!(total as usize, text.len());
    }

    #[test]
    fn numbers() {
        assert_eq!(
            kinds("1 1L 1.0 1f 1e3 0x1p3 0b101 1_000 .5 1.d"),
            vec![
                INT_LITERAL,
                LONG_LITERAL,
                DOUBLE_LITERAL,
                FLOAT_LITERAL,
                DOUBLE_LITERAL,
                DOUBLE_LITERAL,
                INT_LITERAL,
                INT_LITERAL,
                DOUBLE_LITERAL,
                DOUBLE_LITERAL,
            ]
        );
    }

    #[test]
    fn generics_close_as_single_gt() {
        assert_eq!(
            kinds("Map<A, List<B>> x"),
            vec![IDENT, LT, IDENT, COMMA, IDENT, LT, IDENT, GT, GT, IDENT]
        );
    }

    #[test]
    fn comments_and_text_block() {
        let (tokens, errors) = tokenize("/**/ /** d */ \"\"\"\n a \"x\" \"\"\"");
        assert!(errors.is_empty());
        let kinds: Vec<_> = tokens
            .iter()
            .map(|t| t.kind)
            .filter(|k| *k != WHITESPACE)
            .collect();
        assert_eq!(kinds, vec![BLOCK_COMMENT, DOC_COMMENT, TEXT_BLOCK]);
    }

    #[test]
    fn unterminated_string_reports_error() {
        let (_, errors) = tokenize("\"abc\nint");
        assert_eq!(errors.len(), 1);
    }

    /// JLS 3.3：`\u0020` 是空格，在分词之前就应该翻译掉。
    #[test]
    fn unicode_escape_between_tokens_is_translated() {
        let (tokens, errors) = tokenize("class A { int\\u0020x = 1; }");
        assert!(errors.is_empty(), "{errors:?}");
        let kinds: Vec<_> = tokens
            .into_iter()
            .map(|t| t.kind)
            .filter(|k| !k.is_trivia())
            .collect();
        assert_eq!(
            kinds,
            vec![
                CLASS_KW,
                IDENT,
                L_CURLY,
                INT_KW,
                IDENT,
                EQ,
                INT_LITERAL,
                SEMICOLON,
                R_CURLY,
            ]
        );
    }

    /// 两个 `\u002f` 拼成 `//`：这一行在 javac 眼里是注释。
    #[test]
    fn unicode_escapes_can_form_a_comment_marker() {
        let text = "class A {\n\\u002f\\u002f comment\n int y = 2;\n}";
        let (tokens, errors) = tokenize(text);
        assert!(errors.is_empty(), "{errors:?}");
        let total: u32 = tokens.iter().map(|t| t.len).sum();
        assert_eq!(total as usize, text.len());
        let kinds: Vec<_> = tokens
            .into_iter()
            .map(|t| t.kind)
            .filter(|k| *k != WHITESPACE)
            .collect();
        assert_eq!(
            kinds,
            vec![
                CLASS_KW,
                IDENT,
                L_CURLY,
                LINE_COMMENT,
                INT_KW,
                IDENT,
                EQ,
                INT_LITERAL,
                SEMICOLON,
                R_CURLY,
            ]
        );
    }

    /// `\u000A` 是行终止符：注释在它那里结束，后面是真正的代码。
    #[test]
    fn unicode_newline_terminates_a_line_comment() {
        let (_, errors) = tokenize("// \\u000A int x;");
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(kinds("// \\u000A int x;"), vec![INT_KW, IDENT, SEMICOLON]);
    }

    /// 资格规则：`\u` 前面紧挨着偶数个 `\` 时才翻译。
    #[test]
    fn unicode_escape_eligibility_counts_backslashes() {
        // `\\u0041`：偶数个，不翻译——两个 `\` 都是错误字符，`u0041` 是标识符
        let (tokens, errors) = tokenize("\\\\u0041");
        assert_eq!(errors.len(), 2);
        let kinds: Vec<_> = tokens.into_iter().map(|t| t.kind).collect();
        assert_eq!(kinds, vec![ERROR_TOKEN, ERROR_TOKEN, IDENT]);
        // `\\\u0041`：奇数个，最后一个 `\` 合格——仍是两个 `\` 错误字符，但转义变成了 `A`
        let (tokens, errors) = tokenize("\\\\\\u0041");
        assert_eq!(errors.len(), 2);
        let kinds: Vec<_> = tokens.into_iter().map(|t| t.kind).collect();
        assert_eq!(kinds, vec![ERROR_TOKEN, ERROR_TOKEN, IDENT]);
    }

    /// `\u` 后面可以跟多个 `u`：`\uuu0020` 同样是空格。
    #[test]
    fn unicode_escape_may_repeat_the_u() {
        let text = "int\\uuu0020x";
        let (tokens, errors) = tokenize(text);
        assert!(errors.is_empty(), "{errors:?}");
        let kinds: Vec<_> = tokens.iter().map(|t| t.kind).collect();
        assert_eq!(kinds, vec![INT_KW, WHITESPACE, IDENT]);
        assert_eq!(tokens[1].len, 8);
        // 只有 `u` 没有十六进制位：不是转义
        let (_, errors) = tokenize("int\\uu x");
        assert!(!errors.is_empty());
    }

    /// 关键字也能由转义拼出来：`cl\u0061ss` 就是 `class`。
    #[test]
    fn unicode_escape_can_spell_a_keyword() {
        let (tokens, errors) = tokenize("cl\\u0061ss A {}");
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(tokens[0].kind, CLASS_KW);
        assert_eq!(tokens[0].len, 10);
    }

    /// javac 拒绝 `'\u0027'`（翻译后是 `'''`，空字符字面量）。
    #[test]
    fn unicode_quote_escape_is_an_empty_char_literal() {
        let (_, errors) = tokenize("'\\u0027'");
        assert!(!errors.is_empty(), "空字符字面量应当报错");
    }

    /// 普通 `''` 也是 javac 拒绝的空字符字面量。
    #[test]
    fn empty_char_literal_reports_error() {
        let (_, errors) = tokenize("''");
        assert_eq!(errors.len(), 1);
    }

    /// 翻译视图里 token 的长度必须仍是原始字节数，且总和覆盖整个文件。
    #[test]
    fn translated_lengths_cover_whole_input() {
        let text = "class A { int\\u0020x = 1; } // \\u000A int y;";
        let (tokens, errors) = tokenize(text);
        assert!(errors.is_empty(), "{errors:?}");
        let total: u32 = tokens.iter().map(|t| t.len).sum();
        assert_eq!(total as usize, text.len());
    }
}
