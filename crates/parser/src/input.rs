//! parser 的输入：去掉空白和注释之后的 token 序列。

use crate::{lexer::Token, SyntaxKind};

#[derive(Default)]
pub struct Input {
    kind: Vec<SyntaxKind>,
    /// 如果该 token 是 `IDENT` 且文本是上下文关键字，这里放对应的关键字种类，否则与 `kind` 相同
    contextual: Vec<SyntaxKind>,
    /// 该 token 与下一个 token 之间是否没有任何空白/注释
    joint: Vec<bool>,
}

impl Input {
    pub fn push(&mut self, kind: SyntaxKind, contextual: SyntaxKind) {
        self.kind.push(kind);
        self.contextual.push(contextual);
        self.joint.push(false);
    }

    /// 标记最后压入的 token 与下一个 token 紧邻。
    pub fn was_joint(&mut self) {
        if let Some(last) = self.joint.last_mut() {
            *last = true;
        }
    }

    pub fn len(&self) -> usize {
        self.kind.len()
    }

    pub fn is_empty(&self) -> bool {
        self.kind.is_empty()
    }

    pub(crate) fn kind(&self, idx: usize) -> SyntaxKind {
        self.kind.get(idx).copied().unwrap_or(SyntaxKind::EOF)
    }

    pub(crate) fn contextual_kind(&self, idx: usize) -> SyntaxKind {
        self.contextual.get(idx).copied().unwrap_or(SyntaxKind::EOF)
    }

    pub(crate) fn is_joint(&self, idx: usize) -> bool {
        self.joint.get(idx).copied().unwrap_or(false)
    }

    /// 从 lexer 的输出构造 parser 输入。
    pub fn from_tokens(text: &str, tokens: &[Token]) -> Input {
        let mut input = Input::default();
        let mut offset = 0usize;
        let mut prev_was_significant = false;
        for token in tokens {
            let end = offset + token.len as usize;
            if token.kind.is_trivia() {
                prev_was_significant = false;
            } else {
                if prev_was_significant {
                    input.was_joint();
                }
                let contextual = if token.kind == SyntaxKind::IDENT {
                    // token 文本里的 `\uXXXX`（JLS 3.3）翻译之后再认上下文关键字
                    let raw = &text[offset..end];
                    let spelling;
                    let kind_text = if raw.contains('\\') {
                        spelling = crate::lexer::translate_span(raw);
                        &spelling
                    } else {
                        raw
                    };
                    SyntaxKind::from_contextual_keyword(kind_text).unwrap_or(token.kind)
                } else {
                    token.kind
                };
                input.push(token.kind, contextual);
                prev_was_significant = true;
            }
            offset = end;
        }
        input
    }
}
