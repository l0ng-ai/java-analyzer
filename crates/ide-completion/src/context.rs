//! 补全上下文：光标在什么语法位置、周围有哪些语义信息。
//!
//! 光标处的代码通常是残缺的。做法是在光标处插入一个占位标识符后重新解析（"假树"），
//! 在假树上判断语法位置；语义信息（类型、作用域）仍然从数据库里的原始文件上取，
//! 通过文本范围把假树里光标之前的节点对应回原树。

use base_db::{Db, SourceFile};
use hir::{
    class_data, method_sig, resolve_type_path, BodyId, ClassId, Semantics, Ty, TypeNs, TypeScope,
};
use ide_db::annotations::{annotation_site, AnnotationSite};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use syntax::{
    ast::{self, AstNode},
    Parse, SyntaxKind, SyntaxNode, SyntaxToken, TextRange, TextSize,
};

use crate::CompletionConfig;

const MARKER: &str = "__ja_completion_marker__";

/// 类型名出现的位置。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TypeLocation {
    /// `new Foo|`
    New,
    /// `@Foo|`
    Annotation,
    /// 类体里成员声明的开头
    Member,
    /// 编译单元顶层
    TopLevel,
    Other,
}

/// `extends` / `implements` 后面要的父类型。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SupertypeKind {
    /// 类的 `extends`：能继承的类
    Class,
    /// `implements`、接口的 `extends`
    Interface,
}

/// 正在输入的标识符后面紧跟着什么。它限定了这里能写哪类名字：
/// `(` 前面是方法，`=` 前面是变量，`.` 前面是能取成员的东西（对象、类、包），`[` 前面是数组。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Following {
    Paren,
    Assign,
    Dot,
    Bracket,
    Other,
}

impl Following {
    fn of(rest: &str) -> Following {
        let same_line = rest.trim_start_matches([' ', '\t']);
        if same_line.starts_with('(') {
            return Following::Paren;
        }
        if same_line.starts_with('[') {
            return Following::Bracket;
        }
        // `=`、`+=`、`<<=`、`x++` 要求左边是变量；`==` 不是赋值
        const ASSIGN_OPS: &[&str] = &[
            "++", "--", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", ">>>=",
        ];
        if (same_line.starts_with('=') && !same_line.starts_with("=="))
            || ASSIGN_OPS.iter().any(|op| same_line.starts_with(op))
        {
            return Following::Assign;
        }
        // 链式调用常常折到下一行：`.` 可以隔着换行
        let next = rest.trim_start();
        if next.starts_with('.') && !next.starts_with("..") {
            return Following::Dot;
        }
        Following::Other
    }
}

#[derive(Debug, Clone)]
pub(crate) enum ContextKind {
    /// `receiver.|` 或 `receiver::|`
    Dot {
        /// 原树里的接收者表达式（找不到对应节点时为 `None`）
        receiver: Option<ast::Expr>,
        /// 接收者是一串点分名字时的各段（`java.util.Li|` 的 `["java", "util"]`）
        receiver_path: Option<Vec<SmolStr>>,
        receiver_range: TextRange,
        /// 整个 `receiver.xxx` 独占一条语句（可以用语句级的 postfix 模板）
        statement_level: bool,
        method_ref: bool,
    },
    /// `Type::|`
    TypeMethodRef {
        ty: ast::Type,
    },
    Type {
        qualifier: Vec<SmolStr>,
        location: TypeLocation,
    },
    Import {
        qualifier: Vec<SmolStr>,
        is_static: bool,
    },
    Package {
        qualifier: Vec<SmolStr>,
    },
    /// 模块名：`import module java.|`、`requires java.|`、`exports p to m.|`
    Module {
        qualifier: Vec<SmolStr>,
    },
    /// `module-info.java` 里 `exports` / `opens` 的包名
    ModulePackage {
        qualifier: Vec<SmolStr>,
    },
    Expr {
        statement_start: bool,
        /// 位于 `case` 标签里时，被 switch 的表达式的类型
        switch_scrutinee: Option<Ty>,
    },
    AnnotationArg {
        annotation: ClassId,
    },
    /// 文档注释里的 `@tag`；`inline` 表示 `{@tag}` 形式
    JavadocTag {
        inline: bool,
        owner: DocOwner,
    },
    /// `@param ` 之后：被注释的声明的形参名和类型参数，以及这条注释里是不是已经写过它的 `@param`
    JavadocParam {
        names: Vec<(SmolStr, bool)>,
    },
    /// `{@link |}`、`@see |`、`@throws |`：类型名。`qualifier` 是已经写好的 `a.b.` 部分
    JavadocType {
        qualifier: Vec<SmolStr>,
        /// `@throws` / `@exception`：要的是异常类型
        throws: bool,
        /// 在成员引用的形参列表里（`{@link #foo(int, |}`）：还可以写基本类型
        params: Option<JavadocParams>,
    },
    /// `{@link #|}`、`{@link Foo#|}`：成员。`ty` 为空时是被注释的声明所在的类
    JavadocMember {
        ty: Vec<SmolStr>,
    },
}

/// `{@link Foo#foo(|}`：引用的方法。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct JavadocParams {
    /// `#` 前面的类型，空的时候是被注释的声明所在的类
    pub(crate) ty: Vec<SmolStr>,
    pub(crate) name: SmolStr,
    /// 光标在第一个形参的位置上（`(` 之后）：可以给出整组重载的形参列表
    pub(crate) first: bool,
    /// 光标后面已经有 `)`
    pub(crate) closed: bool,
}

/// 文档注释所注释的声明，决定能写哪些块标签。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DocOwner {
    /// 类、接口、枚举、记录、注解类型；`params` 表示能写 `@param`（泛型类型、记录）
    Type {
        params: bool,
    },
    Method {
        returns_value: bool,
    },
    Constructor,
    Field,
    /// 包、模块，或者注释后面还没有声明
    Other,
}

pub(crate) struct CompletionContext<'a> {
    pub(crate) db: &'a dyn Db,
    pub(crate) sema: Semantics<'a>,
    pub(crate) config: &'a CompletionConfig,
    pub(crate) file: SourceFile,
    pub(crate) offset: TextSize,
    pub(crate) original_root: SyntaxNode,
    /// 光标前已经输入的标识符部分
    pub(crate) prefix: String,
    /// `prefix` 在原文里的范围
    pub(crate) source_range: TextRange,
    pub(crate) kind: ContextKind,
    pub(crate) scope: TypeScope,
    pub(crate) enclosing_class: Option<ClassId>,
    /// 光标所在的局部类 / 匿名类（在它们的类体里），由内到外
    pub(crate) local_classes: Vec<ClassId>,
    pub(crate) body: Option<BodyId>,
    pub(crate) expected_ty: Option<Ty>,
    pub(crate) in_static_context: bool,
    /// 光标（及正在输入的标识符）后面紧跟着 `(`
    pub(crate) followed_by_paren: bool,
    /// 正在输入的标识符后面已经写好的内容（修改已有代码时常见）
    pub(crate) following: Following,
    /// 后面是 `.name`（或 `(...).name`，这时是调用结果上的成员）时的 `name`
    pub(crate) next_member: Option<SmolStr>,
    /// 在 `extends` / `implements` 后面：要的是哪种父类型
    pub(crate) supertype: Option<SupertypeKind>,
    /// 改写已有调用 `foo|(a, b)` 的方法名时，已经写好的实参个数
    pub(crate) call_args: Option<usize>,
    /// 改写已有声明 `Foo| name` 的类型时，后面的变量名 / 方法名
    pub(crate) declared_name: Option<SmolStr>,
    /// 正在写类型的变量 / 字段声明的初始化式是 `new X(...)` 时的 `X`
    pub(crate) initializer_class: Option<ClassId>,
    /// 改写已有注解 `@Foo|(a = 1)` 的名字时，参数里用到的元素名
    pub(crate) annotation_elements: Option<Vec<SmolStr>>,
    /// `@Foo|` 所在的位置（被注解的是什么），用来按 `@Target` 筛选注解
    pub(crate) annotation_site: Option<AnnotationSite>,
    /// 假树里光标外层各个 lambda 的形参名（由内到外）
    pub(crate) lambda_params: Vec<SmolStr>,
    /// 当前文件里每个标识符出现的次数（不算注释和字符串）
    pub(crate) usage: FxHashMap<&'a str, i32>,
    /// 光标所在行的缩进
    pub(crate) indent: String,
    /// `prefix` 之前的那个非空白 token
    pub(crate) prev_token: Option<SyntaxKind>,
    /// 假树里占位符后面是否补了一个分号
    pub(crate) fake_terminator: bool,
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '$'
}

impl<'a> CompletionContext<'a> {
    pub(crate) fn new(
        db: &'a dyn Db,
        file: SourceFile,
        offset: TextSize,
        config: &'a CompletionConfig,
    ) -> Option<CompletionContext<'a>> {
        let text: &'a str = file.text(db);
        let pos = usize::from(offset);
        if pos > text.len() || !text.is_char_boundary(pos) {
            return None;
        }
        let sema = Semantics::new(db);
        let original = base_db::parse(db, file);
        let original_root = original.syntax_node();

        // 注释和字符串里不补全；文档注释里只补全 Javadoc 标签
        let mut doc_comment = None;
        if let Some(token) = original_root.token_at_offset(offset).left_biased() {
            let range = token.text_range();
            let kind = token.kind();
            let inside = range.start() < offset && offset < range.end();
            if kind.is_trivia() && token.text().starts_with('/') {
                let line_comment = token.text().starts_with("//");
                if inside || (line_comment && offset == range.end()) {
                    if kind != SyntaxKind::DOC_COMMENT {
                        return None;
                    }
                    doc_comment = Some(token);
                }
            } else if kind.is_literal() {
                let is_number = matches!(
                    kind,
                    SyntaxKind::INT_LITERAL
                        | SyntaxKind::LONG_LITERAL
                        | SyntaxKind::FLOAT_LITERAL
                        | SyntaxKind::DOUBLE_LITERAL
                );
                if inside || (is_number && offset == range.end()) {
                    return None;
                }
            }
        }

        let prefix_len: usize = text[..pos]
            .chars()
            .rev()
            .take_while(|c| is_ident_char(*c))
            .map(char::len_utf8)
            .sum();
        let prefix = text[pos - prefix_len..pos].to_owned();
        // 数字后面不是标识符
        if prefix.starts_with(|c: char| c.is_ascii_digit()) {
            return None;
        }
        let source_range = TextRange::new(TextSize::from((pos - prefix_len) as u32), offset);

        let suffix_len: usize = text[pos..]
            .chars()
            .take_while(|c| is_ident_char(*c))
            .map(char::len_utf8)
            .sum();
        // 只看同一行：下一行开头的 `(` 属于别的语句
        let followed_by_paren = text[pos + suffix_len..]
            .trim_start_matches([' ', '\t'])
            .starts_with('(');
        let following = Following::of(&text[pos + suffix_len..]);
        // `|.name`：点后面已经写好的成员名
        // `|(...).name`：调用后面接着的成员名（跳过配对的括号）
        let after_call = match following {
            Following::Dot => Some(&text[pos + suffix_len..]),
            Following::Paren => skip_parens(text[pos + suffix_len..].trim_start()),
            _ => None,
        };
        let next_member = after_call.and_then(|rest| {
            let after_dot = rest.trim_start().strip_prefix('.')?;
            let after_dot = after_dot.trim_start();
            let len: usize = after_dot
                .chars()
                .take_while(|c| is_ident_char(*c))
                .map(char::len_utf8)
                .sum();
            (len > 0).then(|| SmolStr::new(&after_dot[..len]))
        });

        let line_start = text[..pos].rfind('\n').map_or(0, |i| i + 1);
        let indent: String = text[line_start..pos]
            .chars()
            .take_while(|c| *c == ' ' || *c == '\t')
            .collect();

        let prev_token =
            syntax::algo::non_trivia_token_before(&original_root, source_range.start())
                .map(|t| t.kind());

        // 原树里光标处的锚点节点，用来取作用域和所在的体
        let anchor = original_root
            .token_at_offset(offset)
            .left_biased()
            .and_then(|t| t.parent())
            .unwrap_or_else(|| original_root.clone());
        let scope = sema.type_scope(file, &anchor);
        let enclosing_class = sema.enclosing_class(file, &anchor);
        let local_classes = sema.local_classes_at(file, &anchor);
        let body = sema.body_of(file, &anchor);
        let in_static_context = match body {
            Some(BodyId::Method(m)) => class_data(db, m.class)
                .and_then(|d| d.methods.get(m.idx as usize).map(|m| m.flags.is_static()))
                .unwrap_or(false),
            Some(BodyId::Field(f)) => class_data(db, f.class)
                .and_then(|d| d.fields.get(f.idx as usize).map(|f| f.flags.is_static()))
                .unwrap_or(false),
            _ => false,
        };

        // 直接用 lexer 切词：比遍历语法树快，注释和字符串里的词自然不算
        let mut usage: FxHashMap<&'a str, i32> = FxHashMap::default();
        let mut token_start = 0usize;
        for token in parser::tokenize(text).0 {
            let token_end = token_start + token.len as usize;
            if token.kind == SyntaxKind::IDENT {
                *usage.entry(&text[token_start..token_end]).or_insert(0) += 1;
            }
            token_start = token_end;
        }
        // 正在输入的这个词本身不算一次使用
        if let Some(count) = usage.get_mut(&text[pos - prefix_len..pos]) {
            *count -= 1;
        }

        let mut ctx = CompletionContext {
            db,
            sema,
            config,
            file,
            offset,
            original_root,
            prefix,
            source_range,
            kind: ContextKind::Expr {
                statement_start: false,
                switch_scrutinee: None,
            },
            scope,
            enclosing_class,
            local_classes,
            body,
            expected_ty: None,
            in_static_context,
            followed_by_paren,
            following,
            next_member,
            supertype: None,
            call_args: None,
            declared_name: None,
            initializer_class: None,
            annotation_elements: None,
            annotation_site: None,
            lambda_params: Vec::new(),
            usage,
            indent,
            prev_token,
            fake_terminator: false,
        };
        if let Some(token) = doc_comment {
            ctx.kind = javadoc_context(&token, text, pos - prefix_len, pos)?;
            // 文档里的名字按被注释的声明解析：类的注释里看得见类自己的成员类型和成员
            if let Some(scope_node) = ide_db::doc_links::doc_scope_node(&token) {
                ctx.scope = ctx.sema.type_scope(file, &scope_node);
                ctx.enclosing_class = ctx.scope.class.or(ctx.enclosing_class);
                ctx.local_classes = ctx.sema.local_classes_at(file, &scope_node);
            }
            if matches!(ctx.kind, ContextKind::JavadocType { throws: true, .. }) {
                ctx.expected_ty =
                    Some(Ty::well_known(db, "java/lang/Throwable")).filter(|ty| !ty.is_unknown());
            }
            return Some(ctx);
        }

        let mut fake_text = String::with_capacity(text.len() + MARKER.len());
        fake_text.push_str(&text[..pos]);
        fake_text.push_str(MARKER);
        // `foo.` 写到一半、下一行是另一条以标识符开头的语句：不补一个分号的话，
        // `foo.<占位符>` 会和下一行连成 `类型 变量名` 的声明
        let rest_of_line = text[pos..].split('\n').next().unwrap_or("");
        let next_starts_name = text[pos..].trim_start().starts_with(is_ident_char);
        if ctx.prev_token == Some(SyntaxKind::DOT)
            && rest_of_line.trim().is_empty()
            && next_starts_name
        {
            fake_text.push(';');
            ctx.fake_terminator = true;
        }
        fake_text.push_str(&text[pos..]);
        let fake_root = fake_tree(&original, offset, &fake_text);
        let fake_token = fake_root
            .token_at_offset(offset)
            .find(|t| t.kind() == SyntaxKind::IDENT && t.text().contains(MARKER))?;

        // 光标外层的 lambda 的形参：写到一半的 lambda 在原树里往往解析不出来，推断里没有它们
        for lambda in fake_token
            .parent_ancestors()
            .filter(|n| n.kind() == SyntaxKind::LAMBDA_EXPR)
        {
            for element in lambda.children_with_tokens() {
                if element.kind() == SyntaxKind::ARROW {
                    break;
                }
                let Some(node) = element.into_node() else {
                    continue;
                };
                let names = std::iter::once(node.clone())
                    .chain(node.descendants())
                    .filter(|n| n.kind() == SyntaxKind::NAME);
                for name in names {
                    let text = SmolStr::new(name.text().to_string().trim());
                    if !text.is_empty()
                        && !text.contains(MARKER)
                        && !ctx.lambda_params.contains(&text)
                    {
                        ctx.lambda_params.push(text);
                    }
                }
            }
        }
        ctx.kind = ctx.classify(&fake_token)?;
        Some(ctx)
    }

    /// 文件的语言级别已知且低于 `level`：生成的代码不能用 Java `level` 才有的语法和 API。
    /// 级别未知时什么都可以用。
    pub(crate) fn level_below(&self, level: u32) -> bool {
        ide_diagnostics::language_level(self.db, self.file).is_some_and(|l| l < level)
    }

    /// 假树里的节点对应的原树节点：范围相同（含光标的节点去掉占位符长度）、种类相同。
    pub(crate) fn original_node(&self, fake: &SyntaxNode) -> Option<SyntaxNode> {
        let range = fake.text_range();
        let range = if range.end() <= self.offset {
            range
        } else if range.start() <= self.offset {
            let mut end = range.end().checked_sub(TextSize::of(MARKER))?;
            // 假树里补的分号在占位符后面：跨过它的节点再减去它的长度
            if self.fake_terminator && range.end() > self.offset + TextSize::of(MARKER) {
                end = end.checked_sub(TextSize::of(';'))?;
            }
            if end < range.start() {
                return None;
            }
            TextRange::new(range.start(), end)
        } else {
            return None;
        };
        if range.is_empty() || !self.original_root.text_range().contains_range(range) {
            return None;
        }
        let covering = match self.original_root.covering_element(range) {
            syntax::NodeOrToken::Node(node) => node,
            syntax::NodeOrToken::Token(token) => token.parent()?,
        };
        covering
            .ancestors()
            .find(|n| n.text_range() == range && n.kind() == fake.kind())
    }

    pub(crate) fn original_expr(&self, fake: &ast::Expr) -> Option<ast::Expr> {
        self.original_node(fake.syntax()).and_then(ast::Expr::cast)
    }

    fn resolve_fake_type(&self, ty: &ast::Type) -> Ty {
        let node = self.original_node(ty.syntax()).and_then(ast::Type::cast);
        self.sema
            .resolve_type(self.file, node.as_ref().unwrap_or(ty))
    }

    fn classify(&mut self, fake_token: &SyntaxToken) -> Option<ContextKind> {
        let name_ref = fake_token.parent()?;
        if name_ref.kind() != SyntaxKind::NAME_REF {
            // 声明处的名字（`int fo|`）等位置不补全
            return None;
        }
        let parent = name_ref.parent()?;
        match parent.kind() {
            SyntaxKind::FIELD_ACCESS => {
                let access = ast::FieldAccess::cast(parent.clone())?;
                let receiver = access.receiver()?;
                self.expected_ty = self.expected_type_of(&parent);
                Some(self.dot_context(&parent, receiver, false))
            }
            SyntaxKind::METHOD_CALL => {
                let call = ast::MethodCall::cast(parent.clone())?;
                self.call_args = call.arg_list().map(|args| args.args().count());
                match call.receiver() {
                    Some(receiver) => {
                        self.expected_ty = self.expected_type_of(&parent);
                        Some(self.dot_context(&parent, receiver, false))
                    }
                    // 不带接收者的调用 `foo|(...)`
                    None => {
                        self.expected_ty = self.expected_type_of(&parent);
                        Some(self.expr_context(&parent))
                    }
                }
            }
            SyntaxKind::METHOD_REF => {
                let method_ref = ast::MethodRef::cast(parent.clone())?;
                if let Some(receiver) = method_ref.receiver_expr() {
                    Some(self.dot_context(&parent, receiver, true))
                } else {
                    let ty = method_ref.receiver_type()?;
                    let ty = self
                        .original_node(ty.syntax())
                        .and_then(ast::Type::cast)
                        .unwrap_or(ty);
                    Some(ContextKind::TypeMethodRef { ty })
                }
            }
            SyntaxKind::NAME_EXPR => {
                self.expected_ty = self.expected_type_of(&parent);
                Some(self.expr_context(&parent))
            }
            SyntaxKind::CLASS_TYPE => {
                let class_ty = ast::ClassType::cast(parent.clone())?;
                let qualifier = class_ty
                    .qualifier()
                    .map(|q| q.segments())
                    .unwrap_or_default();
                // 找到最外层的 CLASS_TYPE（`a.b.C|` 的限定符是嵌套在里面的）
                let outer = parent.clone();
                let owner = outer.parent()?;
                let location = match owner.kind() {
                    SyntaxKind::NEW_EXPR => TypeLocation::New,
                    SyntaxKind::COMPILATION_UNIT => TypeLocation::TopLevel,
                    SyntaxKind::CLASS_BODY => TypeLocation::Member,
                    SyntaxKind::FIELD_DECL | SyntaxKind::METHOD_DECL | SyntaxKind::ERROR => {
                        match owner.parent().map(|p| p.kind()) {
                            Some(SyntaxKind::CLASS_BODY) => TypeLocation::Member,
                            Some(SyntaxKind::COMPILATION_UNIT) => TypeLocation::TopLevel,
                            _ if owner.kind() == SyntaxKind::ERROR => TypeLocation::Other,
                            _ => TypeLocation::Other,
                        }
                    }
                    // 语句开头的 `Foo|` 会被解析成局部变量声明的类型：按表达式位置处理更有用
                    SyntaxKind::LOCAL_VAR_DECL if qualifier.is_empty() => {
                        let has_declarator = owner
                            .children()
                            .any(|n| n.kind() == SyntaxKind::VARIABLE_DECLARATOR);
                        // `ret|` 后面换行接着另一条语句（`ret|\n names.clear();`）时，下一行的
                        // 第一个名字会被当成变量名：声明的类型和名字不在同一行就不当它是声明
                        let split_across_lines = owner
                            .children()
                            .find(|n| n.kind() == SyntaxKind::VARIABLE_DECLARATOR)
                            .and_then(|d| {
                                let between = TextRange::new(
                                    parent.text_range().end(),
                                    d.text_range().start(),
                                );
                                let text = owner.text().to_string();
                                let start =
                                    usize::from(between.start() - owner.text_range().start());
                                let end = usize::from(between.end() - owner.text_range().start());
                                text.get(start..end).map(|gap| gap.contains('\n'))
                            })
                            .unwrap_or(false);
                        if !has_declarator || split_across_lines {
                            return Some(ContextKind::Expr {
                                statement_start: true,
                                switch_scrutinee: None,
                            });
                        }
                        TypeLocation::Other
                    }
                    _ => TypeLocation::Other,
                };
                // `new` 之后按期望类型推荐实现类
                if location == TypeLocation::New {
                    self.expected_ty = self.expected_type_of(&owner);
                }
                self.declared_name = declared_name(&owner);
                self.initializer_class = initializer_new_type(&owner).and_then(|path| {
                    match resolve_type_path(self.db, &self.scope, &path) {
                        Some(TypeNs::Class(class)) => Some(class),
                        _ => None,
                    }
                });
                // 能抛出 / 捕获的只有 Throwable 的子类；`extends` / `implements` 后面要类或接口
                let clause = outer
                    .ancestors()
                    .skip(1)
                    .find(|n| n.kind() != SyntaxKind::UNION_TYPE)
                    .map(|n| (n.kind(), n.parent().map(|p| p.kind())));
                match clause {
                    Some((SyntaxKind::THROWS_CLAUSE, _))
                    | Some((SyntaxKind::PARAM, Some(SyntaxKind::CATCH_CLAUSE))) => {
                        self.expected_ty = Some(Ty::well_known(self.db, "java/lang/Throwable"))
                            .filter(|ty| !ty.is_unknown());
                    }
                    Some((SyntaxKind::IMPLEMENTS_CLAUSE, _))
                    | Some((
                        SyntaxKind::EXTENDS_CLAUSE,
                        Some(SyntaxKind::INTERFACE_DECL | SyntaxKind::ANNOTATION_TYPE_DECL),
                    )) => self.supertype = Some(SupertypeKind::Interface),
                    Some((SyntaxKind::EXTENDS_CLAUSE, Some(SyntaxKind::CLASS_DECL))) => {
                        self.supertype = Some(SupertypeKind::Class)
                    }
                    _ => {}
                }
                Some(ContextKind::Type {
                    qualifier,
                    location,
                })
            }
            SyntaxKind::QUALIFIED_NAME => {
                let qualified = ast::QualifiedName::cast(parent.clone())?;
                let qualifier = qualified
                    .qualifier()
                    .map(|q| q.segments())
                    .unwrap_or_default();
                let owner = parent
                    .ancestors()
                    .find(|n| n.kind() != SyntaxKind::QUALIFIED_NAME)?;
                match owner.kind() {
                    SyntaxKind::IMPORT_DECL => {
                        let import = ast::ImportDecl::cast(owner)?;
                        if import.is_module() {
                            return Some(ContextKind::Module { qualifier });
                        }
                        Some(ContextKind::Import {
                            qualifier,
                            is_static: import.is_static(),
                        })
                    }
                    SyntaxKind::REQUIRES_DIRECTIVE => Some(ContextKind::Module { qualifier }),
                    SyntaxKind::EXPORTS_DIRECTIVE | SyntaxKind::OPENS_DIRECTIVE => {
                        // 第一个名字是包，`to` 后面的是模块
                        let outermost = parent
                            .ancestors()
                            .take_while(|n| n.kind() == SyntaxKind::QUALIFIED_NAME)
                            .last()?;
                        let is_package = owner
                            .children()
                            .find(|c| c.kind() == SyntaxKind::QUALIFIED_NAME)
                            .is_some_and(|first| first == outermost);
                        Some(if is_package {
                            ContextKind::ModulePackage { qualifier }
                        } else {
                            ContextKind::Module { qualifier }
                        })
                    }
                    SyntaxKind::PACKAGE_DECL => Some(ContextKind::Package { qualifier }),
                    SyntaxKind::ANNOTATION => {
                        self.annotation_site = annotation_site(&owner);
                        // 已经写好的参数（`@Foo|(name = "x")`）：只有带这些元素的注解才合适
                        self.annotation_elements = ast::Annotation::cast(owner)
                            .and_then(|a| a.arg_list())
                            .map(|args| {
                                args.args()
                                    .map(|arg| match arg.name_ref() {
                                        Some(name) => name.text(),
                                        None => SmolStr::new_static("value"),
                                    })
                                    .collect()
                            });
                        Some(ContextKind::Type {
                            qualifier,
                            location: TypeLocation::Annotation,
                        })
                    }
                    _ => None,
                }
            }
            SyntaxKind::ANNOTATION_ARG => {
                let annotation = parent.ancestors().find_map(ast::Annotation::cast)?;
                let segments = annotation.name()?.segments();
                match hir::resolve_type_path(self.db, &self.scope, &segments)? {
                    TypeNs::Class(class) => Some(ContextKind::AnnotationArg { annotation: class }),
                    TypeNs::TypeParam(_) => None,
                }
            }
            _ => None,
        }
    }

    fn dot_context(
        &self,
        access: &SyntaxNode,
        fake_receiver: ast::Expr,
        method_ref: bool,
    ) -> ContextKind {
        let receiver_range = fake_receiver.syntax().text_range();
        let statement_level = access
            .parent()
            .is_some_and(|p| p.kind() == SyntaxKind::EXPR_STMT);
        ContextKind::Dot {
            receiver: self.original_expr(&fake_receiver),
            receiver_path: expr_path(&fake_receiver),
            receiver_range,
            statement_level,
            method_ref,
        }
    }

    fn expr_context(&self, fake_expr: &SyntaxNode) -> ContextKind {
        let statement_start = fake_expr
            .parent()
            .is_some_and(|p| p.kind() == SyntaxKind::EXPR_STMT);
        let switch_scrutinee = fake_expr
            .ancestors()
            .take_while(|n| !matches!(n.kind(), SyntaxKind::BLOCK | SyntaxKind::SWITCH_CASE))
            .find(|n| n.kind() == SyntaxKind::SWITCH_LABEL)
            .and_then(|label| {
                let switch = label.ancestors().find(|n| {
                    matches!(n.kind(), SyntaxKind::SWITCH_STMT | SyntaxKind::SWITCH_EXPR)
                })?;
                let scrutinee = switch.children().find_map(ast::Expr::cast)?;
                let original = self.original_expr(&scrutinee)?;
                self.sema.type_of_expr(self.file, &original)
            });
        ContextKind::Expr {
            statement_start,
            switch_scrutinee,
        }
    }

    /// 假树里的表达式节点所处位置期望的类型（只覆盖最常见的几种位置）。
    fn expected_type_of(&self, fake_expr: &SyntaxNode) -> Option<Ty> {
        let parent = fake_expr.parent()?;
        let ty = match parent.kind() {
            SyntaxKind::VARIABLE_DECLARATOR => {
                let decl = parent.parent()?;
                let ty = decl.children().find_map(ast::Type::cast)?;
                self.resolve_fake_type(&ty)
            }
            SyntaxKind::RETURN_STMT => match self.body? {
                BodyId::Method(method) => method_sig(self.db, method).ret.clone(),
                _ => return None,
            },
            SyntaxKind::ASSIGN_EXPR => {
                let assign = ast::AssignExpr::cast(parent)?;
                let lhs = assign.lhs()?;
                if lhs.syntax() == fake_expr {
                    return None;
                }
                let lhs = self.original_expr(&lhs)?;
                self.sema.type_of_expr(self.file, &lhs)?
            }
            SyntaxKind::IF_STMT | SyntaxKind::WHILE_STMT | SyntaxKind::DO_WHILE_STMT => Ty::BOOLEAN,
            SyntaxKind::THROW_STMT => Ty::well_known(self.db, "java/lang/Throwable"),
            // 二元运算的右操作数：按左边的类型和运算符推出来
            SyntaxKind::BINARY_EXPR => {
                let binary = ast::BinaryExpr::cast(parent)?;
                let lhs = binary.lhs()?;
                if lhs.syntax() == fake_expr {
                    return None;
                }
                let op = binary.op_kind()?;
                if matches!(op, SyntaxKind::AMP_AMP | SyntaxKind::PIPE_PIPE) {
                    return Some(Ty::BOOLEAN);
                }
                let lhs = self.original_expr(&lhs)?;
                let lhs_ty = self.sema.type_of_expr(self.file, &lhs)?;
                let numeric = lhs_ty
                    .unboxed(self.db)
                    .filter(|p| *p != hir::PrimitiveType::Boolean);
                match op {
                    SyntaxKind::EQ_EQ | SyntaxKind::NEQ => match numeric {
                        Some(_) => Ty::Primitive(hir::PrimitiveType::Double),
                        None => lhs_ty,
                    },
                    // 数值比较和算术：任何数值类型都行，用 double 表示"可以拓宽到它的都算"
                    SyntaxKind::LT
                    | SyntaxKind::GT
                    | SyntaxKind::LT_EQ
                    | SyntaxKind::GT_EQ
                    | SyntaxKind::MINUS
                    | SyntaxKind::STAR
                    | SyntaxKind::SLASH
                    | SyntaxKind::PERCENT => {
                        numeric?;
                        Ty::Primitive(hir::PrimitiveType::Double)
                    }
                    _ => return None,
                }
            }
            // 实参位置：被调用方法对应形参的类型
            SyntaxKind::ARG_LIST => {
                let idx = parent
                    .children()
                    .filter(|n| ast::Expr::can_cast(n.kind()))
                    .position(|n| &n == fake_expr)?;
                let original = self.original_node(&parent)?;
                let result = hir::infer(self.db, self.body?);
                let info = result.call_info(original.text_range())?;
                // 形参类型按接收者代换（`Stream<String>.map` 的形参是 `Function<? super String, …>`）
                let candidate = info
                    .candidates
                    .iter()
                    .find(|c| Some(c.id) == info.chosen)
                    .or_else(|| info.candidates.first());
                let method = info.chosen.or_else(|| candidate.map(|c| c.id))?;
                let sig = method_sig(self.db, method);
                let params = match candidate.filter(|c| c.id == method) {
                    Some(c) => c.param_tys(self.db),
                    None => sig.params.clone(),
                };
                let last = params.len().checked_sub(1)?;
                match params.get(idx.min(last))? {
                    Ty::Array(element) if sig.varargs && idx >= last => (**element).clone(),
                    other => other.clone(),
                }
            }
            _ => return None,
        };
        (!ty.is_unknown() && ty != Ty::Void).then_some(ty)
    }

    /// 由内到外的各层类（光标在局部类 / 匿名类里时从它们开始）。
    pub(crate) fn enclosing_classes(&self) -> Vec<ClassId> {
        let mut res = Vec::new();
        // 局部类 / 匿名类的外层链最终也到具名类
        // 在局部类的声明头里（`class L implements Consumer<|>`）时从这个局部类开始
        let mut current = self
            .local_classes
            .first()
            .copied()
            .or(self.scope.class.filter(|_| self.scope.in_class_header))
            .or(self.enclosing_class);
        while let Some(class) = current {
            res.push(class);
            current = hir::outer_class(self.db, class);
        }
        res
    }
}

/// 假树的根节点：`fake_text` 是原文件在 `offset` 处插入占位符之后的文本。
///
/// 光标在方法体、构造器体或初始化块里时，只重新解析那一个块（块级增量重解析），结果与
/// 整文件解析完全相同（见 `Parse::reparse`）。这是最常见的补全位置，省掉的是每次请求
/// 一次的整文件解析。`reparse` 只在能够保证这一点时适用：其它位置（类体、签名、字段
/// 初始化式……），以及占位符让解析器提前结束这个块的时候（例如它独占语句的开头、后面
/// 还跟着标识符，被当成 `类型 名字` 的声明），都照旧整文件解析。
fn fake_tree(
    original: &Parse<ast::CompilationUnit>,
    offset: TextSize,
    fake_text: &str,
) -> SyntaxNode {
    original
        .reparse(TextRange::empty(offset), fake_text)
        .unwrap_or_else(|| ast::CompilationUnit::parse(fake_text))
        .syntax_node()
}

/// 类型后面已经写好的声明名字：字段 / 局部变量 / 形参的名字，方法名。
fn declared_name(owner: &SyntaxNode) -> Option<SmolStr> {
    let name = match owner.kind() {
        SyntaxKind::FIELD_DECL | SyntaxKind::LOCAL_VAR_DECL => owner
            .children()
            .find_map(ast::VariableDeclarator::cast)?
            .name()?,
        SyntaxKind::PARAM => ast::Param::cast(owner.clone())?.name()?,
        SyntaxKind::METHOD_DECL => ast::MethodDecl::cast(owner.clone())?.name()?,
        _ => return None,
    };
    let text = name.text();
    (!text.contains(MARKER)).then_some(text)
}

/// 变量 / 字段声明的初始化式是 `new a.b.X<...>(...)` 时的类型路径。
fn initializer_new_type(owner: &SyntaxNode) -> Option<Vec<SmolStr>> {
    if !matches!(
        owner.kind(),
        SyntaxKind::FIELD_DECL | SyntaxKind::LOCAL_VAR_DECL
    ) {
        return None;
    }
    let declarator = owner.children().find_map(ast::VariableDeclarator::cast)?;
    let new_expr = declarator
        .syntax()
        .children()
        .find(|n| n.kind() == SyntaxKind::NEW_EXPR)?;
    let ty = new_expr
        .children()
        .find(|n| n.kind() == SyntaxKind::CLASS_TYPE)?;
    let mut path: Vec<SmolStr> = Vec::new();
    let mut current = Some(ty);
    while let Some(node) = current {
        let name = node.children().find_map(ast::NameRef::cast)?;
        path.push(name.text());
        current = node.children().find(|n| n.kind() == SyntaxKind::CLASS_TYPE);
    }
    path.reverse();
    (!path.iter().any(|seg| seg.contains(MARKER))).then_some(path)
}

/// 按驼峰拆成小写的词：`ObjectInputStream` → `object`、`input`、`stream`。
fn camel_words(name: &str) -> Vec<String> {
    let mut words: Vec<String> = Vec::new();
    let mut prev_lower = false;
    for c in name.chars() {
        if c == '_' || c == '$' {
            prev_lower = false;
            words.push(String::new());
            continue;
        }
        if (c.is_uppercase() && prev_lower) || words.is_empty() {
            words.push(String::new());
        }
        if let Some(last) = words.last_mut() {
            last.extend(c.to_lowercase());
        }
        prev_lower = c.is_lowercase() || c.is_ascii_digit();
    }
    words.retain(|w| !w.is_empty());
    words
}

/// 声明的名字像不像是由这个类型名起的：`permission` ← `Permission`，`stream` ← `ObjectInputStream`，
/// `cp` ← `ConstantPool`，`createCaret` ← `Caret`。
pub(crate) fn name_suggests_type(declared: &str, type_name: &str) -> bool {
    let ty = camel_words(type_name);
    let mut name = camel_words(declared);
    // 方法名去掉开头的动词
    if name.len() > 1
        && matches!(
            name[0].as_str(),
            "get" | "create" | "new" | "to" | "as" | "find" | "build" | "make" | "read" | "load"
        )
    {
        name.remove(0);
    }
    if name.is_empty() || ty.is_empty() {
        return false;
    }
    if name.len() <= ty.len() && ty[ty.len() - name.len()..] == name[..] {
        return true;
    }
    // 缩写：每个词的首字母
    let initials: String = ty.iter().filter_map(|w| w.chars().next()).collect();
    ty.len() >= 2 && name.len() == 1 && name[0] == initials
}

/// 表达式是一串点分名字（`a`、`a.b.c`）时返回各段。
fn expr_path(expr: &ast::Expr) -> Option<Vec<SmolStr>> {
    match expr {
        ast::Expr::NameExpr(name) => Some(vec![name.name_ref()?.text()]),
        ast::Expr::FieldAccess(access) => {
            let mut path = expr_path(&access.receiver()?)?;
            path.push(access.name_ref()?.text());
            Some(path)
        }
        _ => None,
    }
}

/// `rest` 以 `(` 开头时跳过配对的括号（不认字符串和字符里的括号，最多看 2000 个字节），
/// 返回后面的部分。
fn skip_parens(rest: &str) -> Option<&str> {
    let mut depth = 0usize;
    for (i, c) in rest.char_indices().take_while(|(i, _)| *i < 2000) {
        match c {
            '(' => depth += 1,
            ')' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(&rest[i + 1..]);
                }
            }
            ';' | '{' | '}' => return None,
            _ => {}
        }
    }
    None
}

/// 文档注释里光标前的内容决定补全什么。`word_start` 是正在输入的词的起始字节偏移。
fn javadoc_context(
    token: &SyntaxToken,
    text: &str,
    word_start: usize,
    pos: usize,
) -> Option<ContextKind> {
    let line_start = text[..word_start].rfind('\n').map_or(0, |i| i + 1);
    let before = &text[line_start..word_start];
    let owner = token.parent();

    if let Some(head) = before.strip_suffix('@') {
        let owner = owner.as_ref().map_or(DocOwner::Other, doc_owner);
        if head.ends_with('{') {
            return Some(ContextKind::JavadocTag {
                inline: true,
                owner,
            });
        }
        // 块标签只能出现在行首（前面只有空白和 `*`，或注释的开头 `/**`）
        return is_doc_line_start(head).then_some(ContextKind::JavadocTag {
            inline: false,
            owner,
        });
    }

    if let Some(kind) = javadoc_reference(before) {
        return Some(kind);
    }
    if let Some(kind) = javadoc_method_params(before, text[pos..].starts_with(')')) {
        return Some(kind);
    }

    let content = before
        .trim()
        .trim_start_matches('/')
        .trim_start_matches('*')
        .trim();
    // `@param <|`：只能是类型参数
    let type_param = content == "@param <" && before.ends_with('<');
    if (content == "@param" && before.ends_with(char::is_whitespace)) || type_param {
        let owner = owner?;
        let comment = token.text();
        // 这条注释里已经有 `@param name` 了
        let documented = |name: &str| {
            comment.match_indices("@param").any(|(i, tag)| {
                let rest = comment[i + tag.len()..].trim_start();
                rest.strip_prefix(name)
                    .is_some_and(|after| !after.starts_with(is_ident_char))
            })
        };
        let mut names: Vec<SmolStr> = Vec::new();
        if type_param {
            // 已经写了 `<`，插入 `T>`
        } else if let Some(params) = owner.children().find_map(ast::ParamList::cast) {
            names.extend(params.params().filter_map(|p| p.name()).map(|n| n.text()));
        }
        if let Some(type_params) = owner.children().find_map(ast::TypeParamList::cast) {
            names.extend(type_params.type_params().filter_map(|p| p.name()).map(|n| {
                if type_param {
                    SmolStr::new(format!("{}>", n.text()))
                } else {
                    SmolStr::new(format!("<{}>", n.text()))
                }
            }));
        }
        let names = names
            .into_iter()
            .map(|name| {
                let written = documented(&name);
                (name, written)
            })
            .collect();
        return Some(ContextKind::JavadocParam { names });
    }
    None
}

/// 标签前面这一行只有空白和 `*`（或者注释的开头 `/**`）。
fn is_doc_line_start(head: &str) -> bool {
    head.trim()
        .trim_start_matches('/')
        .chars()
        .all(|c| c == '*' || c.is_whitespace())
}

/// 引用标签（`{@link`、`{@linkplain`、`{@value`、`@see`、`@throws`、`@exception`）后面正在写的名字。
/// `before` 是光标所在行里正在输入的词之前的部分。
fn javadoc_reference(before: &str) -> Option<ContextKind> {
    // 已经写好的那部分引用（`java.util.`、`Foo#`）：从最后一个空白之后开始
    let fragment_start = before
        .char_indices()
        .rev()
        .find(|(_, c)| c.is_whitespace())
        .map(|(i, c)| i + c.len_utf8())?;
    let fragment = &before[fragment_start..];
    let head = before[..fragment_start].trim_end();
    let at = head.rfind('@')?;
    let tag = &head[at + 1..];
    if tag.is_empty() || !tag.chars().all(|c| c.is_ascii_alphabetic()) {
        return None;
    }
    let inline = head[..at].ends_with('{');
    let block = !inline && is_doc_line_start(&head[..at]);
    let (members, throws) = match tag {
        "link" | "linkplain" | "value" if inline => (true, false),
        "see" if block => (true, false),
        "throws" | "exception" if block => (false, true),
        _ => return None,
    };
    let path = |text: &str| -> Option<Vec<SmolStr>> {
        if text.is_empty() {
            return Some(Vec::new());
        }
        text.split('.')
            .map(|seg| {
                (!seg.is_empty() && seg.chars().all(is_ident_char)).then(|| SmolStr::new(seg))
            })
            .collect()
    };
    if let Some(ty) = fragment.strip_suffix('#') {
        if !members {
            return None;
        }
        return Some(ContextKind::JavadocMember { ty: path(ty)? });
    }
    let qualifier = match fragment.strip_suffix('.') {
        Some(qualifier) => path(qualifier).filter(|q| !q.is_empty())?,
        None if fragment.is_empty() => Vec::new(),
        None => return None,
    };
    Some(ContextKind::JavadocType {
        qualifier,
        throws,
        params: None,
    })
}

/// `{@link #foo(|}`、`{@link Foo#foo(int, java.util.|}`、`@see #foo(|`：形参类型。
fn javadoc_method_params(before: &str, closed: bool) -> Option<ContextKind> {
    let open = before.rfind('(')?;
    let written = &before[open + 1..];
    if written.contains([')', '{', '}', '@', '#']) {
        return None;
    }
    // `(` 前面是 `Foo#name`，再往前是标签
    let head = &before[..open];
    let ref_start = head
        .char_indices()
        .rev()
        .find(|(_, c)| c.is_whitespace())
        .map(|(i, c)| i + c.len_utf8())?;
    let (ty, name) = head[ref_start..].split_once('#')?;
    if name.is_empty() || !name.chars().all(is_ident_char) {
        return None;
    }
    // 借用 `javadoc_reference` 判断标签：把引用换成 `#`
    let ContextKind::JavadocMember { ty } =
        javadoc_reference(&format!("{}{ty}#", &head[..ref_start]))?
    else {
        return None;
    };
    // 正在写的这个形参：最后一个 `,` 之后已经写好的限定部分（`java.util.`）
    let current = written.rsplit(',').next().unwrap_or("").trim_start();
    let first = !written.contains(',') && current.is_empty();
    let qualifier = match current.strip_suffix('.') {
        Some(q) if !q.is_empty() => q
            .split('.')
            .map(|seg| {
                (!seg.is_empty() && seg.chars().all(is_ident_char)).then(|| SmolStr::new(seg))
            })
            .collect::<Option<Vec<_>>>()?,
        _ if current.is_empty() => Vec::new(),
        _ => return None,
    };
    Some(ContextKind::JavadocType {
        qualifier,
        throws: false,
        params: Some(JavadocParams {
            ty,
            name: SmolStr::new(name),
            first,
            closed,
        }),
    })
}

/// 文档注释后面的声明是什么。
fn doc_owner(node: &SyntaxNode) -> DocOwner {
    match node.kind() {
        SyntaxKind::METHOD_DECL => {
            // 第一个类型子节点是返回类型
            let returns_void = node
                .children()
                .find_map(ast::Type::cast)
                .is_some_and(|ty| ty.syntax().text().to_string().trim() == "void");
            DocOwner::Method {
                returns_value: !returns_void,
            }
        }
        SyntaxKind::CONSTRUCTOR_DECL => DocOwner::Constructor,
        SyntaxKind::FIELD_DECL | SyntaxKind::ENUM_CONSTANT => DocOwner::Field,
        kind if ast::TypeDecl::can_cast(kind) => DocOwner::Type {
            params: kind == SyntaxKind::RECORD_DECL
                || node
                    .children()
                    .any(|c| c.kind() == SyntaxKind::TYPE_PARAM_LIST),
        },
        _ => DocOwner::Other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use syntax::green_eq;

    /// 各种位置的样本：方法体、构造器体、初始化块，体里的 lambda、匿名类、数组初始化式，
    /// 以及含花括号的字符串和注释。
    const SOURCE: &str = r#"class A {
    int x = 1;
    String s = "{\"}"; // }

    void f(int n) {
        Runnable r = () -> {
            for (int i = 0; i < n; i++) {
                x += i;
            }
        };

        f(n - 1);

        List<String> names = null;
        int[] a = { 1, 2 };
        Object o = new Object() {
            int g() {
                return n;
            }
        };
        return n;
    }

    A() {
        x = 2;
    }

    {
        f(1);
    }
}
"#;

    /// 在 `offset` 处插入占位符之后的文本；`terminator`：占位符后面是否补了分号。
    fn fake_text(source: &str, offset: usize, terminator: bool) -> String {
        let mut fake = String::with_capacity(source.len() + MARKER.len() + 1);
        fake.push_str(&source[..offset]);
        fake.push_str(MARKER);
        if terminator {
            fake.push(';');
        }
        fake.push_str(&source[offset..]);
        fake
    }

    /// 假树必须与整文件解析给出的树完全相同（补不补分号两种文本都比）。
    fn assert_fake_tree_equals_full_parse(source: &str, offset: usize) {
        let original = ast::CompilationUnit::parse(source);
        for terminator in [false, true] {
            let fake = fake_text(source, offset, terminator);
            let expected = ast::CompilationUnit::parse(&fake).syntax_node();
            let actual = fake_tree(&original, TextSize::from(offset as u32), &fake);
            assert!(
                green_eq(&actual.green(), &expected.green()),
                "offset {offset}, terminator {terminator}"
            );
        }
    }

    #[test]
    fn fake_tree_equals_full_parse_at_every_position() {
        assert!(
            ast::CompilationUnit::parse(SOURCE).errors().is_empty(),
            "样本本身不应当有语法错误"
        );
        for offset in 0..=SOURCE.len() {
            if SOURCE.is_char_boundary(offset) {
                assert_fake_tree_equals_full_parse(SOURCE, offset);
            }
        }
    }

    #[test]
    fn fake_tree_in_bodies_takes_the_incremental_path() {
        let original = ast::CompilationUnit::parse(SOURCE);
        // 光标在这些文本之后：都在某个方法体、构造器体或初始化块里面，`reparse` 必须适用，
        // 而且结果与整文件解析相同
        for (before, description) in [
            ("void f(int n) {", "方法体"),
            ("() -> {", "方法体里的 lambda"),
            ("int g() {", "匿名类的方法"),
            ("A() {", "构造器体"),
            ("f(1);", "初始化块"),
        ] {
            let offset = SOURCE.find(before).expect("样本里应当有这段代码") + before.len();
            let fake = fake_text(SOURCE, offset, false);
            assert!(
                original
                    .reparse(TextRange::empty(TextSize::from(offset as u32)), &fake)
                    .is_some(),
                "{description}里的光标应当走增量路径"
            );
            assert_fake_tree_equals_full_parse(SOURCE, offset);
        }
        // `reparse` 不适用的位置：类体、参数表、字段初始化式；以及占位符独占语句的开头、后面
        // 还跟着标识符的时候（解析器把 `占位符 名字` 当成声明：后面是 `(` 时是成员声明，是
        // `<` 时停在类型实参上，块都在这里提前结束）。都退回整文件解析，结果相同
        for (before, description) in [
            ("class A {", "类体"),
            ("void f(int ", "参数表"),
            ("int x = ", "字段初始化式"),
            ("    {\n", "初始化块的开头"),
            ("        };\n\n", "下一行以 `f(n - 1);` 开头的空行"),
            ("f(n - 1);\n\n", "下一行以 `List<String>` 开头的空行"),
        ] {
            let offset = SOURCE.find(before).expect("样本里应当有这段代码") + before.len();
            let fake = fake_text(SOURCE, offset, false);
            assert!(
                original
                    .reparse(TextRange::empty(TextSize::from(offset as u32)), &fake)
                    .is_none(),
                "{description}里的光标不应走增量路径"
            );
            assert_fake_tree_equals_full_parse(SOURCE, offset);
        }
    }

    #[test]
    fn following_classifies_what_comes_after_the_name() {
        assert_eq!(Following::of("(a, b);"), Following::Paren);
        assert_eq!(Following::of(" = 1;"), Following::Assign);
        assert_eq!(Following::of(" += 1;"), Following::Assign);
        assert_eq!(Following::of("++;"), Following::Assign);
        assert_eq!(Following::of(" == 1"), Following::Other);
        assert_eq!(Following::of(" <= 1"), Following::Other);
        assert_eq!(Following::of("[0]"), Following::Bracket);
        assert_eq!(Following::of("\n        .map(x)"), Following::Dot);
        assert_eq!(Following::of(";"), Following::Other);
        // 下一行开头的 `(` 属于别的语句
        assert_eq!(Following::of("\n(a)"), Following::Other);
    }

    #[test]
    fn declared_names_suggest_types() {
        assert!(name_suggests_type("permission", "Permission"));
        assert!(name_suggests_type("stream", "ObjectInputStream"));
        assert!(name_suggests_type("inputStream", "ObjectInputStream"));
        assert!(name_suggests_type("cp", "ConstantPool"));
        assert!(name_suggests_type("createCaret", "Caret"));
        assert!(!name_suggests_type("count", "Container"));
        assert!(!name_suggests_type("s", "String"));
        assert!(!name_suggests_type("get", "Getter"));
    }
}
