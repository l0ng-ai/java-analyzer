//! 按新签名更新用法。
//!
//! 用户直接在编辑器里改方法 / 构造器的声明（增删、重排、改名形参，改形参类型、方法名或返回类型），
//! 然后在声明上执行这个操作：所有调用处（包括 `super(...)` / `this(...)`、`new`、枚举常量的实参）、
//! 覆写链上的其它声明（父类型、子类型、局部类、匿名类和菱形匿名类里的覆写）、仍然有效的方法引用、
//! 文档注释里的 `@param` 都跟着改。
//!
//! 旧签名由宿主的 [`SignatureTracker`] 提供：它是这个声明在这一轮修改之前的签名头原文。
//! 新旧形参先按名字对应，剩下的按位置对应（视为改名）；没有对应的旧形参被删除，没有对应的
//! 新形参是新增的。
//!
//! 调用处的找法：在搜索范围里按旧名字（构造器按类名）找，再逐个判断它在修改之前是否调用这个方法：
//! - 解析到覆写链上的方法（它们还是旧签名）或者这个方法本身：是；
//! - 否则接收者的类型必须属于覆写链上的某个类，实参能匹配旧签名，并且同名的其它方法里没有
//!   同样适用而旧签名又不比它更具体的。
//!
//! 实参的改写：
//! - 删除的形参：对应的实参去掉；实参有副作用时拒绝整个操作并说明位置；
//! - 重排：实参跟着重排；会改变两个有副作用的实参的先后时拒绝；
//! - 新增的形参：调用处作用域里有同名、类型相容的变量（局部变量、形参、字段）时传它，
//!   否则传类型的默认值（`null`、`0`、`false` …），由用户再填；
//! - 可变参数：仍是最后一个可变参数时原样保留；改成数组时把散开的实参包成 `new T[]{…}`。
//!
//! 方法引用只在形参列表没变（只改了名字、返回类型或形参名）时改名；否则拒绝并说明位置。

use base_db::{Db, SourceFile};
use hir::{
    class_data, infer, is_assignable, method_sig, ClassId, ClassKind, Definition, LocalData,
    LocalKind, MethodId, Semantics, Ty, Visibility,
};
use ide_db::TextEdit;
use rustc_hash::FxHashSet;
use smol_str::SmolStr;
use syntax::{
    ast::{self, AstNode},
    SyntaxKind, SyntaxNode, TextRange, TextSize,
};

use crate::{
    navigation::{all_subclasses, diamond_anonymous_overrides_by_key},
    rename::SourceChange,
    signature_tracker::{header_range, SignatureTracker},
    FileId, FileRange,
};

/// 光标处的声明可以按新签名更新用法。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureUpdate {
    /// 对应的 [`SignatureTracker`] 记录；更新完之后宿主用它结束这条记录
    pub entry: u64,
    pub label: String,
    /// 修改，或者不能修改的原因
    pub change: Result<SourceChange, String>,
}

// ---------------------------------------------------------------------------
// 签名
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct SigParam {
    /// 类型原文（含形参名后面的 `[]`，不含 `...`）
    ty: String,
    name: String,
    varargs: bool,
    node: ast::Param,
}

#[derive(Debug, Clone)]
struct Sig {
    is_ctor: bool,
    name: String,
    ret: Option<String>,
    params: Vec<SigParam>,
}

/// 比较用：去掉不影响含义的空白。
fn normalize(text: &str) -> String {
    let is_word = |c: char| c.is_alphanumeric() || c == '_' || c == '$';
    let mut out = String::with_capacity(text.len());
    let mut space = false;
    for c in text.chars() {
        if c.is_whitespace() {
            space = true;
            continue;
        }
        if space && out.chars().last().is_some_and(is_word) && is_word(c) {
            out.push(' ');
        }
        space = false;
        out.push(c);
    }
    out
}

fn sig_of(decl: &SyntaxNode) -> Option<Sig> {
    let (is_ctor, name, ret, list) = match decl.kind() {
        SyntaxKind::METHOD_DECL => {
            let method = ast::MethodDecl::cast(decl.clone())?;
            let ret = method.return_type()?.syntax().text().to_string();
            let ret = format!("{ret}{}", "[]".repeat(method.extra_dims()));
            (
                false,
                method.name()?.text().to_string(),
                Some(ret),
                method.param_list()?,
            )
        }
        SyntaxKind::CONSTRUCTOR_DECL => {
            let ctor = ast::ConstructorDecl::cast(decl.clone())?;
            (
                true,
                ctor.name()?.text().to_string(),
                None,
                ctor.param_list()?,
            )
        }
        _ => return None,
    };
    let mut params = Vec::new();
    // 接收者形参 `Foo this` 没有名字，不算形参
    for param in list.params().filter(|p| p.name().is_some()) {
        let ty = param.ty()?.syntax().text().to_string();
        params.push(SigParam {
            ty: format!("{ty}{}", "[]".repeat(param.extra_dims())),
            name: param.name()?.text().to_string(),
            varargs: param.is_varargs(),
            node: param,
        });
    }
    Some(Sig {
        is_ctor,
        name,
        ret,
        params,
    })
}

/// 解析记下的旧签名头。
fn parse_header(header: &str) -> Option<Sig> {
    let text = format!("class __Old {{\n{header} {{}}\n}}\n");
    let root = ast::CompilationUnit::parse(&text).syntax_node();
    let decl = root.descendants().find(|n| {
        matches!(
            n.kind(),
            SyntaxKind::METHOD_DECL | SyntaxKind::CONSTRUCTOR_DECL
        )
    })?;
    sig_of(&decl)
}

impl Sig {
    fn same_as(&self, other: &Sig) -> bool {
        self.name == other.name
            && self.ret.as_deref().map(normalize) == other.ret.as_deref().map(normalize)
            && self.params.len() == other.params.len()
            && self.params.iter().zip(&other.params).all(|(a, b)| {
                a.name == b.name && a.varargs == b.varargs && normalize(&a.ty) == normalize(&b.ty)
            })
    }

    fn fits(&self, arg_count: usize) -> bool {
        let n = self.params.len();
        arg_count == n || (self.is_varargs() && arg_count + 1 >= n)
    }

    fn is_varargs(&self) -> bool {
        self.params.last().is_some_and(|p| p.varargs)
    }
}

/// 每个新形参对应的旧形参：先按名字，再按同一位置，最后剩下的按先后一一对应。
fn map_params(old: &[SigParam], new: &[SigParam]) -> Vec<Option<usize>> {
    let mut mapping: Vec<Option<usize>> = vec![None; new.len()];
    let mut used = vec![false; old.len()];
    for (j, param) in new.iter().enumerate() {
        if let Some(i) = old.iter().position(|o| o.name == param.name) {
            if !used[i] {
                mapping[j] = Some(i);
                used[i] = true;
            }
        }
    }
    for j in 0..new.len() {
        if mapping[j].is_none() && j < old.len() && !used[j] {
            mapping[j] = Some(j);
            used[j] = true;
        }
    }
    let free_old: Vec<usize> = (0..old.len()).filter(|i| !used[*i]).collect();
    let free_new: Vec<usize> = (0..new.len()).filter(|j| mapping[*j].is_none()).collect();
    if free_old.len() == free_new.len() {
        for (i, j) in free_old.into_iter().zip(free_new) {
            mapping[j] = Some(i);
        }
    }
    mapping
}

// ---------------------------------------------------------------------------
// 修改的收集
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Piece {
    Text(String),
    /// 原文里的一段（其中的其它修改照样生效）
    Orig(TextRange),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Rewrite {
    range: TextRange,
    pieces: Vec<Piece>,
}

struct Node {
    rewrite: Rewrite,
    children: Vec<Node>,
}

fn insert_node(nodes: &mut Vec<Node>, rewrite: Rewrite) -> Result<(), ()> {
    if let Some(last) = nodes.last_mut() {
        let outer = last.rewrite.range;
        let inner = rewrite.range;
        if outer != inner && outer.contains_range(inner) && !inner.is_empty() {
            return insert_node(&mut last.children, rewrite);
        }
        if inner.start() < outer.end() {
            return Err(());
        }
    }
    nodes.push(Node {
        rewrite,
        children: Vec::new(),
    });
    Ok(())
}

fn render_range(text: &str, range: TextRange, children: &[Node]) -> String {
    let mut out = String::new();
    let mut pos = range.start();
    for child in children {
        let r = child.rewrite.range;
        if !range.contains_range(r) || r.start() < pos {
            continue;
        }
        out.push_str(&text[usize::from(pos)..usize::from(r.start())]);
        out.push_str(&render_node(text, child));
        pos = r.end();
    }
    out.push_str(&text[usize::from(pos)..usize::from(range.end())]);
    out
}

fn render_node(text: &str, node: &Node) -> String {
    let mut out = String::new();
    for piece in &node.rewrite.pieces {
        match piece {
            Piece::Text(s) => out.push_str(s),
            Piece::Orig(range) => out.push_str(&render_range(text, *range, &node.children)),
        }
    }
    out
}

#[derive(Default)]
struct Edits {
    rewrites: Vec<(FileId, SourceFile, Rewrite)>,
    imports: Vec<(FileId, TextEdit)>,
}

impl Edits {
    fn replace(
        &mut self,
        db: &dyn Db,
        file: SourceFile,
        range: TextRange,
        text: impl Into<String>,
    ) {
        self.rewrite(
            db,
            file,
            Rewrite {
                range,
                pieces: vec![Piece::Text(text.into())],
            },
        );
    }

    fn rewrite(&mut self, db: &dyn Db, file: SourceFile, rewrite: Rewrite) {
        self.rewrites.push((file.file_id(db), file, rewrite));
    }

    fn finish(mut self, db: &dyn Db) -> Result<SourceChange, String> {
        let conflict = || {
            base_db::tr!(
                "要做的修改互相重叠，无法自动完成",
                "The required edits overlap and cannot be applied automatically"
            )
        };
        self.rewrites.sort_by_key(|(file_id, _, rw)| {
            (
                *file_id,
                rw.range.start(),
                std::cmp::Reverse(rw.range.end()),
            )
        });
        self.rewrites.dedup_by(|a, b| a.0 == b.0 && a.2 == b.2);
        let mut edits: Vec<(FileId, TextEdit)> = Vec::new();
        let mut idx = 0;
        while idx < self.rewrites.len() {
            let (file_id, file, _) = self.rewrites[idx].clone();
            let mut roots: Vec<Node> = Vec::new();
            while idx < self.rewrites.len() && self.rewrites[idx].0 == file_id {
                insert_node(&mut roots, self.rewrites[idx].2.clone()).map_err(|_| conflict())?;
                idx += 1;
            }
            let text: &str = file.text(db);
            for node in &roots {
                edits.push((
                    file_id,
                    TextEdit::replace(node.rewrite.range, render_node(text, node)),
                ));
            }
        }
        let mut seen: FxHashSet<(FileId, String)> = FxHashSet::default();
        for (file_id, edit) in self.imports {
            if seen.insert((file_id, edit.new_text.clone())) {
                edits.push((file_id, edit));
            }
        }
        Ok(crate::assists::group_edits(edits))
    }
}

fn location(db: &dyn Db, file: SourceFile, offset: TextSize) -> String {
    let text: &str = file.text(db);
    let line = text[..usize::from(offset).min(text.len())]
        .matches('\n')
        .count()
        + 1;
    format!("{}.java:{line}", file.name(db))
}

// ---------------------------------------------------------------------------
// 类型
// ---------------------------------------------------------------------------

/// 形参类型粗略相同（区分重载用）：类相同、基本类型相同；类型变量、推断不出来的从宽。
fn loosely_same(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Class(x, _), Ty::Class(y, _)) => x == y,
        (Ty::Primitive(x), Ty::Primitive(y)) => x == y,
        (Ty::Array(x), Ty::Array(y)) => loosely_same(x, y),
        (Ty::TypeParam(_), _) | (_, Ty::TypeParam(_)) => true,
        (Ty::Unknown, _) | (_, Ty::Unknown) => true,
        _ => false,
    }
}

fn assignable(db: &dyn Db, from: Option<&Ty>, to: &Ty) -> bool {
    match from {
        None | Some(Ty::Unknown) => true,
        Some(Ty::Null) => !matches!(to, Ty::Primitive(_)),
        Some(from) => is_assignable(db, from, to) || is_assignable(db, &from.erasure(db), to),
    }
}

/// 实参（类型推断不出来的为 `None`，按相容处理）能否匹配这组形参。
fn applicable(db: &dyn Db, params: &[Ty], varargs: bool, args: &[Option<Ty>]) -> bool {
    let n = params.len();
    let fixed = args.len() == n
        && args
            .iter()
            .zip(params)
            .all(|(arg, param)| assignable(db, arg.as_ref(), param));
    if fixed {
        return true;
    }
    if !varargs || n == 0 || args.len() + 1 < n {
        return false;
    }
    let element = match &params[n - 1] {
        Ty::Array(element) => (**element).clone(),
        other => other.clone(),
    };
    args.iter().enumerate().all(|(idx, arg)| {
        let param = if idx + 1 < n { &params[idx] } else { &element };
        assignable(db, arg.as_ref(), param)
    })
}

/// 形参 `a` 是否至少和 `b` 一样具体（逐个可以赋给对方）。
fn at_least_as_specific(db: &dyn Db, a: &[Ty], b: &[Ty]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|(x, y)| is_assignable(db, x, y) || loosely_same(x, y))
}

fn classes_of(ty: &Ty, out: &mut Vec<ClassId>) {
    match ty {
        Ty::Class(class, _) => out.push(*class),
        Ty::Array(element) => classes_of(element, out),
        Ty::Intersection(parts) => parts.iter().for_each(|p| classes_of(p, out)),
        _ => {}
    }
}

fn classes_in(ty: &Ty, out: &mut Vec<ClassId>) {
    match ty {
        Ty::Class(class, args) => {
            out.push(*class);
            args.iter().for_each(|a| classes_in(a, out));
        }
        Ty::Array(element) => classes_in(element, out),
        Ty::Wildcard(hir::Wildcard::Extends(b) | hir::Wildcard::Super(b)) => classes_in(b, out),
        Ty::Intersection(parts) => parts.iter().for_each(|p| classes_in(p, out)),
        _ => {}
    }
}

fn default_value(ty: &Ty) -> &'static str {
    use hir::PrimitiveType as P;
    match ty {
        Ty::Primitive(P::Boolean) => "false",
        Ty::Primitive(P::Byte) => "(byte) 0",
        Ty::Primitive(P::Short) => "(short) 0",
        Ty::Primitive(P::Char) => "'\\0'",
        Ty::Primitive(P::Int) => "0",
        Ty::Primitive(P::Long) => "0L",
        Ty::Primitive(P::Float) => "0f",
        Ty::Primitive(P::Double) => "0.0",
        _ => "null",
    }
}

fn has_side_effects(node: &SyntaxNode) -> bool {
    match node.kind() {
        SyntaxKind::LAMBDA_EXPR | SyntaxKind::METHOD_REF => return false,
        SyntaxKind::METHOD_CALL
        | SyntaxKind::NEW_EXPR
        | SyntaxKind::ASSIGN_EXPR
        | SyntaxKind::POSTFIX_EXPR => return true,
        SyntaxKind::UNARY_EXPR
            if node
                .children_with_tokens()
                .filter_map(|e| e.into_token())
                .any(|t| matches!(t.kind(), SyntaxKind::PLUS_PLUS | SyntaxKind::MINUS_MINUS)) =>
        {
            return true
        }
        _ => {}
    }
    node.children().any(|child| has_side_effects(&child))
}

const SCOPE_KINDS: &[SyntaxKind] = &[
    SyntaxKind::BLOCK,
    SyntaxKind::SWITCH_CASE,
    SyntaxKind::FOR_STMT,
    SyntaxKind::FOREACH_STMT,
    SyntaxKind::TRY_STMT,
    SyntaxKind::CATCH_CLAUSE,
    SyntaxKind::LAMBDA_EXPR,
    SyntaxKind::METHOD_DECL,
    SyntaxKind::CONSTRUCTOR_DECL,
    SyntaxKind::CLASS_BODY,
    SyntaxKind::INITIALIZER_BLOCK,
];

/// 局部符号在 `offset` 处是否可见。
fn local_in_scope(root: &SyntaxNode, local: &LocalData, offset: TextSize) -> bool {
    if matches!(
        local.kind,
        LocalKind::LocalClassField | LocalKind::LocalClassMethod
    ) || local.decl_range.end() > offset
        || !root.text_range().contains_range(local.decl_range)
    {
        return false;
    }
    let node = match root.covering_element(local.decl_range) {
        syntax::NodeOrToken::Node(node) => node,
        syntax::NodeOrToken::Token(token) => match token.parent() {
            Some(node) => node,
            None => return false,
        },
    };
    node.ancestors()
        .skip(1)
        .find(|n| SCOPE_KINDS.contains(&n.kind()))
        .is_some_and(|scope| scope.text_range().contains_inclusive(offset))
}

// ---------------------------------------------------------------------------
// 入口
// ---------------------------------------------------------------------------

pub(crate) fn change_signature(
    db: &dyn Db,
    range: FileRange,
    tracker: &SignatureTracker,
) -> Option<SignatureUpdate> {
    if tracker.is_empty() {
        return None;
    }
    let file = base_db::source_file(db, range.file_id)?;
    let root = base_db::parse(db, file).syntax_node();
    if !root.text_range().contains_range(range.range) {
        return None;
    }
    let decl = match root.covering_element(range.range) {
        syntax::NodeOrToken::Node(node) => Some(node),
        syntax::NodeOrToken::Token(token) => token.parent(),
    }
    .into_iter()
    .flat_map(|n| n.ancestors())
    .find(|n| {
        matches!(
            n.kind(),
            SyntaxKind::METHOD_DECL | SyntaxKind::CONSTRUCTOR_DECL
        )
    })?;
    // 光标在方法体里时不提供
    if let Some(body) = decl.children().find(|n| n.kind() == SyntaxKind::BLOCK) {
        if range.range.start() > body.text_range().start() {
            return None;
        }
    }
    let header = header_range(&decl)?;
    let entry = tracker
        .entries()
        .iter()
        .find(|e| e.range.start() <= header.end() && header.start() <= e.range.end())?;
    let old = parse_header(&entry.old_header)?;
    let new = sig_of(&decl)?;
    if old.is_ctor != new.is_ctor || old.same_as(&new) {
        return None;
    }
    let change = Refactoring::new(db, file, &decl, &old, &new).and_then(|r| r.run());
    if change.as_ref().is_ok_and(|c| c.is_empty()) {
        return None;
    }
    Some(SignatureUpdate {
        entry: entry.id,
        label: base_db::tr!("按新签名更新用法", "Update usages to the new signature"),
        change,
    })
}

struct Refactoring<'a> {
    db: &'a dyn Db,
    sema: Semantics<'a>,
    file: SourceFile,
    decl: SyntaxNode,
    old: &'a Sig,
    new: &'a Sig,
    method: MethodId,
    mapping: Vec<Option<usize>>,
    old_tys: Vec<Ty>,
    new_tys: Vec<Ty>,
    /// 覆写链上（按旧签名）的方法，第一个是被修改的方法本身
    family: Vec<MethodId>,
    family_classes: Vec<ClassId>,
    /// 被修改的方法所在的类是枚举
    in_enum: bool,
    class_name: SmolStr,
    private: bool,
    edits: Edits,
    /// 改写了形参列表的覆写方法：`(文件, 声明的范围)`。它们的方法体里，新增的形参已经可用
    rewritten_decls: Vec<(FileId, TextRange)>,
}

impl<'a> Refactoring<'a> {
    fn new(
        db: &'a dyn Db,
        file: SourceFile,
        decl: &SyntaxNode,
        old: &'a Sig,
        new: &'a Sig,
    ) -> Result<Refactoring<'a>, String> {
        let not_found = || {
            base_db::tr!(
                "找不到这个声明的语义信息",
                "Cannot find the semantic information of this declaration"
            )
        };
        let sema = Semantics::new(db);
        let method = sema
            .method_of_decl(file, decl)
            .or_else(|| sema.local_class_method(file, decl))
            .ok_or_else(not_found)?;
        let data = class_data(db, method.class).ok_or_else(not_found)?;
        let method_data = data
            .methods
            .get(method.idx as usize)
            .ok_or_else(not_found)?;
        let mapping = map_params(&old.params, &new.params);
        let scope_node = decl
            .children()
            .find(|n| n.kind() == SyntaxKind::PARAM_LIST)
            .unwrap_or_else(|| decl.clone());
        let scope = sema.type_scope(file, &scope_node);
        let lower =
            |param: &SigParam| hir::lower_type_ref(db, &scope, &hir::lower_param_type(&param.node));
        let old_tys: Vec<Ty> = old.params.iter().map(lower).collect();
        let new_tys: Vec<Ty> = new.params.iter().map(lower).collect();

        let private = method_data.flags.visibility() == Visibility::Private;
        let overridable = !method_data.is_constructor && !method_data.flags.is_static() && !private;
        let mut family = vec![method];
        if overridable {
            family.extend(old_family(db, method, &old.name, &old_tys));
        }
        for member in &family[1..] {
            let is_source = class_data(db, member.class).is_some_and(|d| d.is_source);
            let synthetic = class_data(db, member.class)
                .and_then(|d| d.methods.get(member.idx as usize).map(|m| m.flags))
                .is_some_and(|flags| flags.contains(hir::Modifiers::SYNTHETIC));
            if !is_source || synthetic || Definition::Method(*member).source(db).is_none() {
                return Err(base_db::tr!(
                    "这个方法覆写了依赖库里的方法（或被它覆写），不能修改签名",
                    "The method overrides or is overridden by a library method; its signature cannot be changed"
                ));
            }
        }
        let mut family_classes: Vec<ClassId> = family.iter().map(|m| m.class).collect();
        family_classes.dedup();
        Ok(Refactoring {
            db,
            sema,
            file,
            decl: decl.clone(),
            old,
            new,
            method,
            mapping,
            old_tys,
            new_tys,
            family,
            family_classes,
            in_enum: data.kind == ClassKind::Enum,
            class_name: data.name.clone(),
            private,
            edits: Edits::default(),
            rewritten_decls: Vec::new(),
        })
    }

    fn run(mut self) -> Result<SourceChange, String> {
        let db = self.db;
        // 被修改的声明自身：文档注释、方法体里对改了名的形参的引用
        let own_names: Vec<String> = self.old.params.iter().map(|p| p.name.clone()).collect();
        let targets: Vec<(Option<usize>, String)> = self
            .mapping
            .iter()
            .zip(&self.new.params)
            .map(|(src, p)| (*src, p.name.clone()))
            .collect();
        let decl = self.decl.clone();
        if let Some((range, text)) = doc_rewrite(&decl, &own_names, &targets) {
            self.edits.replace(db, self.file, range, text);
        }
        self.rename_in_own_body(&decl);

        // 覆写链上的其它声明
        let members: Vec<MethodId> = self.family[1..].to_vec();
        for member in members {
            let Some(source) = Definition::Method(member).source(db) else {
                continue;
            };
            let root = base_db::parse(db, source.file).syntax_node();
            let Some(member_decl) = covering_decl(&root, source.full_range) else {
                continue;
            };
            self.rewrite_override(source.file, &member_decl)?;
        }
        if self.is_overridable() {
            let keys: Vec<(ClassId, SmolStr, usize)> = self
                .family_classes
                .iter()
                .map(|class| (*class, SmolStr::new(&self.old.name), self.old.params.len()))
                .collect();
            for (file, method) in diamond_anonymous_overrides_by_key(db, &keys) {
                let root = base_db::parse(db, file).syntax_node();
                if let Some(member_decl) = covering_decl(&root, method.full_range) {
                    self.rewrite_override(file, &member_decl)?;
                }
            }
        }

        // 调用处
        self.rewrite_usages()?;
        self.edits.finish(db)
    }

    fn is_overridable(&self) -> bool {
        let Some(data) = class_data(self.db, self.method.class) else {
            return false;
        };
        data.methods
            .get(self.method.idx as usize)
            .is_some_and(|m| !m.is_constructor && !m.flags.is_static() && !self.private)
    }

    fn params_unchanged(&self) -> bool {
        self.old.params.len() == self.new.params.len()
            && self
                .mapping
                .iter()
                .enumerate()
                .all(|(j, src)| *src == Some(j))
            && self
                .old
                .params
                .iter()
                .zip(&self.new.params)
                .all(|(a, b)| a.varargs == b.varargs && normalize(&a.ty) == normalize(&b.ty))
    }

    fn renamed(&self) -> bool {
        self.old.name != self.new.name
    }

    // -----------------------------------------------------------------------
    // 声明
    // -----------------------------------------------------------------------

    /// 改了名的形参：方法体里原来指向它的名字（现在解析不到，或者落到了同名字段上）换成新名字。
    fn rename_in_own_body(&mut self, decl: &SyntaxNode) {
        let db = self.db;
        let Some(body) = decl.children().find(|n| n.kind() == SyntaxKind::BLOCK) else {
            return;
        };
        for (j, src) in self.mapping.iter().enumerate() {
            let Some(i) = src else { continue };
            let (old_name, new_name) = (&self.old.params[*i].name, &self.new.params[j].name);
            if old_name == new_name {
                continue;
            }
            for token in body
                .descendants_with_tokens()
                .filter_map(|e| e.into_token())
                .filter(|t| t.kind() == SyntaxKind::IDENT && t.text() == old_name.as_str())
            {
                let Some(name_ref) = token.parent().and_then(ast::NameRef::cast) else {
                    continue;
                };
                if name_ref.syntax().parent().map(|p| p.kind()) != Some(SyntaxKind::NAME_EXPR) {
                    continue;
                }
                let inside = |range: TextRange| body.text_range().contains_range(range);
                let ours = match self.sema.classify_name_ref(self.file, &name_ref) {
                    None => true,
                    Some(Definition::Local(local)) => {
                        !inside(infer(db, local.body).local(local.id).decl_range)
                    }
                    Some(Definition::Field(field)) => Definition::Field(field)
                        .source(db)
                        .is_none_or(|s| s.file != self.file || !inside(s.full_range)),
                    Some(_) => false,
                };
                if ours {
                    self.edits
                        .replace(db, self.file, token.text_range(), new_name.as_str());
                }
            }
        }
    }

    /// 覆写链上的另一个声明：名字、返回类型、形参列表、文档注释，以及方法体里改了名的形参。
    fn rewrite_override(&mut self, file: SourceFile, decl: &SyntaxNode) -> Result<(), String> {
        let db = self.db;
        let Some(sig) = sig_of(decl) else {
            return Err(base_db::tr!(
                "{} 处的覆写方法的声明不完整",
                "The overriding declaration at {} is incomplete",
                location(db, file, decl.text_range().start())
            ));
        };
        if sig.params.len() != self.old.params.len() {
            return Ok(());
        }
        let method = ast::MethodDecl::cast(decl.clone());
        let text: &str = file.text(db);
        let slice = |r: TextRange| &text[usize::from(r.start())..usize::from(r.end())];

        if self.renamed() {
            if let Some(name) = method.as_ref().and_then(|m| m.name()) {
                self.edits
                    .replace(db, file, name.syntax().text_range(), self.new.name.as_str());
            }
        }
        let mut ret_replaced = false;
        let ret_changed =
            self.old.ret.as_deref().map(normalize) != self.new.ret.as_deref().map(normalize);
        if ret_changed
            && sig.ret.as_deref().map(normalize) == self.old.ret.as_deref().map(normalize)
        {
            let new_ret = ast::MethodDecl::cast(self.decl.clone())
                .and_then(|m| m.return_type())
                .map(|t| t.syntax().text().to_string());
            if let (Some(ret), Some(new_ret)) =
                (method.as_ref().and_then(|m| m.return_type()), new_ret)
            {
                if method.as_ref().is_some_and(|m| m.extra_dims() == 0) {
                    self.edits
                        .replace(db, file, ret.syntax().text_range(), new_ret);
                    ret_replaced = true;
                }
            }
        }

        // 形参列表
        let mut names: Vec<(Option<usize>, String)> = Vec::new();
        let mut parts: Vec<Vec<Piece>> = Vec::new();
        let mut identity = self.new.params.len() == sig.params.len();
        let mut renames: Vec<(ast::Param, String)> = Vec::new();
        let mut needs_imports: Vec<usize> = Vec::new();
        for (j, new_param) in self.new.params.iter().enumerate() {
            match self.mapping[j] {
                Some(i) => {
                    let own = &sig.params[i];
                    let old_param = &self.old.params[i];
                    let name = if own.name == old_param.name {
                        new_param.name.clone()
                    } else {
                        own.name.clone()
                    };
                    let type_changed = normalize(&old_param.ty) != normalize(&new_param.ty)
                        || old_param.varargs != new_param.varargs;
                    let own_range = own.node.syntax().text_range();
                    let piece = if !type_changed {
                        if name == own.name {
                            vec![Piece::Orig(own_range)]
                        } else {
                            renames.push((own.node.clone(), name.clone()));
                            let name_range = own.node.name().map(|n| n.syntax().text_range());
                            match name_range {
                                Some(nr) => vec![
                                    Piece::Text(
                                        slice(TextRange::new(own_range.start(), nr.start()))
                                            .to_owned(),
                                    ),
                                    Piece::Text(name.clone()),
                                    Piece::Text(
                                        slice(TextRange::new(nr.end(), own_range.end())).to_owned(),
                                    ),
                                ],
                                None => vec![Piece::Orig(own_range)],
                            }
                        }
                    } else {
                        if name != own.name {
                            renames.push((own.node.clone(), name.clone()));
                        }
                        needs_imports.push(j);
                        let modifiers = own
                            .node
                            .modifier_list()
                            .map(|m| m.syntax().text().to_string())
                            .filter(|m| !m.trim().is_empty())
                            .map(|m| format!("{} ", m.trim()))
                            .unwrap_or_default();
                        vec![Piece::Text(format!(
                            "{modifiers}{} {name}",
                            param_type_text(new_param)
                        ))]
                    };
                    identity &= i == j && piece == vec![Piece::Orig(own_range)];
                    names.push((Some(i), name));
                    parts.push(piece);
                }
                None => {
                    identity = false;
                    needs_imports.push(j);
                    names.push((None, new_param.name.clone()));
                    parts.push(vec![Piece::Text(
                        new_param.node.syntax().text().to_string().trim().to_owned(),
                    )]);
                }
            }
        }
        let list = decl
            .children()
            .find_map(ast::ParamList::cast)
            .ok_or_else(|| base_db::tr!("形参列表不完整", "Incomplete parameter list"))?;
        if let Some(inner) = paren_inner(list.syntax()) {
            let own_ranges: Vec<TextRange> = sig
                .params
                .iter()
                .map(|p| p.node.syntax().text_range())
                .collect();
            let separator = separator_of(text, &own_ranges);
            let mut pieces = Vec::new();
            for (idx, part) in parts.into_iter().enumerate() {
                if idx > 0 {
                    pieces.push(Piece::Text(separator.clone()));
                }
                pieces.extend(part);
            }
            if !identity {
                self.edits.rewrite(
                    db,
                    file,
                    Rewrite {
                        range: inner,
                        pieces,
                    },
                );
                self.rewritten_decls
                    .push((file.file_id(db), decl.text_range()));
            }
        }
        // 用到的类型在别的文件里可能还没有导入
        if file != self.file {
            let scope = self.sema.type_scope(file, list.syntax());
            let mut classes = Vec::new();
            for j in needs_imports {
                classes_in(&self.new_tys[j], &mut classes);
            }
            if ret_replaced {
                classes_in(&method_sig(db, self.method).ret, &mut classes);
            }
            for class in classes {
                if let ide_db::imports::ImportAction::Add(edit) =
                    ide_db::imports::import_action(db, file, &scope, class)
                {
                    self.edits.imports.push((file.file_id(db), edit));
                }
            }
        }
        // 方法体里改了名的形参
        for (param, name) in renames {
            let Some(param_name) = param.name() else {
                continue;
            };
            let Some(def @ Definition::Local(_)) = self.sema.classify_name(file, &param_name)
            else {
                continue;
            };
            for reference in ide_db::search::references_in_file(db, file, &def, &param_name.text())
            {
                self.edits.replace(db, file, reference.range, name.as_str());
            }
        }
        // 文档注释
        let own_names: Vec<String> = sig.params.iter().map(|p| p.name.clone()).collect();
        if let Some((range, text)) = doc_rewrite(decl, &own_names, &names) {
            self.edits.replace(db, file, range, text);
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // 用法
    // -----------------------------------------------------------------------

    fn search_files(&self) -> Vec<SourceFile> {
        let db = self.db;
        let local_only =
            self.private || (self.family.len() == 1 && in_local_class(db, self.method.class));
        if local_only {
            return hir::class_decl_file(db, self.method.class)
                .into_iter()
                .collect();
        }
        base_db::workspace(db)
            .files(db)
            .workspace_files()
            .into_iter()
            .map(|(_, file)| file)
            .collect()
    }

    fn rewrite_usages(&mut self) -> Result<(), String> {
        let db = self.db;
        let name = if self.new.is_ctor {
            self.class_name.to_string()
        } else {
            self.old.name.clone()
        };
        for file in self.search_files() {
            db.unwind_if_revision_cancelled();
            let text: &str = file.text(db);
            if !text.contains(name.as_str()) {
                continue;
            }
            let root = base_db::parse(db, file).syntax_node();
            for (offset, _) in text.match_indices(name.as_str()) {
                let Some(token) = root
                    .token_at_offset(TextSize::from(offset as u32))
                    .right_biased()
                else {
                    continue;
                };
                if token.kind() != SyntaxKind::IDENT || token.text() != name {
                    continue;
                }
                let Some(name_ref) = token.parent().and_then(ast::NameRef::cast) else {
                    continue;
                };
                let Some(parent) = name_ref.syntax().parent() else {
                    continue;
                };
                if self.new.is_ctor {
                    self.constructor_usage(file, &name_ref, &parent)?;
                } else {
                    self.method_usage(file, &name_ref, &parent)?;
                }
            }
            if self.new.is_ctor {
                for call in root
                    .descendants()
                    .filter_map(ast::ExplicitConstructorCall::cast)
                {
                    self.explicit_constructor_call(file, &call)?;
                }
            }
        }
        if self.new.is_ctor && self.in_enum {
            self.enum_constants()?;
        }
        Ok(())
    }

    fn method_usage(
        &mut self,
        file: SourceFile,
        name_ref: &ast::NameRef,
        parent: &SyntaxNode,
    ) -> Result<(), String> {
        let db = self.db;
        match parent.kind() {
            SyntaxKind::METHOD_CALL => {
                let Some(call) = ast::MethodCall::cast(parent.clone()) else {
                    return Ok(());
                };
                if call.name_ref().as_ref() != Some(name_ref) {
                    return Ok(());
                }
                let args: Vec<ast::Expr> = call
                    .arg_list()
                    .map(|l| l.args().collect())
                    .unwrap_or_default();
                let ours = match self.sema.classify_name_ref(file, name_ref) {
                    Some(Definition::Method(target)) if self.family.contains(&target) => true,
                    _ => match self.receiver_ty(file, &call) {
                        Some(receiver) => {
                            let candidates = hir::lookup_methods(db, &receiver, &self.old.name);
                            self.old_wins(file, &args, &candidates)
                        }
                        None => false,
                    },
                };
                if !ours {
                    return Ok(());
                }
                if self.renamed() {
                    self.edits.replace(
                        db,
                        file,
                        name_ref.syntax().text_range(),
                        self.new.name.as_str(),
                    );
                }
                self.rewrite_args(file, call.syntax(), call.arg_list(), &args, None)
            }
            SyntaxKind::METHOD_REF => {
                let Some(method_ref) = ast::MethodRef::cast(parent.clone()) else {
                    return Ok(());
                };
                let ours = match self.sema.classify_name_ref(file, name_ref) {
                    Some(Definition::Method(target)) => self.family.contains(&target),
                    Some(_) => false,
                    None => {
                        let receiver =
                            match (method_ref.receiver_expr(), method_ref.receiver_type()) {
                                (Some(expr), _) => self.expr_receiver_ty(file, &expr),
                                (None, Some(ty)) => Some(self.sema.resolve_type(file, &ty)),
                                _ => None,
                            };
                        receiver.is_some_and(|ty| self.relates(&ty))
                    }
                };
                if !ours {
                    return Ok(());
                }
                if !self.params_unchanged() {
                    return Err(method_ref_error(db, file, parent.text_range().start()));
                }
                if self.renamed() {
                    self.edits.replace(
                        db,
                        file,
                        name_ref.syntax().text_range(),
                        self.new.name.as_str(),
                    );
                }
                Ok(())
            }
            SyntaxKind::QUALIFIED_NAME if self.renamed() => {
                // `import static a.B.old;`
                let Some(qualified) = ast::QualifiedName::cast(parent.clone()) else {
                    return Ok(());
                };
                let Some(import) = qualified.syntax().parent().and_then(ast::ImportDecl::cast)
                else {
                    return Ok(());
                };
                if !import.is_static() || import.is_on_demand() {
                    return Ok(());
                }
                let class = qualified.qualifier().and_then(|q| {
                    let segments: Vec<SmolStr> = q.segments();
                    hir::resolve_qualified_class_visible(db, file, &segments)
                        .or_else(|| hir::resolve_qualified_class(db, &segments))
                });
                // 同名的其它方法（重载）还要用这条 import 时不改
                let others = class.is_some_and(|c| {
                    hir::lookup_methods(db, &Ty::class(c), &self.old.name)
                        .iter()
                        .any(|m| !self.family.contains(&m.id))
                });
                if class.is_some_and(|c| self.relates_class(c)) && !others {
                    self.edits.replace(
                        db,
                        file,
                        name_ref.syntax().text_range(),
                        self.new.name.as_str(),
                    );
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn constructor_usage(
        &mut self,
        file: SourceFile,
        name_ref: &ast::NameRef,
        parent: &SyntaxNode,
    ) -> Result<(), String> {
        let db = self.db;
        if parent.kind() != SyntaxKind::CLASS_TYPE {
            return Ok(());
        }
        let Some(grand) = parent.parent() else {
            return Ok(());
        };
        match grand.kind() {
            SyntaxKind::NEW_EXPR => {
                let Some(new) = ast::NewExpr::cast(grand.clone()) else {
                    return Ok(());
                };
                if new.ty().map(|t| t.syntax().clone()).as_ref() != Some(parent) {
                    return Ok(());
                }
                let args: Vec<ast::Expr> = new
                    .arg_list()
                    .map(|l| l.args().collect())
                    .unwrap_or_default();
                let ours = match self.sema.classify_name_ref(file, name_ref) {
                    Some(Definition::Method(target)) if target == self.method => true,
                    Some(Definition::Method(target)) if target.class == self.method.class => {
                        self.constructor_wins(file, &args)
                    }
                    Some(Definition::Class(class)) if class == self.method.class => {
                        self.constructor_wins(file, &args)
                    }
                    _ => false,
                };
                if ours {
                    self.rewrite_args(file, new.syntax(), new.arg_list(), &args, None)?;
                }
                Ok(())
            }
            SyntaxKind::METHOD_REF => {
                let Some(method_ref) = ast::MethodRef::cast(grand.clone()) else {
                    return Ok(());
                };
                if !method_ref.is_constructor() {
                    return Ok(());
                }
                let target = self.sema.constructor_ref_target(file, method_ref.syntax());
                if target == Some(Definition::Method(self.method)) && !self.params_unchanged() {
                    return Err(method_ref_error(db, file, grand.text_range().start()));
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn explicit_constructor_call(
        &mut self,
        file: SourceFile,
        call: &ast::ExplicitConstructorCall,
    ) -> Result<(), String> {
        let db = self.db;
        let Some(keyword) = call
            .syntax()
            .children()
            .find(|n| matches!(n.kind(), SyntaxKind::THIS_EXPR | SyntaxKind::SUPER_EXPR))
        else {
            return Ok(());
        };
        let args: Vec<ast::Expr> = call
            .arg_list()
            .map(|l| l.args().collect())
            .unwrap_or_default();
        let ours = match self.sema.explicit_constructor_target(file, &keyword) {
            Some(Definition::Method(target)) if target == self.method => true,
            Some(Definition::Method(target)) if target.class == self.method.class => {
                self.constructor_wins(file, &args)
            }
            Some(_) => false,
            None => {
                let Some(enclosing) = self.sema.enclosing_class(file, call.syntax()) else {
                    return Ok(());
                };
                let target_class = if call.is_super() {
                    hir::direct_supers(db, enclosing)
                        .iter()
                        .copied()
                        .find(|c| class_data(db, *c).is_some_and(|d| !d.is_interface()))
                } else {
                    Some(enclosing)
                };
                target_class == Some(self.method.class) && self.constructor_wins(file, &args)
            }
        };
        if ours {
            self.rewrite_args(file, call.syntax(), call.arg_list(), &args, None)?;
        }
        Ok(())
    }

    /// 枚举常量的实参调用枚举的构造器。
    fn enum_constants(&mut self) -> Result<(), String> {
        let db = self.db;
        let Some(source) = Definition::Class(self.method.class).source(db) else {
            return Ok(());
        };
        let root = base_db::parse(db, source.file).syntax_node();
        let Some(enum_decl) = root
            .covering_element(source.full_range)
            .ancestors()
            .find(|n| n.kind() == SyntaxKind::ENUM_DECL)
        else {
            return Ok(());
        };
        let constants: Vec<ast::EnumConstant> = enum_decl
            .descendants()
            .filter_map(ast::EnumConstant::cast)
            .filter(|c| {
                c.syntax()
                    .ancestors()
                    .find(|a| a.kind() == SyntaxKind::ENUM_DECL)
                    .as_ref()
                    == Some(&enum_decl)
            })
            .collect();
        for constant in constants {
            let args: Vec<ast::Expr> = constant
                .arg_list()
                .map(|l| l.args().collect())
                .unwrap_or_default();
            if !self.constructor_wins(source.file, &args) {
                continue;
            }
            let insert_at = constant.name().map(|n| n.syntax().text_range().end());
            self.rewrite_args(
                source.file,
                constant.syntax(),
                constant.arg_list(),
                &args,
                insert_at,
            )?;
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // 是不是对这个方法的调用
    // -----------------------------------------------------------------------

    fn relates_class(&self, class: ClassId) -> bool {
        self.family_classes
            .iter()
            .any(|f| hir::is_subclass_of(self.db, class, *f))
    }

    fn relates(&self, ty: &Ty) -> bool {
        let mut classes = Vec::new();
        classes_of(&ty.upper_bound(self.db), &mut classes);
        classes.into_iter().any(|c| self.relates_class(c))
    }

    fn expr_receiver_ty(&self, file: SourceFile, expr: &ast::Expr) -> Option<Ty> {
        let db = self.db;
        if let ast::Expr::SuperExpr(_) = expr {
            let enclosing = self.sema.enclosing_class(file, expr.syntax())?;
            let sup = hir::direct_supers(db, enclosing)
                .iter()
                .copied()
                .find(|c| class_data(db, *c).is_some_and(|d| !d.is_interface()))?;
            return Some(Ty::class(sup));
        }
        if let Some(ty) = self.sema.type_of_expr(file, expr) {
            if !matches!(ty, Ty::Unknown) {
                return Some(ty);
            }
        }
        // `Util.foo()`：接收者是类名
        let name_ref = match expr {
            ast::Expr::NameExpr(name) => name.syntax().children().find_map(ast::NameRef::cast),
            ast::Expr::FieldAccess(access) => access.name_ref(),
            _ => None,
        }?;
        match self.sema.classify_name_ref(file, &name_ref)? {
            Definition::Class(class) => Some(Ty::class(class)),
            _ => None,
        }
    }

    /// 在修改之前，这个调用在哪个类型里找名字为旧名字的方法。和覆写链无关时为 `None`。
    fn receiver_ty(&self, file: SourceFile, call: &ast::MethodCall) -> Option<Ty> {
        let db = self.db;
        if let Some(receiver) = call.receiver() {
            let ty = self.expr_receiver_ty(file, &receiver)?;
            return self.relates(&ty).then_some(ty);
        }
        // 不带限定：由内向外第一个有这个名字的方法的类
        let mut class = self.sema.enclosing_class(file, call.syntax());
        while let Some(current) = class {
            let ty = hir::this_ty(db, current);
            if self.relates_class(current) {
                return Some(ty);
            }
            if !hir::lookup_methods(db, &ty, &self.old.name).is_empty() {
                return None;
            }
            class = hir::outer_class(db, current)
                .or_else(|| hir::local_class_owner(db, current).map(|(owner, _)| owner));
        }
        // 静态导入
        let cu = ast::CompilationUnit::cast(base_db::parse(db, file).syntax_node())?;
        cu.imports().filter(|i| i.is_static()).find_map(|import| {
            let segments = import.name()?.segments();
            let qualifier: &[SmolStr] = if import.is_on_demand() {
                &segments
            } else if segments.last().map(|s| s.as_str()) == Some(self.old.name.as_str()) {
                &segments[..segments.len() - 1]
            } else {
                return None;
            };
            let class = hir::resolve_qualified_class_visible(db, file, qualifier)
                .or_else(|| hir::resolve_qualified_class(db, qualifier))?;
            self.relates_class(class).then(|| Ty::class(class))
        })
    }

    fn arg_types(&self, file: SourceFile, args: &[ast::Expr]) -> Vec<Option<Ty>> {
        args.iter()
            .map(|arg| match arg {
                ast::Expr::LambdaExpr(_) | ast::Expr::MethodRef(_) => None,
                _ => self.sema.type_of_expr(file, arg),
            })
            .collect()
    }

    /// 旧签名适用于这些实参，并且 `candidates` 里不在覆写链上的方法没有一个能胜过它。
    fn old_wins(
        &self,
        file: SourceFile,
        args: &[ast::Expr],
        candidates: &[hir::MethodCandidate],
    ) -> bool {
        let db = self.db;
        let arg_tys = self.arg_types(file, args);
        if !applicable(db, &self.old_tys, self.old.is_varargs(), &arg_tys) {
            return false;
        }
        !candidates.iter().any(|candidate| {
            if self.family.contains(&candidate.id) {
                return false;
            }
            let sig = method_sig(db, candidate.id);
            let params = candidate.param_tys(db);
            applicable(db, &params, sig.varargs, &arg_tys)
                && !at_least_as_specific(db, &self.old_tys, &params)
        })
    }

    fn constructor_wins(&self, file: SourceFile, args: &[ast::Expr]) -> bool {
        let candidates = hir::constructors(self.db, self.method.class, &hir::Subst::default());
        self.old_wins(file, args, &candidates)
    }

    // -----------------------------------------------------------------------
    // 实参
    // -----------------------------------------------------------------------

    /// 按新签名改写一次调用的实参。`insert_at`：没有实参列表时（枚举常量）在哪里补上括号。
    fn rewrite_args(
        &mut self,
        file: SourceFile,
        call: &SyntaxNode,
        arg_list: Option<ast::ArgList>,
        args: &[ast::Expr],
        insert_at: Option<TextSize>,
    ) -> Result<(), String> {
        let db = self.db;
        if !self.old.fits(args.len()) {
            // 已经按新签名写好了，或者本来就不对：不动
            return Ok(());
        }
        let n = self.old.params.len();
        let groups: Vec<Vec<&ast::Expr>> = (0..n)
            .map(|i| {
                if self.old.is_varargs() && i == n - 1 {
                    args[i.min(args.len())..].iter().collect()
                } else {
                    vec![&args[i]]
                }
            })
            .collect();
        // 删掉的实参不能有副作用
        for (i, group) in groups.iter().enumerate() {
            if self.mapping.contains(&Some(i)) {
                continue;
            }
            if let Some(arg) = group.iter().find(|a| has_side_effects(a.syntax())) {
                return Err(base_db::tr!(
                    "{} 处要删除的实参 `{}` 有副作用，不能直接去掉",
                    "The argument `{}` at {} would be removed but has side effects",
                    arg.syntax().text(),
                    location(db, file, arg.syntax().text_range().start())
                ));
            }
        }
        // 有副作用的实参之间的先后不能变
        let impure_order: Vec<usize> = self
            .mapping
            .iter()
            .flatten()
            .copied()
            .filter(|i| groups[*i].iter().any(|a| has_side_effects(a.syntax())))
            .collect();
        if impure_order.windows(2).any(|w| w[0] > w[1]) {
            return Err(base_db::tr!(
                "{} 处重排实参会改变它们的副作用发生的先后",
                "Reordering the arguments at {} would change the order of their side effects",
                location(db, file, call.text_range().start())
            ));
        }
        if self.params_unchanged() {
            return Ok(());
        }

        let separator = separator_of(
            file.text(db),
            &args
                .iter()
                .map(|a| a.syntax().text_range())
                .collect::<Vec<_>>(),
        );
        let mut pieces: Vec<Piece> = Vec::new();
        for (j, new_param) in self.new.params.iter().enumerate() {
            let part: Vec<Piece> = match self.mapping[j] {
                Some(i) => {
                    let group = &groups[i];
                    let old_param = &self.old.params[i];
                    if old_param.varargs && !new_param.varargs {
                        let single_array = group.len() == 1
                            && matches!(
                                self.sema.type_of_expr(file, group[0]),
                                Some(Ty::Array(_)) | Some(Ty::Null)
                            );
                        if single_array {
                            vec![Piece::Orig(group[0].syntax().text_range())]
                        } else {
                            let mut part = vec![Piece::Text(format!("new {}[]{{", old_param.ty))];
                            for (k, arg) in group.iter().enumerate() {
                                if k > 0 {
                                    part.push(Piece::Text(", ".to_owned()));
                                }
                                part.push(Piece::Orig(arg.syntax().text_range()));
                            }
                            part.push(Piece::Text("}".to_owned()));
                            part
                        }
                    } else {
                        let mut part = Vec::new();
                        for (k, arg) in group.iter().enumerate() {
                            if k > 0 {
                                part.push(Piece::Text(separator.clone()));
                            }
                            part.push(Piece::Orig(arg.syntax().text_range()));
                        }
                        part
                    }
                }
                None if new_param.varargs => Vec::new(),
                None => vec![Piece::Text(self.argument_for(file, call, j))],
            };
            if part.is_empty() {
                continue;
            }
            if !pieces.is_empty() {
                pieces.push(Piece::Text(separator.clone()));
            }
            pieces.extend(part);
        }
        match arg_list {
            Some(list) => {
                if let Some(inner) = paren_inner(list.syntax()) {
                    self.edits.rewrite(
                        db,
                        file,
                        Rewrite {
                            range: inner,
                            pieces,
                        },
                    );
                }
            }
            None => {
                if let (Some(at), false) = (insert_at, pieces.is_empty()) {
                    let mut all = vec![Piece::Text("(".to_owned())];
                    all.extend(pieces);
                    all.push(Piece::Text(")".to_owned()));
                    self.edits.rewrite(
                        db,
                        file,
                        Rewrite {
                            range: TextRange::empty(at),
                            pieces: all,
                        },
                    );
                }
            }
        }
        Ok(())
    }

    /// 新增形参在调用处传什么：作用域里同名、类型相容的变量，否则是类型的默认值。
    fn argument_for(&self, file: SourceFile, call: &SyntaxNode, j: usize) -> String {
        let db = self.db;
        let name = &self.new.params[j].name;
        let ty = &self.new_tys[j];
        let offset = call.text_range().start();
        // 在一个同样加上了这个形参的覆写方法里（比如 `super.f(...)`）：直接传它
        let file_id = file.file_id(db);
        if self
            .rewritten_decls
            .iter()
            .any(|(f, range)| *f == file_id && range.contains(offset))
        {
            return name.clone();
        }
        if let Some(body) = self.sema.body_of(file, call) {
            let root = base_db::parse(db, file).syntax_node();
            let result = infer(db, body);
            let found = result.locals().iter().any(|local| {
                local.name == name.as_str()
                    && local_in_scope(&root, local, offset)
                    && assignable(db, Some(&local.ty), ty)
            });
            if found {
                return name.clone();
            }
        }
        if let Some(class) = self.sema.enclosing_class(file, call) {
            if let Some(field) = hir::lookup_field(db, &hir::this_ty(db, class), name) {
                if assignable(db, Some(&field.ty), ty) {
                    return name.clone();
                }
            }
        }
        default_value(ty).to_owned()
    }
}

fn method_ref_error(db: &dyn Db, file: SourceFile, offset: TextSize) -> String {
    base_db::tr!(
        "{} 处的方法引用和新的形参列表对不上，请先把它转换成 lambda",
        "The method reference at {} does not fit the new parameter list; convert it to a lambda first",
        location(db, file, offset)
    )
}

/// 局部类、匿名类或者它们的成员类。
fn in_local_class(db: &dyn Db, class: ClassId) -> bool {
    class
        .binary_name(db)
        .split('$')
        .skip(1)
        .any(|part| part.starts_with(|c: char| c.is_ascii_digit()))
}

/// 按旧签名（名字、参数个数和类型）和 `method` 处在同一条覆写链上的其它方法。
fn old_family(db: &dyn Db, method: MethodId, name: &str, old_tys: &[Ty]) -> Vec<MethodId> {
    let matches = |candidate: MethodId| -> bool {
        let Some(data) = class_data(db, candidate.class) else {
            return false;
        };
        let Some(m) = data.methods.get(candidate.idx as usize) else {
            return false;
        };
        if m.is_constructor
            || m.flags.is_static()
            || m.flags.visibility() == Visibility::Private
            || m.params.len() != old_tys.len()
        {
            return false;
        }
        method_sig(db, candidate)
            .params
            .iter()
            .zip(old_tys)
            .all(|(a, b)| loosely_same(a, b))
    };
    let mut res: Vec<MethodId> = Vec::new();
    let mut seen: FxHashSet<MethodId> = FxHashSet::default();
    seen.insert(method);
    for sup in hir::all_supers(db, method.class).iter().copied() {
        let Some(data) = class_data(db, sup) else {
            continue;
        };
        for (idx, _) in data.methods_named(name) {
            let candidate = MethodId { class: sup, idx };
            if matches(candidate) && seen.insert(candidate) {
                res.push(candidate);
            }
        }
    }
    let mut roots: Vec<ClassId> = vec![method.class];
    roots.extend(res.iter().map(|m| m.class));
    for root in roots {
        for sub in all_subclasses(db, root) {
            let Some(data) = class_data(db, sub) else {
                continue;
            };
            for (idx, _) in data.methods_named(name) {
                let candidate = MethodId { class: sub, idx };
                if matches(candidate) && seen.insert(candidate) {
                    res.push(candidate);
                }
            }
        }
    }
    res
}

fn covering_decl(root: &SyntaxNode, range: TextRange) -> Option<SyntaxNode> {
    if !root.text_range().contains_range(range) {
        return None;
    }
    let element = root.covering_element(range);
    let start = match element {
        syntax::NodeOrToken::Node(node) => node,
        syntax::NodeOrToken::Token(token) => token.parent()?,
    };
    start.ancestors().find(|n| {
        matches!(
            n.kind(),
            SyntaxKind::METHOD_DECL | SyntaxKind::CONSTRUCTOR_DECL
        )
    })
}

/// 括号之间（不含括号）的范围。
fn paren_inner(list: &SyntaxNode) -> Option<TextRange> {
    let open = list
        .children_with_tokens()
        .filter_map(|e| e.into_token())
        .find(|t| t.kind() == SyntaxKind::L_PAREN)?;
    let close = list
        .last_token()
        .filter(|t| t.kind() == SyntaxKind::R_PAREN)?;
    (open.text_range().end() <= close.text_range().start())
        .then(|| TextRange::new(open.text_range().end(), close.text_range().start()))
}

/// 列表元素之间原来的分隔（多行书写时保留换行和缩进），默认 `", "`。
fn separator_of(text: &str, ranges: &[TextRange]) -> String {
    match ranges {
        [first, second, ..] if first.end() <= second.start() => {
            let between = &text[usize::from(first.end())..usize::from(second.start())];
            if between.trim() == "," {
                between.to_owned()
            } else {
                ", ".to_owned()
            }
        }
        _ => ", ".to_owned(),
    }
}

/// 写在覆写方法里的新形参类型：类型原文，可变参数加上 `...`。
fn param_type_text(param: &SigParam) -> String {
    if param.varargs {
        format!("{}...", param.ty.trim())
    } else {
        param.ty.trim().to_owned()
    }
}

/// 改写文档注释里的 `@param`：按新的形参顺序排列，改名的换成新名字，删掉的去掉，新增的补上
/// 空的标签。`names_before` 是文档注释现在写的形参名（按旧顺序），`targets` 是每个新形参
/// 对应的旧形参和它的新名字。没有 `@param` 的文档注释不改。
fn doc_rewrite(
    decl: &SyntaxNode,
    names_before: &[String],
    targets: &[(Option<usize>, String)],
) -> Option<(TextRange, String)> {
    let doc = match ast::MethodDecl::cast(decl.clone()) {
        Some(method) => method.doc_comment(),
        None => ast::ConstructorDecl::cast(decl.clone())?.doc_comment(),
    }?;
    let text = doc.text();
    if !text.contains('\n') {
        return None;
    }
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    // 每一行去掉开头的空白和 `*` 之后的内容
    let content = |line: &str| -> Option<String> {
        let trimmed = line.trim_start();
        if trimmed.starts_with("*/") || trimmed.starts_with("/**") {
            return None;
        }
        Some(trimmed.trim_start_matches('*').trim_start().to_owned())
    };
    let tag_name = |line: &str| -> Option<String> {
        let content = content(line)?;
        let rest = content.strip_prefix("@param")?;
        if !rest.starts_with(char::is_whitespace) {
            return None;
        }
        let name: String = rest
            .trim_start()
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '$')
            .collect();
        (!name.is_empty()).then_some(name)
    };
    // 形参标签：从 `@param x` 那一行到下一个块标签或注释结尾之前
    let mut segments: Vec<(String, std::ops::Range<usize>)> = Vec::new();
    let mut idx = 0;
    while idx < lines.len() {
        if let Some(name) = tag_name(lines[idx]) {
            let start = idx;
            idx += 1;
            while idx < lines.len() {
                match content(lines[idx]) {
                    None => break,
                    Some(c) if c.starts_with('@') => break,
                    Some(_) => idx += 1,
                }
            }
            segments.push((name, start..idx));
        } else {
            idx += 1;
        }
    }
    let first = segments.first()?.1.start;
    let prefix: String = {
        let line = lines[first];
        let at = line.find("@param")?;
        line[..at].to_owned()
    };
    let mut block = String::new();
    for (src, name) in targets {
        match src {
            Some(i) => {
                let old_name = names_before.get(*i)?;
                let Some((_, range)) = segments.iter().find(|(n, _)| n == old_name) else {
                    continue;
                };
                for (k, line) in lines[range.clone()].iter().enumerate() {
                    if k == 0 && old_name != name {
                        let at = line.find("@param")? + "@param".len();
                        let rest = &line[at..];
                        let ws = rest.len() - rest.trim_start().len();
                        let name_start = at + ws;
                        block.push_str(&line[..name_start]);
                        block.push_str(name);
                        block.push_str(&line[name_start + old_name.len()..]);
                    } else {
                        block.push_str(line);
                    }
                }
            }
            None => {
                block.push_str(&prefix);
                block.push_str("@param ");
                block.push_str(name);
                block.push('\n');
            }
        }
    }
    let in_segment = |line: usize| segments.iter().any(|(_, r)| r.contains(&line));
    let mut out = String::new();
    for (k, line) in lines.iter().enumerate() {
        if k == first {
            out.push_str(&block);
        }
        if !in_segment(k) {
            out.push_str(line);
        }
    }
    (out != text).then(|| (doc.text_range(), out))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn params(header: &str) -> Vec<SigParam> {
        parse_header(header).unwrap().params
    }

    #[test]
    fn parameters_match_by_name_then_position() {
        let old = params("void f(int a, int b)");
        assert_eq!(
            map_params(&old, &params("void f(int b, int a)")),
            vec![Some(1), Some(0)]
        );
        assert_eq!(
            map_params(&old, &params("void f(int a, int x)")),
            vec![Some(0), Some(1)]
        );
        assert_eq!(
            map_params(&old, &params("void f(int a, String s, int b)")),
            vec![Some(0), None, Some(1)]
        );
        assert_eq!(map_params(&old, &params("void f(int b)")), vec![Some(1)]);
    }

    #[test]
    fn normalizes_type_text() {
        assert_eq!(
            normalize("Map< String ,  List<Integer> >"),
            "Map<String,List<Integer>>"
        );
        assert_eq!(normalize("final  int"), "final int");
    }

    #[test]
    fn param_tags_follow_the_new_order() {
        let text = "class A {\n    /**\n     * Does it.\n     *\n     * @param a the a\n     * @param b the b\n     *        more b\n     * @return x\n     */\n    int f(int b, int c) { return 0; }\n}\n";
        let root = ast::CompilationUnit::parse(text).syntax_node();
        let decl = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::METHOD_DECL)
            .unwrap();
        let (_, doc) = doc_rewrite(
            &decl,
            &["a".to_owned(), "b".to_owned()],
            &[(Some(1), "b".to_owned()), (None, "c".to_owned())],
        )
        .unwrap();
        assert_eq!(
            doc,
            "/**\n     * Does it.\n     *\n     * @param b the b\n     *        more b\n     * @param c\n     * @return x\n     */"
        );
    }
}
