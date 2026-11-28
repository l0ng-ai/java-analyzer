//! 查找引用。
//!
//! 先按名字做纯文本筛选（绝大多数文件根本不含这个标识符），
//! 只对命中的位置做语义确认，避免对整个工作区做类型推断。

use base_db::{workspace, Db, FileId, FileKind, SourceFile};
use hir::{
    class_data, class_decl_file, is_subclass_of, method_sig, ClassKind, Definition, MethodId,
    Modifiers, Semantics, Visibility,
};
use syntax::{
    ast::{self, AstNode},
    SyntaxKind, SyntaxNode, TextRange, TextSize,
};

use crate::definition_flags;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReferenceKind {
    Read,
    Write,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Reference {
    pub file_id: FileId,
    pub range: TextRange,
    pub kind: ReferenceKind,
}

/// 两个方法是否处于同一条覆写链上（同名、同参数个数与类型、所在类有继承关系）。
fn same_method_family(db: &dyn Db, a: MethodId, b: MethodId) -> bool {
    if a == b {
        return true;
    }
    let (Some(a_data), Some(b_data)) = (class_data(db, a.class), class_data(db, b.class)) else {
        return false;
    };
    let (Some(a_method), Some(b_method)) = (
        a_data.methods.get(a.idx as usize),
        b_data.methods.get(b.idx as usize),
    ) else {
        return false;
    };
    if a_method.is_constructor
        || b_method.is_constructor
        || a_method.name != b_method.name
        || a_method.params.len() != b_method.params.len()
        || a_method.flags.is_static()
        || b_method.flags.is_static()
    {
        return false;
    }
    if !is_subclass_of(db, a.class, b.class) && !is_subclass_of(db, b.class, a.class) {
        return false;
    }
    // 形参类型按"类是否相同"粗略比较，足以区分重载
    let a_sig = method_sig(db, a);
    let b_sig = method_sig(db, b);
    a_sig
        .params
        .iter()
        .zip(b_sig.params.iter())
        .all(|(pa, pb)| match (pa, pb) {
            (hir::Ty::Class(ca, _), hir::Ty::Class(cb, _)) => ca == cb,
            (hir::Ty::Primitive(x), hir::Ty::Primitive(y)) => x == y,
            (hir::Ty::Array(_), hir::Ty::Array(_)) => true,
            (hir::Ty::TypeParam(_), _) | (_, hir::Ty::TypeParam(_)) => true,
            (hir::Ty::Unknown, _) | (_, hir::Ty::Unknown) => true,
            _ => false,
        })
}

/// `found`（某处名字解析到的定义）是否算作对 `target` 的引用。
pub fn refers_to(db: &dyn Db, found: &Definition, target: &Definition) -> bool {
    if found == target {
        return true;
    }
    match (found, target) {
        // `new Foo()` 解析到构造器，同时也是对类 Foo 的引用
        (Definition::Method(method), Definition::Class(class)) => {
            method.class == *class
                && class_data(db, method.class)
                    .and_then(|d| d.methods.get(method.idx as usize).map(|m| m.is_constructor))
                    .unwrap_or(false)
        }
        (Definition::Method(found), Definition::Method(target)) => {
            same_method_family(db, *found, *target)
        }
        // 记录的隐式访问器 `p.x()` 也是对组件 `x` 的引用
        (Definition::Method(method), Definition::Field(field)) => {
            method.class == field.class
                && class_data(db, method.class).is_some_and(|data| {
                    let accessor = data.methods.get(method.idx as usize);
                    let component = data.fields.get(field.idx as usize);
                    matches!((accessor, component), (Some(m), Some(f))
                        if data.kind == ClassKind::Record
                            && m.flags.contains(Modifiers::SYNTHETIC)
                            && m.params.is_empty()
                            && !f.flags.is_static()
                            && m.name == f.name)
                })
        }
        _ => false,
    }
}

/// 需要搜索哪些文件。
fn search_scope(db: &dyn Db, def: &Definition) -> Vec<(FileId, SourceFile)> {
    let single = |class| {
        class_decl_file(db, class)
            .map(|file| vec![(file.file_id(db), file)])
            .unwrap_or_default()
    };
    match def {
        Definition::Local(local) => single(local.body.class()),
        Definition::TypeParam(_) => def.container_class().map(single).unwrap_or_default(),
        Definition::Field(_) | Definition::Method(_)
            if definition_flags(db, def).visibility() == Visibility::Private
                && !is_record_component(db, def) =>
        {
            def.container_class().map(single).unwrap_or_default()
        }
        // 局部类 / 匿名类（及其成员类）只在声明它的文件里可见
        Definition::Class(class) if in_local_class(db, *class) => single(*class),
        Definition::Field(field) if in_local_class(db, field.class) => single(field.class),
        // 覆写父类型方法的除外：通过父类型的调用也算引用
        Definition::Method(method)
            if in_local_class(db, method.class) && !overrides_something(db, *method) =>
        {
            single(method.class)
        }
        _ => {
            let files = workspace(db).files(db);
            let mut res = files.workspace_files();
            // 依赖库里的符号：打开的库源码文件里的用法也算（库源码文件里的高亮、引用）
            let class = match def {
                Definition::Class(class) => Some(*class),
                _ => def.container_class(),
            };
            let is_library = class
                .is_some_and(|class| class_data(db, class).is_some_and(|data| !data.is_source));
            if is_library {
                let mut library: Vec<(FileId, SourceFile)> = files
                    .iter()
                    .filter(|(_, entry)| matches!(entry.kind, FileKind::Library))
                    .map(|(id, entry)| (id, entry.source))
                    .collect();
                library.sort_by_key(|(id, _)| *id);
                res.extend(library);
            }
            res
        }
    }
}

/// 记录组件对应的私有字段：通过公开的访问器 `p.x()` 在别的文件里也会引用到它。
fn is_record_component(db: &dyn Db, def: &Definition) -> bool {
    let Definition::Field(field) = def else {
        return false;
    };
    class_data(db, field.class).is_some_and(|data| {
        data.kind == ClassKind::Record
            && data
                .fields
                .get(field.idx as usize)
                .is_some_and(|f| !f.flags.is_static())
    })
}

/// 构造器：`super(...)` / `this(...)` 里没有类名，按关键字找。
fn is_constructor(db: &dyn Db, def: &Definition) -> bool {
    let Definition::Method(method) = def else {
        return false;
    };
    class_data(db, method.class)
        .and_then(|data| {
            data.methods
                .get(method.idx as usize)
                .map(|m| m.is_constructor)
        })
        .unwrap_or(false)
}

/// 文件里调用 `def`（构造器）的 `super(...)` / `this(...)`。
fn explicit_constructor_calls(
    db: &dyn Db,
    file: SourceFile,
    root: &SyntaxNode,
    def: &Definition,
) -> Vec<Reference> {
    let text = file.text(db);
    let sema = Semantics::new(db);
    let mut res = Vec::new();
    for keyword in ["super", "this"] {
        for (offset, _) in text.match_indices(keyword) {
            let Some(token) = root
                .token_at_offset(TextSize::from(offset as u32))
                .right_biased()
            else {
                continue;
            };
            if !matches!(token.kind(), SyntaxKind::SUPER_KW | SyntaxKind::THIS_KW) {
                continue;
            }
            let Some(parent) = token.parent() else {
                continue;
            };
            if sema.explicit_constructor_target(file, &parent).as_ref() == Some(def) {
                res.push(Reference {
                    file_id: file.file_id(db),
                    range: token.text_range(),
                    kind: ReferenceKind::Read,
                });
            }
        }
    }
    res
}

/// 局部类、匿名类或者它们的成员类：二进制名里有以数字开头的一段（`Outer$1Local`、`Outer$1`）。
fn in_local_class(db: &dyn Db, class: hir::ClassId) -> bool {
    class
        .binary_name(db)
        .split('$')
        .skip(1)
        .any(|part| part.starts_with(|c: char| c.is_ascii_digit()))
        && class_data(db, class).is_some_and(|data| data.is_source)
}

/// 父类型里有同名、同参数个数的方法（可能被 `method` 覆写）。
fn overrides_something(db: &dyn Db, method: MethodId) -> bool {
    let Some(data) = class_data(db, method.class) else {
        return true;
    };
    let Some(m) = data.methods.get(method.idx as usize) else {
        return true;
    };
    hir::all_supers(db, method.class)
        .iter()
        .copied()
        .any(|sup| {
            class_data(db, sup).is_none_or(|sup_data| {
                sup_data
                    .methods_named(&m.name)
                    .any(|(_, other)| other.params.len() == m.params.len())
            })
        })
}

/// 名字引用所在的表达式是不是被写入（赋值的左侧、`++` / `--` 的操作数）。
fn is_write_access(name_ref: &SyntaxNode) -> bool {
    let Some(expr) = name_ref
        .parent()
        .filter(|p| matches!(p.kind(), SyntaxKind::NAME_EXPR | SyntaxKind::FIELD_ACCESS))
    else {
        return false;
    };
    let Some(parent) = expr.parent() else {
        return false;
    };
    match parent.kind() {
        SyntaxKind::ASSIGN_EXPR => parent.first_child().is_some_and(|first| first == expr),
        SyntaxKind::UNARY_EXPR | SyntaxKind::POSTFIX_EXPR => parent
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .any(|t| matches!(t.kind(), SyntaxKind::PLUS_PLUS | SyntaxKind::MINUS_MINUS)),
        _ => false,
    }
}

/// 在一个文件里找对 `def` 的引用（不含声明本身）。
pub fn references_in_file(
    db: &dyn Db,
    file: SourceFile,
    def: &Definition,
    name: &str,
) -> Vec<Reference> {
    let text = file.text(db);
    if name.is_empty() || !text.contains(name) {
        return Vec::new();
    }
    let sema = Semantics::new(db);
    let root = base_db::parse(db, file).syntax_node();
    let file_id = file.file_id(db);
    let mut res = Vec::new();
    if is_constructor(db, def) {
        res.extend(explicit_constructor_calls(db, file, &root, def));
    }

    for (offset, _) in text.match_indices(name) {
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
        let Some(found) = sema.classify_name_ref(file, &name_ref) else {
            continue;
        };
        if refers_to(db, &found, def) {
            let kind = if is_write_access(name_ref.syntax()) {
                ReferenceKind::Write
            } else {
                ReferenceKind::Read
            };
            res.push(Reference {
                file_id,
                range: token.text_range(),
                kind,
            });
        }
    }
    res
}

/// 在整个搜索范围里找代码里对 `def` 的引用（不含声明本身，不含文档注释里的提及）。
/// 要按引用改写代码的重构用它。
pub fn find_references(db: &dyn Db, def: &Definition) -> Vec<Reference> {
    search(db, def, false)
}

/// 同 [`find_references`]，另外加上文档注释里的 `{@link}`、`@see`、`@param` 等。
/// 查找引用、重命名用它。
pub fn find_references_with_docs(db: &dyn Db, def: &Definition) -> Vec<Reference> {
    search(db, def, true)
}

fn search(db: &dyn Db, def: &Definition, docs: bool) -> Vec<Reference> {
    let Some(name) = def.name(db) else {
        return Vec::new();
    };
    let scope = search_scope(db, def);
    // 文件多时分块在多个线程上并行搜索（每块一个共享存储的数据库句柄）
    const PARALLEL_MIN_FILES: usize = 256;
    if scope.len() >= PARALLEL_MIN_FILES {
        let chunk_size = scope
            .len()
            .div_ceil(rayon::current_num_threads() * 4)
            .max(32);
        let forks: Option<Vec<Box<dyn Db + Send>>> = scope
            .chunks(chunk_size)
            .map(|_| db.fork_for_thread())
            .collect();
        if let Some(forks) = forks {
            use rayon::prelude::*;
            let chunks: Vec<Vec<Reference>> = scope
                .par_chunks(chunk_size)
                .zip(forks)
                .map(|(chunk, fork)| {
                    let db = &*fork;
                    let mut res = Vec::new();
                    for (_, file) in chunk {
                        // 被新的编辑取消时在这里展开，由调用方的取消处理接住
                        db.unwind_if_revision_cancelled();
                        res.extend(references_in_file(db, *file, def, &name));
                        if docs {
                            res.extend(crate::doc_links::doc_references_in_file(
                                db, *file, def, &name,
                            ));
                        }
                    }
                    res
                })
                .collect();
            return chunks.into_iter().flatten().collect();
        }
    }
    let mut res = Vec::new();
    for (_, file) in scope {
        // 引用搜索可能很久；每个文件检查一次是否已被新的编辑取消
        db.unwind_if_revision_cancelled();
        res.extend(references_in_file(db, file, def, &name));
        if docs {
            res.extend(crate::doc_links::doc_references_in_file(
                db, file, def, &name,
            ));
        }
    }
    res
}
