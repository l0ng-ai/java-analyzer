//! "一个名字指向的东西"的统一表示，以及它在源码里的位置。

use base_db::{Db, SourceFile};
use hir_def::{
    class_data, class_decl_file, source_map, ClassId, FieldId, GenericOwner, MethodId, Name,
    TypeParamId,
};
use hir_ty::{body_syntax, infer, BodyId, LocalId};
use smol_str::SmolStr;
use syntax::{
    ast::{self, AstNode},
    SyntaxNode, TextRange,
};

/// 方法体里的一个局部符号（局部变量、形参、lambda 形参、模式变量 …）。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LocalDef {
    pub body: BodyId,
    pub id: LocalId,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Definition {
    Class(ClassId),
    Field(FieldId),
    Method(MethodId),
    Local(LocalDef),
    TypeParam(TypeParamId),
    /// 斜杠形式的包名
    Package(SmolStr),
}

/// 声明在源码里的位置。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct DeclSource {
    pub file: SourceFile,
    /// 整个声明的范围
    pub full_range: TextRange,
    /// 名字的范围（跳转后光标落在这里）
    pub focus_range: TextRange,
}

fn name_range(node: &SyntaxNode) -> Option<TextRange> {
    node.children()
        .find_map(ast::Name::cast)
        .map(|n| n.syntax().text_range())
}

fn decl_source(db: &dyn Db, class: ClassId, decl: Option<u32>) -> Option<DeclSource> {
    // 依赖库的类在对应的库源码文件打开时也有声明位置
    let file = class_decl_file(db, class)?;
    let ptr = source_map(db, file).get(decl?)?;
    let root = base_db::parse(db, file).syntax_node();
    let node = ptr.try_to_node(&root)?;
    let full_range = node.text_range();
    Some(DeclSource {
        file,
        full_range,
        focus_range: name_range(&node).unwrap_or(full_range),
    })
}

impl Definition {
    pub fn name(&self, db: &dyn Db) -> Option<Name> {
        match self {
            Definition::Class(class) => class_data(db, *class).map(|d| d.name.clone()),
            Definition::Field(field) => class_data(db, field.class)?
                .fields
                .get(field.idx as usize)
                .map(|f| f.name.clone()),
            Definition::Method(method) => class_data(db, method.class)?
                .methods
                .get(method.idx as usize)
                .map(|m| m.name.clone()),
            Definition::Local(local) => Some(infer(db, local.body).local(local.id).name.clone()),
            Definition::TypeParam(param) => Some(Name::new(hir_ty::type_param_name(db, *param))),
            Definition::Package(package) => package.rsplit('/').next().map(Name::new),
        }
    }

    /// 定义所属的类（局部符号返回所在体的类）。
    pub fn container_class(&self) -> Option<ClassId> {
        match self {
            Definition::Class(_) | Definition::Package(_) => None,
            Definition::Field(field) => Some(field.class),
            Definition::Method(method) => Some(method.class),
            Definition::Local(local) => Some(local.body.class()),
            Definition::TypeParam(param) => Some(match param.owner {
                GenericOwner::Class(class) => class,
                GenericOwner::Method(method) => method.class,
            }),
        }
    }

    /// 源码里的声明位置；二进制类的成员、合成成员和包没有。
    pub fn source(&self, db: &dyn Db) -> Option<DeclSource> {
        match self {
            Definition::Class(class) => decl_source(db, *class, class_data(db, *class)?.decl),
            Definition::Field(field) => {
                let data = class_data(db, field.class)?;
                decl_source(db, field.class, data.fields.get(field.idx as usize)?.decl)
            }
            Definition::Method(method) => {
                let data = class_data(db, method.class)?;
                decl_source(
                    db,
                    method.class,
                    data.methods.get(method.idx as usize)?.decl,
                )
            }
            Definition::Local(local) => {
                let (file, _) = body_syntax(db, local.body)?;
                let range = infer(db, local.body).local(local.id).decl_range;
                Some(DeclSource {
                    file,
                    full_range: range,
                    focus_range: range,
                })
            }
            Definition::TypeParam(param) => {
                let owner_source = match param.owner {
                    GenericOwner::Class(class) => Definition::Class(class).source(db)?,
                    GenericOwner::Method(method) => Definition::Method(method).source(db)?,
                };
                let root = base_db::parse(db, owner_source.file).syntax_node();
                let owner_node = root
                    .covering_element(owner_source.full_range)
                    .ancestors()
                    .find(|n| n.text_range() == owner_source.full_range)?;
                let list = owner_node.children().find_map(ast::TypeParamList::cast)?;
                let type_param = list.type_params().nth(param.idx as usize)?;
                let full_range = type_param.syntax().text_range();
                let focus_range = type_param
                    .name()
                    .map_or(full_range, |n| n.syntax().text_range());
                Some(DeclSource {
                    file: owner_source.file,
                    full_range,
                    focus_range,
                })
            }
            Definition::Package(_) => None,
        }
    }

    /// 声明前的文档注释原文（含 `/** */`）。
    pub fn doc_comment(&self, db: &dyn Db) -> Option<String> {
        if matches!(
            self,
            Definition::Local(_) | Definition::TypeParam(_) | Definition::Package(_)
        ) {
            return None;
        }
        let Some(source) = self.source(db) else {
            return self.library_doc_comment(db);
        };
        let root = base_db::parse(db, source.file).syntax_node();
        // 没有初始值的字段（`int count;`）的 VARIABLE_DECLARATOR 和里面的 NAME 范围相同，
        // 要跳过 NAME 才拿到声明节点
        let node = root
            .covering_element(source.full_range)
            .ancestors()
            .filter(|n| n.text_range() == source.full_range)
            .find(|n| n.kind() != syntax::SyntaxKind::NAME)?;
        // 字段的声明节点是 VARIABLE_DECLARATOR，文档注释挂在外层的 FIELD_DECL 上
        let doc_owner = if node.kind() == syntax::SyntaxKind::VARIABLE_DECLARATOR {
            node.parent()?
        } else {
            node
        };
        ast::doc_comment(&doc_owner).map(|token| token.text().to_owned())
    }

    /// 依赖库 / JDK 里的定义：文档注释来自源码包（`src.zip`、sources jar）。
    fn library_doc_comment(&self, db: &dyn Db) -> Option<String> {
        match self {
            Definition::Class(class) => hir_def::library_class_source(db, *class)?.doc.clone(),
            Definition::Field(field) => {
                let data = class_data(db, field.class)?;
                let name = &data.fields.get(field.idx as usize)?.name;
                hir_def::library_class_source(db, field.class)?
                    .fields
                    .get(name)
                    .cloned()
            }
            Definition::Method(method) => hir_def::library_method_source(db, *method)?.doc,
            _ => None,
        }
    }
}
