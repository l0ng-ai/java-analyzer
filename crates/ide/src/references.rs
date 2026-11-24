//! 查找引用、文档内高亮。

use base_db::Db;
use hir::{AccessorKind, Definition};
use ide_db::search::{find_references_with_docs, references_in_file, ReferenceKind};
use syntax::TextRange;

use crate::{
    navigation::{definition_at, position_file},
    rename::{accessor_origin, field_accessors},
    FileId, FilePosition,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReferenceItem {
    pub file_id: FileId,
    pub range: TextRange,
    pub is_write: bool,
    pub is_declaration: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HighlightedRange {
    pub range: TextRange,
    pub is_write: bool,
}

fn declaration_item(db: &dyn Db, def: &Definition) -> Option<ReferenceItem> {
    let source = def.source(db)?;
    Some(ReferenceItem {
        file_id: source.file.file_id(db),
        range: source.focus_range,
        is_write: false,
        is_declaration: true,
    })
}

pub(crate) fn find_all_refs(
    db: &dyn Db,
    position: FilePosition,
    include_declaration: bool,
) -> Option<Vec<ReferenceItem>> {
    let file = position_file(db, position)?;
    let (_, def) = definition_at(db, file, position.offset).or_else(|| {
        // 端点方法映射注解里的路径：按方法本身查
        let name = crate::endpoints::method_name_at_literal(db, file, position.offset)?;
        definition_at(db, file, name)
    })?;

    let mut res: Vec<ReferenceItem> = Vec::new();
    for (target, setter) in accessor_group(db, &def) {
        res.extend(
            find_references_with_docs(db, &target)
                .into_iter()
                .map(|reference| ReferenceItem {
                    file_id: reference.file_id,
                    range: reference.range,
                    is_write: setter || reference.kind == ReferenceKind::Write,
                    is_declaration: false,
                }),
        );
    }
    // 服务端控制器方法：调用它的 HTTP 客户端方法（Feign / HTTP 接口）也算引用；
    // 反过来，客户端方法对应的服务端方法也列出来
    // Spring Bean（类或 `@Bean` 方法）：收到它的注入点也算引用
    let injection_points = crate::beans::injection_points_of(db, &def);
    for (file_id, range) in crate::endpoints::clients_of_method(db, &def)
        .into_iter()
        .chain(crate::endpoints::servers_of_client(db, &def))
        .chain(injection_points)
    {
        res.push(ReferenceItem {
            file_id,
            range,
            is_write: false,
            is_declaration: false,
        });
    }
    if include_declaration {
        res.extend(declaration_item(db, &def));
    }
    res.sort_by_key(|item| (item.file_id, item.range.start()));
    res.dedup_by_key(|item| (item.file_id, item.range));
    Some(res)
}

/// 查引用时一起查的定义，以及它的调用是否算写入字段。
///
/// 字段和 Lombok 为它生成的访问器（getter / setter / wither、构建器方法）算一组：
/// 从字段或者任一访问器出发，都列出字段的直接访问和全部访问器的调用点，setter 的调用算写入。
fn accessor_group(db: &dyn Db, def: &Definition) -> Vec<(Definition, bool)> {
    let field = match def {
        Definition::Field(field) => Some(*field),
        Definition::Method(method) => accessor_origin(db, *method).map(|(field, _)| field),
        _ => None,
    };
    let Some(field) = field else {
        return vec![(def.clone(), false)];
    };
    let mut res = vec![(Definition::Field(field), false)];
    for (accessor, kind) in field_accessors(db, field) {
        res.push((Definition::Method(accessor), kind == AccessorKind::Setter));
    }
    res
}

/// 当前文件里与光标下符号相同的所有出现位置。
pub(crate) fn highlight_related(
    db: &dyn Db,
    position: FilePosition,
) -> Option<Vec<HighlightedRange>> {
    let file = position_file(db, position)?;
    let (_, def) = definition_at(db, file, position.offset)?;
    let name = def.name(db)?;

    let mut res: Vec<HighlightedRange> = references_in_file(db, file, &def, &name)
        .into_iter()
        .chain(ide_db::doc_links::doc_references_in_file(
            db, file, &def, &name,
        ))
        .map(|reference| HighlightedRange {
            range: reference.range,
            is_write: reference.kind == ReferenceKind::Write,
        })
        .collect();
    if let Some(decl) = declaration_item(db, &def).filter(|d| d.file_id == position.file_id) {
        // 声明处算作写入（变量在这里被赋初值）
        let is_write = matches!(def, Definition::Local(_) | Definition::Field(_));
        res.push(HighlightedRange {
            range: decl.range,
            is_write,
        });
    }
    res.sort_by_key(|item| item.range.start());
    res.dedup_by_key(|item| item.range);
    Some(res)
}
