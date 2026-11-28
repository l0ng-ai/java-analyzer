//! Spring Boot 配置文件（`application*.properties` / `.yml`）里的悬停和跳转：
//! 键的类型、默认值、说明，以及跳到绑定它的 `@ConfigurationProperties` 成员（或依赖库里的类）。

use base_db::{Db, ResourceFile};
use hir::{Definition, FieldId, MethodId};
use ide_db::{
    javadoc::javadoc_to_markdown,
    spring,
    spring_metadata::{GroupMeta, KeyMatch, MetadataSet, PropertyDecl, PropertyMeta},
};
use syntax::TextSize;

use crate::{
    hover::HoverResult,
    navigation::{to_nav, NavigationTarget},
    RangeInfo,
};

fn decl_definition(decl: PropertyDecl) -> Definition {
    match decl {
        PropertyDecl::Field(field) => Definition::Field(field),
        PropertyDecl::Setter(method) => Definition::Method(method),
    }
}

/// 字段的初值（源码里写的样子），用作默认值：`private int port = 8080;` → `8080`。
fn field_initializer(db: &dyn Db, field: FieldId) -> Option<String> {
    let source = Definition::Field(field).source(db)?;
    let text = source.file.text(db);
    let tail =
        text.get(usize::from(source.focus_range.end())..usize::from(source.full_range.end()))?;
    let value = tail.trim_start().strip_prefix('=')?.trim();
    let value = value.trim_end_matches(';').trim();
    (!value.is_empty() && value.len() <= 60 && !value.contains('\n')).then(|| value.to_owned())
}

fn class_display(source_type: &str) -> String {
    source_type.replace('$', ".")
}

/// 配置项的悬停内容。
pub(crate) fn property_hover(db: &dyn Db, property: &PropertyMeta) -> HoverResult {
    let default = property
        .default_value
        .clone()
        .or_else(|| match property.decl {
            Some(PropertyDecl::Field(field)) => field_initializer(db, field),
            _ => None,
        });
    let mut signature = match &property.ty {
        Some(ty) => format!("{ty} {}", property.name),
        None => property.name.clone(),
    };
    if let Some(default) = &default {
        signature.push_str(&format!(" = {default}"));
    }
    let mut docs = Vec::new();
    if let Some(deprecation) = &property.deprecation {
        let mut line = base_db::trs!("**已弃用**", "**Deprecated**").to_owned();
        if let Some(replacement) = &deprecation.replacement {
            line.push_str(&base_db::tr!(
                "，请改用 `{}`",
                ", use `{}` instead",
                replacement
            ));
        }
        if let Some(reason) = &deprecation.reason {
            line.push_str(&format!(": {reason}"));
        }
        docs.push(line);
    }
    let description = property.description.clone().or_else(|| {
        let raw = decl_definition(property.decl?).doc_comment(db)?;
        let markdown = javadoc_to_markdown(&raw);
        (!markdown.is_empty()).then_some(markdown)
    });
    docs.extend(description);
    let values: Vec<String> = property
        .hints
        .iter()
        .map(|h| match &h.description {
            Some(d) => format!("- `{}`: {d}", h.value),
            None => format!("- `{}`", h.value),
        })
        .collect();
    if !values.is_empty() {
        docs.push(values.join("\n"));
    }
    HoverResult {
        signature,
        container: property.source_type.as_deref().map(class_display),
        docs: (!docs.is_empty()).then(|| docs.join("\n\n")),
    }
}

fn group_hover(group: &GroupMeta) -> HoverResult {
    HoverResult {
        signature: match &group.ty {
            Some(ty) => format!(
                "{} {}",
                ide_db::spring_metadata::simplify_type(ty),
                group.name
            ),
            None => group.name.clone(),
        },
        container: group.source_type.as_deref().map(class_display),
        docs: None,
    }
}

pub(crate) fn hover(
    db: &dyn Db,
    resource: &ResourceFile,
    offset: TextSize,
) -> Option<RangeInfo<HoverResult>> {
    let (key, range) = spring::config_key_at(&resource.name, &resource.text, offset)?;
    let set = MetadataSet::load(db);
    let info = match set.resolve(&key) {
        KeyMatch::Property(property) | KeyMatch::Within(property) => property_hover(db, property),
        KeyMatch::Group(group) | KeyMatch::WithinGroup(group) => group_hover(group),
        KeyMatch::Unknown { .. } => return None,
    };
    Some(RangeInfo { range, info })
}

/// 补全条目的文档：按键找到配置项。
pub(crate) fn resolve_key(db: &dyn Db, key: &str) -> Option<HoverResult> {
    let set = MetadataSet::load(db);
    set.property(key).map(|p| property_hover(db, p))
}

/// 依赖库里声明配置项的类的成员：字段（按驼峰名）或 setter。
fn library_member(db: &dyn Db, source_type: &str, key: &str) -> Option<Definition> {
    let class = hir::lookup_class(db, &source_type.replace('.', "/"))?;
    let data = hir::class_data(db, class)?;
    let last = key.rsplit('.').next().unwrap_or(key);
    let wanted = spring::canonical(last);
    if let Some(idx) = data
        .fields
        .iter()
        .position(|f| !f.flags.is_static() && spring::canonical(&f.name) == wanted)
    {
        return Some(Definition::Field(FieldId {
            class,
            idx: idx as u32,
        }));
    }
    if let Some(idx) = data.methods.iter().position(|m| {
        m.params.len() == 1
            && m.name
                .strip_prefix("set")
                .is_some_and(|rest| spring::canonical(rest) == wanted)
    }) {
        return Some(Definition::Method(MethodId {
            class,
            idx: idx as u32,
        }));
    }
    Some(Definition::Class(class))
}

pub(crate) fn goto_definition(
    db: &dyn Db,
    resource: &ResourceFile,
    offset: TextSize,
) -> Option<RangeInfo<Vec<NavigationTarget>>> {
    let (key, range) = spring::config_key_at(&resource.name, &resource.text, offset)?;
    let set = MetadataSet::load(db);
    let def = match set.resolve(&key) {
        KeyMatch::Property(property) | KeyMatch::Within(property) => match property.decl {
            Some(decl) => decl_definition(decl),
            None => library_member(db, property.source_type.as_deref()?, &property.name)?,
        },
        KeyMatch::Group(group) | KeyMatch::WithinGroup(group) => match group.class {
            Some(class) => Definition::Class(class),
            None => {
                let ty = group.ty.as_deref().or(group.source_type.as_deref())?;
                Definition::Class(hir::lookup_class(db, &ty.replace('.', "/"))?)
            }
        },
        KeyMatch::Unknown { .. } => return None,
    };
    Some(RangeInfo {
        range,
        info: to_nav(db, &def).into_iter().collect(),
    })
}
