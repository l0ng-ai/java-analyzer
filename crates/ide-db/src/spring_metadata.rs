//! Spring Boot 配置元数据：配置文件里有哪些已知的键，它们的类型、默认值、说明和可选值。
//!
//! 三个来源，各自缓存：
//! - 依赖 jar 里的 `META-INF/spring-configuration-metadata.json`
//!   （以及 `additional-spring-configuration-metadata.json`），只随类路径变化；
//! - 工作区里的同名文件（构建输出 `target/classes`、`build/...` 或资源目录里手写的），作为资源文件传入；
//! - 工作区里 `@ConfigurationProperties` 标注的类：字段 / 记录组件 / setter 按 kebab-case 展开成键，
//!   嵌套的源码类展开成下一级，`Map` / `List` 类型的配置项下面可以有任意的键。
//!
//! 键一律按 Spring 的宽松绑定比较（[`canonical`]）。

use std::sync::Arc;

use base_db::{workspace, Db};
use hir::{ClassId, ClassKind, FieldId, MethodId, Ty};
use rustc_hash::FxHashMap;
use syntax::{
    ast::{self, AstNode},
    SyntaxKind, SyntaxNode,
};

use crate::spring::canonical;

/// 元数据文件名。
pub const METADATA_FILE: &str = "spring-configuration-metadata.json";
pub const ADDITIONAL_METADATA_FILE: &str = "additional-spring-configuration-metadata.json";

/// 资源文件名是不是配置元数据。
pub fn is_metadata_name(name: &str) -> bool {
    name == METADATA_FILE || name == ADDITIONAL_METADATA_FILE
}

/// 配置项的值的形状：决定它下面还能不能再有键。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    Scalar,
    /// `Map` / `Properties`：`key.任意名字`、`key[任意名字]`
    Map,
    /// 集合和数组：`key[0]`、逗号分隔的值
    List,
    /// 类型未知：不对下面的键做判断
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Deprecation {
    /// `error` 表示已经不再支持
    pub error: bool,
    pub reason: Option<String>,
    pub replacement: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueHint {
    pub value: String,
    pub description: Option<String>,
}

/// 配置项在源码里的声明（`@ConfigurationProperties` 类的成员）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PropertyDecl {
    Field(FieldId),
    Setter(MethodId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropertyMeta {
    /// kebab-case 的完整键：`server.servlet.context-path`
    pub name: String,
    /// 类型的显示形式（元数据里是限定名，源码里是简单名）
    pub ty: Option<String>,
    pub shape: Shape,
    /// 值（`Map` 的值、集合的元素）的类的二进制名，用来补全枚举和布尔值
    pub value_type: Option<String>,
    pub description: Option<String>,
    pub default_value: Option<String>,
    /// 声明它的类（元数据里的 `sourceType`，`$` 分隔成员类）
    pub source_type: Option<String>,
    pub deprecation: Option<Deprecation>,
    pub hints: Vec<ValueHint>,
    pub decl: Option<PropertyDecl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroupMeta {
    pub name: String,
    pub ty: Option<String>,
    pub source_type: Option<String>,
    /// 源码里绑定这一组的类
    pub class: Option<ClassId>,
}

/// 一个来源的元数据。
#[derive(Debug, Default, PartialEq, Eq)]
pub struct ConfigMetadata {
    pub properties: Vec<PropertyMeta>,
    pub groups: Vec<GroupMeta>,
    /// 规范形式 → 下标
    property_index: FxHashMap<String, usize>,
    group_index: FxHashMap<String, usize>,
}

impl ConfigMetadata {
    pub fn property(&self, key: &str) -> Option<&PropertyMeta> {
        self.property_index
            .get(&canonical(key))
            .map(|&i| &self.properties[i])
    }

    pub fn group(&self, key: &str) -> Option<&GroupMeta> {
        self.group_index
            .get(&canonical(key))
            .map(|&i| &self.groups[i])
    }

    pub fn is_empty(&self) -> bool {
        self.properties.is_empty() && self.groups.is_empty()
    }

    /// 同名（宽松绑定下）的以先加入的为准。
    fn add_property(&mut self, property: PropertyMeta) -> Option<usize> {
        let key = canonical(&property.name);
        if property.name.is_empty() || self.property_index.contains_key(&key) {
            return None;
        }
        self.property_index.insert(key, self.properties.len());
        self.properties.push(property);
        Some(self.properties.len() - 1)
    }

    fn add_group(&mut self, group: GroupMeta) {
        let key = canonical(&group.name);
        if group.name.is_empty() || self.group_index.contains_key(&key) {
            return;
        }
        self.group_index.insert(key, self.groups.len());
        self.groups.push(group);
    }
}

// ---------------------------------------------------------------------------
// 元数据 JSON
// ---------------------------------------------------------------------------

/// 读入一份元数据 JSON 的 `groups` 和 `properties`；`hints` 收集到 `hints` 里，
/// 等同一来源的文件都读完后再挂到配置项上（提示可能和配置项不在同一个文件里）。
pub fn parse_metadata_json(
    text: &str,
    out: &mut ConfigMetadata,
    hints: &mut Vec<serde_json::Value>,
) {
    let Ok(root) = serde_json::from_str::<serde_json::Value>(text) else {
        return;
    };
    let str_field = |v: &serde_json::Value, name: &str| {
        v.get(name)
            .and_then(|s| s.as_str())
            .filter(|s| !s.is_empty())
            .map(str::to_owned)
    };
    for group in root
        .get("groups")
        .and_then(|g| g.as_array())
        .into_iter()
        .flatten()
    {
        let Some(name) = str_field(group, "name") else {
            continue;
        };
        out.add_group(GroupMeta {
            name,
            ty: str_field(group, "type"),
            source_type: str_field(group, "sourceType"),
            class: None,
        });
    }
    for property in root
        .get("properties")
        .and_then(|g| g.as_array())
        .into_iter()
        .flatten()
    {
        let Some(name) = str_field(property, "name") else {
            continue;
        };
        let ty = str_field(property, "type");
        let deprecation = match property.get("deprecation") {
            Some(d) => Some(Deprecation {
                error: d.get("level").and_then(|l| l.as_str()) == Some("error"),
                reason: str_field(d, "reason"),
                replacement: str_field(d, "replacement"),
            }),
            None if property.get("deprecated").and_then(|d| d.as_bool()) == Some(true) => {
                Some(Deprecation {
                    error: false,
                    reason: None,
                    replacement: None,
                })
            }
            None => None,
        };
        let (shape, value_type) = match &ty {
            Some(ty) => shape_of_type_name(ty),
            None => (Shape::Unknown, None),
        };
        out.add_property(PropertyMeta {
            name,
            ty: ty.as_deref().map(simplify_type),
            shape,
            value_type,
            description: str_field(property, "description"),
            default_value: property.get("defaultValue").and_then(render_json_value),
            source_type: str_field(property, "sourceType"),
            deprecation,
            hints: Vec::new(),
            decl: None,
        });
    }
    if let Some(list) = root.get("hints").and_then(|h| h.as_array()) {
        hints.extend(list.iter().cloned());
    }
}

/// 把收集到的提示挂到配置项上：`key` 本身、`key.values`（`Map` 的值）；`key.keys` 不用。
/// `handle-as` 提供者给出值的类型（枚举、布尔）。
fn apply_hints(out: &mut ConfigMetadata, hints: &[serde_json::Value]) {
    for hint in hints {
        let Some(name) = hint.get("name").and_then(|n| n.as_str()) else {
            continue;
        };
        if name.ends_with(".keys") {
            continue;
        }
        let base = name.strip_suffix(".values").unwrap_or(name);
        let Some(&idx) = out
            .property_index
            .get(&canonical(base))
            .or_else(|| out.property_index.get(&canonical(name)))
        else {
            continue;
        };
        let property = &mut out.properties[idx];
        for value in hint
            .get("values")
            .and_then(|v| v.as_array())
            .into_iter()
            .flatten()
        {
            let Some(text) = value.get("value").and_then(render_json_value) else {
                continue;
            };
            if property.hints.iter().any(|h| h.value == text) {
                continue;
            }
            property.hints.push(ValueHint {
                value: text,
                description: value
                    .get("description")
                    .and_then(|d| d.as_str())
                    .map(str::to_owned),
            });
        }
        for provider in hint
            .get("providers")
            .and_then(|p| p.as_array())
            .into_iter()
            .flatten()
        {
            if provider.get("name").and_then(|n| n.as_str()) != Some("handle-as") {
                continue;
            }
            if let Some(target) = provider
                .get("parameters")
                .and_then(|p| p.get("target"))
                .and_then(|t| t.as_str())
            {
                let (_, value_type) = shape_of_type_name(target);
                if value_type.is_some() {
                    property.value_type = value_type;
                }
            }
        }
    }
}

fn render_json_value(value: &serde_json::Value) -> Option<String> {
    match value {
        serde_json::Value::Null => None,
        serde_json::Value::String(s) => Some(s.clone()),
        serde_json::Value::Array(items) => Some(
            items
                .iter()
                .filter_map(render_json_value)
                .collect::<Vec<_>>()
                .join(","),
        ),
        other => Some(other.to_string()),
    }
}

/// 限定名 → 二进制名：`a.b.Outer$Inner` → `a/b/Outer$Inner`。
fn binary_name_of(qualified: &str) -> String {
    qualified.trim().replace('.', "/")
}

/// 按元数据里的类型名（`java.util.Map<java.lang.String,a.b.Level>`）判断形状和值的类型。
pub fn shape_of_type_name(ty: &str) -> (Shape, Option<String>) {
    let ty = ty.trim();
    if let Some(element) = ty.strip_suffix("[]") {
        return (Shape::List, Some(binary_name_of(element)));
    }
    let (erasure, args) = match ty.find('<') {
        Some(i) => (&ty[..i], split_type_args(&ty[i + 1..ty.len() - 1])),
        None => (ty, Vec::new()),
    };
    let simple = erasure.rsplit(['.', '$']).next().unwrap_or(erasure);
    if simple.ends_with("Map") || erasure == "java.util.Properties" {
        let value = args.get(1).map(|v| binary_name_of(erasure_of(v)));
        return (Shape::Map, value);
    }
    if simple.ends_with("List")
        || simple.ends_with("Set")
        || simple.ends_with("Collection")
        || simple == "Iterable"
    {
        let element = args.first().map(|v| binary_name_of(erasure_of(v)));
        return (Shape::List, element);
    }
    (Shape::Scalar, Some(binary_name_of(erasure)))
}

/// 分组的类型是 JDK 里的 Map。只认得出这些：自己的类名以 `Map` 结尾（`RoadMap`）不算，
/// 认不出的分组照常检查键。
fn is_jdk_map(ty: &str) -> bool {
    let erasure = erasure_of(ty);
    erasure.starts_with("java.util.")
        && (erasure.ends_with("Map")
            || matches!(erasure, "java.util.Properties" | "java.util.Hashtable"))
}

fn erasure_of(ty: &str) -> &str {
    let ty = ty.trim();
    ty.find('<').map_or(ty, |i| &ty[..i])
}

/// 顶层逗号分隔的类型实参。
fn split_type_args(text: &str) -> Vec<&str> {
    let mut res = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in text.char_indices() {
        match c {
            '<' => depth += 1,
            '>' => depth -= 1,
            ',' if depth == 0 => {
                res.push(text[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < text.len() {
        res.push(text[start..].trim());
    }
    res
}

/// 去掉类型名里的包：`java.util.Map<java.lang.String,a.b.Outer$Inner>` → `Map<String, Outer.Inner>`。
pub fn simplify_type(ty: &str) -> String {
    let mut out = String::new();
    let mut word = String::new();
    let flush = |word: &mut String, out: &mut String| {
        if !word.is_empty() {
            // 包名以小写字母开头；从第一个大写开头的段开始保留
            let segments: Vec<&str> = word.split('.').collect();
            let start = segments
                .iter()
                .position(|s| s.chars().next().is_some_and(|c| c.is_uppercase()))
                .unwrap_or(segments.len() - 1);
            out.push_str(&segments[start..].join(".").replace('$', "."));
            word.clear();
        }
    };
    for c in ty.chars() {
        if c.is_alphanumeric() || c == '.' || c == '$' || c == '_' {
            word.push(c);
        } else {
            flush(&mut word, &mut out);
            out.push(c);
            if c == ',' {
                out.push(' ');
            }
        }
    }
    flush(&mut word, &mut out);
    out.replace(",  ", ", ")
}

/// 依赖 jar 里的元数据。只随类路径变化。
#[salsa::tracked]
pub fn library_metadata(db: &dyn Db) -> Arc<ConfigMetadata> {
    let class_path = workspace(db).class_path(db);
    let mut out = ConfigMetadata::default();
    let mut hints = Vec::new();
    for entry in [
        format!("META-INF/{METADATA_FILE}"),
        format!("META-INF/{ADDITIONAL_METADATA_FILE}"),
    ] {
        for (_, bytes) in class_path.read_resources(&entry) {
            parse_metadata_json(&String::from_utf8_lossy(&bytes), &mut out, &mut hints);
        }
    }
    apply_hints(&mut out, &hints);
    Arc::new(out)
}

/// 工作区里的元数据文件（作为资源文件传入）。生成的文件排在手写的前面。
#[salsa::tracked]
pub fn resource_metadata(db: &dyn Db) -> Arc<ConfigMetadata> {
    let resources = workspace(db).resources(db);
    let mut files: Vec<_> = resources
        .iter()
        .filter(|r| is_metadata_name(&r.name))
        .collect();
    files.sort_by_key(|r| (r.name != METADATA_FILE, r.file_id));
    let mut out = ConfigMetadata::default();
    let mut hints = Vec::new();
    for file in files {
        parse_metadata_json(&file.text, &mut out, &mut hints);
    }
    apply_hints(&mut out, &hints);
    Arc::new(out)
}

// ---------------------------------------------------------------------------
// @ConfigurationProperties
// ---------------------------------------------------------------------------

/// 驼峰名 → kebab-case（Spring 的 `DataObjectPropertyName.toDashedForm`）：`maxSize` → `max-size`。
pub fn to_dashed(name: &str) -> String {
    let mut out = String::with_capacity(name.len() + 4);
    for c in name.chars() {
        if c == '_' {
            out.push('-');
        } else if c.is_uppercase() && !out.is_empty() && !out.ends_with('-') {
            out.push('-');
            out.extend(c.to_lowercase());
        } else {
            out.extend(c.to_lowercase());
        }
    }
    out
}

fn annotation_named(node: &SyntaxNode, simple: &str) -> Option<ast::Annotation> {
    node.children()
        .find_map(ast::ModifierList::cast)?
        .annotations()
        .find(|a| {
            a.name()
                .and_then(|n| n.segments().last().map(|s| s.to_string()))
                .is_some_and(|s| s == simple)
        })
}

/// `@ConfigurationProperties("p")` / `(prefix = "p")` / `(value = "p")` 的前缀；没写时是空串。
/// 前缀不是字面量（常量引用等）时返回 `None`。
fn configuration_prefix(annotation: &ast::Annotation) -> Option<String> {
    let Some(args) = annotation.arg_list() else {
        return Some(String::new());
    };
    for arg in args.args() {
        let named = arg.name_ref().map(|n| n.text().to_string());
        if !matches!(named.as_deref(), None | Some("value" | "prefix")) {
            continue;
        }
        let literal = arg
            .syntax()
            .descendants_with_tokens()
            .filter_map(|e| e.into_token())
            .find(|t| t.kind() == SyntaxKind::STRING_LITERAL)?;
        return Some(literal.text().trim_matches('"').to_owned());
    }
    Some(String::new())
}

fn decl_node(db: &dyn Db, file: base_db::SourceFile, decl: Option<u32>) -> Option<SyntaxNode> {
    let ptr = hir::source_map(db, file).get(decl?)?;
    ptr.try_to_node(&base_db::parse(db, file).syntax_node())
}

/// 工作区里 `@ConfigurationProperties` 绑定的键。
#[salsa::tracked]
pub fn source_metadata(db: &dyn Db) -> Arc<ConfigMetadata> {
    let mut out = ConfigMetadata::default();
    for (_, file) in workspace(db).files(db).workspace_files() {
        let tree = hir::item_tree(db, file);
        for class in &tree.classes {
            let id = hir::class_in_file(db, file, &class.binary_name);
            if class.has_annotation("ConfigurationProperties") {
                let Some(node) = decl_node(db, file, class.decl) else {
                    continue;
                };
                let Some(prefix) = annotation_named(&node, "ConfigurationProperties")
                    .and_then(|a| configuration_prefix(&a))
                else {
                    continue;
                };
                collect_class(db, id, &prefix, &mut Vec::new(), &mut out);
            }
            // `@Bean @ConfigurationProperties("p") Foo foo()`：绑定到返回类型
            let is_configuration = [
                "Configuration",
                "AutoConfiguration",
                "SpringBootApplication",
            ]
            .iter()
            .any(|a| class.has_annotation(a));
            if !is_configuration {
                continue;
            }
            for (idx, method) in class.methods.iter().enumerate() {
                let Some(node) = decl_node(db, file, method.decl) else {
                    continue;
                };
                let Some(prefix) = annotation_named(&node, "ConfigurationProperties")
                    .and_then(|a| configuration_prefix(&a))
                else {
                    continue;
                };
                let sig = hir::method_sig(
                    db,
                    MethodId {
                        class: id,
                        idx: idx as u32,
                    },
                );
                if let Ty::Class(target, _) = &sig.ret {
                    collect_class(db, *target, &prefix, &mut Vec::new(), &mut out);
                }
            }
        }
    }
    Arc::new(out)
}

fn join_key(prefix: &str, name: &str) -> String {
    if prefix.is_empty() {
        name.to_owned()
    } else {
        format!("{prefix}.{name}")
    }
}

/// 类型的形状、值的类，以及（是可以展开的源码类时）要展开的类。
fn classify(db: &dyn Db, ty: &Ty) -> (Shape, Option<String>, Option<ClassId>) {
    let lookup = |name: &str| hir::lookup_class(db, name);
    match ty {
        Ty::Primitive(p) => (Shape::Scalar, Some(p.boxed_class().to_owned()), None),
        Ty::Array(element) => (Shape::List, element_class(db, element), None),
        Ty::Class(class, args) => {
            let is_sub =
                |sup: &str| lookup(sup).is_some_and(|s| hir::is_subclass_of(db, *class, s));
            if is_sub("java/util/Map") {
                return (
                    Shape::Map,
                    args.get(1).and_then(|a| element_class(db, a)),
                    None,
                );
            }
            if is_sub("java/util/Collection") {
                return (
                    Shape::List,
                    args.first().and_then(|a| element_class(db, a)),
                    None,
                );
            }
            let name = class.binary_name(db).to_string();
            let nested = hir::class_data(db, *class).filter(|data| {
                data.is_source
                    && matches!(data.kind, ClassKind::Class | ClassKind::Record)
                    && !name.starts_with("java/")
            });
            (Shape::Scalar, Some(name), nested.map(|_| *class))
        }
        _ => (Shape::Unknown, None, None),
    }
}

fn element_class(db: &dyn Db, ty: &Ty) -> Option<String> {
    match ty {
        Ty::Class(class, _) => Some(class.binary_name(db).to_string()),
        Ty::Primitive(p) => Some(p.boxed_class().to_owned()),
        Ty::Wildcard(hir::Wildcard::Extends(bound)) => element_class(db, bound),
        _ => None,
    }
}

/// 把类 `class` 的可绑定成员展开到 `prefix` 下面。
fn collect_class(
    db: &dyn Db,
    class: ClassId,
    prefix: &str,
    stack: &mut Vec<ClassId>,
    out: &mut ConfigMetadata,
) {
    if stack.contains(&class) || stack.len() > 8 {
        return;
    }
    if hir::class_data(db, class).is_none() {
        return;
    }
    let source_type = class.binary_name(db).replace('/', ".");
    out.add_group(GroupMeta {
        name: prefix.to_owned(),
        ty: Some(source_type.replace('$', ".")),
        source_type: Some(source_type.clone()),
        class: Some(class),
    });
    stack.push(class);
    // 自己和父类（不含接口和 `Object`）
    let mut chain = vec![class];
    chain.extend(hir::all_supers(db, class).iter().copied().filter(|c| {
        hir::class_data(db, *c).is_some_and(|d| {
            !d.is_interface()
                && d.binary_name != "java/lang/Object"
                && d.binary_name != "java/lang/Record"
        })
    }));
    for owner in chain {
        let Some(owner_data) = hir::class_data(db, owner) else {
            continue;
        };
        let owner_type = owner.binary_name(db).replace('/', ".");
        // 源码类按字段（含记录组件），依赖库里的类按 setter
        let mut members: Vec<(String, Ty, PropertyDecl)> = Vec::new();
        if owner_data.is_source {
            for (idx, field) in owner_data.fields.iter().enumerate() {
                if field.flags.is_static() || field.is_enum_constant() {
                    continue;
                }
                let id = FieldId {
                    class: owner,
                    idx: idx as u32,
                };
                members.push((
                    field.name.to_string(),
                    hir::field_ty(db, id),
                    PropertyDecl::Field(id),
                ));
            }
        }
        for (idx, method) in owner_data.methods.iter().enumerate() {
            let Some(rest) = method.name.strip_prefix("set") else {
                continue;
            };
            if method.params.len() != 1
                || method.flags.is_static()
                || method.is_constructor
                || !rest.starts_with(|c: char| c.is_uppercase())
            {
                continue;
            }
            let mut name = String::new();
            let mut chars = rest.chars();
            name.extend(chars.next().into_iter().flat_map(char::to_lowercase));
            name.extend(chars);
            if members.iter().any(|(n, _, _)| *n == name) {
                continue;
            }
            let id = MethodId {
                class: owner,
                idx: idx as u32,
            };
            let ty = hir::method_sig(db, id)
                .params
                .first()
                .cloned()
                .unwrap_or_default();
            members.push((name, ty, PropertyDecl::Setter(id)));
        }
        for (name, ty, decl) in members {
            let key = join_key(prefix, &to_dashed(&name));
            let (shape, value_type, nested) = classify(db, &ty);
            if let Some(nested) = nested {
                collect_class(db, nested, &key, stack, out);
                continue;
            }
            out.add_property(PropertyMeta {
                name: key,
                ty: Some(ty.display(db)),
                shape,
                value_type,
                description: None,
                default_value: None,
                source_type: Some(owner_type.clone()),
                deprecation: None,
                hints: Vec::new(),
                decl: Some(decl),
            });
        }
    }
    stack.pop();
}

// ---------------------------------------------------------------------------
// 合并的视图
// ---------------------------------------------------------------------------

/// 一个键在元数据里的位置。
#[derive(Debug, Clone, Copy)]
pub enum KeyMatch<'a> {
    Property(&'a PropertyMeta),
    /// 落在 `Map` / 集合类型（或类型未知）的配置项下面
    Within(&'a PropertyMeta),
    Group(&'a GroupMeta),
    /// 落在类型是 `Map` 的分组下面（`@Bean @ConfigurationProperties(prefix = "sms.blends") Map<..>`）：
    /// Spring Boot 把下面任意的键都绑定进去
    WithinGroup(&'a GroupMeta),
    /// 没有这个键；`group` 是包含它的最近的已知分组
    Unknown {
        group: Option<&'a GroupMeta>,
    },
}

/// 全部来源合在一起：源码 > 工作区的元数据文件 > 依赖 jar。
#[derive(Debug, Clone)]
pub struct MetadataSet {
    layers: [Arc<ConfigMetadata>; 3],
}

impl MetadataSet {
    pub fn load(db: &dyn Db) -> MetadataSet {
        MetadataSet {
            layers: [
                source_metadata(db),
                resource_metadata(db),
                library_metadata(db),
            ],
        }
    }

    pub fn is_empty(&self) -> bool {
        self.layers.iter().all(|l| l.is_empty())
    }

    pub fn property(&self, key: &str) -> Option<&PropertyMeta> {
        let wanted = canonical(key);
        self.layers
            .iter()
            .find_map(|l| l.property_index.get(&wanted).map(|&i| &l.properties[i]))
    }

    pub fn group(&self, key: &str) -> Option<&GroupMeta> {
        let wanted = canonical(key);
        self.layers
            .iter()
            .find_map(|l| l.group_index.get(&wanted).map(|&i| &l.groups[i]))
    }

    /// 全部配置项，同名的只取优先的那个。
    pub fn properties(&self) -> Vec<&PropertyMeta> {
        let mut seen = rustc_hash::FxHashSet::default();
        let mut res = Vec::new();
        for layer in &self.layers {
            for property in &layer.properties {
                if seen.insert(canonical(&property.name)) {
                    res.push(property);
                }
            }
        }
        res
    }

    /// 全部分组，同名的只取优先的那个。
    pub fn groups(&self) -> Vec<&GroupMeta> {
        let mut seen = rustc_hash::FxHashSet::default();
        let mut res = Vec::new();
        for layer in &self.layers {
            for group in &layer.groups {
                if seen.insert(canonical(&group.name)) {
                    res.push(group);
                }
            }
        }
        res
    }

    /// 配置文件里的一个完整键（可以带 `[0]` 下标）对应什么。
    pub fn resolve(&self, key: &str) -> KeyMatch<'_> {
        if !key.contains('[') {
            if let Some(property) = self.property(key) {
                return KeyMatch::Property(property);
            }
            if let Some(group) = self.group(key) {
                return KeyMatch::Group(group);
            }
        }
        // 由长到短看每个祖先：`a.b[0].c` → `a.b[0]`、`a.b`、`a`
        let mut group = None;
        let mut end = key.len();
        while let Some(cut) = key[..end].rfind(['.', '[']) {
            end = cut;
            let ancestor = &key[..end];
            if ancestor.ends_with(']') {
                continue;
            }
            if let Some(property) = self.property(ancestor) {
                return match property.shape {
                    Shape::Scalar => KeyMatch::Unknown {
                        group: group.or_else(|| self.enclosing_group(ancestor)),
                    },
                    _ => KeyMatch::Within(property),
                };
            }
            if let Some(found) = self.group(ancestor) {
                // 更近的已声明分组（`catalog.entries.fixed` 是 Map `catalog.entries` 里的一个具名 Pojo）
                // 决定：它里面的键照常检查，外层的 Map 只在没有更近的分组时才让键开放
                if group.is_none() && found.ty.as_deref().is_some_and(is_jdk_map) {
                    return KeyMatch::WithinGroup(found);
                }
                if group.is_none() {
                    group = Some(found);
                }
            }
        }
        KeyMatch::Unknown { group }
    }

    fn enclosing_group(&self, key: &str) -> Option<&GroupMeta> {
        let mut end = key.len();
        while let Some(cut) = key[..end].rfind('.') {
            end = cut;
            if let Some(group) = self.group(&key[..end]) {
                return Some(group);
            }
        }
        None
    }
}

/// 配置项可以取的值：提示里列出的、布尔、枚举常量（kebab-case 小写）。
pub fn value_candidates(db: &dyn Db, property: &PropertyMeta) -> Vec<ValueHint> {
    let mut res = property.hints.clone();
    let mut push = |value: String, description: Option<String>| {
        if !res.iter().any(|h| h.value.eq_ignore_ascii_case(&value)) {
            res.push(ValueHint { value, description });
        }
    };
    let Some(value_type) = &property.value_type else {
        return res;
    };
    match value_type.as_str() {
        "java/lang/Boolean" | "boolean" => {
            push("true".to_owned(), None);
            push("false".to_owned(), None);
        }
        name => {
            let class = hir::lookup_class(db, name);
            if let Some(data) = class.and_then(|c| hir::class_data(db, c)) {
                if data.kind == ClassKind::Enum {
                    for field in data.fields.iter().filter(|f| f.is_enum_constant()) {
                        push(field.name.to_lowercase().replace('_', "-"), None);
                    }
                }
            }
        }
    }
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dashed_names() {
        assert_eq!(to_dashed("maxSize"), "max-size");
        assert_eq!(to_dashed("port"), "port");
        assert_eq!(to_dashed("URL"), "u-r-l");
        assert_eq!(to_dashed("some_value"), "some-value");
    }

    #[test]
    fn type_shapes() {
        assert_eq!(
            shape_of_type_name("java.util.Map<java.lang.String,org.example.Level>"),
            (Shape::Map, Some("org/example/Level".to_owned()))
        );
        assert_eq!(
            shape_of_type_name("java.util.List<java.lang.String>"),
            (Shape::List, Some("java/lang/String".to_owned()))
        );
        assert_eq!(
            shape_of_type_name("java.lang.String[]"),
            (Shape::List, Some("java/lang/String".to_owned()))
        );
        assert_eq!(
            shape_of_type_name("a.b.Outer$Mode"),
            (Shape::Scalar, Some("a/b/Outer$Mode".to_owned()))
        );
        assert_eq!(
            simplify_type("java.util.Map<java.lang.String,a.b.Outer$Inner>"),
            "Map<String, Outer.Inner>"
        );
        assert_eq!(simplify_type("java.time.Duration"), "Duration");
    }

    #[test]
    fn parses_metadata_json() {
        let text = r#"{
          "groups": [{"name": "server", "type": "a.ServerProperties", "sourceType": "a.ServerProperties"}],
          "properties": [
            {"name": "server.port", "type": "java.lang.Integer", "description": "Server HTTP port.", "defaultValue": 8080},
            {"name": "server.shutdown", "type": "a.Shutdown", "defaultValue": "immediate"},
            {"name": "server.old", "type": "java.lang.String", "deprecated": true,
             "deprecation": {"level": "error", "replacement": "server.new"}},
            {"name": "logging.level", "type": "java.util.Map<java.lang.String,java.lang.String>"},
            {"name": "server.list", "type": "java.util.List<java.lang.String>", "defaultValue": ["a", "b"]}
          ],
          "hints": [
            {"name": "logging.level.values", "values": [{"value": "debug"}, {"value": "info"}]},
            {"name": "server.port", "values": [{"value": 8080, "description": "default"}]}
          ]
        }"#;
        let mut meta = ConfigMetadata::default();
        let mut hints = Vec::new();
        parse_metadata_json(text, &mut meta, &mut hints);
        apply_hints(&mut meta, &hints);
        let port = meta.property("server.port").unwrap();
        assert_eq!(port.ty.as_deref(), Some("Integer"));
        assert_eq!(port.default_value.as_deref(), Some("8080"));
        assert_eq!(port.hints[0].value, "8080");
        assert_eq!(
            meta.property("server.old").unwrap().deprecation,
            Some(Deprecation {
                error: true,
                reason: None,
                replacement: Some("server.new".to_owned()),
            })
        );
        let level = meta.property("logging.level").unwrap();
        assert_eq!(level.shape, Shape::Map);
        assert_eq!(level.hints.len(), 2);
        assert_eq!(
            meta.property("server.list")
                .unwrap()
                .default_value
                .as_deref(),
            Some("a,b")
        );
        assert!(meta.group("server").is_some());
        // 宽松绑定
        assert!(meta.property("SERVER_PORT").is_none());
        assert!(meta.property("server.Port").is_some());

        let set = MetadataSet {
            layers: [
                Arc::new(ConfigMetadata::default()),
                Arc::new(ConfigMetadata::default()),
                Arc::new(meta),
            ],
        };
        assert!(matches!(set.resolve("server.port"), KeyMatch::Property(_)));
        assert!(matches!(
            set.resolve("logging.level.org.example"),
            KeyMatch::Within(_)
        ));
        assert!(matches!(set.resolve("server.list[0]"), KeyMatch::Within(_)));
        assert!(matches!(
            set.resolve("server.prot"),
            KeyMatch::Unknown { group: Some(_) }
        ));
        assert!(matches!(
            set.resolve("server.port.x"),
            KeyMatch::Unknown { group: Some(_) }
        ));
        assert!(matches!(
            set.resolve("app.custom"),
            KeyMatch::Unknown { group: None }
        ));
        assert!(matches!(set.resolve("server"), KeyMatch::Group(_)));
    }

    /// 类型是 `Map` 的分组是开放的：`sms.blends.任意名字.任意键` 都不算未知的键。
    #[test]
    fn map_typed_group_accepts_any_key() {
        let text = r#"{
          "groups": [
            { "name": "sms", "type": "a.Sms" },
            { "name": "sms.blends", "type": "java.util.Map" }
          ],
          "properties": [{ "name": "sms.config-type", "type": "java.lang.String" }]
        }"#;
        let mut meta = ConfigMetadata::default();
        let mut hints = Vec::new();
        parse_metadata_json(text, &mut meta, &mut hints);
        let set = MetadataSet {
            layers: [
                Arc::new(ConfigMetadata::default()),
                Arc::new(ConfigMetadata::default()),
                Arc::new(meta),
            ],
        };
        assert!(matches!(
            set.resolve("sms.blends.config1.supplier"),
            KeyMatch::WithinGroup(group) if group.name == "sms.blends"
        ));
        assert!(matches!(
            set.resolve("sms.blends.config1.templates[0].id"),
            KeyMatch::WithinGroup(_)
        ));
        assert!(matches!(set.resolve("sms.blends"), KeyMatch::Group(_)));
        assert!(matches!(
            set.resolve("sms.typo"),
            KeyMatch::Unknown { group: Some(_) }
        ));
    }

    /// 名字以 `Map` 结尾不代表它是 Map：类型不是已知的 JDK Map 时，分组照常检查键。
    #[test]
    fn group_named_like_a_map_is_not_open() {
        let text = r#"{
          "groups": [{ "name": "road", "type": "example.RoadMap" }],
          "properties": [{ "name": "road.title", "type": "java.lang.String" }]
        }"#;
        let mut meta = ConfigMetadata::default();
        let mut hints = Vec::new();
        parse_metadata_json(text, &mut meta, &mut hints);
        let set = MetadataSet {
            layers: [
                Arc::new(ConfigMetadata::default()),
                Arc::new(ConfigMetadata::default()),
                Arc::new(meta),
            ],
        };
        assert!(matches!(
            set.resolve("road.title-typo"),
            KeyMatch::Unknown { group: Some(_) }
        ));
    }

    /// 更近的、已声明的分组决定：Map 分组下面的某个键如果自己是个声明过的普通分组，
    /// 它里面的拼写错误照常报；Map 里其它任意的键仍然都算合法。
    #[test]
    fn declared_group_inside_a_map_group_is_still_checked() {
        let text = r#"{
          "groups": [
            { "name": "catalog", "type": "example.Catalog" },
            { "name": "catalog.entries", "type": "java.util.Map<java.lang.String,example.Pojo>" },
            { "name": "catalog.entries.fixed", "type": "example.Pojo" }
          ],
          "properties": [{ "name": "catalog.entries.fixed.title", "type": "java.lang.String" }]
        }"#;
        let mut meta = ConfigMetadata::default();
        let mut hints = Vec::new();
        parse_metadata_json(text, &mut meta, &mut hints);
        let set = MetadataSet {
            layers: [
                Arc::new(ConfigMetadata::default()),
                Arc::new(ConfigMetadata::default()),
                Arc::new(meta),
            ],
        };
        assert!(matches!(
            set.resolve("catalog.entries.fixed.titel"),
            KeyMatch::Unknown { group: Some(group) } if group.name == "catalog.entries.fixed"
        ));
        assert!(matches!(
            set.resolve("catalog.entries.dynamic.anything"),
            KeyMatch::WithinGroup(group) if group.name == "catalog.entries"
        ));
    }
}
