//! Lombok 注解生成的成员。
//!
//! Lombok 在编译期往类里加方法，源码里看不到。这里按注解把对应的签名合成进 [`ClassData`]，
//! 上层（补全、跳转、类型推断）就能像对待手写成员一样对待它们。合成成员带 `SYNTHETIC`
//! 标志，声明位置指向触发它的字段（或类），所以"跳转到定义"会落在字段上。
//!
//! 只按注解的简单名识别（`@Getter` 和 `@lombok.Getter` 等价）。会解读参数的注解（见
//! [`WITH_OPTIONS`]）在降级时把每个参数记成一条伪注解 `@Getter(value=NONE)` 跟在注解名后面：
//! `AccessLevel` 取最后一段，字符串去掉引号，数组用逗号连起来。据此支持的定制有
//! `AccessLevel`（字段级覆盖类级，`NONE` 不生成）、构造器的 `staticName` / `access`、
//! `@Builder` 的 `builderMethodName` / `buildMethodName` / `builderClassName` / `toBuilder` /
//! `setterPrefix` / `access`、`@Singular`、`@Builder.Default`、`@Accessors` 的
//! `chain` / `fluent` / `prefix`、`@FieldDefaults`、`@FieldNameConstants`。
//!
//! 构建器按 Lombok 实际生成的签名合成：泛型类的构建器带类型参数；`@SuperBuilder` 的构建器是
//! 带自身类型参数 `C` / `B` 的抽象类，继承父类的构建器，父类的设置方法因此由普通的继承得到。
//!
//! 需要别的类的签名才能合成的成员（`@Delegate` 转发的方法）不在这里，见 [`crate::lombok_expand`]。

use smol_str::SmolStr;
use syntax::{
    ast::{self, AstNode},
    SyntaxKind,
};

use crate::data::{
    ClassData, ClassKind, FieldConstant, FieldData, MethodData, Modifiers, Name, ParamData,
    PrimitiveType, TypeParamData, TypeRef, Visibility, WildcardBound,
};

fn simple(annotation: &str) -> &str {
    annotation
        .rsplit(['.', '/', '$'])
        .next()
        .unwrap_or(annotation)
}

/// 注解列表里有没有这个简单名的注解。伪注解以 `@` 开头、以 `)` 结尾，不会被当成注解名。
fn has(annotations: &[SmolStr], name: &str) -> bool {
    annotations.iter().any(|a| simple(a) == name)
}

/// 带外层名的注解（`@Builder.Default`、`@FieldNameConstants.Exclude`），按写出来的后缀匹配。
fn has_qualified(annotations: &[SmolStr], name: &str) -> bool {
    annotations.iter().any(|a| {
        a.as_str() == name
            || a.strip_suffix(name)
                .is_some_and(|rest| rest.ends_with('.') && !rest.starts_with('@'))
    })
}

/// 会解读参数的 Lombok 注解（简单名）。
const WITH_OPTIONS: &[&str] = &[
    "Getter",
    "Setter",
    "With",
    "Accessors",
    "Builder",
    "SuperBuilder",
    "NoArgsConstructor",
    "AllArgsConstructor",
    "RequiredArgsConstructor",
    "Data",
    "Value",
    "FieldNameConstants",
    "StandardException",
    "FieldDefaults",
    "Singular",
];

/// 注解参数记成的伪注解：`@简单名(参数名=值)`。不认识的注解、取不出值的参数不记。
pub(crate) fn annotation_options(annotation: &ast::Annotation, name: &str) -> Vec<SmolStr> {
    let name = simple(name);
    let mut res = Vec::new();
    if !WITH_OPTIONS.contains(&name) {
        return res;
    }
    let Some(args) = annotation.arg_list() else {
        return res;
    };
    for arg in args.args() {
        if arg.value_annotation().is_some() {
            continue;
        }
        let key = arg
            .name_ref()
            .map(|n| n.text())
            .unwrap_or_else(|| SmolStr::new("value"));
        if let Some(value) = option_value(arg.syntax(), arg.name_ref().is_some()) {
            res.push(SmolStr::new(format!("@{name}({key}={value})")));
        }
    }
    res
}

/// 参数值的文本：字符串（数组里的多个字符串用逗号连起来）、`true` / `false`、
/// 枚举常量或常量名的最后一段（`AccessLevel.PRIVATE` → `PRIVATE`）。
fn option_value(arg: &syntax::SyntaxNode, named: bool) -> Option<String> {
    let mut tokens: Vec<syntax::SyntaxToken> = arg
        .descendants_with_tokens()
        .filter_map(|e| e.into_token())
        .collect();
    if named {
        let eq = tokens.iter().position(|t| t.kind() == SyntaxKind::EQ)?;
        tokens.drain(..=eq);
    }
    let strings: Vec<&str> = tokens
        .iter()
        .filter(|t| t.kind() == SyntaxKind::STRING_LITERAL)
        .map(|t| {
            let text = t.text();
            text.strip_prefix('"')
                .and_then(|t| t.strip_suffix('"'))
                .unwrap_or(text)
        })
        .collect();
    if !strings.is_empty() {
        return Some(strings.join(","));
    }
    if tokens.iter().any(|t| t.kind() == SyntaxKind::L_CURLY) {
        // 空数组 `{}`
        return Some(String::new());
    }
    tokens
        .iter()
        .rev()
        .find(|t| {
            matches!(
                t.kind(),
                SyntaxKind::IDENT | SyntaxKind::TRUE_KW | SyntaxKind::FALSE_KW
            )
        })
        .map(|t| t.text().to_owned())
}

/// 注解 `name` 的参数 `key` 的值（没写时为 `None`）。
fn option<'a>(annotations: &'a [SmolStr], name: &str, key: &str) -> Option<&'a str> {
    let prefix = format!("@{name}({key}=");
    annotations
        .iter()
        .find_map(|a| a.strip_prefix(prefix.as_str())?.strip_suffix(')'))
}

fn flag(annotations: &[SmolStr], name: &str, key: &str) -> bool {
    option(annotations, name, key) == Some("true")
}

/// 写了且非空的字符串参数。
fn text_option<'a>(annotations: &'a [SmolStr], name: &str, key: &str) -> Option<&'a str> {
    option(annotations, name, key).filter(|v| !v.is_empty())
}

/// Lombok 的 `AccessLevel`。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Level {
    Public,
    Protected,
    Package,
    Private,
    /// `AccessLevel.NONE`：不生成
    Off,
}

impl Level {
    fn parse(text: &str) -> Option<Level> {
        Some(match text {
            "PUBLIC" => Level::Public,
            "PROTECTED" => Level::Protected,
            "PACKAGE" | "MODULE" => Level::Package,
            "PRIVATE" => Level::Private,
            "NONE" => Level::Off,
            _ => return None,
        })
    }

    /// 对应的访问修饰符位；`NONE` 时为 `None`。
    fn bits(self) -> Option<u32> {
        match self {
            Level::Public => Some(Modifiers::PUBLIC),
            Level::Protected => Some(Modifiers::PROTECTED),
            Level::Package => Some(0),
            Level::Private => Some(Modifiers::PRIVATE),
            Level::Off => None,
        }
    }
}

/// 注解参数里的访问级别（没写或写的不是 `AccessLevel` 常量时为 `None`）。
fn level(annotations: &[SmolStr], name: &str, key: &str) -> Option<Level> {
    option(annotations, name, key).and_then(Level::parse)
}

/// 注解 `name`（`@Getter` / `@Setter` / `@With`）在这组注解里要求的访问级别：
/// 没有这个注解时为 `None`，有但没写级别时为 `PUBLIC`。
fn annotated_level(annotations: &[SmolStr], name: &str) -> Option<Level> {
    has(annotations, name).then(|| level(annotations, name, "value").unwrap_or(Level::Public))
}

/// 访问器的风格：`fluent` 时访问器与（去掉前缀的）字段同名，`chain` 时设置方法返回 `this`，
/// `prefix` 是要从字段名上去掉的前缀。字段上的 `@Accessors` 没写的参数沿用类上的。
#[derive(Clone, Default)]
struct AccessorStyle {
    chain: bool,
    fluent: bool,
    prefixes: Vec<String>,
}

impl AccessorStyle {
    /// 注解上没写的参数取 `lombok.config` 里的配置。
    fn of(field: &[SmolStr], class: &[SmolStr], config: &LombokConfig) -> AccessorStyle {
        let get =
            |key: &str| option(field, "Accessors", key).or_else(|| option(class, "Accessors", key));
        let fluent = get("fluent").map_or(config.fluent.unwrap_or(false), |v| v == "true");
        let chain = get("chain").map_or(config.chain.unwrap_or(fluent), |v| v == "true");
        let prefixes = match get("prefix") {
            Some(v) if !v.is_empty() => v.split(',').map(str::to_owned).collect(),
            Some(_) => Vec::new(),
            None => config.prefixes.clone(),
        };
        AccessorStyle {
            chain,
            fluent,
            prefixes,
        }
    }

    /// 访问器按哪个名字生成：去掉前缀后的字段。字段名不带任何一个前缀时 Lombok 不生成访问器。
    fn property(&self, field: &FieldData) -> Option<FieldData> {
        if self.prefixes.is_empty() {
            return Some(field.clone());
        }
        let name = remove_prefix(&field.name, &self.prefixes)?;
        Some(FieldData {
            name: Name::new(name),
            ..field.clone()
        })
    }
}

/// Lombok 的去前缀规则：前缀以字母结尾时，后面紧跟的字符不能是小写字母；剩下部分首字母小写。
fn remove_prefix(name: &str, prefixes: &[String]) -> Option<String> {
    for prefix in prefixes {
        if prefix.is_empty() {
            return Some(name.to_owned());
        }
        let Some(rest) = name.strip_prefix(prefix.as_str()) else {
            continue;
        };
        let Some(next) = rest.chars().next() else {
            continue;
        };
        let ends_with_letter = prefix.chars().last().is_some_and(char::is_alphabetic);
        if ends_with_letter && next.is_lowercase() {
            continue;
        }
        let mut chars = rest.chars();
        let first = chars.next()?;
        return Some(first.to_lowercase().chain(chars).collect());
    }
    None
}

fn capitalize(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().chain(chars).collect(),
        None => String::new(),
    }
}

fn is_boolean(ty: &TypeRef) -> bool {
    matches!(ty, TypeRef::Primitive(PrimitiveType::Boolean))
}

/// `isActive` 这种已经带 `is` 前缀的 boolean 字段，去掉前缀后的属性名。
fn boolean_property(name: &str) -> Option<&str> {
    let rest = name.strip_prefix("is")?;
    rest.starts_with(|c: char| c.is_uppercase()).then_some(rest)
}

pub(crate) fn getter_name(field: &FieldData) -> Name {
    if is_boolean(&field.ty) {
        match boolean_property(&field.name) {
            Some(_) => field.name.clone(),
            None => Name::new(format!("is{}", capitalize(&field.name))),
        }
    } else {
        Name::new(format!("get{}", capitalize(&field.name)))
    }
}

pub(crate) fn setter_name(field: &FieldData) -> Name {
    let property = match boolean_property(&field.name) {
        Some(rest) if is_boolean(&field.ty) => rest.to_owned(),
        _ => capitalize(&field.name),
    };
    Name::new(format!("set{property}"))
}

fn with_name(field: &FieldData) -> Name {
    Name::new(format!("with{}", capitalize(&field.name)))
}

/// 从字段合成出来的访问器的种类（名字怎样由字段名推出来）。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AccessorKind {
    /// `getName()` / `isActive()`
    Getter,
    /// `setName(..)`
    Setter,
    /// `withName(..)`
    Wither,
    /// 与字段同名：构建器上的 `name(..)`、记录的访问器 `name()`
    SameName,
}

impl AccessorKind {
    /// 合成方法 `method` 是字段 `field` 的哪种访问器。
    pub fn of(field: &FieldData, method: &MethodData) -> Option<AccessorKind> {
        let arity = method.params.len();
        if arity == 0 && method.name == getter_name(field) {
            Some(AccessorKind::Getter)
        } else if arity == 1 && method.name == setter_name(field) {
            Some(AccessorKind::Setter)
        } else if arity == 1 && method.name == with_name(field) {
            Some(AccessorKind::Wither)
        } else if arity <= 1 && method.name == field.name {
            Some(AccessorKind::SameName)
        } else {
            None
        }
    }

    /// 字段（按它的名字和类型）对应的这种访问器的名字。
    pub fn name_for(self, field: &FieldData) -> Name {
        match self {
            AccessorKind::Getter => getter_name(field),
            AccessorKind::Setter => setter_name(field),
            AccessorKind::Wither => with_name(field),
            AccessorKind::SameName => field.name.clone(),
        }
    }

    /// 反推：要让这种访问器叫 `accessor`，字段应当叫什么。推不出来（前缀不对、
    /// 剩下的部分为空）时返回 `None`。`field` 提供类型和原来的命名风格。
    pub fn field_name_for(self, field: &FieldData, accessor: &str) -> Option<Name> {
        let rest = match self {
            AccessorKind::SameName => return Some(Name::new(accessor)),
            AccessorKind::Getter => accessor
                .strip_prefix("get")
                .filter(|_| !is_boolean(&field.ty))
                .or_else(|| {
                    accessor
                        .strip_prefix("is")
                        .filter(|_| is_boolean(&field.ty))
                }),
            AccessorKind::Setter => accessor.strip_prefix("set"),
            AccessorKind::Wither => accessor.strip_prefix("with"),
        }?;
        if rest.is_empty() {
            return None;
        }
        // 原字段名以大写开头（`Effect`）就保留大小写，否则首字母小写
        let plain = if field.name.starts_with(|c: char| c.is_uppercase()) {
            rest.to_owned()
        } else {
            let mut chars = rest.chars();
            let first = chars.next()?;
            first.to_lowercase().chain(chars).collect()
        };
        // boolean 字段原来就带 `is` 前缀时，优先保留这个风格
        let prefixed = format!("is{}", capitalize(rest));
        let candidates = if boolean_property(&field.name).is_some() {
            [prefixed, plain]
        } else {
            [plain, prefixed]
        };
        candidates.into_iter().map(Name::new).find(|candidate| {
            let renamed = FieldData {
                name: candidate.clone(),
                ..field.clone()
            };
            self.name_for(&renamed) == accessor
        })
    }
}

const SYNTHETIC_PUBLIC: Modifiers = Modifiers(Modifiers::PUBLIC | Modifiers::SYNTHETIC);

/// `lombok.config` 里影响生成成员签名的配置项：源文件所在目录往上的各个 `lombok.config`
/// 叠加后的结果（见 [`crate::index::lombok_config`]）。
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct LombokConfig {
    /// `lombok.accessors.chain`
    pub chain: Option<bool>,
    /// `lombok.accessors.fluent`
    pub fluent: Option<bool>,
    /// `lombok.accessors.prefix`（`+=` 追加、`-=` 删除、`clear` 清空）
    pub prefixes: Vec<String>,
    /// `lombok.getter.noIsPrefix`：boolean 字段的 getter 也用 `get` 前缀
    pub no_is_prefix: bool,
    /// `lombok.log.fieldName`
    pub log_field_name: Option<String>,
}

impl LombokConfig {
    /// 文件里写了 `config.stopBubbling = true`：再往上的目录里的 `lombok.config` 不再生效。
    pub fn stops_bubbling(text: &str) -> bool {
        text.lines().any(|line| {
            line.split_once('=').is_some_and(|(key, value)| {
                key.trim() == "config.stopBubbling"
                    && value.trim().trim_matches('"').eq_ignore_ascii_case("true")
            })
        })
    }

    /// 按顺序叠加一个 `lombok.config` 文件的内容。
    pub fn apply_file(&mut self, text: &str) {
        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if let Some(key) = line.strip_prefix("clear ") {
                match key.trim() {
                    "lombok.accessors.chain" => self.chain = None,
                    "lombok.accessors.fluent" => self.fluent = None,
                    "lombok.accessors.prefix" => self.prefixes.clear(),
                    "lombok.getter.noIsPrefix" => self.no_is_prefix = false,
                    "lombok.log.fieldName" => self.log_field_name = None,
                    _ => {}
                }
                continue;
            }
            let (key, op, value) = if let Some((k, v)) = line.split_once("+=") {
                (k.trim(), '+', v.trim())
            } else if let Some((k, v)) = line.split_once("-=") {
                (k.trim(), '-', v.trim())
            } else if let Some((k, v)) = line.split_once('=') {
                (k.trim(), '=', v.trim())
            } else {
                continue;
            };
            let value = value.trim_matches('"');
            let flag = value.eq_ignore_ascii_case("true");
            match (key, op) {
                ("lombok.accessors.chain", '=') => self.chain = Some(flag),
                ("lombok.accessors.fluent", '=') => self.fluent = Some(flag),
                ("lombok.accessors.prefix", '+') => {
                    if !self.prefixes.iter().any(|p| p == value) {
                        self.prefixes.push(value.to_owned());
                    }
                }
                ("lombok.accessors.prefix", '-') => self.prefixes.retain(|p| p != value),
                ("lombok.accessors.prefix", '=') => self.prefixes = vec![value.to_owned()],
                ("lombok.getter.noIsPrefix", '=') => self.no_is_prefix = flag,
                ("lombok.log.fieldName", '=') if !value.is_empty() => {
                    self.log_field_name = Some(value.to_owned())
                }
                _ => {}
            }
        }
    }
}

/// 降级时收集的、`ClassData` 里没有而 Lombok 需要的信息。
#[derive(Default)]
pub(crate) struct LombokInput {
    pub(crate) fields: Vec<FieldExtra>,
    pub(crate) builder_methods: Vec<BuilderMethod>,
}

/// 一个字段的注解和它有没有初值（`@RequiredArgsConstructor` 等不管有初值的 final 字段）。
pub(crate) struct FieldExtra {
    pub(crate) idx: usize,
    pub(crate) annotations: Vec<SmolStr>,
    pub(crate) initialized: bool,
}

/// 带 `@Builder` 的构造器或静态方法：方法下标、方法上的注解、各形参上的注解。
pub(crate) struct BuilderMethod {
    pub(crate) idx: usize,
    pub(crate) annotations: Vec<SmolStr>,
    pub(crate) params: Vec<Vec<SmolStr>>,
}

pub(crate) fn is_builder_annotation(name: &str) -> bool {
    simple(name) == "Builder"
}

impl LombokInput {
    fn annotations(&self, idx: usize) -> &[SmolStr] {
        self.fields
            .iter()
            .find(|f| f.idx == idx)
            .map(|f| f.annotations.as_slice())
            .unwrap_or(&[])
    }

    fn initialized(&self, idx: usize) -> bool {
        self.fields.iter().any(|f| f.idx == idx && f.initialized)
    }
}

fn declared(data: &ClassData, name: &str, arity: usize) -> bool {
    data.methods
        .iter()
        .any(|m| !m.is_constructor && m.name == name && m.params.len() == arity)
}

fn method(
    name: Name,
    params: Vec<ParamData>,
    ret: TypeRef,
    flags: Modifiers,
    decl: Option<u32>,
) -> MethodData {
    MethodData {
        name,
        is_constructor: false,
        type_params: Vec::new(),
        params,
        ret,
        throws: Vec::new(),
        flags,
        has_body: true,
        decl,
    }
}

fn param(name: &str, ty: TypeRef) -> ParamData {
    ParamData {
        name: Some(Name::new(name)),
        ty,
        nullness: Default::default(),
    }
}

fn field_param(field: &FieldData) -> ParamData {
    ParamData {
        name: Some(field.name.clone()),
        ty: field.ty.clone(),
        nullness: field.flags.null_annotation(),
    }
}

fn constructor(data: &ClassData, params: Vec<ParamData>, flags: u32) -> MethodData {
    MethodData {
        name: data.name.clone(),
        is_constructor: true,
        type_params: Vec::new(),
        params,
        ret: TypeRef::Void,
        throws: Vec::new(),
        flags: Modifiers(flags | Modifiers::SYNTHETIC),
        has_body: true,
        decl: data.decl,
    }
}

/// 类在自己的静态方法里的类型：带上类型参数（静态工厂方法把类的类型参数声明成自己的）。
fn generic_self(data: &ClassData) -> TypeRef {
    TypeRef::Class {
        name: data.binary_name.clone(),
        args: data
            .type_params
            .iter()
            .map(|p| TypeRef::TypeVar(p.name.clone()))
            .collect(),
    }
}

/// `@XArgsConstructor` 生成的构造器。`staticName` 时构造器私有，另生成一个同参数的静态工厂方法。
fn add_constructor(
    data: &mut ClassData,
    params: Vec<ParamData>,
    level: Level,
    static_name: Option<&str>,
) {
    let Some(bits) = level.bits() else {
        return;
    };
    let exists = data
        .methods
        .iter()
        .any(|m| m.is_constructor && m.params.len() == params.len());
    let ctor_bits = if static_name.is_some() {
        Modifiers::PRIVATE
    } else {
        bits
    };
    if !exists {
        let ctor = constructor(data, params.clone(), ctor_bits);
        data.methods.push(ctor);
    }
    if let Some(name) = static_name {
        if !declared(data, name, params.len()) {
            let mut factory = method(
                Name::new(name),
                params,
                generic_self(data),
                Modifiers(bits | Modifiers::STATIC | Modifiers::SYNTHETIC),
                data.decl,
            );
            factory.type_params = data.type_params.clone();
            data.methods.push(factory);
        }
    }
}

/// 按注解 `name` 上的 `access` / `staticName` 生成构造器。
fn annotated_constructor(
    data: &mut ClassData,
    annotations: &[SmolStr],
    name: &str,
    params: Vec<ParamData>,
) {
    let level = level(annotations, name, "access").unwrap_or(Level::Public);
    let static_name = text_option(annotations, name, "staticName");
    add_constructor(data, params, level, static_name);
}

/// 参数类型相同（按类型的简单名比较）的构造器已经存在。
fn has_constructor(data: &ClassData, types: &[&str]) -> bool {
    data.methods.iter().any(|m| {
        m.is_constructor
            && m.params.len() == types.len()
            && m.params
                .iter()
                .zip(types)
                .all(|(p, ty)| type_parts(&p.ty).is_some_and(|(name, _)| name == *ty))
    })
}

/// 日志注解 → 日志器类型。
fn logger_type(annotations: &[SmolStr]) -> Option<&'static str> {
    const LOGGERS: &[(&str, &str)] = &[
        ("Slf4j", "org/slf4j/Logger"),
        ("XSlf4j", "org/slf4j/ext/XLogger"),
        ("Log4j2", "org/apache/logging/log4j/Logger"),
        ("Log4j", "org/apache/log4j/Logger"),
        ("Log", "java/util/logging/Logger"),
        ("CommonsLog", "org/apache/commons/logging/Log"),
        ("JBossLog", "org/jboss/logging/Logger"),
        ("Flogger", "com/google/common/flogger/FluentLogger"),
    ];
    LOGGERS
        .iter()
        .find(|(name, _)| has(annotations, name))
        .map(|(_, ty)| *ty)
}

/// 类型的简单名和类型实参。
fn type_parts(ty: &TypeRef) -> Option<(&str, &[TypeRef])> {
    match ty {
        TypeRef::Path(segments) => segments
            .last()
            .map(|s| (s.name.as_str(), s.args.as_slice())),
        TypeRef::Class { name, args } => Some((simple(name), args.as_slice())),
        _ => None,
    }
}

fn object() -> TypeRef {
    TypeRef::class("java/lang/Object")
}

/// 集合的元素类型：`? extends E` 取上界，其它通配符按 `Object`。
fn element(args: &[TypeRef], idx: usize) -> TypeRef {
    match args.get(idx) {
        Some(TypeRef::Wildcard(WildcardBound::Extends(bound))) => (**bound).clone(),
        Some(TypeRef::Wildcard(_)) | None => object(),
        Some(ty) => ty.clone(),
    }
}

fn extends(ty: TypeRef) -> TypeRef {
    TypeRef::Wildcard(WildcardBound::Extends(Box::new(ty)))
}

/// 英文复数 → 单数（`@Singular` 没写名字时）。推不出来时为 `None`（Lombok 此时要求显式写名字）。
fn singularize(plural: &str) -> Option<String> {
    const IRREGULAR: &[(&str, &str)] = &[
        ("people", "person"),
        ("children", "child"),
        ("men", "man"),
        ("women", "woman"),
        ("indices", "index"),
        ("matrices", "matrix"),
        ("vertices", "vertex"),
        ("criteria", "criterion"),
    ];
    // 驼峰名只看最后一个单词
    let split = plural
        .char_indices()
        .rfind(|(_, c)| c.is_uppercase())
        .map_or(0, |(i, _)| i);
    let (head, word) = plural.split_at(split);
    let lower = word.to_lowercase();
    let restore = |single: &str| -> String {
        // 保留原来首字母的大小写
        if word.starts_with(char::is_uppercase) {
            format!("{head}{}", capitalize(single))
        } else {
            format!("{head}{single}")
        }
    };
    if let Some((_, single)) = IRREGULAR.iter().find(|(p, _)| *p == lower) {
        return Some(restore(single));
    }
    let single = if let Some(stem) = lower.strip_suffix("ies").filter(|s| s.len() > 1) {
        format!("{stem}y")
    } else if ["sses", "shes", "ches", "xes", "zzes"]
        .iter()
        .any(|suffix| lower.ends_with(suffix))
    {
        lower[..lower.len() - 2].to_owned()
    } else if lower.ends_with('s') && !lower.ends_with("ss") && lower.len() > 1 {
        lower[..lower.len() - 1].to_owned()
    } else {
        return None;
    };
    Some(restore(&single))
}

/// 构建器的一个设置项（字段或者被 `@Builder` 标注的方法的形参）。
struct BuilderParam {
    name: Name,
    ty: TypeRef,
    nullness: crate::data::NullAnnotation,
    decl: Option<u32>,
    /// 带 `@Singular`：单数名（推不出来时为 `None`）
    singular: Option<Option<String>>,
}

fn singular_of(annotations: &[SmolStr], plural: &str) -> Option<Option<String>> {
    if !has(annotations, "Singular") {
        return None;
    }
    let explicit = text_option(annotations, "Singular", "value").map(str::to_owned);
    Some(explicit.or_else(|| singularize(plural)))
}

/// 构建器在哪个注解上、默认叫什么、`build()` 返回什么。
struct BuilderSpec<'a> {
    annotations: &'a [SmolStr],
    default_name: String,
    /// 构建器类的类型参数：类上的 `@Builder` 是类的类型参数，静态方法上的是方法的类型参数
    type_params: Vec<TypeParamData>,
    build_ret: TypeRef,
    decl: Option<u32>,
    /// 是否可以生成 `toBuilder()`（静态方法上的 `@Builder` 不生成）
    allow_to_builder: bool,
}

const MAP_TYPES: &[&str] = &[
    "Map",
    "SortedMap",
    "NavigableMap",
    "ImmutableMap",
    "ImmutableBiMap",
    "ImmutableSortedMap",
];

fn type_var(name: &Name) -> TypeRef {
    TypeRef::TypeVar(name.clone())
}

/// 以这些类型参数为实参的类型 `binary<T1, T2, ..>`。
fn applied(binary: &str, params: &[TypeParamData]) -> TypeRef {
    TypeRef::Class {
        name: SmolStr::new(binary),
        args: params.iter().map(|p| type_var(&p.name)).collect(),
    }
}

/// 空的成员类型（构建器）。
fn member_class(
    outer: &ClassData,
    name: &str,
    flags: u32,
    type_params: Vec<TypeParamData>,
    decl: Option<u32>,
) -> ClassData {
    ClassData {
        name: Name::new(name),
        binary_name: format!("{}${}", outer.binary_name, name).into(),
        kind: ClassKind::Class,
        flags: Modifiers(flags | Modifiers::STATIC | Modifiers::SYNTHETIC),
        type_params,
        superclass: Some(object()),
        interfaces: Vec::new(),
        permits: Vec::new(),
        fields: Vec::new(),
        methods: Vec::new(),
        nested: Vec::new(),
        outer: Some(outer.binary_name.clone()),
        annotations: Vec::new(),
        targets: None,
        decl,
        is_source: true,
    }
}

/// 构建器上每个设置项的方法（`@Singular` 的是逐个添加、整批添加和清空三个），都返回 `ret`。
fn add_setters(builder: &mut ClassData, params: Vec<BuilderParam>, prefix: &str, ret: &TypeRef) {
    let setter = |name: &str| -> Name {
        if prefix.is_empty() {
            Name::new(name)
        } else {
            Name::new(format!("{prefix}{}", capitalize(name)))
        }
    };
    let mut push = |name: Name, params: Vec<ParamData>, decl: Option<u32>| {
        builder
            .methods
            .push(method(name, params, ret.clone(), SYNTHETIC_PUBLIC, decl));
    };
    for p in params {
        let parts = type_parts(&p.ty).filter(|(name, _)| *name != "ImmutableTable");
        let Some((single, (type_name, args))) = p.singular.clone().zip(parts) else {
            // 普通设置项
            let param = ParamData {
                name: Some(p.name.clone()),
                ty: p.ty.clone(),
                nullness: p.nullness,
            };
            push(setter(&p.name), vec![param], p.decl);
            continue;
        };
        // `@Singular`：逐个添加、整批添加、清空
        if MAP_TYPES.contains(&type_name) {
            let (key, value) = (element(args, 0), element(args, 1));
            if let Some(single) = &single {
                push(
                    setter(single),
                    vec![
                        param(&format!("{single}Key"), key.clone()),
                        param(&format!("{single}Value"), value.clone()),
                    ],
                    p.decl,
                );
            }
            let map = TypeRef::Class {
                name: SmolStr::new("java/util/Map"),
                args: vec![extends(key), extends(value)],
            };
            push(setter(&p.name), vec![param(&p.name, map)], p.decl);
        } else {
            let item = element(args, 0);
            if let Some(single) = &single {
                push(setter(single), vec![param(single, item.clone())], p.decl);
            }
            let collection = TypeRef::Class {
                name: SmolStr::new("java/util/Collection"),
                args: vec![extends(item)],
            };
            push(setter(&p.name), vec![param(&p.name, collection)], p.decl);
        }
        push(
            Name::new(format!("clear{}", capitalize(&p.name))),
            Vec::new(),
            p.decl,
        );
    }
}

/// `@Builder`：生成构建器类，并往 `data` 里加 `builder()` / `toBuilder()`。
///
/// 泛型类（或泛型静态方法）的构建器带同样的类型参数：`PairBuilder<A, B>` 的设置方法返回
/// `PairBuilder<A, B>`，`build()` 返回 `Pair<A, B>`，`builder()` 是 `static <A, B>` 的。
fn add_builder(
    data: &mut ClassData,
    spec: BuilderSpec<'_>,
    params: Vec<BuilderParam>,
    out: &mut Vec<ClassData>,
) {
    const KIND: &str = "Builder";
    let ann = spec.annotations;
    let class_name = text_option(ann, KIND, "builderClassName")
        .map(str::to_owned)
        .unwrap_or(spec.default_name);
    let access = level(ann, KIND, "access")
        .and_then(Level::bits)
        .unwrap_or(Modifiers::PUBLIC);
    let mut builder = member_class(
        data,
        &class_name,
        access,
        spec.type_params.clone(),
        spec.decl,
    );
    let builder_ty = applied(&builder.binary_name, &spec.type_params);
    let prefix = option(ann, KIND, "setterPrefix").unwrap_or("");
    add_setters(&mut builder, params, prefix, &builder_ty);
    let build_name = text_option(ann, KIND, "buildMethodName").unwrap_or("build");
    builder.methods.push(method(
        Name::new(build_name),
        Vec::new(),
        spec.build_ret,
        SYNTHETIC_PUBLIC,
        spec.decl,
    ));

    let builder_method = option(ann, KIND, "builderMethodName").unwrap_or("builder");
    if !builder_method.is_empty() && !declared(data, builder_method, 0) {
        let flags = Modifiers(access | Modifiers::STATIC | Modifiers::SYNTHETIC);
        let mut factory = method(
            Name::new(builder_method),
            Vec::new(),
            builder_ty.clone(),
            flags,
            spec.decl,
        );
        factory.type_params = spec.type_params;
        data.methods.push(factory);
    }
    if spec.allow_to_builder && flag(ann, KIND, "toBuilder") && !declared(data, "toBuilder", 0) {
        data.methods.push(method(
            Name::new("toBuilder"),
            Vec::new(),
            builder_ty,
            Modifiers(access | Modifiers::SYNTHETIC),
            spec.decl,
        ));
    }
    out.push(builder);
}

/// 不和类自己的类型参数重名的类型参数名：`C`、`C2`、`C3` …
fn fresh_type_param(base: &str, taken: &[TypeParamData]) -> Name {
    let mut candidate = base.to_owned();
    let mut n = 1;
    while taken.iter().any(|p| p.name == candidate.as_str()) {
        n += 1;
        candidate = format!("{base}{n}");
    }
    Name::new(candidate)
}

/// `@SuperBuilder` 的子类构建器继承的父类构建器：`extends Parent<String>` 时是
/// `Parent.ParentBuilder<String, C, B>`。和 Lombok 一样只看 `extends` 子句的写法，
/// 不看父类有没有 `@SuperBuilder`（没有时 Lombok 生成的代码本身就编译不过）。
fn parent_builder(superclass: Option<&TypeRef>, c: &Name, b: &Name) -> Option<TypeRef> {
    let TypeRef::Path(segments) = superclass? else {
        return None;
    };
    let (last, init) = segments.split_last()?;
    let mut path = init.to_vec();
    path.push(crate::data::PathSegment {
        name: last.name.clone(),
        args: Vec::new(),
    });
    let mut args = last.args.clone();
    args.push(type_var(c));
    args.push(type_var(b));
    path.push(crate::data::PathSegment {
        name: Name::new(format!("{}Builder", last.name)),
        args,
    });
    Some(TypeRef::Path(path))
}

/// `@SuperBuilder`，按 Lombok 实际生成的签名：
///
/// ```java
/// public static abstract class FooBuilder<T, C extends Foo<T>, B extends FooBuilder<T, C, B>>
///         extends Parent.ParentBuilder<.., C, B> {
///     public B field(..);
///     protected abstract B self();
///     public abstract C build();
/// }
/// protected Foo(FooBuilder<T, ?, ?> b);
/// public static <T> FooBuilder<T, ?, ?> builder();      // 抽象类没有
/// public FooBuilder<T, ?, ?> toBuilder();               // `toBuilder = true` 且不是抽象类
/// ```
///
/// 父类构建器的设置方法通过继承得到，在子类构建器上返回 `B`，所以先调父类的设置方法再调子类的
/// 也能接着链下去。实际创建实例的私有类 `FooBuilderImpl` 外面看不到，不生成。
fn add_super_builder(
    data: &mut ClassData,
    ann: &[SmolStr],
    params: Vec<BuilderParam>,
    out: &mut Vec<ClassData>,
) {
    const KIND: &str = "SuperBuilder";
    let class_name = format!("{}Builder", data.name);
    let own = data.type_params.clone();
    let c = fresh_type_param("C", &own);
    let b = fresh_type_param("B", &own);
    let mut type_params = own.clone();
    type_params.push(TypeParamData {
        name: c.clone(),
        bounds: vec![generic_self(data)],
    });
    let binary: SmolStr = format!("{}${}", data.binary_name, class_name).into();
    type_params.push(TypeParamData {
        name: b.clone(),
        bounds: Vec::new(),
    });
    let self_builder = applied(&binary, &type_params);
    if let Some(last) = type_params.last_mut() {
        last.bounds.push(self_builder);
    }
    let mut builder = member_class(
        data,
        &class_name,
        Modifiers::PUBLIC | Modifiers::ABSTRACT,
        type_params,
        data.decl,
    );
    if let Some(parent) = parent_builder(data.superclass.as_ref(), &c, &b) {
        builder.superclass = Some(parent);
    }
    let prefix = option(ann, KIND, "setterPrefix").unwrap_or("");
    add_setters(&mut builder, params, prefix, &type_var(&b));
    let abstract_flags = |bits: u32| Modifiers(bits | Modifiers::ABSTRACT | Modifiers::SYNTHETIC);
    let mut self_method = method(
        Name::new("self"),
        Vec::new(),
        type_var(&b),
        abstract_flags(Modifiers::PROTECTED),
        data.decl,
    );
    self_method.has_body = false;
    builder.methods.push(self_method);
    let build_name = text_option(ann, KIND, "buildMethodName").unwrap_or("build");
    let mut build = method(
        Name::new(build_name),
        Vec::new(),
        type_var(&c),
        abstract_flags(Modifiers::PUBLIC),
        data.decl,
    );
    build.has_body = false;
    builder.methods.push(build);

    // 外面看到的构建器类型：`FooBuilder<T, ?, ?>`
    let mut wildcard_args: Vec<TypeRef> = own.iter().map(|p| type_var(&p.name)).collect();
    wildcard_args.extend([
        TypeRef::Wildcard(WildcardBound::Unbounded),
        TypeRef::Wildcard(WildcardBound::Unbounded),
    ]);
    let wildcard_builder = TypeRef::Class {
        name: binary,
        args: wildcard_args,
    };
    if !has_constructor(data, &[class_name.as_str()]) {
        let ctor = constructor(
            data,
            vec![param("b", wildcard_builder.clone())],
            Modifiers::PROTECTED,
        );
        data.methods.push(ctor);
    }
    // 抽象类没有 `builder()` / `toBuilder()`：没有可以实例化的构建器
    if !data.flags.is_abstract() {
        let builder_method = option(ann, KIND, "builderMethodName").unwrap_or("builder");
        if !builder_method.is_empty() && !declared(data, builder_method, 0) {
            let mut factory = method(
                Name::new(builder_method),
                Vec::new(),
                wildcard_builder.clone(),
                Modifiers(Modifiers::PUBLIC | Modifiers::STATIC | Modifiers::SYNTHETIC),
                data.decl,
            );
            factory.type_params = own;
            data.methods.push(factory);
        }
        if flag(ann, KIND, "toBuilder") && !declared(data, "toBuilder", 0) {
            data.methods.push(method(
                Name::new("toBuilder"),
                Vec::new(),
                wildcard_builder,
                SYNTHETIC_PUBLIC,
                data.decl,
            ));
        }
    }
    out.push(builder);
}

/// `@FieldNameConstants`：内部类 `Fields`，每个实例字段一个同名的字符串常量（`asEnum` 时是枚举）。
fn field_name_constants(data: &ClassData, input: &LombokInput) -> Option<ClassData> {
    let ann = &data.annotations;
    let bits = level(ann, "FieldNameConstants", "level")
        .unwrap_or(Level::Public)
        .bits()?;
    let inner = text_option(ann, "FieldNameConstants", "innerTypeName").unwrap_or("Fields");
    let as_enum = flag(ann, "FieldNameConstants", "asEnum");
    let only_included = flag(ann, "FieldNameConstants", "onlyExplicitlyIncluded");
    let binary: SmolStr = format!("{}${}", data.binary_name, inner).into();
    let self_ty = TypeRef::class(&binary);
    let names: Vec<&FieldData> = data
        .fields
        .iter()
        .enumerate()
        .filter(|(idx, f)| {
            let list = input.annotations(*idx);
            !f.flags.is_static()
                && !f.is_enum_constant()
                && !f.name.starts_with('$')
                && !has_qualified(list, "FieldNameConstants.Exclude")
                && (!only_included || has_qualified(list, "FieldNameConstants.Include"))
        })
        .map(|(_, f)| f)
        .collect();
    let constant_flags = Modifiers::PUBLIC | Modifiers::STATIC | Modifiers::FINAL;
    let fields = names
        .iter()
        .map(|f| FieldData {
            name: f.name.clone(),
            ty: if as_enum {
                self_ty.clone()
            } else {
                TypeRef::class("java/lang/String")
            },
            flags: Modifiers(
                constant_flags
                    | if as_enum {
                        Modifiers::ENUM_CONSTANT
                    } else {
                        Modifiers::SYNTHETIC
                    },
            ),
            decl: f.decl,
            constant: (!as_enum).then(|| FieldConstant::Str(f.name.clone())),
        })
        .collect();
    let mut methods = Vec::new();
    if as_enum {
        let static_public = Modifiers(Modifiers::PUBLIC | Modifiers::STATIC | Modifiers::SYNTHETIC);
        methods.push(method(
            Name::new("values"),
            Vec::new(),
            TypeRef::Array(Box::new(self_ty.clone())),
            static_public,
            None,
        ));
        methods.push(method(
            Name::new("valueOf"),
            vec![param("name", TypeRef::class("java/lang/String"))],
            self_ty.clone(),
            static_public,
            None,
        ));
    }
    Some(ClassData {
        name: Name::new(inner),
        binary_name: binary,
        kind: if as_enum {
            ClassKind::Enum
        } else {
            ClassKind::Class
        },
        flags: Modifiers(bits | Modifiers::STATIC | Modifiers::FINAL | Modifiers::SYNTHETIC),
        type_params: Vec::new(),
        superclass: Some(if as_enum {
            TypeRef::Class {
                name: SmolStr::new("java/lang/Enum"),
                args: vec![self_ty],
            }
        } else {
            object()
        }),
        interfaces: Vec::new(),
        permits: Vec::new(),
        fields,
        methods,
        nested: Vec::new(),
        outer: Some(data.binary_name.clone()),
        annotations: Vec::new(),
        targets: None,
        decl: data.decl,
        is_source: true,
    })
}

/// 把生成的成员类型合并进用户自己写了一部分的同名类（常见的定制构建器的方式）：只补没写的成员。
pub(crate) fn merge_into(existing: &mut ClassData, generated: ClassData) {
    for m in generated.methods {
        if m.is_constructor || declared(existing, &m.name, m.params.len()) {
            continue;
        }
        existing.methods.push(m);
    }
    for f in generated.fields {
        if existing.field_named(&f.name).is_none() {
            existing.fields.push(f);
        }
    }
}

/// 按类和成员上的 Lombok 注解合成成员。生成的成员类型（构建器、`Fields`）作为返回值交给调用方登记。
pub(crate) fn apply(
    data: &mut ClassData,
    input: &LombokInput,
    config: &LombokConfig,
) -> Vec<ClassData> {
    let mut generated = Vec::new();
    // 实例方法（链式设置方法、`withX`）返回的本类类型，泛型类带上自己的类型参数
    let generic = generic_self(data);
    let self_ty = &generic;
    let class_ann = data.annotations.clone();
    let any_field_annotation = input.fields.iter().any(|f| {
        ["Getter", "Setter", "With", "Delegate"]
            .iter()
            .any(|name| has(&f.annotations, name))
    });
    const CLASS_LEVEL: &[&str] = &[
        "Getter",
        "Setter",
        "Data",
        "Value",
        "With",
        "Builder",
        "SuperBuilder",
        "NoArgsConstructor",
        "AllArgsConstructor",
        "RequiredArgsConstructor",
        "UtilityClass",
        "ToString",
        "EqualsAndHashCode",
        "FieldNameConstants",
        "StandardException",
        "FieldDefaults",
    ];
    let any_class_annotation = CLASS_LEVEL.iter().any(|name| has(&class_ann, name));
    let logger = logger_type(&class_ann);
    if !any_class_annotation
        && !any_field_annotation
        && logger.is_none()
        && input.builder_methods.is_empty()
    {
        return generated;
    }
    if !matches!(
        data.kind,
        ClassKind::Class | ClassKind::Enum | ClassKind::Record
    ) {
        return generated;
    }

    let is_data = has(&class_ann, "Data");
    let is_value = has(&class_ann, "Value") && data.kind == ClassKind::Class;
    let explicit_ctor = data.methods.iter().any(|m| m.is_constructor);

    // `@UtilityClass`：类变成 final，所有成员变成静态的，构造器私有
    if has(&class_ann, "UtilityClass") && data.kind == ClassKind::Class {
        data.flags.insert(Modifiers::FINAL);
        for field in &mut data.fields {
            field.flags.insert(Modifiers::STATIC);
        }
        for method in data.methods.iter_mut().filter(|m| !m.is_constructor) {
            method.flags.insert(Modifiers::STATIC);
        }
        if !explicit_ctor {
            let ctor = constructor(data, Vec::new(), Modifiers::PRIVATE);
            data.methods.push(ctor);
        }
    }

    // `@Delegate` 的字段：转发的方法要看字段类型的成员，留给 `lombok_expand` 补
    for extra in &input.fields {
        if has(&extra.annotations, "Delegate") {
            if let Some(field) = data.fields.get_mut(extra.idx) {
                field.flags.insert(Modifiers::LOMBOK_DELEGATE);
            }
        }
    }

    // `@FieldDefaults` / `@Value`：包级访问的实例字段改成指定的访问级别，实例字段变成 final。
    // `@PackagePrivate` / `@NonFinal` 的字段除外；静态字段保守起见不动
    let default_level = level(&class_ann, "FieldDefaults", "level")
        .or(is_value.then_some(Level::Private))
        .and_then(Level::bits)
        .filter(|bits| *bits != 0);
    let make_final = flag(&class_ann, "FieldDefaults", "makeFinal") || is_value;
    if default_level.is_some() || make_final {
        for (idx, field) in data.fields.iter_mut().enumerate() {
            if field.flags.is_static() || field.is_enum_constant() || field.name.starts_with('$') {
                continue;
            }
            let list = input.annotations(idx);
            if let Some(bits) = default_level {
                if field.flags.visibility() == Visibility::Package && !has(list, "PackagePrivate") {
                    field.flags.insert(bits);
                }
            }
            if make_final && !has(list, "NonFinal") {
                field.flags.insert(Modifiers::FINAL);
            }
        }
    }
    // `@Value` 的类是 final 的
    if is_value && !has(&class_ann, "NonFinal") {
        data.flags.insert(Modifiers::FINAL);
    }

    // 访问器
    let class_getter =
        annotated_level(&class_ann, "Getter").or((is_data || is_value).then_some(Level::Public));
    let class_setter = annotated_level(&class_ann, "Setter").or(is_data.then_some(Level::Public));
    let class_with = annotated_level(&class_ann, "With");
    let fields: Vec<(usize, FieldData)> = data.fields.iter().cloned().enumerate().collect();
    for (idx, field) in &fields {
        if field.is_enum_constant() {
            continue;
        }
        let annotations = input.annotations(*idx);
        let is_static = field.flags.is_static();
        // 类级注解不作用于静态字段和 `$` 开头的字段；字段级注解可以
        let class_applies = !is_static && !field.name.starts_with('$');
        let from_class = |level: Option<Level>| level.filter(|_| class_applies);
        let getter = annotated_level(annotations, "Getter").or(from_class(class_getter));
        let setter = annotated_level(annotations, "Setter").or(from_class(class_setter));
        let wither = annotated_level(annotations, "With").or(from_class(class_with));
        if getter.is_none() && setter.is_none() && wither.is_none() {
            continue;
        }
        let style = AccessorStyle::of(annotations, &class_ann, config);
        let Some(property) = style.property(field) else {
            continue;
        };
        let flags_for = |bits: u32| {
            let mut flags = Modifiers(bits | Modifiers::SYNTHETIC);
            if is_static {
                flags.insert(Modifiers::STATIC);
            }
            flags
        };

        if let Some(bits) = getter.and_then(Level::bits) {
            let name = if style.fluent {
                property.name.clone()
            } else if config.no_is_prefix && is_boolean(&property.ty) {
                Name::new(format!("get{}", capitalize(&property.name)))
            } else {
                getter_name(&property)
            };
            if !declared(data, &name, 0) {
                data.methods.push(method(
                    name,
                    Vec::new(),
                    field.ty.clone(),
                    flags_for(bits),
                    field.decl,
                ));
            }
        }
        let settable = !field.flags.is_final();
        if let Some(bits) = setter.and_then(Level::bits).filter(|_| settable) {
            let name = if style.fluent {
                property.name.clone()
            } else {
                setter_name(&property)
            };
            if !declared(data, &name, 1) {
                // 链式设置方法返回 `this`；静态字段的设置方法没有 `this` 可返回
                let ret = if style.chain && !is_static {
                    self_ty.clone()
                } else {
                    TypeRef::Void
                };
                data.methods.push(method(
                    name,
                    vec![field_param(field)],
                    ret,
                    flags_for(bits),
                    field.decl,
                ));
            }
        }
        // 有初值的 final 字段没法 with
        let withable = !is_static && !(field.flags.is_final() && input.initialized(*idx));
        if let Some(bits) = wither.and_then(Level::bits).filter(|_| withable) {
            let name = with_name(&property);
            if !declared(data, &name, 1) {
                data.methods.push(method(
                    name,
                    vec![field_param(field)],
                    self_ty.clone(),
                    Modifiers(bits | Modifiers::SYNTHETIC),
                    field.decl,
                ));
            }
        }
    }

    // 日志器字段
    if let Some(logger) = logger {
        let log_name = config.log_field_name.as_deref().unwrap_or("log");
        if data.field_named(log_name).is_none() {
            data.fields.push(FieldData {
                name: Name::new(log_name),
                ty: TypeRef::class(logger),
                flags: Modifiers(
                    Modifiers::PRIVATE
                        | Modifiers::STATIC
                        | Modifiers::FINAL
                        | Modifiers::SYNTHETIC,
                ),
                decl: data.decl,
                constant: None,
            });
        }
    }

    // `toString()` / `equals()` / `hashCode()` / `canEqual()`
    if matches!(data.kind, ClassKind::Class | ClassKind::Enum) {
        if (is_data || is_value || has(&class_ann, "ToString")) && !declared(data, "toString", 0) {
            let ret = TypeRef::class("java/lang/String");
            data.methods.push(method(
                Name::new("toString"),
                Vec::new(),
                ret,
                SYNTHETIC_PUBLIC,
                data.decl,
            ));
        }
        // 手写了 `equals` 或 `hashCode` 中的任何一个，Lombok 两个都不生成
        let wants_equals = is_data || is_value || has(&class_ann, "EqualsAndHashCode");
        if wants_equals
            && data.kind == ClassKind::Class
            && !declared(data, "equals", 1)
            && !declared(data, "hashCode", 0)
        {
            let boolean = TypeRef::Primitive(PrimitiveType::Boolean);
            data.methods.push(method(
                Name::new("equals"),
                vec![param("o", object())],
                boolean.clone(),
                SYNTHETIC_PUBLIC,
                data.decl,
            ));
            data.methods.push(method(
                Name::new("hashCode"),
                Vec::new(),
                TypeRef::Primitive(PrimitiveType::Int),
                SYNTHETIC_PUBLIC,
                data.decl,
            ));
            // final 且直接继承 `Object` 的类不需要 `canEqual`
            let direct_object = data
                .superclass
                .as_ref()
                .and_then(type_parts)
                .is_none_or(|(name, _)| name == "Object");
            if (!data.flags.is_final() || !direct_object) && !declared(data, "canEqual", 1) {
                data.methods.push(method(
                    Name::new("canEqual"),
                    vec![param("other", object())],
                    boolean,
                    Modifiers(Modifiers::PROTECTED | Modifiers::SYNTHETIC),
                    data.decl,
                ));
            }
        }
    }

    // 构造器
    let instance_fields: Vec<&(usize, FieldData)> = fields
        .iter()
        .filter(|(_, f)| !f.flags.is_static() && !f.is_enum_constant() && !f.name.starts_with('$'))
        .collect();
    let builder_default = |idx: usize| has_qualified(input.annotations(idx), "Builder.Default");
    // 全参：有初值的 final 字段除外（`@Builder.Default` 的初值会被移走，算在内）
    let all_args: Vec<&(usize, FieldData)> = instance_fields
        .iter()
        .copied()
        .filter(|(idx, f)| {
            !(f.flags.is_final() && input.initialized(*idx) && !builder_default(*idx))
        })
        .collect();
    // 必需：没有初值的 final 字段和 `@NonNull` 字段
    let required: Vec<&(usize, FieldData)> = instance_fields
        .iter()
        .copied()
        .filter(|(idx, f)| {
            (f.flags.is_final() || has(input.annotations(*idx), "NonNull"))
                && !input.initialized(*idx)
        })
        .collect();
    let to_params = |list: &[&(usize, FieldData)]| -> Vec<ParamData> {
        list.iter().map(|(_, f)| field_param(f)).collect()
    };
    let class_builder = has(&class_ann, "Builder");
    let super_builder = has(&class_ann, "SuperBuilder");

    if data.kind == ClassKind::Class {
        let ctor_annotation = [
            "NoArgsConstructor",
            "AllArgsConstructor",
            "RequiredArgsConstructor",
        ]
        .iter()
        .any(|name| has(&class_ann, name));
        // `@Data` / `@Value` / `@Builder` 隐含的构造器：类里已经有构造器、或者写了
        // `@XArgsConstructor` 时不生成；`@Data` / `@Value` 遇到 `@Builder` / `@SuperBuilder` 也让给它
        let implied = !explicit_ctor && !ctor_annotation;
        if has(&class_ann, "NoArgsConstructor") {
            annotated_constructor(data, &class_ann, "NoArgsConstructor", Vec::new());
        }
        if has(&class_ann, "RequiredArgsConstructor") {
            annotated_constructor(
                data,
                &class_ann,
                "RequiredArgsConstructor",
                to_params(&required),
            );
        } else if is_data && implied && !class_builder && !super_builder {
            let static_name = text_option(&class_ann, "Data", "staticConstructor");
            add_constructor(data, to_params(&required), Level::Public, static_name);
        }
        if has(&class_ann, "AllArgsConstructor") {
            annotated_constructor(data, &class_ann, "AllArgsConstructor", to_params(&all_args));
        } else if is_value && implied && !class_builder && !super_builder {
            let static_name = text_option(&class_ann, "Value", "staticConstructor");
            add_constructor(data, to_params(&all_args), Level::Public, static_name);
        }
        // `@SuperBuilder` 的构造器（接收构建器）和构建器一起生成
        if class_builder && implied {
            add_constructor(data, to_params(&all_args), Level::Package, None);
        }

        // `@StandardException`：异常的四个标准构造器
        if has(&class_ann, "StandardException") {
            let level = level(&class_ann, "StandardException", "access").unwrap_or(Level::Public);
            if let Some(bits) = level.bits() {
                let string = || TypeRef::class("java/lang/String");
                let throwable = || TypeRef::class("java/lang/Throwable");
                let variants: [(&[&str], Vec<ParamData>); 4] = [
                    (&[], Vec::new()),
                    (&["String"], vec![param("message", string())]),
                    (&["Throwable"], vec![param("cause", throwable())]),
                    (
                        &["String", "Throwable"],
                        vec![param("message", string()), param("cause", throwable())],
                    ),
                ];
                for (types, params) in variants {
                    if !has_constructor(data, types) {
                        let ctor = constructor(data, params, bits);
                        data.methods.push(ctor);
                    }
                }
            }
        }
    }

    // `@FieldNameConstants`
    if has(&class_ann, "FieldNameConstants") {
        generated.extend(field_name_constants(data, input));
    }

    // 构建器
    let field_params = || -> Vec<BuilderParam> {
        all_args
            .iter()
            .map(|(idx, f)| BuilderParam {
                name: f.name.clone(),
                ty: f.ty.clone(),
                nullness: f.flags.null_annotation(),
                decl: f.decl,
                singular: singular_of(input.annotations(*idx), &f.name),
            })
            .collect()
    };
    if data.kind != ClassKind::Enum {
        if class_builder {
            let spec = BuilderSpec {
                annotations: &class_ann,
                default_name: format!("{}Builder", data.name),
                type_params: data.type_params.clone(),
                build_ret: generic.clone(),
                decl: data.decl,
                allow_to_builder: true,
            };
            add_builder(data, spec, field_params(), &mut generated);
        } else if super_builder && data.kind == ClassKind::Class {
            add_super_builder(data, &class_ann, field_params(), &mut generated);
        }
    }
    // 构造器 / 静态方法上的 `@Builder`
    for info in &input.builder_methods {
        let Some(m) = data.methods.get(info.idx).cloned() else {
            continue;
        };
        let (default_name, build_ret, type_params) = if m.is_constructor {
            (
                format!("{}Builder", data.name),
                generic_self(data),
                data.type_params.clone(),
            )
        } else if m.flags.is_static() {
            let name = match &m.ret {
                TypeRef::Void => "Void",
                ty => match type_parts(ty) {
                    Some((name, _)) => name,
                    None => continue,
                },
            };
            (
                format!("{}Builder", capitalize(name)),
                m.ret.clone(),
                m.type_params.clone(),
            )
        } else {
            continue;
        };
        let params = m
            .params
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                let name = p.name.clone()?;
                let list = info.params.get(i).map(Vec::as_slice).unwrap_or(&[]);
                Some(BuilderParam {
                    singular: singular_of(list, &name),
                    name,
                    ty: p.ty.clone(),
                    nullness: p.nullness,
                    decl: m.decl,
                })
            })
            .collect();
        let spec = BuilderSpec {
            annotations: &info.annotations,
            default_name,
            type_params,
            build_ret,
            decl: m.decl,
            allow_to_builder: m.is_constructor,
        };
        add_builder(data, spec, params, &mut generated);
    }
    generated
}

#[cfg(test)]
mod tests {
    #[test]
    fn lombok_config_files_stack() {
        let mut config = super::LombokConfig::default();
        config.apply_file(
            "# root\nlombok.accessors.chain = true\nlombok.accessors.prefix += m\nlombok.accessors.prefix += _\nlombok.log.fieldName = LOG\n",
        );
        config.apply_file("lombok.accessors.prefix -= _\nclear lombok.accessors.chain\nlombok.getter.noIsPrefix = true\n");
        assert_eq!(config.chain, None);
        assert_eq!(config.prefixes, vec!["m".to_owned()]);
        assert!(config.no_is_prefix);
        assert_eq!(config.log_field_name.as_deref(), Some("LOG"));
    }

    use syntax::ast::CompilationUnit;

    use crate::{
        data::{ClassData, ClassKind, FieldConstant, TypeRef, Visibility},
        lower::lower_file,
    };

    fn class_of(text: &str, class: &str) -> ClassData {
        let (tree, _) = lower_file(&CompilationUnit::parse(text).tree());
        let data = tree
            .classes
            .iter()
            .find(|c| c.name == class)
            .unwrap_or_else(|| panic!("没有类 {class}"));
        ClassData::clone(data)
    }

    /// 方法（构造器写作 `<init>`）的访问级别。
    fn visibility(data: &ClassData, name: &str, arity: usize) -> Visibility {
        data.methods
            .iter()
            .find(|m| {
                let n = if m.is_constructor { "<init>" } else { &m.name };
                n == name && m.params.len() == arity
            })
            .unwrap_or_else(|| panic!("没有方法 {name}/{arity}"))
            .flags
            .visibility()
    }

    fn methods_of(text: &str, class: &str) -> Vec<String> {
        let data = class_of(text, class);
        let mut names: Vec<String> = data
            .methods
            .iter()
            .map(|m| {
                if m.is_constructor {
                    format!("<init>/{}", m.params.len())
                } else {
                    format!("{}/{}", m.name, m.params.len())
                }
            })
            .collect();
        names.sort();
        names
    }

    #[test]
    fn data_generates_accessors_and_required_constructor() {
        let methods = methods_of(
            "import lombok.Data;\n@Data class User { private final long id; private String name; private boolean active; private boolean isAdmin; static int count; }",
            "User",
        );
        assert_eq!(
            methods,
            [
                "<init>/1",
                "canEqual/1",
                "equals/1",
                "getId/0",
                "getName/0",
                "hashCode/0",
                "isActive/0",
                "isAdmin/0",
                "setActive/1",
                "setAdmin/1",
                "setName/1",
                "toString/0",
            ]
        );
    }

    #[test]
    fn field_level_annotations_and_existing_methods() {
        let methods = methods_of(
            "class A { @lombok.Getter @lombok.Setter int x; @lombok.Getter int y; int z; int getY() { return 1; } }",
            "A",
        );
        // 已有的 getY 不重复生成；没有注解的 z 不生成；还有隐式无参构造器
        assert_eq!(methods, ["<init>/0", "getX/0", "getY/0", "setX/1"]);
    }

    #[test]
    fn builder_creates_nested_class() {
        let text = "@lombok.Builder class Point { int x; int y; }";
        assert_eq!(methods_of(text, "Point"), ["<init>/2", "builder/0"]);
        assert_eq!(methods_of(text, "PointBuilder"), ["build/0", "x/1", "y/1"]);
        let (tree, _) = lower_file(&CompilationUnit::parse(text).tree());
        let builder = tree
            .classes
            .iter()
            .find(|c| c.name == "PointBuilder")
            .unwrap();
        assert_eq!(builder.binary_name, "Point$PointBuilder");
        assert_eq!(builder.outer.as_deref(), Some("Point"));
    }

    #[test]
    fn value_and_logger() {
        let text = "@lombok.Value @lombok.extern.slf4j.Slf4j class V { String a; int b; }";
        assert_eq!(
            methods_of(text, "V"),
            [
                "<init>/2",
                "equals/1",
                "getA/0",
                "getB/0",
                "hashCode/0",
                "toString/0"
            ]
        );
        let (tree, _) = lower_file(&CompilationUnit::parse(text).tree());
        let data = tree.classes.iter().find(|c| c.name == "V").unwrap();
        assert!(data
            .fields
            .iter()
            .filter(|f| f.name != "log")
            .all(|f| f.flags.is_final()));
        assert!(data.field_named("log").is_some());
    }

    #[test]
    fn accessor_names_map_back_to_field_names() {
        use super::AccessorKind;
        use crate::data::{FieldData, Modifiers, PrimitiveType, TypeRef};

        let field = |name: &str, ty: TypeRef| FieldData {
            name: name.into(),
            ty,
            flags: Modifiers::default(),
            decl: None,
            constant: None,
        };
        let string = field("name", TypeRef::class("java/lang/String"));
        let flag = field("active", TypeRef::Primitive(PrimitiveType::Boolean));
        let prefixed = field("isAdmin", TypeRef::Primitive(PrimitiveType::Boolean));
        let upper = field("Effect", TypeRef::class("java/lang/String"));

        let back = |kind: AccessorKind, f: &FieldData, accessor: &str| {
            kind.field_name_for(f, accessor).map(|n| n.to_string())
        };
        assert_eq!(
            back(AccessorKind::Getter, &string, "getTitle").as_deref(),
            Some("title")
        );
        assert_eq!(
            back(AccessorKind::Setter, &string, "setTitle").as_deref(),
            Some("title")
        );
        assert_eq!(
            back(AccessorKind::SameName, &string, "title").as_deref(),
            Some("title")
        );
        assert_eq!(back(AccessorKind::Getter, &string, "title"), None);
        assert_eq!(back(AccessorKind::Getter, &string, "isTitle"), None);
        assert_eq!(
            back(AccessorKind::Getter, &flag, "isOn").as_deref(),
            Some("on")
        );
        assert_eq!(
            back(AccessorKind::Setter, &prefixed, "setRoot").as_deref(),
            Some("isRoot")
        );
        assert_eq!(
            back(AccessorKind::Getter, &upper, "getAction").as_deref(),
            Some("Action")
        );
    }

    #[test]
    fn plain_classes_are_untouched() {
        assert_eq!(methods_of("class P { int x; }", "P"), ["<init>/0"]);
    }

    #[test]
    fn access_levels_on_fields_and_classes() {
        let text = "import lombok.*;\n@Getter @Setter(AccessLevel.PROTECTED) class A { @Getter(AccessLevel.NONE) int hidden; @Setter(value = AccessLevel.PRIVATE) int x; int y; static int s; }";
        let data = class_of(text, "A");
        assert_eq!(
            methods_of(text, "A"),
            [
                "<init>/0",
                "getX/0",
                "getY/0",
                "setHidden/1",
                "setX/1",
                "setY/1"
            ]
        );
        assert_eq!(visibility(&data, "getX", 0), Visibility::Public);
        assert_eq!(visibility(&data, "setX", 1), Visibility::Private);
        assert_eq!(visibility(&data, "setY", 1), Visibility::Protected);
        // `@Data` 遇到类上的 `@Setter(NONE)`：不生成设置方法
        assert_eq!(
            methods_of(
                "@lombok.Data @lombok.Setter(lombok.AccessLevel.NONE) class B { int v; }",
                "B"
            ),
            [
                "<init>/0",
                "canEqual/1",
                "equals/1",
                "getV/0",
                "hashCode/0",
                "toString/0"
            ]
        );
    }

    #[test]
    fn constructor_options() {
        let text = "@lombok.RequiredArgsConstructor(staticName = \"of\") @lombok.AllArgsConstructor(access = lombok.AccessLevel.PRIVATE) @lombok.NoArgsConstructor(force = true) class B<T> { private final T a; private final int b = 1; @lombok.NonNull String c; String d; }";
        let data = class_of(text, "B");
        assert_eq!(
            methods_of(text, "B"),
            ["<init>/0", "<init>/2", "<init>/3", "of/2"]
        );
        assert_eq!(visibility(&data, "<init>", 0), Visibility::Public);
        assert_eq!(visibility(&data, "<init>", 2), Visibility::Private);
        assert_eq!(visibility(&data, "<init>", 3), Visibility::Private);
        let of = data.methods.iter().find(|m| m.name == "of").unwrap();
        assert!(of.flags.is_static());
        assert_eq!(of.type_params.len(), 1);
    }

    #[test]
    fn builder_options_singular_and_default() {
        let text = "@lombok.Builder(builderMethodName = \"make\", buildMethodName = \"create\", toBuilder = true, setterPrefix = \"with\") class C { private String name; @lombok.Singular private java.util.List<String> items; @lombok.Singular(\"entry\") java.util.Map<String, Integer> entries; @lombok.Builder.Default private final int size = 3; private final int fixed = 1; }";
        assert_eq!(methods_of(text, "C"), ["<init>/4", "make/0", "toBuilder/0"]);
        assert_eq!(
            visibility(&class_of(text, "C"), "<init>", 4),
            Visibility::Package
        );
        assert_eq!(
            methods_of(text, "CBuilder"),
            [
                "clearEntries/0",
                "clearItems/0",
                "create/0",
                "withEntries/1",
                "withEntry/2",
                "withItem/1",
                "withItems/1",
                "withName/1",
                "withSize/1",
            ]
        );
    }

    #[test]
    fn singular_name_same_as_plural_keeps_both_adders() {
        // Lombok 照样生成逐个添加的方法，它和整批添加的方法只是同名重载
        let text = "@lombok.Builder class C { @lombok.Singular(\"metadata\") java.util.Map<String, String> metadata; @lombok.Singular(\"items\") java.util.List<String> items; }";
        assert_eq!(
            methods_of(text, "CBuilder"),
            [
                "build/0",
                "clearItems/0",
                "clearMetadata/0",
                "items/1",
                "items/1",
                "metadata/1",
                "metadata/2",
            ]
        );
    }

    #[test]
    fn builder_on_methods_and_constructors() {
        let text = "class D { @lombok.Builder static D of(String a, int b) { return null; } }";
        assert!(methods_of(text, "D").contains(&"builder/0".to_owned()));
        assert_eq!(methods_of(text, "DBuilder"), ["a/1", "b/1", "build/0"]);
        let text = "class E { @lombok.Builder(builderMethodName = \"b\") E(String x, @lombok.Singular java.util.Set<String> tags) {} }";
        assert_eq!(methods_of(text, "E"), ["<init>/2", "b/0"]);
        assert_eq!(
            methods_of(text, "EBuilder"),
            ["build/0", "clearTags/0", "tag/1", "tags/1", "x/1"]
        );
    }

    fn type_param_names(data: &ClassData) -> Vec<String> {
        data.type_params
            .iter()
            .map(|p| p.name.to_string())
            .collect()
    }

    fn find<'a>(data: &'a ClassData, name: &str) -> &'a crate::data::MethodData {
        data.methods
            .iter()
            .find(|m| m.name == name)
            .unwrap_or_else(|| panic!("没有方法 {name}"))
    }

    fn generic(name: &str, args: &[&str]) -> TypeRef {
        TypeRef::Class {
            name: name.into(),
            args: args.iter().map(|a| TypeRef::TypeVar((*a).into())).collect(),
        }
    }

    #[test]
    fn generic_builders_carry_type_params() {
        let text = "@lombok.Builder(toBuilder = true) class P<A, B extends Comparable<B>> { A a; B b; @lombok.Builder(builderMethodName = \"make\", builderClassName = \"MakeBuilder\") static <X> P<X, Integer> of(X x) { return null; } }";
        let p = class_of(text, "P");
        let builder = find(&p, "builder");
        assert!(builder.flags.is_static());
        assert_eq!(builder.type_params, p.type_params);
        assert_eq!(builder.ret, generic("P$PBuilder", &["A", "B"]));
        assert_eq!(
            find(&p, "toBuilder").ret,
            generic("P$PBuilder", &["A", "B"])
        );
        let pb = class_of(text, "PBuilder");
        assert_eq!(pb.type_params, p.type_params);
        assert_eq!(find(&pb, "a").ret, generic("P$PBuilder", &["A", "B"]));
        assert_eq!(find(&pb, "build").ret, generic("P", &["A", "B"]));

        // 泛型静态方法上的 `@Builder`：构建器带方法的类型参数
        assert_eq!(find(&p, "make").ret, generic("P$MakeBuilder", &["X"]));
        let make_params: Vec<&str> = find(&p, "make")
            .type_params
            .iter()
            .map(|p| p.name.as_str())
            .collect();
        assert_eq!(make_params, ["X"]);
        let mb = class_of(text, "MakeBuilder");
        assert_eq!(type_param_names(&mb), ["X"]);
        assert_eq!(find(&mb, "x").ret, generic("P$MakeBuilder", &["X"]));
    }

    #[test]
    fn super_builder_signatures() {
        let text = "import lombok.experimental.SuperBuilder;\n@SuperBuilder abstract class Base<T> { T id; @lombok.Singular java.util.List<String> tags; }\n@SuperBuilder(toBuilder = true) class Child extends Base<String> { int age; }\n@SuperBuilder class Leaf extends Child { int x; }";
        // 抽象类没有 `builder()`，只有接收构建器的受保护构造器
        let base = class_of(text, "Base");
        assert_eq!(methods_of(text, "Base"), ["<init>/1"]);
        assert_eq!(visibility(&base, "<init>", 1), Visibility::Protected);
        let base_builder = class_of(text, "BaseBuilder");
        assert!(base_builder.flags.is_abstract() && base_builder.flags.is_static());
        assert_eq!(type_param_names(&base_builder), ["T", "C", "B"]);
        assert_eq!(
            base_builder.type_params[1].bounds,
            [generic("Base", &["T"])]
        );
        assert_eq!(
            base_builder.type_params[2].bounds,
            [generic("Base$BaseBuilder", &["T", "C", "B"])]
        );
        assert_eq!(
            methods_of(text, "BaseBuilder"),
            [
                "build/0",
                "clearTags/0",
                "id/1",
                "self/0",
                "tag/1",
                "tags/1"
            ]
        );
        assert_eq!(find(&base_builder, "id").ret, TypeRef::TypeVar("B".into()));
        assert_eq!(
            find(&base_builder, "build").ret,
            TypeRef::TypeVar("C".into())
        );

        // `toBuilder` 只在要求时生成；构建器继承父类的构建器
        assert_eq!(
            methods_of(text, "Child"),
            ["<init>/1", "builder/0", "toBuilder/0"]
        );
        assert_eq!(methods_of(text, "Leaf"), ["<init>/1", "builder/0"]);
        let child = class_of(text, "Child");
        let wildcard = TypeRef::Wildcard(crate::data::WildcardBound::Unbounded);
        let child_builder_ty = TypeRef::Class {
            name: "Child$ChildBuilder".into(),
            args: vec![wildcard.clone(), wildcard],
        };
        assert_eq!(find(&child, "builder").ret, child_builder_ty);
        assert_eq!(find(&child, "toBuilder").ret, child_builder_ty);
        let child_builder = class_of(text, "ChildBuilder");
        assert_eq!(type_param_names(&child_builder), ["C", "B"]);
        let Some(TypeRef::Path(segments)) = &child_builder.superclass else {
            panic!("父类构建器: {:?}", child_builder.superclass);
        };
        let names: Vec<&str> = segments.iter().map(|s| s.name.as_str()).collect();
        assert_eq!(names, ["Base", "BaseBuilder"]);
        assert_eq!(segments[1].args.len(), 3);
        assert_eq!(segments[1].args[2], TypeRef::TypeVar("B".into()));
        assert_eq!(
            methods_of(text, "ChildBuilder"),
            ["age/1", "build/0", "self/0"]
        );
    }

    #[test]
    fn super_builder_type_params_avoid_clashes() {
        let text = "@lombok.experimental.SuperBuilder class G<B> { B c; }";
        assert_eq!(
            type_param_names(&class_of(text, "GBuilder")),
            ["B", "C", "B2"]
        );
        // `@Data` / `@Value` 遇到 `@SuperBuilder` 不再生成自己的构造器
        let text = "@lombok.Data @lombok.experimental.SuperBuilder class D { private final String a; private int b; }";
        let ctors: Vec<String> = methods_of(text, "D")
            .into_iter()
            .filter(|m| m.starts_with("<init>"))
            .collect();
        assert_eq!(ctors, ["<init>/1"]);
        let d = class_of(text, "D");
        let ctor = d.methods.iter().find(|m| m.is_constructor).unwrap();
        assert!(matches!(&ctor.params[0].ty, TypeRef::Class { name, .. } if name == "D$DBuilder"));
    }

    #[test]
    fn user_written_builder_is_completed() {
        let text = "@lombok.Builder class K { String a; String b; static class KBuilder { KBuilder a(String a) { return this; } } }";
        assert_eq!(
            methods_of(text, "KBuilder"),
            ["<init>/0", "a/1", "b/1", "build/0"]
        );
        let (tree, _) = lower_file(&CompilationUnit::parse(text).tree());
        assert_eq!(
            tree.classes.iter().filter(|c| c.name == "KBuilder").count(),
            1
        );
    }

    #[test]
    fn accessor_prefixes() {
        let text = "@lombok.Getter @lombok.Setter @lombok.experimental.Accessors(prefix = {\"m\", \"_\"}, chain = true) class F { String mName; boolean mActive; String _id; String other; String mixed; }";
        let data = class_of(text, "F");
        assert_eq!(
            methods_of(text, "F"),
            [
                "<init>/0",
                "getId/0",
                "getName/0",
                "isActive/0",
                "setActive/1",
                "setId/1",
                "setName/1"
            ]
        );
        let set_name = data.methods.iter().find(|m| m.name == "setName").unwrap();
        assert_eq!(set_name.ret, TypeRef::class("F"));
    }

    #[test]
    fn field_defaults_and_required_args() {
        let text = "@lombok.experimental.FieldDefaults(level = lombok.AccessLevel.PRIVATE, makeFinal = true) @lombok.RequiredArgsConstructor class G { String a; @lombok.experimental.NonFinal int b; public int c; static int s; }";
        let data = class_of(text, "G");
        let field = |name: &str| data.field_named(name).unwrap().1.flags;
        assert!(field("a").is_final() && field("a").visibility() == Visibility::Private);
        assert!(!field("b").is_final() && field("b").visibility() == Visibility::Private);
        assert!(field("c").is_final() && field("c").visibility() == Visibility::Public);
        assert!(!field("s").is_final() && field("s").visibility() == Visibility::Package);
        assert_eq!(methods_of(text, "G"), ["<init>/2"]);
    }

    #[test]
    fn field_name_constants_and_standard_exception() {
        let text = "@lombok.experimental.FieldNameConstants class H { String name; int age; @FieldNameConstants.Exclude int x; static int s; }";
        let fields = class_of(text, "Fields");
        assert_eq!(fields.binary_name, "H$Fields");
        let names: Vec<_> = fields.fields.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(names, ["name", "age"]);
        assert!(fields.fields[0].flags.is_static());
        assert_eq!(
            fields.fields[0].constant,
            Some(FieldConstant::Str("name".into()))
        );
        let text = "@lombok.experimental.FieldNameConstants(asEnum = true, innerTypeName = \"Props\") class H2 { String name; }";
        assert_eq!(class_of(text, "Props").kind, ClassKind::Enum);

        let text = "@lombok.experimental.StandardException class MyEx extends Exception { MyEx(String message) { super(message); } }";
        assert_eq!(
            methods_of(text, "MyEx"),
            ["<init>/0", "<init>/1", "<init>/1", "<init>/2"]
        );
    }

    #[test]
    fn to_string_equals_and_with() {
        assert_eq!(
            methods_of("@lombok.ToString @lombok.EqualsAndHashCode class I {}", "I"),
            [
                "<init>/0",
                "canEqual/1",
                "equals/1",
                "hashCode/0",
                "toString/0"
            ]
        );
        // 手写了 `equals` 时 `hashCode` 也不生成
        assert_eq!(
            methods_of(
                "@lombok.EqualsAndHashCode class I2 { public boolean equals(Object o) { return true; } }",
                "I2"
            ),
            ["<init>/0", "equals/1"]
        );
        assert_eq!(
            methods_of(
                "@lombok.With @lombok.AllArgsConstructor class J { final int a; final int b = 2; }",
                "J"
            ),
            ["<init>/1", "withA/1"]
        );
    }

    #[test]
    fn data_with_builder_has_only_the_builder_constructor() {
        let methods = methods_of("@lombok.Data @lombok.Builder class L { String a; }", "L");
        assert!(methods.contains(&"<init>/1".to_owned()));
        assert!(!methods.contains(&"<init>/0".to_owned()));
    }

    #[test]
    fn singular_names() {
        use super::singularize;
        let cases = [
            ("items", Some("item")),
            ("entries", Some("entry")),
            ("addresses", Some("address")),
            ("boxes", Some("box")),
            ("userIds", Some("userId")),
            ("people", Some("person")),
            ("data", None),
        ];
        for (plural, single) in cases {
            assert_eq!(singularize(plural).as_deref(), single, "{plural}");
        }
    }
}
