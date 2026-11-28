//! 局部变量和 `@Nullable` 字段的空值数据流分析。
//!
//! 沿着方法体跟踪每个局部变量 / 形参"一定是 null"还是"一定不是 null"，报两类问题：
//!
//! - 解引用一个此处一定为 null 的变量（`x.foo()`、`x.f`、`x[i]`）；
//! - `x == null` / `x != null` 的结果在此处是确定的（条件恒真或恒假）。
//!
//! 空值注解（`@Nullable` / `@NotNull` 等）参与分析：标了 `@Nullable` 的方法返回值、字段和形参
//! "可能是 null"，解引用它们（没检查过时）报警告；把 null 传给 `@NotNull` 形参、
//! 从 `@NotNull` 方法返回 null 也报警告。方法没写注解时沿用被它覆写的方法上的注解；
//! `@NullMarked` 一类的类 / 包 / 模块级默认值让没写注解的形参和返回值默认不为 null
//! （类型变量除外）；依赖库里的类按 class 文件上（以及同一个 jar 里的 `package-info.class`、
//! `module-info.class` 上）的注解套用默认值。
//!
//! `this` 上标了 `@Nullable` 的字段像局部变量一样跟踪，初始为"可能是 null"；判空得到的事实
//! 在下一次方法调用（可能修改字段）时作废。分析是保守的，拿不准的地方一律当作未知：
//! 循环、`try`、`switch`、带标签的语句在入口处丢掉内部赋值过的变量的信息，
//! 出口处只保留入口时就成立的事实。

use std::{cell::RefCell, sync::Arc};

use base_db::{Db, FileKind, ModuleId};
use hir::{
    class_data, BinaryAnnotation, BodyId, ClassData, ClassId, FieldId, GenericOwner,
    InferenceResult, LocalId, LocalKind, MethodId, MethodSig, Modifiers, NullAnnotation,
    Resolution, Subst, Ty, TypeParamId, Visibility,
};
use rustc_hash::{FxHashMap, FxHashSet};
use syntax::{
    ast::{self, AstNode},
    SyntaxKind, SyntaxNode, TextRange,
};

use crate::{flow::has_break, view::View, Diagnostic, DiagnosticCode, Severity};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Nullness {
    Null,
    NotNull,
    /// 来自 `@Nullable`：可能是 null，用之前应当检查
    MaybeNull,
}

/// 被跟踪的变量：局部变量 / 形参，或者 `this` 上（以及静态的）标了 `@Nullable` 的字段。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Var {
    Local(LocalId),
    Field(FieldId),
}

/// 变量 → 已知的空值状态；不在表里的是未知。
type State = FxHashMap<Var, Nullness>;

/// 两条路径汇合：只保留两边一致的事实。`None` 表示那条路径走不到。
fn join(a: Option<State>, b: Option<State>) -> Option<State> {
    match (a, b) {
        (None, other) | (other, None) => other,
        (Some(a), Some(b)) => Some(
            a.into_iter()
                .filter_map(|(id, x)| {
                    let y = *b.get(&id)?;
                    if x == y {
                        Some((id, x))
                    } else if x == Nullness::MaybeNull || y == Nullness::MaybeNull {
                        // 某条路径上可能是 null，汇合后仍然可能是 null
                        Some((id, Nullness::MaybeNull))
                    } else {
                        None
                    }
                })
                .collect(),
        ),
    }
}

/// 某一层作用域（方法、类、包、模块）对没写空值注解的形参 / 返回值的规定：
/// `Some(true)` 默认不为 null，`Some(false)` 明确不套用默认值，`None` 看外层。
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
struct Defaults {
    params: Option<bool>,
    returns: Option<bool>,
}

impl Defaults {
    const MARKED: Defaults = Defaults {
        params: Some(true),
        returns: Some(true),
    };
    const UNMARKED: Defaults = Defaults {
        params: Some(false),
        returns: Some(false),
    };

    fn settled(self) -> bool {
        self.params.is_some() && self.returns.is_some()
    }

    /// 内层没有规定的位置用 `outer` 的规定补上。
    fn or(self, outer: Defaults) -> Defaults {
        Defaults {
            params: self.params.or(outer.params),
            returns: self.returns.or(outer.returns),
        }
    }

    /// 一个注解（简单名）规定的默认值。
    fn of_annotation(simple: &str) -> Defaults {
        match simple {
            // JSpecify、Spring、Eclipse（不带参数时管形参、返回值和字段）
            "NullMarked" | "NonNullApi" | "NonNullByDefault" => Defaults::MARKED,
            "NullUnmarked" => Defaults::UNMARKED,
            // JSR-305 一类
            "ParametersAreNonnullByDefault" => Defaults {
                params: Some(true),
                returns: None,
            },
            "ParametersAreNullableByDefault" => Defaults {
                params: Some(false),
                returns: None,
            },
            "ReturnValuesAreNonnullByDefault" | "MethodsReturnNonnullByDefault" => Defaults {
                params: None,
                returns: Some(true),
            },
            _ => Defaults::default(),
        }
    }

    /// 一组注解名（源码里写的样子或 class 文件里的描述符）规定的默认值。
    fn of_names<'a>(names: impl IntoIterator<Item = &'a str>) -> Defaults {
        names.into_iter().fold(Defaults::default(), |acc, name| {
            acc.or(Defaults::of_annotation(simple_annotation_name(name)))
        })
    }

    /// class 文件里的一组注解规定的默认值（带参数的注解按读出来的元素值）。
    fn of_binary(annotations: &[BinaryAnnotation]) -> Defaults {
        annotations
            .iter()
            .fold(Defaults::default(), |acc, annotation| {
                let element = |name: &str| {
                    annotation
                        .elements
                        .iter()
                        .find(|(n, _)| n == name)
                        .map(|(_, values)| values.join(","))
                };
                let own = match simple_annotation_name(&annotation.name) {
                    "DefaultQualifier" => default_qualifier_of(
                        &element("value").unwrap_or_default(),
                        element("locations").as_deref(),
                    ),
                    "NonNullByDefault" => non_null_by_default_of(element("value").as_deref()),
                    simple => Defaults::of_annotation(simple),
                };
                acc.or(own)
            })
    }

    /// 修饰符列表上的注解规定的默认值；还认 Checker Framework 的
    /// `@DefaultQualifier(NonNull.class)`（可以用 `locations` 限定位置）和 Eclipse 的
    /// `@NonNullByDefault({DefaultLocation.PARAMETER, …})`。
    fn of_modifiers(list: Option<ast::ModifierList>) -> Defaults {
        let Some(list) = list else {
            return Defaults::default();
        };
        list.annotations()
            .fold(Defaults::default(), |acc, annotation| {
                let Some(name) = annotation
                    .name()
                    .and_then(|n| n.name_ref())
                    .map(|n| n.text())
                else {
                    return acc;
                };
                let own = match name.as_str() {
                    "DefaultQualifier" => default_qualifier(&annotation),
                    "NonNullByDefault" => non_null_by_default(&annotation),
                    _ => Defaults::of_annotation(&name),
                };
                acc.or(own)
            })
    }
}

/// 文本里有没有 `word` 这个词（按标识符切分，`EXCEPTION_PARAMETER` 不算 `PARAMETER`）。
fn has_word(text: &str, word: &str) -> bool {
    text.split(|c: char| !c.is_alphanumeric() && c != '_')
        .any(|t| t == word)
}

/// `@DefaultQualifier(NonNull.class)` / `@DefaultQualifier(value = NonNull.class, locations = …)`。
fn default_qualifier(annotation: &ast::Annotation) -> Defaults {
    let Some(args) = annotation.arg_list() else {
        return Defaults::default();
    };
    let text = args.syntax().text().to_string();
    let qualifier = text
        .split(".class")
        .next()
        .unwrap_or("")
        .rsplit(|c: char| !c.is_alphanumeric() && c != '_')
        .next()
        .unwrap_or("");
    default_qualifier_of(
        qualifier,
        text.split_once("locations").map(|(_, locations)| locations),
    )
}

/// `@DefaultQualifier`：限定符（名字或描述符）是 `NonNull` 一类时，按 `locations`
/// （不写时是 `ALL`）规定默认值。
fn default_qualifier_of(qualifier: &str, locations: Option<&str>) -> Defaults {
    if NullAnnotation::from_name(qualifier) != NullAnnotation::NotNull {
        return Defaults::default();
    }
    let Some(locations) = locations else {
        return Defaults::MARKED;
    };
    let all = has_word(locations, "ALL");
    Defaults {
        params: (all || has_word(locations, "PARAMETER")).then_some(true),
        returns: (all || has_word(locations, "RETURN")).then_some(true),
    }
}

/// Eclipse 的 `@NonNullByDefault` / `@NonNullByDefault({DefaultLocation.PARAMETER, …})` /
/// `@NonNullByDefault(false)`。
fn non_null_by_default(annotation: &ast::Annotation) -> Defaults {
    let text = annotation
        .arg_list()
        .map(|args| args.syntax().text().to_string())
        .unwrap_or_default();
    let inner = text
        .trim()
        .trim_start_matches('(')
        .trim_end_matches(')')
        .trim();
    non_null_by_default_of((!inner.is_empty()).then_some(inner))
}

/// `@NonNullByDefault` 的 `value`：不写时管形参、返回值（和字段），写了时只管列出的位置
/// （`{}` 和老版本的 `false` 表示取消外层的默认值）。
fn non_null_by_default_of(value: Option<&str>) -> Defaults {
    let Some(value) = value else {
        return Defaults::MARKED;
    };
    if has_word(value, "false") {
        Defaults::UNMARKED
    } else if has_word(value, "true") {
        Defaults::MARKED
    } else {
        Defaults {
            params: Some(has_word(value, "PARAMETER")),
            returns: Some(has_word(value, "RETURN_TYPE")),
        }
    }
}

/// 规定作用域默认值的注解（`@NullMarked`、`@NonNullByDefault` …），不是写在某个位置上的空值注解。
fn is_scope_annotation(simple: &str) -> bool {
    Defaults::of_annotation(simple) != Defaults::default()
        || matches!(simple, "DefaultQualifier" | "NonNullFields")
}

/// 名字和空值有关、但不是规定作用域默认值的注解。
fn is_null_related(name: &str) -> bool {
    let simple = simple_annotation_name(name);
    simple.to_ascii_lowercase().contains("null") && !is_scope_annotation(simple)
}

fn simple_annotation_name(name: &str) -> &str {
    let name = name.strip_suffix(';').unwrap_or(name);
    name.rsplit(['/', '.', '$']).next().unwrap_or(name)
}

/// 工作区里 `package-info.java` / `module-info.java` 上的默认值。
#[derive(Default, PartialEq, Eq, Debug)]
struct ScopeDefaults {
    /// 包名（斜杠形式）→ 默认值
    packages: FxHashMap<String, Defaults>,
    /// 构建模块 → 它的 `module-info.java` 上的默认值
    modules: FxHashMap<Option<ModuleId>, Defaults>,
}

#[salsa::tracked]
fn scope_defaults(db: &dyn Db) -> Arc<ScopeDefaults> {
    let mut res = ScopeDefaults::default();
    let workspace = base_db::workspace(db);
    for (file_id, file) in workspace.files(db).workspace_files() {
        let name = file.name(db);
        if name != "package-info" && name != "module-info" {
            continue;
        }
        let cu = base_db::parse(db, file).tree();
        if let Some(package) = cu.package() {
            let defaults = Defaults::of_modifiers(package.modifier_list());
            if defaults != Defaults::default() {
                if let Some(qualified) = package.name() {
                    res.packages
                        .insert(qualified.segments().join("/"), defaults);
                }
            }
        }
        if let Some(module) = cu.module() {
            let defaults = Defaults::of_modifiers(
                module.syntax().children().find_map(ast::ModifierList::cast),
            );
            if defaults != Defaults::default() {
                let module = match base_db::file_entry(db, file_id).map(|e| e.kind) {
                    Some(FileKind::Workspace { module, .. }) => module,
                    _ => None,
                };
                res.modules.insert(module, defaults);
            }
        }
    }
    Arc::new(res)
}

/// 一个位置（返回值 / 形参）最终采用的空值注解和它的来历。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Effective {
    nullness: NullAnnotation,
    origin: Origin,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Origin {
    /// 写在这个声明上
    Declared,
    /// 来自被覆写的方法
    Inherited,
    /// 来自 `@NullMarked` 一类的默认值
    Default,
}

impl Effective {
    const UNKNOWN: Effective = Effective {
        nullness: NullAnnotation::Unknown,
        origin: Origin::Declared,
    };

    /// 写明的注解优先；否则看被覆写的方法（`Some(Unknown)` 表示它们互相矛盾）和默认值，
    /// 两者矛盾时当作未知。
    fn combine(
        declared: NullAnnotation,
        inherited: Option<NullAnnotation>,
        default_not_null: bool,
    ) -> Effective {
        let (nullness, origin) = match (declared, inherited) {
            (NullAnnotation::Unknown, Some(inherited)) => {
                if default_not_null && inherited != NullAnnotation::NotNull {
                    (NullAnnotation::Unknown, Origin::Declared)
                } else {
                    (inherited, Origin::Inherited)
                }
            }
            (NullAnnotation::Unknown, None) if default_not_null => {
                (NullAnnotation::NotNull, Origin::Default)
            }
            (declared, _) => (declared, Origin::Declared),
        };
        Effective { nullness, origin }
    }
}

/// 被覆写的方法上写明的空值注解：`None` 是都没写，`Some(Unknown)` 是互相矛盾。
#[derive(Default)]
struct Inherited {
    ret: Option<NullAnnotation>,
    params: Vec<Option<NullAnnotation>>,
}

fn merge_inherited(slot: &mut Option<NullAnnotation>, value: NullAnnotation) {
    if value == NullAnnotation::Unknown {
        return;
    }
    *slot = match *slot {
        None => Some(value),
        Some(old) if old == value => Some(old),
        Some(_) => Some(NullAnnotation::Unknown),
    };
}

/// 方法返回值和各形参最终采用的空值注解。
struct MethodNullness {
    ret: Effective,
    params: Vec<Effective>,
}

/// 类所在的包（斜杠形式）。
fn class_package(db: &dyn Db, class: ClassId) -> String {
    let name = class.binary_name(db);
    name.rsplit_once('/')
        .map_or_else(String::new, |(p, _)| p.to_owned())
}

/// 擦除后的类型完全已知（没有推断不出来的部分）。
fn is_known(ty: &Ty) -> bool {
    match ty {
        Ty::Unknown => false,
        Ty::Array(element) => is_known(element),
        _ => true,
    }
}

/// 类型是具体的类 / 数组类型，`@NullMarked` 下没写注解时不为 null。类型变量的空值性
/// 取决于实例化，通配符、交叉类型和推断不出来的类型都不套用默认值。
fn takes_default(ty: &Ty) -> bool {
    matches!(ty, Ty::Class(..) | Ty::Array(_))
}

/// 声明上有没有我们不按"没写注解"处理的空值相关注解：不认识的（`@ParametricNullness`、
/// `@PolyNull`、`@MonotonicNonNull` …）、修饰数组元素的、或者写在类型内部的
/// （`Map.@Nullable Entry`）。这样的位置不套用默认值。
fn has_other_null_annotation(
    modifiers: Option<ast::ModifierList>,
    ty: Option<&SyntaxNode>,
) -> bool {
    let null_related = is_null_related;
    let in_modifiers = modifiers.is_some_and(|list| {
        list.annotations()
            .filter_map(|a| a.name())
            .any(|n| null_related(&n.text()))
    });
    let in_type = ty.is_some_and(|ty| {
        ty.descendants()
            .filter_map(ast::Annotation::cast)
            .filter(|a| {
                // 类型实参上的注解修饰的是实参，不影响这个位置本身
                !a.syntax()
                    .ancestors()
                    .take_while(|n| n != ty)
                    .any(|n| n.kind() == SyntaxKind::TYPE_ARG_LIST)
            })
            .filter_map(|a| a.name())
            .any(|n| null_related(&n.text()))
    });
    in_modifiers || in_type
}

/// 一个文件的空值分析共用的缓存：同一个文件里反复查的总是那几个类和方法。
struct Ctx<'a> {
    db: &'a dyn Db,
    classes: RefCell<FxHashMap<ClassId, Option<Arc<ClassData>>>>,
    supers: RefCell<FxHashMap<ClassId, Arc<Vec<ClassId>>>>,
    defaults: RefCell<FxHashMap<ClassId, Defaults>>,
    inherited: RefCell<FxHashMap<MethodId, Arc<Inherited>>>,
    methods: RefCell<FxHashMap<MethodId, Arc<MethodNullness>>>,
    /// 类的祖先里有没有写了空值注解的方法
    annotated_supers: RefCell<FxHashMap<ClassId, bool>>,
}

impl<'a> Ctx<'a> {
    fn new(db: &'a dyn Db) -> Ctx<'a> {
        Ctx {
            db,
            classes: RefCell::default(),
            supers: RefCell::default(),
            defaults: RefCell::default(),
            inherited: RefCell::default(),
            methods: RefCell::default(),
            annotated_supers: RefCell::default(),
        }
    }

    /// 类的祖先里有没有写了空值注解（返回值或形参）的方法：没有时不必逐个找被覆写的方法。
    fn has_annotated_supers(&self, class: ClassId) -> bool {
        if let Some(res) = self.annotated_supers.borrow().get(&class) {
            return *res;
        }
        let res = has_annotated_supers(self.db, class);
        self.annotated_supers.borrow_mut().insert(class, res);
        res
    }

    fn get(&self, class: ClassId) -> Option<Arc<ClassData>> {
        if let Some(data) = self.classes.borrow().get(&class) {
            return data.clone();
        }
        let data = class_data(self.db, class);
        self.classes.borrow_mut().insert(class, data.clone());
        data
    }

    fn supers(&self, class: ClassId) -> Arc<Vec<ClassId>> {
        if let Some(supers) = self.supers.borrow().get(&class) {
            return supers.clone();
        }
        let supers = hir::all_supers(self.db, class);
        self.supers.borrow_mut().insert(class, supers.clone());
        supers
    }

    // 成员的修饰符只读这个成员的签名：类里别的成员变化时，用到它的体不必重新检查
    fn field_flags(&self, field: FieldId) -> Option<Modifiers> {
        hir::field_flags(self.db, field)
    }

    fn method_flags(&self, method: MethodId) -> Option<Modifiers> {
        hir::method_flags(self.db, method)
    }

    /// 声明对应的语法节点（工作区源码或打开的库源码里的类才有）。
    /// 只有声明头（不含方法体、类体），位置从 0 开始：别的文件里的体内编辑不会让这里失效。
    fn decl_node(&self, class: ClassId, decl: Option<u32>) -> Option<SyntaxNode> {
        let decl = decl?;
        let file = hir::class_decl_file(self.db, class)?;
        hir::decl_header(self.db, file, decl)
    }

    /// 类里的成员没写空值注解时的默认值：类自身、外层类、`package-info.java`、
    /// `module-info.java` 由内向外，内层的规定优先。class 文件里的类看 class 文件上的注解和
    /// 同一个容器里的 `package-info.class`、`module-info.class`。
    fn class_defaults(&self, class: ClassId) -> Defaults {
        if let Some(defaults) = self.defaults.borrow().get(&class) {
            return *defaults;
        }
        let defaults = self.compute_class_defaults(class);
        self.defaults.borrow_mut().insert(class, defaults);
        defaults
    }

    fn compute_class_defaults(&self, class: ClassId) -> Defaults {
        let Some(data) = hir::class_header(self.db, class) else {
            return Defaults::default();
        };
        let mut defaults = Defaults::of_names(data.annotations.iter().map(|a| a.as_str()));
        let has_args = data.annotations.iter().any(|a| {
            matches!(
                simple_annotation_name(a),
                "DefaultQualifier" | "NonNullByDefault"
            )
        });
        if !data.is_source {
            if has_args {
                if let Some(info) = hir::binary_null_annotations(self.db, class) {
                    defaults = Defaults::of_binary(&info.class);
                }
            }
            if defaults.settled() {
                return defaults;
            }
            if data.outer.is_some() {
                if let Some(outer) = hir::outer_class(self.db, class) {
                    return defaults.or(self.class_defaults(outer));
                }
            }
            defaults = defaults.or(Defaults::of_binary(&hir::binary_package_annotations(
                self.db, class,
            )));
            if !defaults.settled() {
                defaults = defaults.or(Defaults::of_binary(&hir::binary_module_annotations(
                    self.db, class,
                )));
            }
            return defaults;
        }
        if has_args {
            let modifiers = self
                .decl_node(class, self.get(class).and_then(|d| d.decl))
                .and_then(|node| node.children().find_map(ast::ModifierList::cast));
            defaults = Defaults::of_modifiers(modifiers).or(defaults);
        }
        if defaults.settled() {
            return defaults;
        }
        if data.outer.is_some() {
            if let Some(outer) = hir::outer_class(self.db, class) {
                return defaults.or(self.class_defaults(outer));
            }
        }
        let scopes = scope_defaults(self.db);
        if let Some(package) = scopes.packages.get(data.package()) {
            defaults = defaults.or(*package);
        }
        if !defaults.settled() && !scopes.modules.is_empty() {
            let module = hir::class_source_file(self.db, class)
                .and_then(|file| base_db::file_entry(self.db, file.file_id(self.db)))
                .and_then(|entry| match entry.kind {
                    FileKind::Workspace { module, .. } => Some(module),
                    FileKind::Library => None,
                });
            if let Some(module) = module.and_then(|m| scopes.modules.get(&m)) {
                defaults = defaults.or(*module);
            }
        }
        defaults
    }

    fn inherited(&self, method: MethodId) -> Arc<Inherited> {
        if let Some(res) = self.inherited.borrow().get(&method) {
            return res.clone();
        }
        let res = Arc::new(self.compute_inherited(method));
        self.inherited.borrow_mut().insert(method, res.clone());
        res
    }

    /// 收集所有被 `method` 覆写的方法上写明的空值注解。
    fn compute_inherited(&self, method: MethodId) -> Inherited {
        // 只读这个方法和类头的签名：类里别的成员变化时，用到它的体不必重新检查
        let Some(decl) = hir::method_data(self.db, method) else {
            return Inherited::default();
        };
        if decl.is_constructor
            || decl.flags.is_static()
            || decl.flags.visibility() == Visibility::Private
            || !self.has_annotated_supers(method.class)
        {
            return Inherited::default();
        }
        let mut res = Inherited {
            ret: None,
            params: vec![None; decl.params.len()],
        };
        let own_package = class_package(self.db, method.class);
        for sup in self.supers(method.class).iter() {
            let Some(sup_data) = self.get(*sup) else {
                continue;
            };
            for (idx, candidate) in sup_data.methods.iter().enumerate() {
                if candidate.is_constructor
                    || candidate.name != decl.name
                    || candidate.params.len() != decl.params.len()
                    || candidate.type_params.len() != decl.type_params.len()
                    || candidate.flags.is_static()
                {
                    continue;
                }
                let annotated = candidate.flags.null_annotation() != NullAnnotation::Unknown
                    || candidate
                        .params
                        .iter()
                        .any(|p| p.nullness != NullAnnotation::Unknown);
                if !annotated {
                    continue;
                }
                // 私有方法不被覆写；包私有的只被同一个包里的类覆写
                let visibility = if sup_data.is_interface() {
                    Visibility::Public
                } else {
                    candidate.flags.visibility()
                };
                if visibility == Visibility::Private
                    || (visibility == Visibility::Package && sup_data.package() != own_package)
                {
                    continue;
                }
                let candidate_id = MethodId {
                    class: *sup,
                    idx: idx as u32,
                };
                if !self.overrides(method, candidate_id) {
                    continue;
                }
                merge_inherited(&mut res.ret, candidate.flags.null_annotation());
                for (slot, param) in res.params.iter_mut().zip(&candidate.params) {
                    merge_inherited(slot, param.nullness);
                }
            }
        }
        res
    }

    /// `method` 的签名是不是 `candidate`（祖先里的同名方法）按继承关系代换后的子签名。
    fn overrides(&self, method: MethodId, candidate: MethodId) -> bool {
        let db = self.db;
        let Some(Ty::Class(_, args)) =
            hir::find_super(db, &hir::this_ty(db, method.class), candidate.class)
        else {
            return false;
        };
        let sig = hir::method_sig(db, method);
        let candidate_sig = hir::method_sig(db, candidate);
        let mut subst = Subst::for_class(db, candidate.class, &args);
        for idx in 0..candidate_sig.n_type_params {
            subst.set(
                TypeParamId {
                    owner: GenericOwner::Method(candidate),
                    idx,
                },
                Ty::TypeParam(TypeParamId {
                    owner: GenericOwner::Method(method),
                    idx,
                }),
            );
        }
        sig.params.len() == candidate_sig.params.len()
            && sig
                .params
                .iter()
                .zip(&candidate_sig.params)
                .all(|(own, theirs)| {
                    let own = own.erasure(db);
                    is_known(&own) && own == theirs.subst(&subst).erasure(db)
                })
    }

    /// 方法返回值和各形参最终采用的空值注解：写明的、继承的、默认的。
    fn method(&self, method: MethodId) -> Option<Arc<MethodNullness>> {
        if let Some(res) = self.methods.borrow().get(&method) {
            return Some(res.clone());
        }
        let res = Arc::new(self.compute_method(method)?);
        self.methods.borrow_mut().insert(method, res.clone());
        Some(res)
    }

    fn compute_method(&self, method: MethodId) -> Option<MethodNullness> {
        // 只读这个方法自己的签名：类里别的成员变化时，调用它的体不必重新检查
        let decl = hir::method_data(self.db, method)?;
        let inherited = self.inherited(method);
        let declared_ret = decl.flags.null_annotation();
        let mut defaults = Defaults::default();
        let mut node = None;
        // class 文件里的方法上的注解
        let mut binary = None;
        // 只在需要时才找声明的语法：写明了注解的位置用不到默认值
        let needs_default = declared_ret == NullAnnotation::Unknown
            || decl
                .params
                .iter()
                .any(|p| p.nullness == NullAnnotation::Unknown);
        let class_defaults = if needs_default {
            self.class_defaults(method.class)
        } else {
            Defaults::default()
        };
        if class_defaults.params == Some(true) || class_defaults.returns == Some(true) {
            let is_binary = hir::class_header(self.db, method.class).is_some_and(|h| !h.is_source);
            if is_binary {
                // 和签名里的方法对不上（读不到 class 文件、源码补上的方法）时不套用默认值
                binary = hir::binary_null_annotations(self.db, method.class).filter(|info| {
                    info.methods.get(method.idx as usize).is_some_and(|m| {
                        let name = if decl.is_constructor {
                            "<init>"
                        } else {
                            decl.name.as_str()
                        };
                        m.name == name && m.params.len() == decl.params.len()
                    })
                });
                if let Some(info) = &binary {
                    defaults = Defaults::of_binary(&info.methods[method.idx as usize].annotations)
                        .or(class_defaults);
                }
            } else if decl.decl.is_some() {
                // 合成的成员（Lombok、记录、枚举）没有声明，不套用默认值
                node = self.decl_node(method.class, decl.decl).filter(|n| {
                    matches!(
                        n.kind(),
                        SyntaxKind::METHOD_DECL | SyntaxKind::CONSTRUCTOR_DECL
                    )
                });
                let modifiers = node
                    .as_ref()
                    .and_then(|n| n.children().find_map(ast::ModifierList::cast));
                defaults = Defaults::of_modifiers(modifiers).or(class_defaults);
            }
        }
        let binary_method = binary
            .as_ref()
            .map(|info| &info.methods[method.idx as usize]);
        let sig: Option<Arc<MethodSig>> =
            (node.is_some() || binary_method.is_some()).then(|| hir::method_sig(self.db, method));
        let modifiers = node
            .as_ref()
            .and_then(|n| n.children().find_map(ast::ModifierList::cast));
        let ret_default = defaults.returns == Some(true)
            && !decl.is_constructor
            && sig.as_ref().is_some_and(|s| takes_default(&s.ret))
            && match binary_method {
                Some(m) => !m.annotations.iter().any(|a| is_null_related(&a.name)),
                None => !has_other_null_annotation(
                    modifiers,
                    node.as_ref()
                        .and_then(|n| ast::MethodDecl::cast(n.clone()))
                        .and_then(|m| m.return_type())
                        .as_ref()
                        .map(|t| t.syntax()),
                ),
            };
        let ret = Effective::combine(declared_ret, inherited.ret, ret_default);
        // 形参的语法节点（跳过没有名字的接收者参数），和 `decl.params` 一一对应
        let param_nodes: Vec<ast::Param> = node
            .as_ref()
            .and_then(|n| n.children().find(|c| c.kind() == SyntaxKind::PARAM_LIST))
            .map(|list| {
                list.children()
                    .filter_map(ast::Param::cast)
                    .filter(|p| p.name().is_some())
                    .collect()
            })
            .unwrap_or_default();
        let varargs = decl.flags.contains(Modifiers::VARARGS);
        let params = decl
            .params
            .iter()
            .enumerate()
            .map(|(i, param)| {
                let default = defaults.params == Some(true)
                    && sig
                        .as_ref()
                        .and_then(|s| s.params.get(i))
                        .is_some_and(takes_default)
                    && match binary_method {
                        Some(m) => {
                            !(varargs && i + 1 == decl.params.len())
                                && m.params[i].iter().all(|name| !is_null_related(name))
                        }
                        None => {
                            param_nodes.len() == decl.params.len()
                                && param_nodes.get(i).is_some_and(|p| {
                                    !p.is_varargs()
                                        && !has_other_null_annotation(
                                            p.modifier_list(),
                                            p.ty().as_ref().map(|t| t.syntax()),
                                        )
                                })
                        }
                    };
                Effective::combine(
                    param.nullness,
                    inherited.params.get(i).copied().flatten(),
                    default,
                )
            })
            .collect();
        Some(MethodNullness { ret, params })
    }
}

/// 类的祖先里有没有写了空值注解（返回值或形参）的方法。绝大多数类没有，据此跳过逐个
/// 找被覆写方法的工作。
fn has_annotated_supers(db: &dyn Db, class: ClassId) -> bool {
    has_annotated_supers_tracked(db, base_db::workspace(db), class)
}

// 跨文件共用：每个文件都要查一遍用到的类，逐个文件重算祖先太慢
#[salsa::tracked]
fn has_annotated_supers_tracked(db: &dyn Db, _ws: base_db::Workspace, class: ClassId) -> bool {
    hir::all_supers(db, class).iter().copied().any(|sup| {
        class_data(db, sup).is_some_and(|data| {
            data.methods.iter().any(|m| {
                m.flags.null_annotation() != NullAnnotation::Unknown
                    || m.params
                        .iter()
                        .any(|p| p.nullness != NullAnnotation::Unknown)
            })
        })
    })
}

struct Analysis<'a> {
    ctx: &'a Ctx<'a>,
    /// 所在的体
    body_id: BodyId,
    /// 被跟踪的 `@Nullable` 字段
    tracked_fields: FxHashSet<FieldId>,
    result: &'a InferenceResult,
    /// 所在文件的源码文本
    file_text: &'a str,
    /// 方法体的源码文本，用来判断某个调用有没有被判空过
    text: &'a str,
    /// 整个体的语法节点
    body: &'a SyntaxNode,
    /// 体里所有对被跟踪变量的赋值（表达式的范围，按起点排序），用到时才收集
    assignments: Option<Vec<(TextRange, Var)>>,
    /// 所在方法的返回值最终采用的空值注解，用到时才计算
    returns: Option<Effective>,
    /// 当前在几层 lambda 里面（lambda 里的 `return` 不是方法的返回）
    lambda_depth: u32,
    /// 当前位置的状态；`None` 表示当前位置不可达
    state: Option<State>,
    out: Vec<(TextRange, DiagnosticCode, String)>,
}

fn strip_parens(mut node: SyntaxNode) -> SyntaxNode {
    while node.kind() == SyntaxKind::PAREN_EXPR {
        match node.children().find(|c| ast::Expr::can_cast(c.kind())) {
            Some(inner) => node = inner,
            None => break,
        }
    }
    node
}

fn is_null_literal(node: &SyntaxNode) -> bool {
    let node = strip_parens(node.clone());
    node.kind() == SyntaxKind::LITERAL
        && node
            .first_token()
            .is_some_and(|t| t.kind() == SyntaxKind::NULL_KW)
}

fn operator(node: &SyntaxNode) -> Option<SyntaxKind> {
    node.children_with_tokens()
        .filter_map(|e| e.into_token())
        .map(|t| t.kind())
        .find(|k| !k.is_trivia())
}

fn exprs(node: &SyntaxNode) -> Vec<SyntaxNode> {
    node.children()
        .filter(|c| ast::Expr::can_cast(c.kind()))
        .collect()
}

/// 名字像断言 / 前置条件 / 初始化的方法：调用之后字段的状态可能已经被检查或设置过。
fn is_precondition_like(name: &str) -> bool {
    [
        "check", "assert", "verify", "ensure", "require", "validate", "init",
    ]
    .iter()
    .any(|prefix| name.starts_with(prefix))
}

impl Analysis<'_> {
    /// 表达式是不是对一个被跟踪的变量的引用：局部变量 / 形参，或者被跟踪的字段
    /// （`f`、`this.f`，静态字段还可以是 `C.f`）。
    fn var_of(&self, expr: &SyntaxNode) -> Option<(Var, TextRange)> {
        let expr = strip_parens(expr.clone());
        let name = match expr.kind() {
            SyntaxKind::NAME_EXPR => expr.children().find(|c| c.kind() == SyntaxKind::NAME_REF)?,
            SyntaxKind::FIELD_ACCESS if !self.tracked_fields.is_empty() => {
                let receiver = exprs(&expr).into_iter().next()?;
                let name = expr
                    .children()
                    .filter(|c| c.kind() == SyntaxKind::NAME_REF)
                    .last()?;
                let Some(Resolution::Field(field)) = self.result.resolution(name.text_range())
                else {
                    return None;
                };
                if !self.tracked_fields.contains(field) {
                    return None;
                }
                let on_this = receiver.kind() == SyntaxKind::THIS_EXPR
                    && receiver.children().next().is_none();
                let on_class = receiver.kind() == SyntaxKind::NAME_EXPR
                    && receiver
                        .children()
                        .find(|c| c.kind() == SyntaxKind::NAME_REF)
                        .and_then(|n| self.result.resolution(n.text_range()))
                        .is_some_and(|r| matches!(r, Resolution::Class(_)));
                return (on_this || on_class).then_some((Var::Field(*field), name.text_range()));
            }
            _ => return None,
        };
        match self.result.resolution(name.text_range())? {
            Resolution::Local(id) => {
                let local = self.result.local(*id);
                let tracked = !matches!(
                    local.kind,
                    LocalKind::LocalClassField | LocalKind::LocalClassMethod
                ) && !matches!(local.ty, Ty::Primitive(_) | Ty::Void);
                tracked.then_some((Var::Local(*id), name.text_range()))
            }
            Resolution::Field(field) if self.tracked_fields.contains(field) => {
                Some((Var::Field(*field), name.text_range()))
            }
            _ => None,
        }
    }

    fn var_name(&self, var: Var) -> String {
        match var {
            Var::Local(id) => self.result.local(id).name.to_string(),
            Var::Field(field) => hir::field_data(self.ctx.db, field)
                .map(|f| f.name.to_string())
                .unwrap_or_default(),
        }
    }

    fn get(&self, var: Var) -> Option<Nullness> {
        self.state.as_ref()?.get(&var).copied()
    }

    fn set(&mut self, var: Var, nullness: Option<Nullness>) {
        if let Some(state) = &mut self.state {
            match nullness {
                Some(n) => {
                    state.insert(var, n);
                }
                None => {
                    state.remove(&var);
                }
            }
        }
    }

    /// 一次可能修改字段的调用之后：判空、赋值得到的字段事实作废。`all` 时连"可能是 null"
    /// 也一并丢掉（调用可能检查或设置了字段，如 `ensureInitialized()`）。
    fn invalidate_fields(&mut self, all: bool) {
        if self.tracked_fields.is_empty() {
            return;
        }
        if let Some(state) = &mut self.state {
            state.retain(|var, n| match var {
                Var::Local(_) => true,
                Var::Field(_) => !all && *n == Nullness::MaybeNull,
            });
        }
    }

    /// 体里所有对被跟踪变量的赋值。
    fn collect_assignments(&self) -> Vec<(TextRange, Var)> {
        let mut res = Vec::new();
        for n in self.body.descendants() {
            let target = match n.kind() {
                SyntaxKind::ASSIGN_EXPR | SyntaxKind::UNARY_EXPR | SyntaxKind::POSTFIX_EXPR => {
                    exprs(&n).into_iter().next()
                }
                _ => None,
            };
            if let Some((var, _)) = target.and_then(|t| self.var_of(&t)) {
                res.push((n.text_range(), var));
            }
        }
        res
    }

    /// 丢掉 `node` 里赋值过的变量的信息；`node` 里有调用时，字段的事实也作废。
    /// 赋值表达式先对整个体收集一次，每次只按范围查找，免得嵌套的循环 / try 一层层重复遍历子树。
    fn kill_assigned_in(&mut self, node: &SyntaxNode) {
        if self.state.is_none() {
            return;
        }
        if self.assignments.is_none() {
            self.assignments = Some(self.collect_assignments());
        }
        let range = node.text_range();
        let assignments = self.assignments.as_deref().unwrap_or_default();
        let first = assignments.partition_point(|(r, _)| r.start() < range.start());
        let killed: Vec<Var> = assignments[first..]
            .iter()
            .take_while(|(r, _)| r.start() < range.end())
            .filter(|(r, _)| range.contains_range(*r))
            .map(|(_, var)| *var)
            .collect();
        for var in killed {
            self.set(var, None);
        }
        let has_field_facts = self.state.as_ref().is_some_and(|s| {
            s.iter()
                .any(|(var, n)| matches!(var, Var::Field(_)) && *n != Nullness::MaybeNull)
        });
        if has_field_facts
            && node
                .descendants()
                .any(|d| matches!(d.kind(), SyntaxKind::METHOD_CALL | SyntaxKind::NEW_EXPR))
        {
            self.invalidate_fields(false);
        }
    }

    /// 表达式的值一定是 null / 一定不是 null。
    fn nullness_of(&self, expr: &SyntaxNode) -> Option<Nullness> {
        let expr = strip_parens(expr.clone());
        match expr.kind() {
            SyntaxKind::LITERAL => Some(if is_null_literal(&expr) {
                Nullness::Null
            } else {
                Nullness::NotNull
            }),
            SyntaxKind::NEW_EXPR
            | SyntaxKind::ARRAY_CREATION_EXPR
            | SyntaxKind::ARRAY_INITIALIZER
            | SyntaxKind::THIS_EXPR
            | SyntaxKind::LAMBDA_EXPR
            | SyntaxKind::METHOD_REF
            | SyntaxKind::BINARY_EXPR
            | SyntaxKind::CLASS_LITERAL => Some(Nullness::NotNull),
            SyntaxKind::NAME_EXPR | SyntaxKind::FIELD_ACCESS => match self.var_of(&expr) {
                // 字段可能被别的线程改掉，"一定是 null"只当作"可能是 null"
                Some((var @ Var::Field(_), _)) => self.get(var).map(|n| match n {
                    Nullness::Null => Nullness::MaybeNull,
                    n => n,
                }),
                Some((var, _)) => self.get(var),
                None => self.annotated_maybe_null(&expr),
            },
            SyntaxKind::METHOD_CALL => self.annotated_maybe_null(&expr),
            SyntaxKind::CAST_EXPR => exprs(&expr).last().and_then(|e| self.nullness_of(e)),
            SyntaxKind::ASSIGN_EXPR => exprs(&expr).get(1).and_then(|e| self.nullness_of(e)),
            SyntaxKind::CONDITIONAL_EXPR => {
                let parts = exprs(&expr);
                let then = self.nullness_of(parts.get(1)?)?;
                let otherwise = self.nullness_of(parts.get(2)?)?;
                if then == otherwise {
                    Some(then)
                } else if then == Nullness::MaybeNull || otherwise == Nullness::MaybeNull {
                    Some(Nullness::MaybeNull)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// 方法调用 / 字段引用的目标上的空值注解（方法的注解可以继承自被覆写的方法）。
    fn annotated(&self, expr: &SyntaxNode) -> Option<Effective> {
        let name = match expr.kind() {
            SyntaxKind::METHOD_CALL => ast::MethodCall::cast(expr.clone())?
                .name_ref()?
                .syntax()
                .clone(),
            SyntaxKind::FIELD_ACCESS | SyntaxKind::NAME_EXPR => expr
                .children()
                .filter(|c| c.kind() == SyntaxKind::NAME_REF)
                .last()?,
            _ => return None,
        };
        match self.result.resolution(name.text_range())? {
            Resolution::Method(m) => {
                let declared = self.ctx.method_flags(*m)?.null_annotation();
                // 默认值只会让返回值"不为 null"，这里只关心"可能为 null"：没写注解也没有
                // 继承来的注解时不必再看默认值
                if declared != NullAnnotation::Unknown || self.ctx.inherited(*m).ret.is_none() {
                    return Some(Effective {
                        nullness: declared,
                        origin: Origin::Declared,
                    });
                }
                Some(self.ctx.method(*m)?.ret)
            }
            Resolution::Field(f) => Some(Effective {
                nullness: self.ctx.field_flags(*f)?.null_annotation(),
                origin: Origin::Declared,
            }),
            _ => None,
        }
    }

    /// 标了 `@Nullable` 的方法调用 / 不跟踪的字段（别的对象上的），而且方法体里没有检查过它。
    fn annotated_maybe_null(&self, expr: &SyntaxNode) -> Option<Nullness> {
        self.annotated(expr)
            .filter(|a| a.nullness == NullAnnotation::Nullable && !self.null_checked_text(expr))
            .map(|_| Nullness::MaybeNull)
    }

    /// 方法体里有没有拿 `expr` 的文本和 null 比较过（`getX() != null`、`x instanceof T` 之类）。
    fn null_checked_text(&self, expr: &SyntaxNode) -> bool {
        let text = &self.file_text[expr.text_range()];
        [
            format!("{text} != null"),
            format!("{text} == null"),
            format!("null != {text}"),
            format!("null == {text}"),
            format!("requireNonNull({text}"),
            format!("{text} instanceof"),
        ]
        .iter()
        .any(|p| self.text.contains(p.as_str()))
    }

    /// 这些实参里可能为 null 的变量改为未知。
    fn forget_maybe_null(&mut self, args: &[ast::Expr]) {
        for arg in args {
            if let Some((var, _)) = self.var_of(arg.syntax()) {
                if self.get(var) == Some(Nullness::MaybeNull) {
                    self.set(var, None);
                }
            }
        }
    }

    /// `receiver` 在这里被解引用。
    fn dereference(&mut self, receiver: &SyntaxNode) {
        let Some((var, range)) = self.var_of(receiver) else {
            // 直接解引用 `@Nullable` 方法的返回值：`getParent().getName()`
            let receiver = strip_parens(receiver.clone());
            if receiver.kind() != SyntaxKind::METHOD_CALL {
                return;
            }
            let Some(annotated) = self
                .annotated(&receiver)
                .filter(|a| a.nullness == NullAnnotation::Nullable)
            else {
                return;
            };
            if self.null_checked_text(&receiver) {
                return;
            }
            if let Some(name) = ast::MethodCall::cast(receiver.clone()).and_then(|c| c.name_ref()) {
                let method = name.text();
                let message = if annotated.origin == Origin::Inherited {
                    base_db::tr!(
                        "`{method}` 覆写的方法标注了 @Nullable，返回值可能是 null，直接解引用可能抛出 NullPointerException",
                        "`{method}` overrides a method annotated @Nullable; dereferencing its result may throw NullPointerException"
                    )
                } else {
                    base_db::tr!(
                        "`{method}` 标注了 @Nullable，返回值可能是 null，直接解引用可能抛出 NullPointerException",
                        "`{method}` is annotated @Nullable; dereferencing its result may throw NullPointerException"
                    )
                };
                self.out.push((
                    name.syntax().text_range(),
                    DiagnosticCode::NullableDereference,
                    message,
                ));
            }
            return;
        };
        let name = self.var_name(var);
        match (var, self.get(var)) {
            (Var::Field(_), Some(Nullness::Null | Nullness::MaybeNull)) => self.out.push((
                range,
                DiagnosticCode::NullableDereference,
                base_db::tr!(
                    "字段 `{name}` 标注了 @Nullable，在这里可能是 null，解引用可能抛出 NullPointerException",
                    "Field `{name}` is annotated @Nullable and may be null here; dereferencing it may throw NullPointerException"
                ),
            )),
            (_, Some(Nullness::Null)) => self.out.push((
                range,
                DiagnosticCode::NullDereference,
                base_db::tr!(
                    "`{name}` 在这里一定是 null，解引用会抛出 NullPointerException",
                    "`{name}` is always null here; dereferencing it throws NullPointerException"
                ),
            )),
            (_, Some(Nullness::MaybeNull)) => self.out.push((
                range,
                DiagnosticCode::NullableDereference,
                base_db::tr!(
                    "`{name}` 在这里可能是 null，解引用可能抛出 NullPointerException",
                    "`{name}` may be null here; dereferencing it may throw NullPointerException"
                ),
            )),
            _ => {}
        }
        // 走到下一步说明没有抛异常
        self.set(var, Some(Nullness::NotNull));
    }

    /// 求值一个条件，返回它为真 / 为假时的状态。
    fn cond(&mut self, node: &SyntaxNode) -> (Option<State>, Option<State>) {
        let node = strip_parens(node.clone());
        if self.state.is_none() {
            return (None, None);
        }
        match node.kind() {
            SyntaxKind::LITERAL => {
                let token = node.first_token().map(|t| t.kind());
                match token {
                    Some(SyntaxKind::TRUE_KW) => return (self.state.clone(), None),
                    Some(SyntaxKind::FALSE_KW) => return (None, self.state.clone()),
                    _ => {}
                }
            }
            SyntaxKind::UNARY_EXPR if operator(&node) == Some(SyntaxKind::BANG) => {
                if let Some(operand) = exprs(&node).into_iter().next() {
                    let (t, f) = self.cond(&operand);
                    return (f, t);
                }
            }
            SyntaxKind::BINARY_EXPR => {
                let parts = exprs(&node);
                let op = ast::BinaryExpr::cast(node.clone()).and_then(|b| b.op_kind());
                if let (Some(op), [lhs, rhs]) = (op, parts.as_slice()) {
                    match op {
                        SyntaxKind::AMP_AMP => {
                            let (t1, f1) = self.cond(lhs);
                            self.state = t1;
                            let (t2, f2) = self.cond(rhs);
                            return (t2, join(f1, f2));
                        }
                        SyntaxKind::PIPE_PIPE => {
                            let (t1, f1) = self.cond(lhs);
                            self.state = f1;
                            let (t2, f2) = self.cond(rhs);
                            return (join(t1, t2), f2);
                        }
                        SyntaxKind::EQ_EQ | SyntaxKind::NEQ => {
                            let tested = if is_null_literal(rhs) {
                                Some(lhs)
                            } else if is_null_literal(lhs) {
                                Some(rhs)
                            } else {
                                None
                            };
                            if let Some(tested) = tested {
                                self.node(tested);
                                // `(x = next()) != null` 检查的是赋值之后的 x
                                let tested_var = self.var_of(tested).or_else(|| {
                                    let assign = strip_parens(tested.clone());
                                    (assign.kind() == SyntaxKind::ASSIGN_EXPR
                                        && operator(&assign) == Some(SyntaxKind::EQ))
                                    .then(|| exprs(&assign).into_iter().next())
                                    .flatten()
                                    .and_then(|lhs| self.var_of(&lhs))
                                });
                                if let Some((var, _)) = tested_var {
                                    let equals = op == SyntaxKind::EQ_EQ;
                                    // 字段可能被别的线程改掉（双重检查锁定），不报"条件恒定"
                                    let known = self.get(var);
                                    if let (Var::Local(id), Some(known)) =
                                        (var, known.filter(|n| *n != Nullness::MaybeNull))
                                    {
                                        self.constant_condition(
                                            &node,
                                            id,
                                            known,
                                            (known == Nullness::Null) == equals,
                                        );
                                    }
                                    // 已知结果时，另一种情况走不到
                                    let mut when_null = (known != Some(Nullness::NotNull))
                                        .then(|| self.state.clone())
                                        .flatten();
                                    let mut when_not_null = (known != Some(Nullness::Null))
                                        .then(|| self.state.clone())
                                        .flatten();
                                    if let Some(s) = &mut when_null {
                                        s.insert(var, Nullness::Null);
                                    }
                                    if let Some(s) = &mut when_not_null {
                                        s.insert(var, Nullness::NotNull);
                                    }
                                    return if equals {
                                        (when_null, when_not_null)
                                    } else {
                                        (when_not_null, when_null)
                                    };
                                }
                                return (self.state.clone(), self.state.clone());
                            }
                        }
                        _ => {}
                    }
                }
            }
            SyntaxKind::INSTANCEOF_EXPR => {
                if let Some(tested) = exprs(&node).into_iter().next() {
                    self.node(&tested);
                    let mut when_true = self.state.clone();
                    if let (Some((var, _)), Some(s)) = (self.var_of(&tested), &mut when_true) {
                        s.insert(var, Nullness::NotNull);
                    }
                    return (when_true, self.state.clone());
                }
            }
            _ => {}
        }
        // 条件里把可能为 null 的变量交给某个方法判断（`hasText(s)`、`isEmpty(s)`、`nonNull(s)`），
        // 两个分支上都不再认为它可能是 null；当作条件的调用（`isInitialized()`、`hasParent()`）
        // 可能检查的就是字段，字段的状态一并作废
        if node.kind() == SyntaxKind::METHOD_CALL {
            self.node(&node);
            let args: Vec<ast::Expr> = ast::MethodCall::cast(node.clone())
                .and_then(|c| c.arg_list())
                .map(|l| l.args().collect())
                .unwrap_or_default();
            self.forget_maybe_null(&args);
            self.invalidate_fields(true);
            return (self.state.clone(), self.state.clone());
        }
        // 这几种节点在 `node` 里会转回 `cond`，这里直接看它们的子节点
        match node.kind() {
            SyntaxKind::BINARY_EXPR | SyntaxKind::UNARY_EXPR | SyntaxKind::INSTANCEOF_EXPR => {
                self.children(&node)
            }
            _ => self.node(&node),
        }
        (self.state.clone(), self.state.clone())
    }

    fn constant_condition(&mut self, node: &SyntaxNode, id: LocalId, known: Nullness, value: bool) {
        // 断言里的检查是有意写的
        if node
            .ancestors()
            .any(|a| a.kind() == SyntaxKind::ASSERT_STMT)
        {
            return;
        }
        let name = self.result.local(id).name.clone();
        let fact = match known {
            Nullness::Null => base_db::trs!("一定是 null", "is always null"),
            Nullness::NotNull | Nullness::MaybeNull => {
                base_db::trs!("一定不是 null", "is never null")
            }
        };
        self.out.push((
            node.text_range(),
            DiagnosticCode::ConstantCondition,
            base_db::tr!(
                "条件恒为 {value}：`{name}` 在这里{fact}",
                "Condition is always {value}: `{name}` {fact} here"
            ),
        ));
    }

    /// 分析 `node` 之后的状态；分析前后把当前状态恢复成 `entry`。
    fn branch(&mut self, node: Option<&SyntaxNode>, entry: Option<State>) -> Option<State> {
        self.state = entry;
        if let Some(node) = node {
            self.node(node);
        }
        self.state.take()
    }

    fn children(&mut self, node: &SyntaxNode) {
        for child in node.children() {
            self.node(&child);
        }
    }

    /// 在入口处丢掉 `node` 内部赋值过的变量；它的每个组成部分都从入口状态开始分析
    /// （各部分的执行顺序、是否执行都不建模），分析完之后回到入口状态。
    fn opaque(&mut self, node: &SyntaxNode) {
        self.kill_assigned_in(node);
        let entry = self.state.clone();
        for child in node.children() {
            self.branch(Some(&child), entry.clone());
        }
        self.state = entry;
    }

    /// 所在方法的返回值最终采用的空值注解。
    fn returns(&mut self) -> Effective {
        if let Some(returns) = self.returns {
            return returns;
        }
        let returns = match self.body_id {
            BodyId::Method(method) => self.ctx.method(method).map(|m| m.ret),
            _ => None,
        }
        .unwrap_or(Effective::UNKNOWN);
        self.returns = Some(returns);
        returns
    }

    fn node(&mut self, node: &SyntaxNode) {
        if self.state.is_none() {
            return;
        }
        match node.kind() {
            // 类体里是别的方法
            SyntaxKind::CLASS_BODY
            | SyntaxKind::CLASS_DECL
            | SyntaxKind::INTERFACE_DECL
            | SyntaxKind::ENUM_DECL
            | SyntaxKind::RECORD_DECL => {}
            // lambda 体稍后执行：捕获的局部变量不会再变，字段的事实到那时不一定还成立
            SyntaxKind::LAMBDA_EXPR => {
                let entry = self.state.clone();
                self.invalidate_fields(false);
                self.lambda_depth += 1;
                self.children(node);
                self.lambda_depth -= 1;
                self.state = entry;
            }
            SyntaxKind::RETURN_STMT if self.lambda_depth == 0 => {
                self.children(node);
                let value = exprs(node).into_iter().next();
                let maybe_null = value.as_ref().is_some_and(|v| {
                    matches!(
                        self.nullness_of(v),
                        Some(Nullness::Null | Nullness::MaybeNull)
                    )
                });
                if let (true, Some(value)) = (maybe_null, value) {
                    let returns = self.returns();
                    if returns.nullness == NullAnnotation::NotNull {
                        let (when_null, when_maybe) = return_messages(returns.origin);
                        self.check_not_null(&value, when_null, when_maybe);
                    }
                }
                self.state = None;
            }

            // ---- 语句 ----
            SyntaxKind::RETURN_STMT
            | SyntaxKind::THROW_STMT
            | SyntaxKind::BREAK_STMT
            | SyntaxKind::CONTINUE_STMT
            | SyntaxKind::YIELD_STMT => {
                self.children(node);
                self.state = None;
            }
            SyntaxKind::IF_STMT => {
                let Some(if_stmt) = ast::IfStmt::cast(node.clone()) else {
                    return;
                };
                let (when_true, when_false) = match if_stmt.condition() {
                    Some(condition) => self.cond(condition.syntax()),
                    None => (self.state.clone(), self.state.clone()),
                };
                let then = if_stmt.then_branch();
                let otherwise = if_stmt.else_branch();
                let after_then = self.branch(then.as_ref().map(|s| s.syntax()), when_true);
                let after_else = self.branch(otherwise.as_ref().map(|s| s.syntax()), when_false);
                self.state = join(after_then, after_else);
            }
            SyntaxKind::WHILE_STMT => {
                self.kill_assigned_in(node);
                let condition = exprs(node).into_iter().next();
                let (when_true, when_false) = match &condition {
                    Some(condition) => self.cond(condition),
                    None => (self.state.clone(), self.state.clone()),
                };
                let entry = self.state.clone();
                let body = node.children().find(|c| ast::Stmt::can_cast(c.kind()));
                self.branch(body.as_ref(), when_true);
                // 有 break 时循环可能在任何地方结束，条件为假的事实不一定成立
                self.state = if has_break(node) { entry } else { when_false };
            }
            // 断言可能被关掉，它的条件不能当作之后成立的事实；但断言里提到的变量说明
            // 作者认为它在这里不是 null，不再当作可能为 null
            SyntaxKind::ASSERT_STMT => {
                self.opaque(node);
                let vars: Vec<Var> = node
                    .descendants()
                    .filter_map(|d| self.var_of(&d))
                    .map(|(var, _)| var)
                    .collect();
                for var in vars {
                    if self.get(var) == Some(Nullness::MaybeNull) {
                        self.set(var, None);
                    }
                }
            }
            SyntaxKind::DO_WHILE_STMT
            | SyntaxKind::FOR_STMT
            | SyntaxKind::FOREACH_STMT
            | SyntaxKind::SWITCH_STMT
            | SyntaxKind::SWITCH_EXPR
            | SyntaxKind::LABELED_STMT
            | SyntaxKind::TRY_STMT
            | SyntaxKind::SWITCH_BLOCK => self.opaque(node),

            // ---- 表达式 ----
            SyntaxKind::VARIABLE_DECLARATOR => {
                let initializer = exprs(node).into_iter().next();
                if let Some(initializer) = &initializer {
                    self.node(initializer);
                }
                let declared = node
                    .children()
                    .find(|c| c.kind() == SyntaxKind::NAME)
                    .and_then(|name| self.result.local_at_decl(name.text_range()));
                if let (Some(id), Some(initializer)) = (declared, initializer) {
                    let local = self.result.local(id);
                    if !matches!(local.ty, Ty::Primitive(_)) {
                        let nullness = self.nullness_of(&initializer);
                        self.set(Var::Local(id), nullness);
                    }
                }
            }
            SyntaxKind::ASSIGN_EXPR => {
                let parts = exprs(node);
                let [lhs, rhs] = parts.as_slice() else {
                    self.children(node);
                    return;
                };
                match self.var_of(lhs) {
                    Some((var, _)) => {
                        self.node(rhs);
                        let simple = operator(node) == Some(SyntaxKind::EQ);
                        let nullness = if simple { self.nullness_of(rhs) } else { None };
                        self.set(var, nullness);
                    }
                    None => {
                        self.node(lhs);
                        self.node(rhs);
                    }
                }
            }
            SyntaxKind::UNARY_EXPR if operator(node) == Some(SyntaxKind::BANG) => {
                let (t, f) = self.cond(node);
                self.state = join(t, f);
            }
            SyntaxKind::UNARY_EXPR | SyntaxKind::POSTFIX_EXPR => {
                self.children(node);
                if let Some((var, _)) = exprs(node).first().and_then(|e| self.var_of(e)) {
                    self.set(var, None);
                }
            }
            SyntaxKind::BINARY_EXPR => {
                let op = ast::BinaryExpr::cast(node.clone()).and_then(|b| b.op_kind());
                if matches!(
                    op,
                    Some(
                        SyntaxKind::AMP_AMP
                            | SyntaxKind::PIPE_PIPE
                            | SyntaxKind::EQ_EQ
                            | SyntaxKind::NEQ
                    )
                ) {
                    let (t, f) = self.cond(node);
                    self.state = join(t, f);
                } else {
                    self.children(node);
                }
            }
            SyntaxKind::INSTANCEOF_EXPR => {
                let (t, f) = self.cond(node);
                self.state = join(t, f);
            }
            SyntaxKind::CONDITIONAL_EXPR => {
                let parts = exprs(node);
                let [condition, then, otherwise] = parts.as_slice() else {
                    self.children(node);
                    return;
                };
                let (when_true, when_false) = self.cond(condition);
                let after_then = self.branch(Some(then), when_true);
                let after_else = self.branch(Some(otherwise), when_false);
                self.state = join(after_then, after_else);
            }
            SyntaxKind::METHOD_CALL => {
                let Some(call) = ast::MethodCall::cast(node.clone()) else {
                    return;
                };
                if let Some(receiver) = call.receiver() {
                    self.node(receiver.syntax());
                    self.dereference(receiver.syntax());
                }
                let args: Vec<ast::Expr> = call
                    .arg_list()
                    .map(|l| l.args().collect())
                    .unwrap_or_default();
                for arg in &args {
                    self.node(arg.syntax());
                }
                // `Objects.requireNonNull(x)`、`Preconditions.checkNotNull(x)`、`Assert.notNull(x, ..)`
                // 之后 x 一定不是 null
                let method_name = call.name_ref().map(|n| n.text()).unwrap_or_default();
                let receiver_text = || {
                    call.receiver()
                        .map_or("", |r| &self.file_text[r.syntax().text_range()])
                };
                let requires_non_null = match method_name.as_str() {
                    "requireNonNull" => {
                        let receiver = receiver_text();
                        receiver.ends_with("Objects") || receiver.is_empty()
                    }
                    "checkNotNull" => true,
                    "notNull" => {
                        let receiver = receiver_text();
                        receiver.ends_with("Assert") || receiver.ends_with("Validate")
                    }
                    _ => false,
                };
                // 断言类方法（`assertNotNull(x)` 等）：不再认为 x 可能是 null
                if method_name.starts_with("assert") {
                    self.forget_maybe_null(&args);
                }
                if let Some(list) = call.arg_list() {
                    self.check_args(list.syntax());
                }
                // 调用可能修改字段
                self.invalidate_fields(is_precondition_like(&method_name));
                if requires_non_null {
                    if let Some((var, _)) = args.first().and_then(|a| self.var_of(a.syntax())) {
                        self.set(var, Some(Nullness::NotNull));
                    }
                }
            }
            SyntaxKind::NEW_EXPR => {
                self.children(node);
                if let Some(list) = node.children().find(|c| c.kind() == SyntaxKind::ARG_LIST) {
                    self.check_args(&list);
                }
                self.invalidate_fields(false);
            }
            SyntaxKind::FIELD_ACCESS | SyntaxKind::ARRAY_ACCESS => {
                let parts = exprs(node);
                if let Some(receiver) = parts.first() {
                    self.node(receiver);
                    self.dereference(receiver);
                }
                for rest in parts.iter().skip(1) {
                    self.node(rest);
                }
            }
            _ => self.children(node),
        }
    }
}

/// 返回值不可为 null 时，返回一定为 null / 可能为 null 的值的提示文案。
fn return_messages(origin: Origin) -> (String, fn(String) -> String) {
    match origin {
        Origin::Declared => (
            base_db::trs!(
                "方法标注了 @NotNull，却返回了 null",
                "`null` is returned by a method annotated @NotNull"
            )
            .to_string(),
            |value| {
                base_db::tr!(
                    "`{value}` 可能是 null，但方法标注了 @NotNull",
                    "`{value}` may be null but the method is annotated @NotNull"
                )
            },
        ),
        Origin::Inherited => (
            base_db::trs!(
                "被覆写的方法标注了 @NotNull，却返回了 null",
                "`null` is returned by a method that overrides a method annotated @NotNull"
            )
            .to_string(),
            |value| {
                base_db::tr!(
                    "`{value}` 可能是 null，但被覆写的方法标注了 @NotNull",
                    "`{value}` may be null but the overridden method is annotated @NotNull"
                )
            },
        ),
        Origin::Default => (
            base_db::trs!(
                "返回值默认不可为 null（@NullMarked 等），却返回了 null",
                "`null` is returned by a method whose return value is non-null by default (@NullMarked or similar)"
            )
            .to_string(),
            |value| {
                base_db::tr!(
                    "`{value}` 可能是 null，但返回值默认不可为 null（@NullMarked 等）",
                    "`{value}` may be null but the return value is non-null by default (@NullMarked or similar)"
                )
            },
        ),
    }
}

impl Analysis<'_> {
    /// `value` 流向一个 `@NotNull` 的位置：一定是 null 时报 `when_null`，可能是 null 时报 `when_maybe`。
    fn check_not_null(
        &mut self,
        value: &SyntaxNode,
        when_null: String,
        when_maybe: impl FnOnce(String) -> String,
    ) {
        let message = match self.nullness_of(value) {
            Some(Nullness::Null) => when_null,
            Some(Nullness::MaybeNull) => when_maybe(value.text().to_string()),
            _ => return,
        };
        self.out.push((
            value.text_range(),
            DiagnosticCode::NullabilityViolation,
            message,
        ));
    }

    /// 实参流向 `@NotNull` 形参。
    fn check_args(&mut self, arg_list: &SyntaxNode) {
        if self.state.is_none() {
            return;
        }
        let args = exprs(arg_list);
        // 先看实参：没有一定 / 可能为 null 的实参时不必查被调方法
        if !args.iter().any(|a| {
            matches!(
                self.nullness_of(a),
                Some(Nullness::Null | Nullness::MaybeNull)
            )
        }) {
            return;
        }
        let Some(method) = self
            .result
            .call_info(arg_list.text_range())
            .and_then(|c| c.chosen)
        else {
            return;
        };
        let Some(decl) = hir::method_data(self.ctx.db, method) else {
            return;
        };
        let Some(nullness) = self.ctx.method(method) else {
            return;
        };
        let varargs = decl.flags.contains(Modifiers::VARARGS);
        for (i, ((arg, param), effective)) in args
            .iter()
            .zip(&decl.params)
            .zip(&nullness.params)
            .enumerate()
        {
            // 可变参数位置上的实参不一定对应那个数组形参
            if varargs && i + 1 == decl.params.len() {
                break;
            }
            if effective.nullness != NullAnnotation::NotNull {
                continue;
            }
            let param_name = param
                .name
                .as_ref()
                .map(|n| n.to_string())
                .unwrap_or_else(|| format!("#{}", i + 1));
            let origin = effective.origin;
            let when_null = match origin {
                Origin::Declared => base_db::tr!(
                    "形参 `{param_name}` 标注了 @NotNull，却传入了 null",
                    "Passing `null` to parameter `{param_name}` annotated @NotNull"
                ),
                Origin::Inherited => base_db::tr!(
                    "形参 `{param_name}` 在被覆写的方法里标注了 @NotNull，却传入了 null",
                    "Passing `null` to parameter `{param_name}`, which is annotated @NotNull in the overridden method"
                ),
                Origin::Default => base_db::tr!(
                    "形参 `{param_name}` 默认不可为 null（@NullMarked 等），却传入了 null",
                    "Passing `null` to parameter `{param_name}`, which is non-null by default (@NullMarked or similar)"
                ),
            };
            self.check_not_null(arg, when_null, |value| match origin {
                Origin::Declared => base_db::tr!(
                    "`{value}` 可能是 null，但形参 `{param_name}` 标注了 @NotNull",
                    "`{value}` may be null but parameter `{param_name}` is annotated @NotNull"
                ),
                Origin::Inherited => base_db::tr!(
                    "`{value}` 可能是 null，但形参 `{param_name}` 在被覆写的方法里标注了 @NotNull",
                    "`{value}` may be null but parameter `{param_name}` is annotated @NotNull in the overridden method"
                ),
                Origin::Default => base_db::tr!(
                    "`{value}` 可能是 null，但形参 `{param_name}` 默认不可为 null（@NullMarked 等）",
                    "`{value}` may be null but parameter `{param_name}` is non-null by default (@NullMarked or similar)"
                ),
            });
        }
    }
}

fn analyze(
    ctx: &Ctx<'_>,
    body: BodyId,
    node: &SyntaxNode,
    file_text: &str,
    result: &InferenceResult,
) -> Vec<(TextRange, DiagnosticCode, String)> {
    // `this` 上（以及静态的）`@Nullable` 字段像局部变量一样跟踪，入口处可能是 null
    let tracked_fields: FxHashSet<FieldId> = result
        .resolutions()
        .filter_map(|(_, r)| match r {
            Resolution::Field(f) => Some(*f),
            _ => None,
        })
        .filter(|f| {
            ctx.field_flags(*f)
                .is_some_and(|flags| flags.null_annotation() == NullAnnotation::Nullable)
        })
        .collect();
    let mut analysis = Analysis {
        ctx,
        body_id: body,
        result,
        file_text,
        text: &file_text[node.text_range()],
        body: node,
        assignments: None,
        returns: None,
        lambda_depth: 0,
        state: Some(State::default()),
        out: Vec::new(),
        tracked_fields,
    };
    let fields: Vec<FieldId> = analysis.tracked_fields.iter().copied().collect();
    for field in fields {
        analysis.set(Var::Field(field), Some(Nullness::MaybeNull));
    }
    if let BodyId::Method(method) = body {
        // `@Nullable` 形参（写明的，或者继承自被覆写的方法）在入口处可能是 null
        let inherited = ctx
            .inherited(method)
            .params
            .contains(&Some(NullAnnotation::Nullable))
            .then(|| ctx.method(method))
            .flatten();
        let params = node
            .children()
            .find(|c| c.kind() == SyntaxKind::PARAM_LIST)
            .into_iter()
            .flat_map(|list| list.children().filter_map(ast::Param::cast))
            .filter(|p| p.name().is_some());
        for (i, param) in params.enumerate() {
            let nullable = match hir::param_null_annotation(&param) {
                NullAnnotation::Nullable => true,
                NullAnnotation::NotNull => false,
                NullAnnotation::Unknown => inherited
                    .as_ref()
                    .and_then(|m| m.params.get(i))
                    .is_some_and(|p| p.nullness == NullAnnotation::Nullable),
            };
            if !nullable {
                continue;
            }
            let id = param
                .name()
                .and_then(|n| result.local_at_decl(n.syntax().text_range()));
            if let Some(id) = id {
                analysis.set(Var::Local(id), Some(Nullness::MaybeNull));
            }
        }
    }
    analysis.children(node);
    analysis.out
}

/// 体里有没有用到标了 `@Nullable` 的方法或字段（包括覆写了 `@Nullable` 方法的方法）。
fn uses_nullable_member(ctx: &Ctx<'_>, result: &InferenceResult) -> bool {
    result
        .resolutions()
        .any(|(_, resolution)| match resolution {
            Resolution::Field(f) => ctx
                .field_flags(*f)
                .is_some_and(|flags| flags.null_annotation() == NullAnnotation::Nullable),
            Resolution::Method(m) => match ctx.method_flags(*m).map(|f| f.null_annotation()) {
                Some(NullAnnotation::Nullable) => true,
                // 没写注解的方法可能继承了 `@Nullable`
                Some(NullAnnotation::Unknown) => {
                    ctx.inherited(*m).ret == Some(NullAnnotation::Nullable)
                }
                _ => false,
            },
            _ => false,
        })
}

/// 方法有没有从被覆写的方法继承来的 `@Nullable` 形参。
fn inherits_nullable_param(ctx: &Ctx<'_>, body: BodyId) -> bool {
    let BodyId::Method(method) = body else {
        return false;
    };
    let has_params = hir::method_data(ctx.db, method).is_some_and(|m| !m.params.is_empty());
    has_params
        && ctx
            .inherited(method)
            .params
            .contains(&Some(NullAnnotation::Nullable))
}

pub(crate) fn nullness_diagnostics(view: &View<'_>, out: &mut Vec<Diagnostic>) {
    let db = view.db;
    let ctx = Ctx::new(db);
    for body in &view.bodies {
        db.unwind_if_revision_cancelled();
        let text = body.text(view);
        let result = body.result(view);
        // "一定是 null" 只能来自 `null` 字面量，"可能是 null" 只能来自 `@Nullable` 形参（注解名都含
        // `Null`）、继承来的 `@Nullable` 形参或者标了 `@Nullable` 的成员：都没有时分析不出任何问题
        if !text.contains("null")
            && !text.contains("Null")
            && !uses_nullable_member(&ctx, &result)
            && !inherits_nullable_param(&ctx, body.id)
        {
            continue;
        }
        let file_text = view.text();
        for (range, code, message) in analyze(&ctx, body.id, &body.node, file_text, &result) {
            out.push(Diagnostic {
                range,
                message,
                severity: Severity::Warning,
                code,
                unused: false,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use test_fixture::fixture;

    use crate::{diagnostics, whole_file_diagnostics, DiagnosticCode, DiagnosticsConfig};

    /// 第一个文件里的空值诊断：(代码, 诊断范围的文本)。
    fn nullness(text: &str) -> Vec<(DiagnosticCode, String)> {
        let fx = fixture(text);
        let file = fx.file().source;
        let source: &str = file.text(&fx.db);
        let diags = diagnostics(&fx.db, file, &DiagnosticsConfig::default());
        assert_eq!(
            diags,
            whole_file_diagnostics(&fx.db, file, &DiagnosticsConfig::default())
        );
        diags
            .into_iter()
            .filter(|d| {
                matches!(
                    d.code,
                    DiagnosticCode::NullabilityViolation
                        | DiagnosticCode::NullableDereference
                        | DiagnosticCode::NullDereference
                        | DiagnosticCode::ConstantCondition
                )
            })
            .map(|d| {
                let range = usize::from(d.range.start())..usize::from(d.range.end());
                (d.code, source[range].to_owned())
            })
            .collect()
    }

    #[test]
    fn module_defaults_apply_to_its_classes() {
        let diags = nullness(
            r#"
//- /p/A.java
package p;

class A {
    String get() { return null; }
    void take(String s) {}
    void use() { take(null); }
}
//- /module-info.java
@org.jspecify.annotations.NullMarked
module m {}
"#,
        );
        assert_eq!(diags.len(), 2, "{diags:?}");
        assert!(diags
            .iter()
            .all(|(code, text)| *code == DiagnosticCode::NullabilityViolation && text == "null"));
    }

    #[test]
    fn package_unmarked_overrides_module() {
        let diags = nullness(
            r#"
//- /p/A.java
package p;

class A {
    String get() { return null; }
}
//- /p/package-info.java
@NullUnmarked
package p;
//- /module-info.java
@NullMarked
module m {}
"#,
        );
        assert!(diags.is_empty(), "{diags:?}");
    }

    #[test]
    fn default_qualifier_with_locations() {
        let diags = nullness(
            r#"
@DefaultQualifier(value = NonNull.class, locations = TypeUseLocation.PARAMETER)
class A {
    String get() { return null; }
    void take(String s) {}
    void use() { take(null); }
}
"#,
        );
        assert_eq!(
            diags,
            [(DiagnosticCode::NullabilityViolation, "null".to_owned())]
        );
    }

    #[test]
    fn default_locations_match_whole_names() {
        let diags = nullness(
            r#"
@DefaultQualifier(value = NonNull.class, locations = TypeUseLocation.EXCEPTION_PARAMETER)
class A {
    void take(String s) {}
    void use() { take(null); }
}
"#,
        );
        assert!(diags.is_empty(), "{diags:?}");
    }

    #[test]
    fn eclipse_default_with_locations() {
        let diags = nullness(
            r#"
@NonNullByDefault({DefaultLocation.TYPE_PARAMETER, DefaultLocation.RETURN_TYPE})
class A {
    String get() { return null; }
    void take(String s) {}
    @NonNullByDefault(false)
    String legacy() { return null; }
    void use() { take(null); }
}
"#,
        );
        assert_eq!(
            diags,
            [(DiagnosticCode::NullabilityViolation, "null".to_owned())]
        );
    }
}
