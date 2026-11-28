//! 诊断：语法错误 + 保守的语义诊断。
//!
//! 语义诊断只报"确定是错的"：推断拿不准的地方一律是未知类型，不产生诊断。
//! 没有 JDK（类路径为空）时语义诊断整体关闭，否则满屏都是 `String` 无法解析。

mod exceptions;
mod field_final;
mod field_local;
mod final_fields;
mod format_strings;
pub use arrays::array_misuse;
pub use boxing::unnecessary_boxing_fixes;
pub use diamond::redundant_diamond_ranges;
pub use exceptions::{
    redundant_throws, thrown_exceptions, unhandled_exceptions, RedundantThrows, UnhandledException,
};
pub use field_local::{fields_to_locals, FieldToLocal};
pub use language_level::language_level;
pub use loops::string_concat_in_loops;
pub use may_be_static::methods_that_may_be_static;
pub use optionals::unchecked_optional_get_diagnostics;
pub use probable_bugs::probable_bug_diagnostics;
pub use redundancy::{redundancy_fixes, RedundancyFix};
pub use spring::config_file_diagnostics;
pub use suppress::suppression_key;
mod annotation_targets;
mod arrays;
mod boxing;
mod bug_patterns;
mod collections;
mod dead_stores;
mod diamond;
mod empty_blocks;
mod flow;
mod ignored_results;
mod inspections;
mod jumps;
mod lambdas;
mod language_level;
mod loops;
mod map_api;
mod may_be_static;
mod module_access;
mod nullness;
mod optionals;
mod pattern_vars;
mod probable_bugs;
mod raw_types;
mod recursion;
mod redundancy;
mod redundant_modifiers;
mod simplifiable_calls;
mod spring;
mod suppress;
mod suspicious_calls;
pub mod timing;
mod try_resources;
mod typeck;
mod unchecked;
mod view;

use std::sync::Arc;

use base_db::{workspace, Db, FileKind, SourceFile};
use hir::{package_exists, resolve_qualified_class, BodyId, InferDiagnosticKind, Semantics};
use rustc_hash::{FxHashMap, FxHashSet};
use syntax::{
    ast::{self, AstNode},
    SyntaxKind, SyntaxNode, TextRange, TextSize,
};
use view::View;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Severity {
    Error,
    Warning,
    Hint,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DiagnosticCode {
    SyntaxError,
    UnresolvedName,
    UnresolvedType,
    UnresolvedField,
    UnresolvedMethod,
    TypeMismatch,
    ArgumentMismatch,
    AmbiguousCall,
    TypeArgOutOfBounds,
    BadOperand,
    DuplicateVariable,
    AssignToFinal,
    InaccessibleMember,
    StaticContext,
    MissingImplementation,
    InvalidOverride,
    SealedSubtype,
    NonExhaustiveSwitch,
    DominatedCase,
    UnresolvedImport,
    UnresolvedModule,
    CompactSourceFile,
    FeatureNotAvailable,
    UnusedImport,
    UnusedLocal,
    UnusedParameter,
    UnusedPrivateMember,
    UnreachableCode,
    MissingReturn,
    StringEquality,
    SelfAssignment,
    SelfComparison,
    UninitializedVariable,
    UnhandledException,
    /// `catch` 了 try 块不会抛出的受检异常
    ExceptionNeverThrown,
    /// `final` 字段没有被初值、初始化块或构造器赋值
    UninitializedFinalField,
    NullDereference,
    /// 解引用可能为 null 的值（来自 `@Nullable`）
    NullableDereference,
    /// 把 null 传给 `@NotNull` 形参、从 `@NotNull` 方法返回 null
    NullabilityViolation,
    ConstantCondition,
    DeprecatedUsage,
    PointlessBoolean,
    UseIsEmpty,
    RedundantIf,
    RedundantCast,
    UnusedAssignment,
    FieldMayBeFinal,
    RedundantModifier,
    RedundantLocal,
    MalformedFormatString,
    SuspiciousCall,
    IgnoredResult,
    ArrayEquals,
    ArrayToString,
    NumberEquality,
    LoopConditionNotUpdated,
    StringConcatInLoop,
    InfiniteRecursion,
    RedundantJump,
    MismatchedCollection,
    IntegerDivision,
    OctalLiteral,
    EqualsHashCode,
    ThreadRun,
    MethodMayBeStatic,
    LambdaToMethodRef,
    OptionalGetWithoutCheck,
    FieldCanBeLocal,
    RedundantThrows,
    UnnecessaryBoxing,
    RedundantTypeArguments,
    CStyleArray,
    RedundantToString,
    RedundantStringConstructor,
    PatternVariable,
    MapApi,
    TryWithResources,
    AbstractInstantiation,
    MisplacedJump,
    DuplicateCaseLabel,
    EmptyBlock,
    EmptyStatementBody,
    UnresolvedConfigProperty,
    /// Spring 配置文件里，已知分组下不存在的键
    UnknownConfigProperty,
    /// Spring 配置文件里已弃用的配置项
    DeprecatedConfigProperty,
    StreamApiChain,
    CollectionsSort,
    IndexOfContains,
    RedundantValueOf,
    RawType,
    ThrowableNotThrown,
    SyncOnNonFinalField,
    NonAtomicVolatile,
    IntMultiplicationToLong,
    RedundantArrayCreation,
    AppendConcatenation,
    UnusedLabel,
    DuplicateBranches,
    DuplicateCondition,
    /// 注解的 `@Target` 不允许用在这种声明上
    AnnotationNotApplicable,
    /// 未经检查的转换、调用和强制转换（javac 的 `-Xlint:unchecked`）
    Unchecked,
}

impl DiagnosticCode {
    pub fn as_str(self) -> &'static str {
        match self {
            DiagnosticCode::SyntaxError => "syntax-error",
            DiagnosticCode::UnresolvedName => "unresolved-name",
            DiagnosticCode::UnresolvedType => "unresolved-type",
            DiagnosticCode::UnresolvedField => "unresolved-field",
            DiagnosticCode::UnresolvedMethod => "unresolved-method",
            DiagnosticCode::TypeMismatch => "type-mismatch",
            DiagnosticCode::ArgumentMismatch => "argument-mismatch",
            DiagnosticCode::AmbiguousCall => "ambiguous-call",
            DiagnosticCode::TypeArgOutOfBounds => "type-arg-out-of-bounds",
            DiagnosticCode::BadOperand => "bad-operand",
            DiagnosticCode::DuplicateVariable => "duplicate-variable",
            DiagnosticCode::AssignToFinal => "assign-to-final",
            DiagnosticCode::InaccessibleMember => "inaccessible-member",
            DiagnosticCode::StaticContext => "static-context",
            DiagnosticCode::MissingImplementation => "missing-implementation",
            DiagnosticCode::InvalidOverride => "invalid-override",
            DiagnosticCode::SealedSubtype => "sealed-subtype",
            DiagnosticCode::NonExhaustiveSwitch => "non-exhaustive-switch",
            DiagnosticCode::DominatedCase => "dominated-case",
            DiagnosticCode::UnresolvedImport => "unresolved-import",
            DiagnosticCode::UnresolvedModule => "unresolved-module",
            DiagnosticCode::CompactSourceFile => "compact-source-file",
            DiagnosticCode::FeatureNotAvailable => "feature-not-available",
            DiagnosticCode::UnusedImport => "unused-import",
            DiagnosticCode::UnusedLocal => "unused-local",
            DiagnosticCode::UnusedParameter => "unused-parameter",
            DiagnosticCode::UnusedPrivateMember => "unused-private-member",
            DiagnosticCode::UnreachableCode => "unreachable-code",
            DiagnosticCode::MissingReturn => "missing-return",
            DiagnosticCode::StringEquality => "string-equality",
            DiagnosticCode::SelfAssignment => "self-assignment",
            DiagnosticCode::SelfComparison => "self-comparison",
            DiagnosticCode::UninitializedVariable => "uninitialized-variable",
            DiagnosticCode::UnhandledException => "unhandled-exception",
            DiagnosticCode::ExceptionNeverThrown => "exception-never-thrown",
            DiagnosticCode::UninitializedFinalField => "uninitialized-final-field",
            DiagnosticCode::NullDereference => "null-dereference",
            DiagnosticCode::NullableDereference => "nullable-dereference",
            DiagnosticCode::NullabilityViolation => "nullability-violation",
            DiagnosticCode::ConstantCondition => "constant-condition",
            DiagnosticCode::DeprecatedUsage => "deprecated",
            DiagnosticCode::PointlessBoolean => "pointless-boolean",
            DiagnosticCode::UseIsEmpty => "use-is-empty",
            DiagnosticCode::RedundantIf => "redundant-if",
            DiagnosticCode::RedundantCast => "redundant-cast",
            DiagnosticCode::UnusedAssignment => "unused-assignment",
            DiagnosticCode::FieldMayBeFinal => "field-may-be-final",
            DiagnosticCode::RedundantModifier => "redundant-modifier",
            DiagnosticCode::RedundantLocal => "redundant-local",
            DiagnosticCode::MalformedFormatString => "malformed-format-string",
            DiagnosticCode::SuspiciousCall => "suspicious-call",
            DiagnosticCode::IgnoredResult => "ignored-result",
            DiagnosticCode::ArrayEquals => "array-equals",
            DiagnosticCode::ArrayToString => "array-to-string",
            DiagnosticCode::NumberEquality => "number-equality",
            DiagnosticCode::LoopConditionNotUpdated => "loop-condition-not-updated",
            DiagnosticCode::StringConcatInLoop => "string-concat-in-loop",
            DiagnosticCode::InfiniteRecursion => "infinite-recursion",
            DiagnosticCode::RedundantJump => "redundant-jump",
            DiagnosticCode::MismatchedCollection => "mismatched-collection",
            DiagnosticCode::IntegerDivision => "integer-division",
            DiagnosticCode::OctalLiteral => "octal-literal",
            DiagnosticCode::EqualsHashCode => "equals-hash-code",
            DiagnosticCode::ThreadRun => "thread-run",
            DiagnosticCode::MethodMayBeStatic => "method-may-be-static",
            DiagnosticCode::LambdaToMethodRef => "lambda-to-method-ref",
            DiagnosticCode::OptionalGetWithoutCheck => "optional-get-without-check",
            DiagnosticCode::FieldCanBeLocal => "field-can-be-local",
            DiagnosticCode::RedundantThrows => "redundant-throws",
            DiagnosticCode::UnnecessaryBoxing => "unnecessary-boxing",
            DiagnosticCode::RedundantTypeArguments => "redundant-type-arguments",
            DiagnosticCode::CStyleArray => "c-style-array",
            DiagnosticCode::RedundantToString => "redundant-to-string",
            DiagnosticCode::RedundantStringConstructor => "redundant-string-constructor",
            DiagnosticCode::PatternVariable => "pattern-variable",
            DiagnosticCode::MapApi => "map-api",
            DiagnosticCode::TryWithResources => "try-with-resources",
            DiagnosticCode::AbstractInstantiation => "abstract-instantiation",
            DiagnosticCode::MisplacedJump => "misplaced-jump",
            DiagnosticCode::DuplicateCaseLabel => "duplicate-case-label",
            DiagnosticCode::EmptyBlock => "empty-block",
            DiagnosticCode::EmptyStatementBody => "empty-statement-body",
            DiagnosticCode::UnresolvedConfigProperty => "unresolved-config-property",
            DiagnosticCode::UnknownConfigProperty => "unknown-config-property",
            DiagnosticCode::DeprecatedConfigProperty => "deprecated-config-property",
            DiagnosticCode::StreamApiChain => "stream-api-chain",
            DiagnosticCode::CollectionsSort => "collections-sort",
            DiagnosticCode::IndexOfContains => "index-of-contains",
            DiagnosticCode::RedundantValueOf => "redundant-value-of",
            DiagnosticCode::RawType => "raw-type",
            DiagnosticCode::ThrowableNotThrown => "throwable-not-thrown",
            DiagnosticCode::SyncOnNonFinalField => "sync-on-non-final-field",
            DiagnosticCode::NonAtomicVolatile => "non-atomic-volatile",
            DiagnosticCode::IntMultiplicationToLong => "int-multiplication-to-long",
            DiagnosticCode::RedundantArrayCreation => "redundant-array-creation",
            DiagnosticCode::AppendConcatenation => "append-concatenation",
            DiagnosticCode::UnusedLabel => "unused-label",
            DiagnosticCode::DuplicateBranches => "duplicate-branches",
            DiagnosticCode::DuplicateCondition => "duplicate-condition",
            DiagnosticCode::AnnotationNotApplicable => "annotation-not-applicable",
            DiagnosticCode::Unchecked => "unchecked",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub range: TextRange,
    pub message: String,
    pub severity: Severity,
    pub code: DiagnosticCode,
    /// 编辑器会把这段代码显示成灰色（未使用）
    pub unused: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiagnosticsConfig {
    pub semantic: bool,
    pub unused_imports: bool,
    /// 未使用的局部变量和私有成员
    pub unused_symbols: bool,
    /// 流分析（不可达语句、缺少 return）和表达式检查项
    pub inspections: bool,
}

impl Default for DiagnosticsConfig {
    fn default() -> Self {
        DiagnosticsConfig {
            semantic: true,
            unused_imports: true,
            unused_symbols: true,
            inspections: true,
        }
    }
}

pub fn syntax_diagnostics(db: &dyn Db, file: SourceFile) -> Vec<Diagnostic> {
    base_db::parse(db, file)
        .errors()
        .iter()
        .map(|err| Diagnostic {
            range: err.range,
            message: base_db::syntax_error_message(&err.message, base_db::lang()),
            severity: Severity::Error,
            code: DiagnosticCode::SyntaxError,
            unused: false,
        })
        .collect()
}

/// 文件里所有可推断的体。
pub fn bodies_in_file(db: &dyn Db, file: SourceFile) -> Vec<BodyId> {
    // 同一个文件的诊断要调用很多次，结果缓存在 salsa 里
    bodies_tracked(db, file).as_ref().clone()
}

/// 文件里所有可推断的体和它们的语法节点（拿不到语法节点的体不在其中）。
/// 很多检查都要逐个看体的语法，先找好节点给它们共用。
pub(crate) fn file_bodies_syntax(db: &dyn Db, file: SourceFile) -> Vec<(BodyId, SyntaxNode)> {
    bodies_tracked(db, file)
        .iter()
        .filter_map(|&id| {
            let (body_file, node) = hir::body_syntax(db, id)?;
            (body_file == file).then_some((id, node))
        })
        .collect()
}

#[salsa::tracked]
fn bodies_tracked(db: &dyn Db, file: SourceFile) -> std::sync::Arc<Vec<BodyId>> {
    std::sync::Arc::new(compute_bodies_in_file(db, file))
}

fn compute_bodies_in_file(db: &dyn Db, file: SourceFile) -> Vec<BodyId> {
    let sema = Semantics::new(db);
    let root = base_db::parse(db, file).syntax_node();
    let mut seen = FxHashSet::default();
    let mut res = Vec::new();
    for node in root.descendants() {
        let is_body_root = match node.kind() {
            SyntaxKind::METHOD_DECL
            | SyntaxKind::CONSTRUCTOR_DECL
            | SyntaxKind::ENUM_CONSTANT
            | SyntaxKind::INITIALIZER_BLOCK => true,
            SyntaxKind::VARIABLE_DECLARATOR => node
                .parent()
                .is_some_and(|p| p.kind() == SyntaxKind::FIELD_DECL),
            _ => false,
        };
        if !is_body_root {
            continue;
        }
        if let Some(body) = sema.body_of(file, &node) {
            if seen.insert(body) {
                res.push(body);
            }
        }
    }
    res
}

/// 诊断所在的语句（复合语句只算到它的子语句之前，即 `if (...)`、`for (...)` 这样的头部）
/// 里有语法错误：这条语句还没写完，基于它的类型检查结果没有意义。
fn in_incomplete_statement(root: &SyntaxNode, errors: &[TextSize], range: TextRange) -> bool {
    if errors.is_empty() {
        return false;
    }
    let is_statement = |kind: SyntaxKind| {
        matches!(
            kind,
            SyntaxKind::LOCAL_VAR_DECL
                | SyntaxKind::EXPR_STMT
                | SyntaxKind::IF_STMT
                | SyntaxKind::WHILE_STMT
                | SyntaxKind::DO_WHILE_STMT
                | SyntaxKind::FOR_STMT
                | SyntaxKind::FOREACH_STMT
                | SyntaxKind::RETURN_STMT
                | SyntaxKind::THROW_STMT
                | SyntaxKind::YIELD_STMT
                | SyntaxKind::ASSERT_STMT
                | SyntaxKind::SYNCHRONIZED_STMT
                | SyntaxKind::SWITCH_STMT
                | SyntaxKind::FIELD_DECL
        )
    };
    let node = match root.covering_element(range) {
        syntax::NodeOrToken::Node(node) => node,
        syntax::NodeOrToken::Token(token) => match token.parent() {
            Some(parent) => parent,
            None => return false,
        },
    };
    let Some(statement) = node.ancestors().find(|n| is_statement(n.kind())) else {
        return false;
    };
    let start = statement.text_range().start();
    // 子语句 / 块之前的部分；诊断本身在子语句里时不会走到这里（最内层的语句就是它所在的）
    let end = statement
        .children()
        .find(|c| {
            c.kind() == SyntaxKind::BLOCK
                || (is_statement(c.kind()) && c.kind() != SyntaxKind::LOCAL_VAR_DECL)
        })
        .map_or(statement.text_range().end(), |c| c.text_range().start());
    errors
        .iter()
        .any(|&offset| start <= offset && offset <= end)
}

/// 推断时发现的错误。写了一半的语句里的错误由调用方去掉（要看整个文件的语法错误）。
fn infer_diagnostics(view: &View<'_>, out: &mut Vec<Diagnostic>) {
    for body in &view.bodies {
        view.db.unwind_if_revision_cancelled();
        let result = body.result(view);
        for diag in result.diagnostics() {
            let (message, code) = match &diag.kind {
                InferDiagnosticKind::UnresolvedName { name } => (
                    base_db::tr!("无法解析符号 `{name}`", "Cannot resolve symbol `{name}`"),
                    DiagnosticCode::UnresolvedName,
                ),
                InferDiagnosticKind::UnresolvedField { name, receiver } => (
                    base_db::tr!(
                        "类型 `{receiver}` 上没有字段 `{name}`",
                        "No field `{name}` on type `{receiver}`"
                    ),
                    DiagnosticCode::UnresolvedField,
                ),
                InferDiagnosticKind::UnresolvedMethod { name, receiver } => (
                    match receiver {
                        Some(receiver) => base_db::tr!(
                            "类型 `{receiver}` 上没有方法 `{name}`",
                            "No method `{name}` on type `{receiver}`"
                        ),
                        None => {
                            base_db::tr!("无法解析方法 `{name}`", "Cannot resolve method `{name}`")
                        }
                    },
                    DiagnosticCode::UnresolvedMethod,
                ),
                InferDiagnosticKind::TypeMismatch { expected, actual } => (
                    base_db::tr!(
                        "类型不匹配：需要 `{expected}`，实际是 `{actual}`",
                        "Type mismatch: expected `{expected}`, found `{actual}`"
                    ),
                    DiagnosticCode::TypeMismatch,
                ),
                InferDiagnosticKind::ArgumentMismatch { name, args } => (
                    base_db::tr!(
                        "`{name}` 没有可以接受实参 ({args}) 的重载",
                        "No overload of `{name}` accepts the arguments ({args})"
                    ),
                    DiagnosticCode::ArgumentMismatch,
                ),
                InferDiagnosticKind::BadOperand { op, operands } => (
                    base_db::tr!(
                        "运算符 `{op}` 不能用于 {operands}",
                        "Operator `{op}` cannot be applied to {operands}"
                    ),
                    DiagnosticCode::BadOperand,
                ),
                InferDiagnosticKind::DuplicateLocal { name } => (
                    base_db::tr!(
                        "变量 `{name}` 已经在这个方法里定义过",
                        "Variable `{name}` is already defined in this method"
                    ),
                    DiagnosticCode::DuplicateVariable,
                ),
                InferDiagnosticKind::AmbiguousCall {
                    name,
                    first,
                    second,
                } => (
                    base_db::tr!(
                        "对 `{name}` 的调用不明确：`{first}` 和 `{second}` 都匹配",
                        "Reference to `{name}` is ambiguous: both `{first}` and `{second}` match"
                    ),
                    DiagnosticCode::AmbiguousCall,
                ),
                InferDiagnosticKind::LambdaArity {
                    target,
                    expected,
                    found,
                } => (
                    base_db::tr!(
                        "lambda 有 {found} 个形参，但 `{target}` 的方法需要 {expected} 个",
                        "Lambda has {found} parameter(s), but the method of `{target}` takes {expected}"
                    ),
                    DiagnosticCode::TypeMismatch,
                ),
                InferDiagnosticKind::LambdaReturnsValue { target } => (
                    base_db::tr!(
                        "`{target}` 的方法返回 void，lambda 体不能是一个值",
                        "The method of `{target}` returns void, so the lambda body cannot be a value"
                    ),
                    DiagnosticCode::TypeMismatch,
                ),
                InferDiagnosticKind::LambdaMissingValue { target, expected } => (
                    base_db::tr!(
                        "lambda 体缺少返回值：`{target}` 的方法要返回 `{expected}`",
                        "Lambda body is missing a return value: the method of `{target}` returns `{expected}`"
                    ),
                    DiagnosticCode::TypeMismatch,
                ),
                InferDiagnosticKind::PrimitiveDereference { ty, method } => (
                    base_db::tr!(
                        "`{ty}` 不是引用类型，不能访问它的成员",
                        "`{ty}` is not a reference type and cannot be dereferenced"
                    ),
                    if *method {
                        DiagnosticCode::UnresolvedMethod
                    } else {
                        DiagnosticCode::UnresolvedField
                    },
                ),
                InferDiagnosticKind::NotAnArray { ty } => (
                    base_db::tr!(
                        "`{ty}` 不是数组类型，不能用下标访问",
                        "Array required, but `{ty}` found"
                    ),
                    DiagnosticCode::TypeMismatch,
                ),
                InferDiagnosticKind::NotIterable { ty } => (
                    base_db::tr!(
                        "`{ty}` 既不是数组也不是 `Iterable`，不能用在增强 for 循环里",
                        "For-each not applicable to expression type `{ty}`"
                    ),
                    DiagnosticCode::TypeMismatch,
                ),
                InferDiagnosticKind::CannotInferVar { name, reason } => (
                    base_db::tr!(
                        "无法推断局部变量 `{name}` 的类型：{reason}",
                        "Cannot infer type for local variable `{name}`: {reason}"
                    ),
                    DiagnosticCode::TypeMismatch,
                ),
            };
            out.push(Diagnostic {
                range: diag.range,
                message,
                severity: Severity::Error,
                code,
                unused: false,
            });
        }
    }
}

/// 类及其所有祖先是否都解析成功：只有这样，"继承来的成员类型里也没有"才是确定的。
pub(crate) fn hierarchy_is_resolved(db: &dyn Db, class: hir::ClassId) -> bool {
    std::iter::once(class)
        .chain(hir::all_supers(db, class))
        .all(|c| {
            hir::class_header(db, c).is_some_and(|data| {
                let declared = data.superclass.iter().count() + data.interfaces.len();
                hir::class_supertypes(db, c).len() == declared
            })
        })
}

/// 按需 import 和模块导入都解析得了：只有这样，解析不了的简单名才确定是错的。
#[salsa::tracked]
fn type_names_checkable(db: &dyn Db, file: SourceFile) -> bool {
    let tree = hir::item_tree(db, file);
    let on_demand_ok = tree.imports.iter().filter(|i| i.is_on_demand).all(|i| {
        package_exists(db, &i.segments.join("/"))
            || resolve_qualified_class(db, &i.segments).is_some()
    });
    let graph = hir::module_graph(db);
    let module_imports_ok = tree
        .module_imports
        .iter()
        .all(|module| graph.get(module).is_some());
    on_demand_ok && module_imports_ok
}

/// 文件里声明的类型名、类型参数名，以及单类型 import 带进来的名字（解析不了的 import 已经
/// 单独报过）。每次编辑后重新计算，但方法体里的编辑通常不改变它。
#[salsa::tracked]
fn known_type_names(db: &dyn Db, file: SourceFile) -> Arc<FxHashSet<String>> {
    let tree = hir::item_tree(db, file);
    let mut known: FxHashSet<String> = tree
        .imports
        .iter()
        .filter(|i| !i.is_on_demand)
        .filter_map(|i| i.segments.last().map(|s| s.to_string()))
        .collect();
    let root = base_db::parse(db, file).syntax_node();
    for node in root.descendants() {
        if matches!(
            node.kind(),
            SyntaxKind::TYPE_PARAM
                | SyntaxKind::CLASS_DECL
                | SyntaxKind::INTERFACE_DECL
                | SyntaxKind::ENUM_DECL
                | SyntaxKind::RECORD_DECL
                | SyntaxKind::ANNOTATION_TYPE_DECL
        ) {
            if let Some(name) = node.children().find_map(ast::Name::cast) {
                known.insert(name.text().to_string());
            }
        }
    }
    Arc::new(known)
}

/// 类型位置上解析不了的类型名：声明的类型、类型实参、`new`、强制转换、`throws`、`catch`、
/// 注解名等。
///
/// 只报确定的：带限定符的名字只在限定符解析成已知的类（继承链完整）或已知的包时才报；
/// 没有登记成类的匿名类里的名字只在能确定它不是父类型继承来的成员类型时才报
/// （`outer.new Inner() { ... }`、枚举常量的类体里一律不报）；有按需 import 解析不了的文件不报。
fn unresolved_types(view: &View<'_>, out: &mut Vec<Diagnostic>) {
    let (db, file, sema) = (view.db, view.file, &view.sema);
    if !type_names_checkable(db, file) {
        return;
    }
    // 文件里声明的和 import 带进来的名字：只在遇到解析不了的名字时才读（加一条 import 会
    // 改变它，读了它的体都得重新检查）
    let mut known: Option<Arc<FxHashSet<String>>> = None;

    let mut resolved_hierarchy: FxHashMap<hir::ClassId, bool> = FxHashMap::default();
    let mut resolved_names: FxHashMap<(hir::TypeScope, hir::Name), bool> = FxHashMap::default();
    for node in view.nodes() {
        let name_ref = if let Some(class_ty) = ast::ClassType::cast(node.clone()) {
            if node
                .parent()
                .is_some_and(|p| p.kind() == SyntaxKind::CLASS_TYPE)
            {
                continue;
            }
            if class_ty.qualifier().is_some() {
                let names = known
                    .get_or_insert_with(|| known_type_names(db, file))
                    .clone();
                if let Some(diagnostic) =
                    unresolved_qualified_type(db, sema, file, &class_ty, &names)
                {
                    out.push(diagnostic);
                }
                continue;
            }
            class_ty.name_ref()
        } else if let Some(annotation) = ast::Annotation::cast(node.clone()) {
            // 注解名是 `QualifiedName`，不是 `ClassType`：只查简单名 `@Foo`
            annotation
                .name()
                .filter(|name| name.qualifier().is_none())
                .and_then(|name| name.name_ref())
        } else {
            continue;
        };
        let Some(name_ref) = name_ref else {
            continue;
        };
        let name = name_ref.text();
        if name == "var" {
            continue;
        }
        if may_inherit_from_anonymous_class(db, sema, file, &node, &name) {
            continue;
        }
        // `outer.new Inner()`：`Inner` 是 `outer` 的类型的成员，不按简单名解析
        let qualified_new = node.parent().is_some_and(|p| {
            p.kind() == SyntaxKind::NEW_EXPR && p.children().any(|c| ast::Expr::can_cast(c.kind()))
        });
        if qualified_new {
            continue;
        }
        let scope = sema.type_scope(file, &node);
        // 同一个作用域里同一个名字只解析一次
        let resolved = *resolved_names
            .entry((scope, name.clone()))
            .or_insert_with(|| hir::resolve_simple_type(db, &scope, &name).is_some());
        if resolved
            || known
                .get_or_insert_with(|| known_type_names(db, file))
                .contains(name.as_str())
        {
            continue;
        }
        // 记录头部的组件类型可以用记录自己继承来的成员类型
        let inherited_by_decl = node
            .ancestors()
            .find_map(ast::TypeDecl::cast)
            .and_then(|decl| sema.class_of_decl(file, &decl))
            .is_some_and(|class| hir::member_type(db, class, &name).is_some());
        if inherited_by_decl {
            continue;
        }
        // 外围各层类的继承链必须完整，否则名字可能是没解析出来的父类型的成员类型
        let mut enclosing = scope.class;
        let mut reliable = true;
        while let Some(class) = enclosing {
            let ok = *resolved_hierarchy
                .entry(class)
                .or_insert_with(|| hierarchy_is_resolved(db, class));
            if !ok {
                reliable = false;
                break;
            }
            enclosing = hir::outer_class(db, class);
        }
        if !reliable {
            continue;
        }
        // 几个模块导入带进了同名的类
        let ambiguous = hir::module_import_candidates(db, file, &name);
        let message = if ambiguous.len() > 1 {
            let names: Vec<String> = ambiguous
                .iter()
                .map(|class| class.binary_name(db).replace(['/', '$'], "."))
                .collect();
            base_db::tr!(
                "类型 `{name}` 不明确：模块导入同时带进了 {}",
                "Type `{name}` is ambiguous: module imports bring in {}",
                names.join(", ")
            )
        } else {
            base_db::tr!("无法解析类型 `{name}`", "Cannot resolve type `{name}`")
        };
        out.push(Diagnostic {
            range: name_ref.syntax().text_range(),
            message,
            severity: Severity::Error,
            code: DiagnosticCode::UnresolvedType,
            unused: false,
        });
    }
}

/// 节点在没有登记成类的匿名类（菱形 `new T<>() { ... }`、`outer.new Inner() { ... }`）
/// 里面，简单名 `name` 可能是它的父类型继承来的成员类型。
///
/// 菱形匿名类的父类型就是写出来的那个类（只有类型实参要推断）：它解析得出来、继承链完整、
/// 也没有叫 `name` 的成员类型时，名字就不是继承来的。其余的匿名类拿不准。
fn may_inherit_from_anonymous_class(
    db: &dyn Db,
    sema: &Semantics<'_>,
    file: SourceFile,
    node: &syntax::SyntaxNode,
    name: &str,
) -> bool {
    node.ancestors().any(|ancestor| {
        if ancestor.kind() != SyntaxKind::CLASS_BODY {
            return false;
        }
        let Some(owner) = ancestor.parent() else {
            return false;
        };
        if !matches!(
            owner.kind(),
            SyntaxKind::NEW_EXPR | SyntaxKind::ENUM_CONSTANT
        ) || sema.anonymous_class_of_body(file, &ancestor).is_some()
        {
            return false;
        }
        let Some(new_expr) = ast::NewExpr::cast(owner).filter(|n| n.qualifier().is_none()) else {
            return true;
        };
        let Some(ty) = new_expr.ty() else {
            return true;
        };
        let diamond = matches!(&ty, ast::Type::ClassType(class_ty)
            if class_ty.type_arg_list().is_some_and(|args| args.args().next().is_none()));
        if !diamond {
            return true;
        }
        match sema.resolve_type(file, &ty) {
            hir::Ty::Class(class, _) => {
                !hierarchy_is_resolved(db, class) || hir::member_type(db, class, name).is_some()
            }
            _ => true,
        }
    })
}

/// 带限定符的类型名 `a.b.Missing` / `Outer.Missing`：从左往右逐段解析，第一段按简单名
/// 解析（解析不了时当作包名），之后每段是上一段的类的成员类型，或上一段的包里的类 / 子包。
/// 某一段在一个继承链完整的类里找不到成员类型，或者在一个已知的包里既不是类也不是子包时报错。
fn unresolved_qualified_type(
    db: &dyn Db,
    sema: &Semantics<'_>,
    file: SourceFile,
    class_ty: &ast::ClassType,
    known: &FxHashSet<String>,
) -> Option<Diagnostic> {
    enum Prefix {
        Class(hir::ClassId),
        /// 包名，以及它是不是已知的包（`java` 这样只有子包的前缀不一定登记过）
        Package(String, bool),
    }
    let mut names = Vec::new();
    let mut cur = Some(class_ty.clone());
    while let Some(ty) = cur {
        names.push(ty.name_ref()?);
        cur = ty.qualifier();
    }
    names.reverse();
    let (first, rest) = names.split_first()?;
    let first_text = first.text();
    if may_inherit_from_anonymous_class(db, sema, file, class_ty.syntax(), &first_text) {
        return None;
    }
    let scope = sema.type_scope(file, class_ty.syntax());
    let mut prefix = match hir::resolve_simple_type(db, &scope, &first_text) {
        Some(hir::TypeNs::Class(class)) => Prefix::Class(class),
        Some(hir::TypeNs::TypeParam(_)) => return None,
        None => {
            // 文件里声明或 import 了这个名字却解析不出来：拿不准，不当作包
            if known.contains(first_text.as_str()) {
                return None;
            }
            Prefix::Package(first_text.to_string(), package_exists(db, &first_text))
        }
    };
    for (idx, name) in rest.iter().enumerate() {
        let text = name.text();
        prefix = match prefix {
            Prefix::Class(class) => match hir::member_type(db, class, &text) {
                Some(member) => Prefix::Class(member),
                None => {
                    if !hierarchy_is_resolved(db, class) || typeck::lombok_involved(db, class) {
                        return None;
                    }
                    return Some(unresolved_segment(&names[..idx + 2], name));
                }
            },
            Prefix::Package(package, package_known) => {
                let qualified = format!("{package}/{text}");
                if let Some(class) = hir::lookup_class(db, &qualified) {
                    Prefix::Class(class)
                } else if package_exists(db, &qualified) {
                    Prefix::Package(qualified, true)
                } else if package_known {
                    return Some(unresolved_segment(&names[..idx + 2], name));
                } else {
                    // 前缀本身就不是已知的包：可能是解析不出来的类型
                    Prefix::Package(qualified, false)
                }
            }
        };
    }
    None
}

fn unresolved_segment(path: &[ast::NameRef], name: &ast::NameRef) -> Diagnostic {
    let path = path
        .iter()
        .map(|n| n.text().to_string())
        .collect::<Vec<_>>()
        .join(".");
    Diagnostic {
        range: name.syntax().text_range(),
        message: base_db::tr!("无法解析类型 `{path}`", "Cannot resolve type `{path}`"),
        severity: Severity::Error,
        code: DiagnosticCode::UnresolvedType,
        unused: false,
    }
}

/// 除 import 以外，文件里出现过的全部标识符（含注释里的词，Javadoc 的 `{@link Foo}` 也算使用）。
pub fn used_identifiers(cu: &ast::CompilationUnit) -> FxHashSet<String> {
    let mut used = FxHashSet::default();
    let tokens = cu
        .syntax()
        .descendants_with_tokens()
        .filter_map(|element| element.into_token());
    for token in tokens {
        match token.kind() {
            SyntaxKind::IDENT => {
                let in_import = token
                    .parent_ancestors()
                    .any(|n| n.kind() == SyntaxKind::IMPORT_DECL);
                if !in_import {
                    used.insert(token.text().to_owned());
                }
            }
            kind if kind.is_trivia() && token.text().starts_with('/') => {
                for word in token
                    .text()
                    .split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '$'))
                    .filter(|w| !w.is_empty())
                {
                    used.insert(word.to_owned());
                }
            }
            _ => {}
        }
    }
    used
}

fn import_diagnostics(
    db: &dyn Db,
    file: SourceFile,
    config: &DiagnosticsConfig,
    out: &mut Vec<Diagnostic>,
) {
    let cu = base_db::parse(db, file).tree();
    let used = used_identifiers(&cu);
    let mut seen: FxHashSet<(bool, bool, String)> = FxHashSet::default();

    let graph = hir::module_graph(db);
    let access = module_access::ModuleAccess::for_file(db, file, &graph);
    for import in cu.imports() {
        let Some(name) = import.name() else { continue };
        // 模块导入：模块不存在时报错（类路径上一个模块也没有时说明没找到 JDK，不报）；不提示"未使用"
        if import.is_module() {
            if graph.get(&name.text()).is_none() && !graph.is_empty() {
                out.push(Diagnostic {
                    range: name.syntax().text_range(),
                    message: base_db::tr!("找不到模块 `{}`", "Module `{}` not found", name.text()),
                    severity: Severity::Error,
                    code: DiagnosticCode::UnresolvedImport,
                    unused: false,
                });
            }
            continue;
        }
        let segments = name.segments();
        let Some(last) = segments.last() else {
            continue;
        };
        let range = import.syntax().text_range();
        let is_static = import.is_static();
        let on_demand = import.is_on_demand();

        // 能否解析
        // 只认这个文件看得到的类和包（模块依赖之外的、主代码里的测试类都不算）
        let resolved = if on_demand {
            hir::resolve_qualified_class_visible(db, file, &segments).is_some()
                || (!is_static && hir::package_visible_from(db, file, &segments.join("/")))
        } else if is_static {
            // 只确认类存在；成员可能是继承来的或由注解处理器生成
            segments.len() >= 2
                && hir::resolve_qualified_class_visible(db, file, &segments[..segments.len() - 1])
                    .is_some()
        } else {
            hir::resolve_qualified_class_visible(db, file, &segments).is_some()
        };
        if !resolved {
            out.push(Diagnostic {
                range: name.syntax().text_range(),
                message: base_db::tr!(
                    "无法解析 import `{}`",
                    "Cannot resolve import `{}`",
                    name.text()
                ),
                severity: Severity::Error,
                code: DiagnosticCode::UnresolvedImport,
                unused: false,
            });
            continue;
        }

        // 命名模块里只能导入读得到、并且导出了的包里的类
        if let Some(access) = &access {
            let class_segments = if is_static && !on_demand {
                &segments[..segments.len() - 1]
            } else {
                &segments[..]
            };
            let message = match hir::resolve_qualified_class_visible(db, file, class_segments) {
                Some(class) => access.check_class(db, &graph, class),
                None if on_demand && !is_static => {
                    access.check_package(&graph, &segments.join("/"))
                }
                None => None,
            };
            if let Some(message) = message {
                out.push(Diagnostic {
                    range: name.syntax().text_range(),
                    message,
                    severity: Severity::Error,
                    code: DiagnosticCode::InaccessibleMember,
                    unused: false,
                });
                continue;
            }
        }

        if !config.unused_imports {
            continue;
        }
        let duplicate = !seen.insert((is_static, on_demand, name.text()));
        let unused = duplicate || (!on_demand && !used.contains(last.as_str()));
        if unused {
            out.push(Diagnostic {
                range,
                message: if duplicate {
                    base_db::tr!("重复的 import `{}`", "Duplicate import `{}`", name.text())
                } else {
                    base_db::tr!("未使用的 import `{}`", "Unused import `{}`", name.text())
                },
                severity: Severity::Hint,
                code: DiagnosticCode::UnusedImport,
                unused: true,
            });
        }
    }
}

/// 可以简化的写法（快速修复用）。
pub fn simplification_diagnostics(db: &dyn Db, file: SourceFile) -> Vec<Diagnostic> {
    let view = View::file(db, file);
    let mut res = Vec::new();
    inspections::simplifications(&view, &mut res);
    field_final::field_may_be_final(&view, &mut res);
    redundant_modifiers::redundant_modifiers(view.nodes(), &mut res);
    jumps::redundant_jumps(view.nodes(), &mut res);
    res
}

/// 未使用的局部变量和私有成员，以及从未被读到的赋值（快速修复用）。
pub fn unused_symbols(db: &dyn Db, file: SourceFile) -> Vec<Diagnostic> {
    let view = View::file(db, file);
    let mut res = Vec::new();
    dead_stores::dead_stores(&view, &mut res);
    unused_locals(&view, &mut res);
    unused_private_members(db, file, &mut res);
    res
}

/// 缺少 `return` 的方法（诊断的范围）。语法有错时不判断。
pub fn missing_returns(db: &dyn Db, file: SourceFile) -> Vec<TextRange> {
    if !syntax_diagnostics(db, file).is_empty() {
        return Vec::new();
    }
    let mut res = Vec::new();
    flow::flow_diagnostics(
        base_db::parse(db, file).syntax_node().descendants(),
        &mut res,
    );
    res.into_iter()
        .filter(|d| d.code == DiagnosticCode::MissingReturn)
        .map(|d| d.range)
        .collect()
}

/// 声明了但从未读写的局部变量。
fn unused_locals(view: &View<'_>, out: &mut Vec<Diagnostic>) {
    for body in &view.bodies {
        let result = body.result(view);
        let mut used = vec![false; result.locals().len()];
        for (_, resolution) in result.resolutions() {
            if let hir::Resolution::Local(id) = resolution {
                if let Some(slot) = used.get_mut(*id as usize) {
                    *slot = true;
                }
            }
        }
        for (local, used) in result.locals().iter().zip(used) {
            // 形参、catch 参数、lambda 参数、模式变量没用到很常见，不提示；
            // `for (E e : xs) n++;` 这种只为计数的遍历也一样
            let reportable = local.kind == hir::LocalKind::Local;
            // `ignored` / `unused` 是"有意不用"的约定名字
            let intentionally_unused = local.name.starts_with('_')
                || matches!(&*local.name, "ignored" | "ignore" | "unused");
            if used || !reportable || intentionally_unused {
                continue;
            }
            out.push(Diagnostic {
                range: local.decl_range,
                message: base_db::tr!(
                    "局部变量 `{}` 从未被使用",
                    "Local variable `{}` is never used",
                    local.name
                ),
                severity: Severity::Hint,
                code: DiagnosticCode::UnusedLocal,
                unused: true,
            });
        }
    }
}

/// 私有方法里从没用到的形参。私有方法不参与覆写，形参可以放心删掉；带注解的方法可能是
/// 框架的入口、被方法引用的方法签名受函数式接口约束、序列化方法的签名是固定的，都不提示。
fn unused_parameters(view: &View<'_>, out: &mut Vec<Diagnostic>) {
    const SERIALIZATION: &[&str] = &[
        "readObject",
        "writeObject",
        "readObjectNoData",
        "readResolve",
        "writeReplace",
    ];
    let db = view.db;
    for file_body in &view.bodies {
        let body = file_body.id;
        let hir::BodyId::Method(method) = body else {
            continue;
        };
        let Some(method_data) = hir::method_data(db, method) else {
            continue;
        };
        if method_data.is_constructor
            || method_data.flags.visibility() != hir::Visibility::Private
            || !method_data.has_body
            || method_data.params.is_empty()
            || SERIALIZATION.contains(&&*method_data.name)
            || view.file_contains(&format!("::{}", method_data.name))
        {
            continue;
        }
        let Some(decl) = ast::MethodDecl::cast(file_body.node.clone()) else {
            continue;
        };
        if decl
            .modifier_list()
            .is_some_and(|m| m.annotations().next().is_some())
        {
            continue;
        }
        let Some(params) = decl.param_list() else {
            continue;
        };
        let params_range = params.syntax().text_range();
        let result = file_body.result(view);
        let mut used = vec![false; result.locals().len()];
        for (_, resolution) in result.resolutions() {
            if let hir::Resolution::Local(id) = resolution {
                if let Some(slot) = used.get_mut(*id as usize) {
                    *slot = true;
                }
            }
        }
        for (local, used) in result.locals().iter().zip(used) {
            let intentionally_unused = local.name.starts_with('_')
                || matches!(&*local.name, "ignored" | "ignore" | "unused");
            if used
                || local.kind != hir::LocalKind::Param
                || !params_range.contains_range(local.decl_range)
                || intentionally_unused
            {
                continue;
            }
            out.push(Diagnostic {
                range: local.decl_range,
                message: base_db::tr!(
                    "形参 `{}` 从未被使用",
                    "Parameter `{}` is never used",
                    local.name
                ),
                severity: Severity::Hint,
                code: DiagnosticCode::UnusedParameter,
                unused: true,
            });
        }
    }
}

/// 没有任何引用的私有字段和私有方法。带注解的成员可能被框架反射使用，不提示。
fn unused_private_members(db: &dyn Db, file: SourceFile, out: &mut Vec<Diagnostic>) {
    use hir::{Definition, FieldId, MethodId, Visibility};

    let tree = hir::item_tree(db, file);
    let root = base_db::parse(db, file).syntax_node();
    let has_annotation = |range: TextRange| {
        let node = match root.covering_element(range) {
            syntax::NodeOrToken::Node(node) => node,
            syntax::NodeOrToken::Token(token) => match token.parent() {
                Some(node) => node,
                None => return true,
            },
        };
        // 字段的声明节点是 VARIABLE_DECLARATOR，注解挂在外层的 FIELD_DECL 上
        // 范围可能正好落在名字 token 上：NAME → VARIABLE_DECLARATOR → FIELD_DECL
        node.ancestors()
            .take(3)
            .filter_map(|n| n.children().find_map(ast::ModifierList::cast))
            .any(|mods| mods.annotations().next().is_some())
    };

    for class_data in tree.classes.iter() {
        // 类上有注解（Lombok、JPA、序列化框架 …）时成员可能被间接使用
        if !class_data.annotations.is_empty() {
            continue;
        }
        // 局部类（及其成员类）的成员在外层的体里就地推断，类体里的引用解析成局部符号，
        // 按成员查引用会漏掉
        let in_local_class = class_data.flags.contains(hir::Modifiers::LOCAL_CLASS)
            || class_data
                .binary_name
                .split('$')
                .skip(1)
                .any(|part| part.starts_with(|c: char| c.is_ascii_digit()));
        if in_local_class {
            continue;
        }
        let class = hir::class_in_file(db, file, &class_data.binary_name);
        let mut candidates: Vec<(Definition, &str, &str)> = Vec::new();
        for (idx, field) in class_data.fields.iter().enumerate() {
            // 记录的组件通过同名的访问器使用，字段本身看不到引用
            let record_component =
                class_data.kind == hir::ClassKind::Record && !field.flags.is_static();
            if field.flags.visibility() == Visibility::Private
                && !field.flags.contains(hir::Modifiers::SYNTHETIC)
                && field.name != "serialVersionUID"
                && !record_component
            {
                let def = Definition::Field(FieldId {
                    class,
                    idx: idx as u32,
                });
                candidates.push((def, field.name.as_str(), base_db::trs!("字段", "field")));
            }
        }
        for (idx, method) in class_data.methods.iter().enumerate() {
            let serialization_hook = matches!(
                method.name.as_str(),
                "readObject" | "writeObject" | "readResolve" | "writeReplace" | "readObjectNoData"
            );
            if method.flags.visibility() == Visibility::Private
                && !method.is_constructor
                && !method.flags.contains(hir::Modifiers::SYNTHETIC)
                && !serialization_hook
            {
                let def = Definition::Method(MethodId {
                    class,
                    idx: idx as u32,
                });
                candidates.push((def, method.name.as_str(), base_db::trs!("方法", "method")));
            }
        }
        for (def, name, what) in candidates {
            let Some(source) = def.source(db) else {
                continue;
            };
            if has_annotation(source.full_range) {
                continue;
            }
            // 私有成员只可能在本文件里被引用
            if ide_db::search::references_in_file(db, file, &def, name).is_empty() {
                out.push(Diagnostic {
                    range: source.focus_range,
                    message: base_db::tr!(
                        "私有{what} `{name}` 从未被使用",
                        "Private {what} `{name}` is never used"
                    ),
                    severity: Severity::Hint,
                    code: DiagnosticCode::UnusedPrivateMember,
                    unused: true,
                });
            }
        }
    }
}

/// `module-info.java`：`requires` 的模块必须存在，`exports` / `opens` 的包必须在工作区里有类。
fn module_info_diagnostics(db: &dyn Db, file: SourceFile, out: &mut Vec<Diagnostic>) {
    if hir::item_tree(db, file).module.is_none() {
        return;
    }
    let cu = base_db::parse(db, file).tree();
    let Some(body) = cu.module().and_then(|m| m.body()) else {
        return;
    };
    let graph = hir::module_graph(db);
    if !graph.is_empty() {
        for requires in body.requires() {
            let Some(name) = requires.name() else {
                continue;
            };
            if graph.get(&name.text()).is_none() {
                out.push(Diagnostic {
                    range: name.syntax().text_range(),
                    message: base_db::tr!("找不到模块 `{}`", "Module `{}` not found", name.text()),
                    severity: Severity::Error,
                    code: DiagnosticCode::UnresolvedModule,
                    unused: false,
                });
            }
        }
    }
    let index = hir::source_class_index(db);
    let packages = body
        .exports()
        .filter_map(|e| e.name())
        .chain(body.opens().filter_map(|o| o.name()));
    for name in packages {
        let package = name.segments().join("/");
        if hir::package_classes(db, &package)
            .iter()
            .any(|class| index.get(&format!("{package}/{class}")).is_some())
        {
            continue;
        }
        out.push(Diagnostic {
            range: name.syntax().text_range(),
            message: base_db::tr!(
                "包 `{}` 是空的或者不存在",
                "Package `{}` is empty or does not exist",
                name.text()
            ),
            severity: Severity::Error,
            code: DiagnosticCode::UnresolvedModule,
            unused: false,
        });
    }
}

/// 紧凑源文件：不能声明包，必须有可以启动的 `main`（`void main()` 或 `void main(String[])`）。
fn compact_source_diagnostics(db: &dyn Db, file: SourceFile, out: &mut Vec<Diagnostic>) {
    let sema = Semantics::new(db);
    let Some(class) = sema.implicit_class(file) else {
        return;
    };
    let cu = base_db::parse(db, file).tree();
    if let Some(package) = cu.package() {
        out.push(Diagnostic {
            range: package.syntax().text_range(),
            message: base_db::trs!(
                "紧凑源文件不能声明包",
                "A compact source file cannot have a package declaration"
            )
            .to_owned(),
            severity: Severity::Error,
            code: DiagnosticCode::CompactSourceFile,
            unused: false,
        });
    }
    let Some(data) = hir::class_data(db, class) else {
        return;
    };
    let launchable = data.methods.iter().enumerate().any(|(idx, method)| {
        if method.is_constructor
            || method.name != "main"
            || method.flags.visibility() == hir::Visibility::Private
        {
            return false;
        }
        let sig = hir::method_sig(
            db,
            hir::MethodId {
                class,
                idx: idx as u32,
            },
        );
        sig.ret == hir::Ty::Void
            && match sig.params.as_slice() {
                [] => true,
                [hir::Ty::Array(element)] => element
                    .as_class()
                    .is_some_and(|c| c.binary_name(db) == "java/lang/String"),
                _ => false,
            }
    });
    if launchable {
        return;
    }
    // 报在第一个顶层方法 / 字段的名字上
    let anchor = cu
        .syntax()
        .children()
        .filter(|n| matches!(n.kind(), SyntaxKind::METHOD_DECL | SyntaxKind::FIELD_DECL))
        .find_map(|n| {
            n.descendants()
                .find(|d| d.kind() == SyntaxKind::NAME)
                .map(|name| name.text_range())
        });
    if let Some(range) = anchor {
        out.push(Diagnostic {
            range,
            message: base_db::trs!(
                "紧凑源文件没有可以启动的 `main` 方法（`void main()` 或 `void main(String[] args)`）",
                "The compact source file has no launchable `main` method (`void main()` or `void main(String[] args)`)"
            )
            .to_owned(),
            severity: Severity::Error,
            code: DiagnosticCode::CompactSourceFile,
            unused: false,
        });
    }
}

/// 一个文件的全部诊断，按位置排序。
/// 文件的诊断。默认配置下的结果按文件缓存在 salsa 里：同一版本的文件上的多次请求
/// （推送、拉取、整个工程的诊断、代码操作里的压制和修复）只算一次。
pub fn diagnostics(db: &dyn Db, file: SourceFile, config: &DiagnosticsConfig) -> Vec<Diagnostic> {
    if *config == DiagnosticsConfig::default() {
        return default_diagnostics(db, file).as_ref().clone();
    }
    compute_diagnostics(db, file, config, Split::Bodies)
}

/// 默认配置下的诊断（缓存）。
pub fn cached_diagnostics(db: &dyn Db, file: SourceFile) -> std::sync::Arc<Vec<Diagnostic>> {
    default_diagnostics(db, file)
}

/// 整个文件一起检查（不按体缓存）得到的诊断。和 [`diagnostics`] 的结果应当完全相同，
/// 用来核对按体划分的检查。
#[doc(hidden)]
pub fn whole_file_diagnostics(
    db: &dyn Db,
    file: SourceFile,
    config: &DiagnosticsConfig,
) -> Vec<Diagnostic> {
    compute_diagnostics(db, file, config, Split::WholeFile)
}

#[salsa::tracked]
fn default_diagnostics(db: &dyn Db, file: SourceFile) -> std::sync::Arc<Vec<Diagnostic>> {
    std::sync::Arc::new(compute_diagnostics(
        db,
        file,
        &DiagnosticsConfig::default(),
        Split::Bodies,
    ))
}

fn compute_diagnostics(
    db: &dyn Db,
    file: SourceFile,
    config: &DiagnosticsConfig,
    split: Split,
) -> Vec<Diagnostic> {
    let mut res = timing::timed("syntax_diagnostics", || syntax_diagnostics(db, file));
    let syntax_ok = res.is_empty();

    let ws = workspace(db);
    let is_workspace_file = ws
        .files(db)
        .get(file.file_id(db))
        .is_some_and(|entry| matches!(entry.kind, FileKind::Workspace { .. }));
    // 没有 JDK 时连 `String` 都解析不了，语义诊断没有意义
    let has_jdk = hir::lookup_class(db, "java/lang/Object").is_some();

    let mut groups = Groups::default();
    if config.semantic && is_workspace_file {
        if has_jdk {
            match split {
                Split::Bodies => body_groups(db, file, syntax_ok, &mut groups),
                Split::WholeFile => {
                    let view = View::file(db, file);
                    basic_groups(&view, &mut groups);
                    if syntax_ok {
                        checked_groups(&view, &mut groups);
                    }
                }
            }
        } else {
            timing::timed("language_level::feature_diagnostics", || {
                language_level::feature_diagnostics(&View::file(db, file), &mut groups.features)
            });
        }
        res.append(&mut groups.features);
    }
    if config.semantic && is_workspace_file && has_jdk {
        // 写了一半的语句里的推断错误没有意义
        let parse = base_db::parse(db, file);
        let errors: Vec<TextSize> = parse.errors().iter().map(|e| e.range.start()).collect();
        let root = parse.syntax_node();
        res.extend(
            groups
                .infer
                .drain(..)
                .filter(|d| !in_incomplete_statement(&root, &errors, d.range)),
        );
        res.append(&mut groups.unresolved);
        if syntax_ok {
            res.append(&mut groups.typeck);
            // 注解的 `@Target` 检查看的是声明，整文件做
            timing::timed("annotation_targets::annotation_target_diagnostics", || {
                annotation_targets::annotation_target_diagnostics(db, file, &mut res)
            });
        }
        timing::timed("import_diagnostics", || {
            import_diagnostics(db, file, config, &mut res)
        });
        module_info_diagnostics(db, file, &mut res);
        compact_source_diagnostics(db, file, &mut res);
        // 残缺的语法树上做流分析只会得到误报
        if config.inspections && syntax_ok {
            res.append(&mut groups.inspections);
            file_inspections(&View::file(db, file), &mut res);
        }
        if config.unused_symbols {
            res.append(&mut groups.unused);
            timing::timed("unused_private_members", || {
                unused_private_members(db, file, &mut res)
            });
        }
    }
    timing::timed("suppress::remove_suppressed", || {
        suppress::remove_suppressed(&base_db::parse(db, file).syntax_node(), &mut res)
    });
    // 各组的诊断拼在一起，顺序和检查的先后无关：同一个范围上的按内容排
    res.sort_by(|a, b| {
        (a.range.start(), a.range.end(), a.code.as_str(), &a.message)
            .cmp(&(b.range.start(), b.range.end(), b.code.as_str(), &b.message))
            .then_with(|| (a.severity as u8, a.unused).cmp(&(b.severity as u8, b.unused)))
    });
    res.dedup();
    res
}

/// 诊断怎么算：各个体分别检查、按体缓存（默认），还是整个文件一起检查（用来核对前者）。
#[derive(Clone, Copy, PartialEq, Eq)]
enum Split {
    Bodies,
    WholeFile,
}

/// 按种类分组的诊断：文件的诊断按配置和有没有语法错误挑出需要的组。
#[derive(Default, Clone, PartialEq, Eq, Debug)]
struct Groups {
    /// 语言级别不支持的写法
    features: Vec<Diagnostic>,
    /// 推断时发现的错误（写了一半的语句里的由调用方去掉）
    infer: Vec<Diagnostic>,
    /// 解析不了的类型名
    unresolved: Vec<Diagnostic>,
    /// 类型检查（只在没有语法错误时）
    typeck: Vec<Diagnostic>,
    /// 流分析和表达式检查（只在没有语法错误时）
    inspections: Vec<Diagnostic>,
    /// 未使用的局部变量和形参
    unused: Vec<Diagnostic>,
}

impl Groups {
    fn all(&self) -> impl Iterator<Item = &Diagnostic> {
        self.features
            .iter()
            .chain(&self.infer)
            .chain(&self.unresolved)
            .chain(&self.typeck)
            .chain(&self.inspections)
            .chain(&self.unused)
    }

    /// 把 `other` 的诊断挪到 `offset` 处加进来。
    fn extend_shifted(&mut self, other: &Groups, offset: TextSize) {
        fn shift(to: &mut Vec<Diagnostic>, from: &[Diagnostic], offset: TextSize) {
            to.extend(from.iter().map(|d| Diagnostic {
                range: d.range + offset,
                ..d.clone()
            }));
        }
        shift(&mut self.features, &other.features, offset);
        shift(&mut self.infer, &other.infer, offset);
        shift(&mut self.unresolved, &other.unresolved, offset);
        shift(&mut self.typeck, &other.typeck, offset);
        shift(&mut self.inspections, &other.inspections, offset);
        shift(&mut self.unused, &other.unused, offset);
    }

    /// 范围都换算成相对于 `member` 的起点；有范围落在 `member` 之外时为 `None`。
    fn relative_to(mut self, member: TextRange) -> Option<Groups> {
        if !self.all().all(|d| member.contains_range(d.range)) {
            return None;
        }
        for diags in [
            &mut self.features,
            &mut self.infer,
            &mut self.unresolved,
            &mut self.typeck,
            &mut self.inspections,
            &mut self.unused,
        ] {
            for d in diags.iter_mut() {
                d.range -= member.start();
            }
        }
        Some(self)
    }
}

/// 语法有没有错误都要做的检查。
fn basic_groups(view: &View<'_>, groups: &mut Groups) {
    timing::timed("language_level::feature_diagnostics", || {
        language_level::feature_diagnostics(view, &mut groups.features)
    });
    timing::timed("infer_diagnostics", || {
        infer_diagnostics(view, &mut groups.infer)
    });
    timing::timed("unresolved_types", || {
        unresolved_types(view, &mut groups.unresolved)
    });
    timing::timed("unused_locals", || unused_locals(view, &mut groups.unused));
    timing::timed("unused_parameters", || {
        unused_parameters(view, &mut groups.unused)
    });
}

/// 只在没有语法错误时做的检查：类型检查，以及能按体划分的流分析和表达式检查。
fn checked_groups(view: &View<'_>, groups: &mut Groups) {
    timing::timed("typeck::typeck_diagnostics", || {
        typeck::typeck_diagnostics(view, &mut groups.typeck)
    });
    let out = &mut groups.inspections;
    timing::timed("flow::flow_diagnostics", || {
        flow::flow_diagnostics(view.nodes(), out)
    });
    timing::timed("flow::expression_inspections", || {
        flow::expression_inspections(view, out)
    });
    timing::timed("exceptions::exception_diagnostics", || {
        exceptions::exception_diagnostics(view, out)
    });
    timing::timed("unchecked::unchecked_diagnostics", || {
        unchecked::unchecked_diagnostics(view, out)
    });
    timing::timed("nullness::nullness_diagnostics", || {
        nullness::nullness_diagnostics(view, out)
    });
    timing::timed("inspections::deprecated_usages", || {
        inspections::deprecated_usages(view, out)
    });
    timing::timed("inspections::simplifications", || {
        inspections::simplifications(view, out)
    });
    timing::timed("dead_stores::dead_stores", || {
        dead_stores::dead_stores(view, out)
    });
    timing::timed("format_strings::format_string_diagnostics", || {
        format_strings::format_string_diagnostics(view, out)
    });
    timing::timed("suspicious_calls::suspicious_calls", || {
        suspicious_calls::suspicious_calls(view, out)
    });
    timing::timed("ignored_results::ignored_results", || {
        ignored_results::ignored_results(view, out)
    });
    timing::timed("arrays::array_diagnostics", || {
        arrays::array_diagnostics(view, out)
    });
    timing::timed("loops::loop_diagnostics", || {
        loops::loop_diagnostics(view, out)
    });
    timing::timed("recursion::infinite_recursion", || {
        recursion::infinite_recursion(view, out)
    });
    timing::timed("collections::mismatched_collections", || {
        collections::mismatched_collections(view, out)
    });
    timing::timed("probable_bugs::probable_bugs", || {
        probable_bugs::probable_bugs(view, out)
    });
    timing::timed("may_be_static::methods_may_be_static", || {
        may_be_static::methods_may_be_static(view, out)
    });
    timing::timed("lambdas::lambdas_to_method_refs", || {
        lambdas::lambdas_to_method_refs(view, out)
    });
    timing::timed("optionals::unchecked_optional_gets", || {
        optionals::unchecked_optional_gets(view, out)
    });
    timing::timed("exceptions::redundant_throws_diagnostics", || {
        exceptions::redundant_throws_diagnostics(view, out)
    });
    timing::timed("boxing::unnecessary_boxing", || {
        boxing::unnecessary_boxing(view, out)
    });
    timing::timed("diamond::redundant_diamond_args", || {
        diamond::redundant_diamond_args(view, out)
    });
    timing::timed("redundancy::redundancies", || {
        redundancy::redundancies(view, out)
    });
    timing::timed("redundant_modifiers::redundant_modifiers", || {
        redundant_modifiers::redundant_modifiers(view.nodes(), out)
    });
    timing::timed("empty_blocks::empty_blocks", || {
        empty_blocks::empty_blocks(view.nodes(), out)
    });
    timing::timed("jumps::redundant_jumps", || {
        jumps::redundant_jumps(view.nodes(), out)
    });
}

/// 要看整个文件的检查项：字段在各个体里的用法、配置文件里的属性。`view` 是整个文件。
fn file_inspections(view: &View<'_>, out: &mut Vec<Diagnostic>) {
    timing::timed("final_fields::uninitialized_final_fields", || {
        final_fields::uninitialized_final_fields(view, out)
    });
    timing::timed("field_final::field_may_be_final", || {
        field_final::field_may_be_final(view, out)
    });
    timing::timed("collections::mismatched_collection_fields", || {
        collections::mismatched_collection_fields(view, out)
    });
    timing::timed("field_local::field_can_be_local", || {
        field_local::field_can_be_local(view, out)
    });
    timing::timed("spring::unresolved_properties", || {
        spring::unresolved_properties(view.db, view.file, out)
    });
}

/// 源码不到这么多字节的体不单独缓存，和体之外的部分一起检查：这样的体（常量的初值、
/// 简单的 getter 等）很多，每个都单独缓存时记下的依赖占的内存比重新检查它们的开销划不来。
/// 本 crate 的测试里每个体都单独检查，覆盖体的语法树上的检查。
const MIN_CACHED_BODY_LEN: u32 = if cfg!(test) { 1 } else { 512 };

/// 各个体的检查结果（较大的体按体缓存）加上其余部分的检查结果。
fn body_groups(db: &dyn Db, file: SourceFile, syntax_ok: bool, groups: &mut Groups) {
    let ws = workspace(db);
    // 没有语法错误时一个体的全部检查放在一个查询里：两部分用到的签名级查询大都相同，
    // 合在一起记的依赖少得多
    let query: BodyQuery = if syntax_ok { body_full } else { body_basic };
    let (mut kept, mut cached) = (Vec::new(), Vec::new());
    timing::timed("bodies", || {
        for (body, node) in file_bodies_syntax(db, file) {
            if u32::from(node.text_range().len()) < MIN_CACHED_BODY_LEN {
                kept.push((body, node));
                continue;
            }
            db.unwind_if_revision_cancelled();
            match query(db, ws, body) {
                BodyChecks::Empty => cached.push((body, node)),
                BodyChecks::Found(found) => {
                    groups.extend_shifted(&found, hir::body_member(&node).text_range().start());
                    cached.push((body, node));
                }
                // 体的语法树表示不了检查结果：和其余部分一起在文件的语法树上检查
                BodyChecks::Escaped => kept.push((body, node)),
            }
        }
    });
    let rest = View::rest(db, file, kept, &cached);
    timing::timed("rest::basic", || basic_groups(&rest, groups));
    if syntax_ok {
        timing::timed("rest::checked", || checked_groups(&rest, groups));
    }
}

type BodyQuery = fn(&dyn Db, base_db::Workspace, BodyId) -> BodyChecks;

/// 一个体单独检查的结果。大多数体没有诊断，不占额外的内存。
#[derive(Clone, PartialEq, Eq, Debug)]
enum BodyChecks {
    Empty,
    /// 范围相对于体所在成员的起点
    Found(Arc<Groups>),
    /// 检查结果落在成员之外，体的语法树表示不了
    Escaped,
}

fn full_groups(view: &View<'_>, groups: &mut Groups) {
    basic_groups(view, groups);
    checked_groups(view, groups);
}

/// 文件有语法错误时一个体上的检查（只有语法有没有错误都要做的那些），范围相对于体所在成员
/// 的起点（见 [`hir::BodyTree`]）。
///
/// 只依赖体所在的成员、外层的声明头和签名级的查询：别的体里的编辑、让这个体挪动位置的编辑
/// 都不会让它重新执行。
#[salsa::tracked]
fn body_basic(db: &dyn Db, _ws: base_db::Workspace, body: BodyId) -> BodyChecks {
    in_body_tree(db, body, basic_groups)
}

/// 同 [`body_basic`]，文件没有语法错误时一个体上的全部检查。
#[salsa::tracked]
fn body_full(db: &dyn Db, _ws: base_db::Workspace, body: BodyId) -> BodyChecks {
    in_body_tree(db, body, full_groups)
}

fn in_body_tree(db: &dyn Db, body: BodyId, check: fn(&View<'_>, &mut Groups)) -> BodyChecks {
    let Some(tree) = hir::body_tree(db, body) else {
        return BodyChecks::Escaped;
    };
    let member = tree.member_range();
    let Some(view) = View::body(db, tree) else {
        return BodyChecks::Escaped;
    };
    let mut groups = Groups::default();
    check(&view, &mut groups);
    match groups.relative_to(member) {
        Some(groups) if groups.all().next().is_none() => BodyChecks::Empty,
        Some(groups) => BodyChecks::Found(Arc::new(groups)),
        None => BodyChecks::Escaped,
    }
}

#[cfg(test)]
mod tests {
    use test_fixture::fixture;

    use super::*;

    fn check(text: &str) -> Vec<(DiagnosticCode, String)> {
        let fx = fixture(text);
        let file = fx.file().source;
        let source: &str = file.text(&fx.db);
        let diags = diagnostics(&fx.db, file, &DiagnosticsConfig::default());
        // 测试里每个体都单独检查（见 MIN_CACHED_BODY_LEN）：结果要和整个文件一起检查的相同
        assert_eq!(
            diags,
            whole_file_diagnostics(&fx.db, file, &DiagnosticsConfig::default())
        );
        diags
            .into_iter()
            .map(|d| {
                let range = usize::from(d.range.start())..usize::from(d.range.end());
                (d.code, source[range].to_owned())
            })
            .collect()
    }

    /// 注释里的 `\u000A`（JLS 3.3 在分词前翻译）结束注释：后面的
    /// `int x = 1;` 是真代码，javac 能编译，不该报 Cannot resolve symbol。
    #[test]
    fn unicode_newline_in_comment_reveals_the_declaration() {
        let diags = check(
            r#"
class Main {
    int use() {
        // \u000A int x = 1;
        return x;
    }
}
"#,
        );
        let unresolved: Vec<_> = diags
            .iter()
            .filter(|(code, _)| {
                matches!(
                    code,
                    DiagnosticCode::UnresolvedName
                        | DiagnosticCode::UnresolvedField
                        | DiagnosticCode::UnresolvedMethod
                )
            })
            .collect();
        assert!(unresolved.is_empty(), "{diags:?}");
    }

    /// 两个同参数个数的泛型构造器竞争、实参里夹着多态表达式（菱形构造）时，
    /// lambda 形参的类型要来自幸存候选解出来的签名，而不是第一个实参的类型。
    /// javac 编译无警告（JLS 18.5.2 / 18.5.4）。
    #[test]
    fn lambda_params_follow_the_surviving_overload_not_the_first_arg() {
        let diags = check(
            r#"
public class Main {
    interface Callable<T> {
        T call() throws Exception;
    }

    interface Textish {
        String asString();
    }

    static final class Wrap implements Textish {
        @Override
        public String asString() {
            return "wrap";
        }
    }

    interface Scalar<S> {
        S value() throws Exception;
    }

    interface Func<A, B> {
        B apply(A a) throws Exception;
    }

    static final class IsBlank implements Scalar<Boolean> {
        final Textish origin;

        IsBlank(Textish text) {
            this.origin = text;
        }

        @Override
        public Boolean value() {
            return true;
        }
    }

    static final class Flattened<X, Y> implements Func<X, Y> {
        final Func<X, Scalar<Y>> origin;

        Flattened(Func<X, Scalar<Y>> origin) {
            this.origin = origin;
        }

        @Override
        public Y apply(X x) throws Exception {
            return this.origin.apply(x).value();
        }
    }

    static final class ScalarOf<T> implements Scalar<T> {
        final Callable<? extends T> origin;

        ScalarOf(Callable<? extends T> origin) {
            this.origin = origin;
        }

        @Override
        public T value() throws Exception {
            return this.origin.call();
        }
    }

    static final class Ternary<T> {
        final T value;

        <X> Ternary(
            X input,
            Func<? super X, Boolean> cond,
            Func<? super X, ? extends T> cons,
            Func<? super X, ? extends T> alter
        ) {
            throw new UnsupportedOperationException();
        }

        <X> Ternary(
            Scalar<? extends X> input,
            Func<? super X, Boolean> cond,
            Func<? super X, ? extends T> cons,
            Func<? super X, ? extends T> alter
        ) throws Exception {
            this.value = cond.apply(input.value()) ? cons.apply(input.value()) : alter.apply(input.value());
        }
    }

    public static void main(String[] args) throws Exception {
        CharSequence cs = new Ternary<>(
            new ScalarOf<>(() -> new Wrap()),
            new Flattened<>(IsBlank::new),
            t -> t,
            t -> t.asString() + "!"
        ).value.toString();
        System.out.println(cs);
    }
}
"#,
        );
        let bad: Vec<_> = diags
            .iter()
            .filter(|(code, _)| {
                matches!(
                    code,
                    DiagnosticCode::UnresolvedName
                        | DiagnosticCode::UnresolvedField
                        | DiagnosticCode::UnresolvedMethod
                        | DiagnosticCode::ArgumentMismatch
                        | DiagnosticCode::AmbiguousCall
                )
            })
            .collect();
        assert!(bad.is_empty(), "{diags:?}");
    }

    /// 泛型类的构造器引用作实参、调用结果又没有目标类型时，类的类型实参由函数类型的形参推出：
    /// `apply(Box::new, "x")` 是 `Box<String>`，不是原始的 `Box`。
    #[test]
    fn generic_constructor_refs_take_type_args_from_functional_inputs() {
        let diags = check(
            r#"
interface Function<A, B> { B apply(A a); }
interface BiFunction<A, B, C> { C apply(A a, B b); }
class Box<T> { T v; Box(T v) { this.v = v; } T get() { return v; } }
class Pair<K, V> {
    K k; V v;
    Pair(K k, V v) { this.k = k; this.v = v; }
    K key() { return k; }
    V value() { return v; }
}
public class Main {
    static <A, B> B apply(Function<A, B> f, A a) { return f.apply(a); }
    static <A, B, C> C apply2(BiFunction<A, B, C> f, A a, B b) { return f.apply(a, b); }
    void m() {
        String w = apply(Box::new, "x").get().trim();
        int q = apply2(Pair::new, "a", 1).value().intValue();
        String r = apply2(Pair::new, "a", 1).key().trim();
    }
}
"#,
        );
        assert!(
            !diags
                .iter()
                .any(|(code, _)| *code == DiagnosticCode::UnresolvedMethod),
            "{diags:?}"
        );
    }

    #[test]
    fn annotations_outside_their_target() {
        let diags = check(
            r#"
import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

@Target({ElementType.FIELD, ElementType.TYPE_USE})
@interface Col {}

@Target(ElementType.LOCAL_VARIABLE)
@interface Tmp {}

@Override
class Main {
    @Col int x;
    @Col String name() { return ""; }
    @Col void run() {}
    @Override public String toString() { return ""; }
    void f(@Col String s) {
        @Tmp int a = 0;
        try {} catch (@Tmp RuntimeException e) {}
    }
    @FunctionalInterface int y;
}
"#,
        );
        let found: Vec<&str> = diags
            .iter()
            .filter(|(code, _)| *code == DiagnosticCode::AnnotationNotApplicable)
            .map(|(_, text)| text.as_str())
            .collect();
        // 类上的 `@Override`、void 方法上的类型注解、字段上的 `@FunctionalInterface`
        assert_eq!(
            found,
            ["Override", "Col", "FunctionalInterface"],
            "{diags:?}"
        );
    }

    #[test]
    fn clean_file_has_no_diagnostics() {
        let diags = check(
            r#"
import java.util.List;
import java.util.ArrayList;

class Main {
    int total(List<Integer> xs) {
        int sum = 0;
        for (Integer x : xs) {
            sum += x;
        }
        List<String> names = new ArrayList<>();
        names.add("a");
        return sum + names.size();
    }
}
"#,
        );
        assert!(diags.is_empty(), "{diags:?}");
    }

    #[test]
    fn reports_syntax_errors() {
        let diags = check("class Main { void f() { int x = ; } }");
        assert!(
            diags
                .iter()
                .any(|(code, _)| *code == DiagnosticCode::SyntaxError),
            "{diags:?}"
        );
    }

    #[test]
    fn reports_unresolved_and_unused_imports() {
        let diags = check(
            r#"
import java.util.List;
import java.util.Missing;
import java.util.Map;

class Main { Map<String, String> m; }
"#,
        );
        assert!(diags.contains(&(
            DiagnosticCode::UnresolvedImport,
            "java.util.Missing".to_owned()
        )));
        assert!(diags.contains(&(
            DiagnosticCode::UnusedImport,
            "import java.util.List;".to_owned()
        )));
        assert!(
            !diags.iter().any(|(_, text)| text.contains("Map")),
            "{diags:?}"
        );
    }

    #[test]
    fn reports_unused_locals_and_private_members() {
        let diags = check(
            r#"
class Main {
    private int used;
    private int unused;
    private void helper() {}
    private void dead() {}
    @Deprecated private int annotated;

    int f(int param) {
        int a = 1;
        int b = 2;
        helper();
        return used + a;
    }
}
"#,
        );
        let unused: Vec<&str> = diags
            .iter()
            .filter(|(code, _)| {
                matches!(
                    code,
                    DiagnosticCode::UnusedLocal | DiagnosticCode::UnusedPrivateMember
                )
            })
            .map(|(_, text)| text.as_str())
            .collect();
        assert_eq!(unused, ["unused", "dead", "b"]);
    }

    #[test]
    fn reports_unresolved_name() {
        let diags = check("class Main { int f() { return missing; } }");
        assert!(
            diags.contains(&(DiagnosticCode::UnresolvedName, "missing".to_owned())),
            "{diags:?}"
        );
    }

    #[test]
    fn inspections_report_suspicious_expressions() {
        let diags = check(
            r#"
class Main {
    private int count;
    boolean f(String a, String b, int n) {
        this.count = this.count;
        n = n;
        if (n == n) { return false; }
        return a == b;
    }
    boolean g(String a) { return a == null; }
}
"#,
        );
        let codes: Vec<DiagnosticCode> = diags.iter().map(|(code, _)| *code).collect();
        assert_eq!(
            codes,
            [
                DiagnosticCode::SelfAssignment,
                DiagnosticCode::SelfAssignment,
                DiagnosticCode::SelfComparison,
                DiagnosticCode::StringEquality,
            ],
            "{diags:?}"
        );
    }

    #[test]
    fn flow_checks_are_skipped_on_broken_code() {
        let diags = check("class Main { int f() { return 1; int x = ; } }");
        let flow_codes = [
            DiagnosticCode::UnreachableCode,
            DiagnosticCode::MissingReturn,
        ];
        assert!(
            diags.iter().all(|(code, _)| !flow_codes.contains(code)),
            "{diags:?}"
        );
    }

    #[test]
    fn reports_reads_of_unassigned_locals() {
        let diags = check(
            r#"
class Main {
    int f(boolean b, int n) {
        int never;
        int later;
        int ok;
        int both;
        int oneBranch;
        int inLoop;
        int orReturn;
        int inTry;
        ok = 1;
        if (b) { both = 1; } else { both = 2; }
        if (b) { oneBranch = 1; }
        while (n > 0) { inLoop = n; n--; }
        if (b) { orReturn = 1; } else { return 0; }
        try { inTry = Integer.parseInt("1"); } catch (RuntimeException e) { e.toString(); }
        int sum = never + later + ok + both + oneBranch + inLoop + orReturn + inTry;
        later = later + 1;
        return sum + later;
    }
}
"#,
        );
        let uninit: Vec<&str> = diags
            .iter()
            .filter(|(code, _)| *code == DiagnosticCode::UninitializedVariable)
            .map(|(_, text)| text.as_str())
            .collect();
        assert_eq!(
            uninit,
            ["never", "later", "oneBranch", "inLoop", "inTry"],
            "{diags:?}"
        );
    }

    #[test]
    fn definite_assignment_has_no_false_positives() {
        let diags = check(
            r#"
class Main {
    int f(boolean b, int n) {
        int viaSwitch;
        switch (n) {
            case 1: viaSwitch = 1; break;
            default: viaSwitch = 2;
        }
        int viaFinally;
        try { n++; } finally { viaFinally = 3; }
        int viaLoop;
        while (true) { viaLoop = 4; break; }
        int viaDo;
        do { viaDo = 5; } while (b);
        int viaThrow;
        if (b) { viaThrow = 6; } else { throw new RuntimeException(); }
        int inLambda;
        inLambda = 7;
        Runnable r = () -> { int copy = inLambda; };
        r.run();
        return viaSwitch + viaFinally + viaLoop + viaDo + viaThrow;
    }
}
"#,
        );
        assert!(
            diags
                .iter()
                .all(|(code, _)| *code != DiagnosticCode::UninitializedVariable),
            "{diags:?}"
        );
    }

    #[test]
    fn reports_unhandled_checked_exceptions() {
        let diags = check(
            r#"
import java.io.IOException;

class Main {
    void read() throws IOException { throw new IOException(); }

    void declared() throws IOException { read(); }
    void wider() throws Exception { read(); }
    void caught() {
        try { read(); } catch (IOException e) { e.toString(); }
    }
    void unchecked() { throw new RuntimeException(); }
    void inLambda() { Runnable r = () -> { read(); }; r.run(); }

    void missing() { read(); }
    void wrongCatch() {
        try { read(); } catch (RuntimeException e) { e.toString(); }
    }
    void thrown() { throw new IOException("x"); }
    void inCatch() {
        try { unchecked(); } catch (RuntimeException e) { read(); }
    }
}
"#,
        );
        let unhandled: Vec<&str> = diags
            .iter()
            .filter(|(code, _)| *code == DiagnosticCode::UnhandledException)
            .map(|(_, text)| text.as_str())
            .collect();
        assert_eq!(
            unhandled,
            // 第一条在 lambda 里：`Runnable.run()` 不声明任何受检异常
            ["read", "read", "read", "IOException", "read"],
            "{diags:?}"
        );
    }

    #[test]
    fn throw_of_call_and_cast_uses_the_static_type() {
        let diags = check(
            r#"
import java.io.IOException;

class Main {
    static IOException io() { return new IOException(); }
    static RuntimeException rt() { return new IllegalStateException(); }
    static <X extends Throwable> X generic() { return null; }

    void call() { throw io(); }
    void cast(Throwable t) { throw (IOException) t; }
    void declared() throws IOException { throw io(); }
    void unchecked(Throwable t) { throw rt(); }
    void inferred() { throw generic(); }
    void never() {
        try { throw rt(); } catch (IOException e) { e.toString(); }
    }
}
"#,
        );
        let flagged: Vec<(DiagnosticCode, &str)> = diags
            .iter()
            .filter(|(code, _)| {
                matches!(
                    code,
                    DiagnosticCode::UnhandledException | DiagnosticCode::ExceptionNeverThrown
                )
            })
            .map(|(code, text)| (*code, text.as_str()))
            .collect();
        assert_eq!(
            flagged,
            [
                (DiagnosticCode::UnhandledException, "io()"),
                (DiagnosticCode::UnhandledException, "(IOException) t"),
                (DiagnosticCode::ExceptionNeverThrown, "IOException"),
            ],
            "{diags:?}"
        );
    }

    #[test]
    fn reads_of_blank_finals_before_assignment() {
        let diags = check(
            r#"
class Main {
    static class Init {
        private final int a;
        private final int c = a + 1;
        Init() { a = 1; }
    }

    static class Block {
        private final int a;
        { System.out.println(this.a); }
        Block() { a = 1; }
    }

    static class Ctor {
        private final int a;
        private final int b;

        Ctor(Ctor other) {
            b = a + other.b;
            a = 2;
            System.out.println(a + b);
        }

        Ctor() {
            this(null);
            System.out.println(a);
        }
    }

    static class Static {
        static final int S;
        static {
            System.out.println(S);
            S = 1;
        }
    }
}
"#,
        );
        let reads: Vec<&str> = diags
            .iter()
            .filter(|(code, _)| *code == DiagnosticCode::UninitializedVariable)
            .map(|(_, text)| text.as_str())
            .collect();
        // 字段初值、实例初始化块（`this.a`）、构造器、静态初始化块；`other.b` 和 `this(...)` 之后的不算
        assert_eq!(reads, ["a", "a", "a", "S"], "{diags:?}");
    }

    #[test]
    fn unchecked_conversions_calls_and_casts() {
        let diags = check(
            r#"
import java.util.ArrayList;
import java.util.List;

class Main<E> {
    List<String> conversions(List raw) {
        List<String> a = raw;
        List<?> ok = raw;
        raw.add("x");
        raw.size();
        a.add("y");
        return ok.isEmpty() ? new ArrayList() : a;
    }

    <T> T casts(Object o, List<String> strings, E e) {
        List<String> a = (List<String>) o;
        List<?> b = (List<?>) o;
        ArrayList<String> c = (ArrayList<String>) strings;
        E d = (E) e;
        System.out.println(a + "" + b + c + d);
        return (T) o;
    }

    @SuppressWarnings("unchecked")
    void quiet(List raw) {
        raw.add("x");
    }
}
"#,
        );
        let unchecked: Vec<&str> = diags
            .iter()
            .filter(|(code, _)| *code == DiagnosticCode::Unchecked)
            .map(|(_, text)| text.as_str())
            .collect();
        assert_eq!(unchecked, ["raw", "add", "List<String>", "T"], "{diags:?}");
    }

    #[test]
    fn unresolved_qualified_type_names() {
        let diags = check(
            r#"
import java.util.Map;

class Main {
    static class Inner {}

    java.util.Missing a;
    Main.Nope b;
    Map.Entry<String, String> ok1;
    Main.Inner ok2;
    java.util.List<String> ok3;
    no.such.Thing ok4;
}
"#,
        );
        let unresolved: Vec<&str> = diags
            .iter()
            .filter(|(code, _)| *code == DiagnosticCode::UnresolvedType)
            .map(|(_, text)| text.as_str())
            .collect();
        assert_eq!(unresolved, ["Missing", "Nope"], "{diags:?}");
    }

    #[test]
    fn unresolved_annotation_names() {
        let diags = check(
            r#"
@EnableFeignClients
class Main {
    @interface Marker {}

    @Marker
    int marked;

    @Override
    public String toString() { return ""; }

    @Missing
    @Deprecated
    void run(@Nope int x) {}

    @no.such.Thing
    int ok;
}
"#,
        );
        let unresolved: Vec<&str> = diags
            .iter()
            .filter(|(code, _)| *code == DiagnosticCode::UnresolvedType)
            .map(|(_, text)| text.as_str())
            .collect();
        assert_eq!(
            unresolved,
            ["EnableFeignClients", "Missing", "Nope"],
            "{diags:?}"
        );
    }

    /// 每个文件里错误级的诊断（提示和警告不算）。
    fn errors_in_all_files(text: &str) -> Vec<(String, DiagnosticCode, String)> {
        let fx = fixture(text);
        let mut res = Vec::new();
        for file in &fx.files {
            let source: &str = file.source.text(&fx.db);
            let diags = diagnostics(&fx.db, file.source, &DiagnosticsConfig::default());
            assert_eq!(
                diags,
                whole_file_diagnostics(&fx.db, file.source, &DiagnosticsConfig::default())
            );
            for d in diags {
                if d.severity == Severity::Error {
                    let range = usize::from(d.range.start())..usize::from(d.range.end());
                    res.push((file.path.clone(), d.code, source[range].to_owned()));
                }
            }
        }
        res
    }

    // 下面几组都是在 JDK 源码上跑全量分析时遇到过的误报，写法取自真实代码。

    #[test]
    fn no_false_errors_in_anonymous_and_local_classes() {
        let errors = errors_in_all_files(
            r#"
//- /app/Parser.java
package app;

abstract class Parser {
    enum Kind { INLINE, BLOCK }
    abstract int parse(int pos, Kind kind);
    int base() { return 1; }
}
//- /app/Main.java
package app;

class Main {
    int anonymous(String name) {
        Parser p = new Parser() {
            boolean done = true;
            int count;

            boolean done() { return done; }
            String name() { return name.trim(); }

            @Override
            int parse(int pos, Kind kind) {
                this.count = pos;
                int extra = switch (kind) {
                    case INLINE -> 1;
                    case BLOCK -> Kind.BLOCK == kind ? 2 : 3;
                };
                return super.base() + this.count + extra + (done() ? 1 : 0);
            }
        };
        return p.parse(0, Parser.Kind.INLINE);
    }

    int varOfAnonymousType() {
        var counter = new Object() {
            int hits = 3;
        };
        return counter.hits;
    }

    Object localClass(boolean b) {
        class Dummy {
            static final int LIMIT = 4;
        }
        if (b) {
            return Dummy.class;
        }
        return Dummy.LIMIT;
    }
}
"#,
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn no_false_errors_from_type_name_lookup() {
        let errors = errors_in_all_files(
            r#"
//- /lib/Table.java
package lib;

public class Table {
    // 私有的成员类型不被继承，也挡住了更上层的同名类型
    private static class Entry { }
    Object first() { return new Entry(); }
}
//- /lib/Hidden.java
package lib;

// 包私有：`import lib.*` 带不进它
class Shape { }
//- /lib/Tree.java
package lib;

public interface Tree {
    enum Kind { LEAF }
}
//- /lib/Node.java
package lib;

public class Node implements Tree {
    public static class Leaf extends Node { }
}
//- /app/Kinds.java
package app;

public class Kinds {
    public enum Kind { VAL, ERR }
}
//- /app/Shape.java
package app;

public class Shape {
    public int sides() { return 3; }
}
//- /app/Main.java
package app;

import lib.*;
import lib.Node.*;
import static app.Kinds.*;

class Main {
    static final class Entry {
        int version() { return 1; }
    }

    static final class Cache extends Table {
        int read(Object item) {
            var entry = (Entry) item;
            return entry.version();
        }
    }

    class Inner {
        int size() { return 2; }
    }

    int imports(Shape shape, Leaf leaf) {
        // `Kind` 来自静态 import：`lib.Node.*` 不带进 Node 继承来的 `Tree.Kind`
        Kind kind = Kind.ERR;
        return shape.sides() + (kind == Kind.VAL ? 1 : 0) + leaf.hashCode();
    }

    int qualifiedNew(Main outer) {
        Main.Inner inner = outer.new Inner();
        return inner.size();
    }
}
"#,
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn no_false_errors_from_flow_analysis() {
        let errors = errors_in_all_files(
            r#"
import java.io.IOException;

class Main {
    static final boolean DEBUG = false;

    int labeled(int[] xs) {
        outer:
        for (;;) {
            for (int x : xs) {
                if (x > 0) {
                    break outer;
                }
                if (x < 0) {
                    return x;
                }
            }
        }
        return 0;
    }

    int endless(int[] xs) {
        scan:
        for (;;) {
            inner:
            for (int x : xs) {
                if (x == 0) continue scan;
                if (x == 1) break inner;
                return x;
            }
        }
    }

    int sharedSwitchScope(int tag) {
        switch (tag) {
            case 1:
                int width = 2;
                return width;
            case 2:
                width = 3;
                return width;
            default:
                return 0;
        }
    }

    int constantCondition(int n) {
        int pos;
        if (DEBUG) {
            pos = n;
        }
        try {
            n++;
        } finally {
            if (DEBUG) {
                n += pos;
            }
        }
        return n;
    }

    int assignedOrThrown(int code) throws IOException {
        int[] values;
        try {
            values = load(code);
        } catch (IOException e) {
            switch (code) {
                case 1:
                case 2:
                    throw new IllegalStateException();
                default:
                    throw e;
            }
        }
        return values.length;
    }

    int[] load(int code) throws IOException {
        if (code < 0) throw new IOException();
        return new int[code];
    }

    int arrays(byte[] key) {
        byte[] copy = key.clone();
        Object[] boxes = new Object[] { copy }.clone();
        return copy.length + boxes.length;
    }
}
"#,
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn no_false_errors_from_generic_inference() {
        let errors = errors_in_all_files(
            r#"
import java.util.List;
import java.util.Map;
import java.util.Optional;

class Box<T> {
    T value;
}

class Main {
    static <V> V pick(Box<?> hint, Box<? extends V> typed, V fallback) { return fallback; }

    int size() { return 1; }

    // 第一个实参是 `Box<?>`，不提供信息；V 要由后面的实参定出来
    int wildcardFirst(Box<?> any, Box<Main> typed) {
        return pick(any, typed, this).size();
    }

    // 接收者是不带实参的泛型类：返回类型靠目标类型推断，这里不能当成 Object
    String rawReceiverMethodRef(List<Map.Entry<String, Integer>> entries) {
        return entries.stream().map(Map.Entry::getKey).findFirst().orElse("none");
    }
}
"#,
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    /// 菱形构造选中 `Req(MV<String, String>, ...)` 而不是 `Req(T, ...)`：`T` 由目标类型定成
    /// `Void`，不能按 `T = H` 报类型不匹配。javac 编译无警告。
    #[test]
    fn diamond_overload_choice_does_not_fix_the_type_argument() {
        let diags = check(
            r#"
import java.util.HashMap;

public class Main {
    interface MV<K, V> extends java.util.Map<K, V> {}

    static class H extends HashMap<String, String> implements MV<String, String> {}

    static class Req<T> {
        Req(T body, String method, String url) {}
        Req(MV<String, String> headers, String method, String url) {}
    }

    void f() {
        H h = new H();
        Req<Void> r = new Req<>(h, "GET", "u");
    }
}
"#,
        );
        let mismatches: Vec<_> = diags
            .iter()
            .filter(|(code, _)| *code == DiagnosticCode::TypeMismatch)
            .collect();
        assert!(mismatches.is_empty(), "{diags:?}");
    }

    /// `Consumer<?>` 交给 `Consumer<? super K1>`（`K1` 是被调用方法还没推断的类型变量）：
    /// JLS 18.2.3 由 `CAP#1 <: ? super K1` 得到 `K1 <: CAP#1`，取 `K1 = CAP#1` 就适用。javac 编译通过。
    #[test]
    fn capture_satisfies_a_super_bound_on_an_inferred_type_variable() {
        let diags = check(
            r#"
interface Consumer<T> { void accept(T t); }

public class G<K> {
    <K1 extends K> G<K1> f(Consumer<? super K1> c) { return null; }
    static void t(Consumer<?> c, G<Object> g) { g.f(c); }
    static void u(Consumer<? extends Number> c, G<Object> g) { g.f(c); }
}

interface Box<T extends Number> { void put(T t); }
interface Listener<K, V> { void on(K k, V v); }

class H<K, V> {
    <K1 extends K, V1 extends V> H<K1, V1> listen(Listener<? super K1, ? super V1> l) { return null; }
    static void t(H<Object, Object> h, Listener<?, ?> l) { h.listen(l); }
    static <K1 extends Number> void box(Box<? super K1> b) {}
    static void u(Box<?> b) { box(b); }
    static <K1 extends Comparable<K1>> void cmp(Consumer<? super K1> c) {}
    static void v(Consumer<?> c) { cmp(c); }
    static <K1 extends String> void str(Consumer<? super K1> c) {}
    static void w(Consumer<? extends String> c) { str(c); }
}

class Constrained {
    static <K1> void second(Consumer<? super K1> c, K1 k) {}
    static void sc(Consumer<?> c) { second(c, null); }
    static <K1> void spread(Consumer<? super K1> c, K1... ks) {}
    static void sp(Consumer<?> c) { spread(c); }
    static <K1 extends V1, V1> void dep(Consumer<? super K1> c) {}
    static void dp(Consumer<?> c) { dep(c); }
    static <T> void copy(java.util.List<? super T> dest, java.util.List<? extends T> src) {}
    static <T> java.util.List<T> empty() { return null; }
    static void cp(java.util.List<?> d) { copy(d, empty()); }
}
"#,
        );
        assert!(diags.is_empty(), "{diags:?}");
    }

    /// 上一条的反面，javac 都拒绝：显式写出了类型实参；捕获变量确定不满足 `K1` 代换后的声明上界。
    /// `K1` 还出现在别处或上界提到别的类型变量时（`copy(d, s)`、`second(c, "s")`、`twice`、`sib`）
    /// javac 也拒绝，但同样的形状换个实参就通过（见上一条的 `Constrained`），不报。
    #[test]
    fn capture_does_not_satisfy_a_super_bound_on_a_constrained_type_variable() {
        let diags = check(
            r#"
import java.util.List;

interface Consumer<T> { void accept(T t); }
interface BiConsumer<T, U> { void accept(T t, U u); }
interface Box<T extends Number> { void put(T t); }

class G<K> {
    <K1 extends K> G<K1> f(Consumer<? super K1> c) { return null; }
    <K1> void any(Consumer<? super K1> c) {}
    static void explicit(Consumer<?> c, G<Object> g) { g.<Object>f(c); }
    <K2> void explicitParam(Consumer<?> c) { this.<K2>any(c); }
    static void number(Consumer<?> c, G<Number> g) { g.f(c); }
    static void integer(Consumer<? extends Number> c, G<Integer> g) { g.f(c); }
    static <K2> void param(Consumer<?> c, G<K2> g) { g.f(c); }
    static <K1 extends String> void str(Consumer<? super K1> c) {}
    static void s(Consumer<?> c) { str(c); }
    static <K1 extends Integer> void box(Box<? super K1> b) {}
    static void b(Box<?> b) { box(b); }
    static <T> void copy(List<? super T> dest, List<? extends T> src) {}
    static void cp(List<?> d, List<String> s) { copy(d, s); }
    static <K1> void second(Consumer<? super K1> c, K1 k) {}
    static void sc(Consumer<?> c) { second(c, "s"); }
    static <K1> void twice(BiConsumer<? super K1, ? super K1> c) {}
    static void tw(BiConsumer<?, ?> c) { twice(c); }
    static <K1 extends V1, V1 extends String> void sib(Consumer<? super K1> c) {}
    static void sb(Consumer<?> c) { sib(c); }
}
"#,
        );
        assert_eq!(
            diags,
            [
                (DiagnosticCode::ArgumentMismatch, "f".to_owned()),
                (DiagnosticCode::ArgumentMismatch, "any".to_owned()),
                (DiagnosticCode::ArgumentMismatch, "f".to_owned()),
                (DiagnosticCode::ArgumentMismatch, "f".to_owned()),
                (DiagnosticCode::ArgumentMismatch, "f".to_owned()),
                (DiagnosticCode::ArgumentMismatch, "str".to_owned()),
                (DiagnosticCode::ArgumentMismatch, "box".to_owned()),
            ],
        );
    }

    /// 界是作用域内的类型变量、具体类型或含类型变量的类型时，捕获变量仍确定不满足 `? super`。
    /// javac 都拒绝。
    #[test]
    fn capture_does_not_satisfy_other_super_bounds() {
        let diags = check(
            r#"
import java.util.List;

interface Consumer<T> { void accept(T t); }

class Main {
    <T> void m(Consumer<?> c) { Consumer<? super T> d = c; }
    static void s(Consumer<? super String> c) {}
    static void t(Consumer<?> c) { s(c); }
    static <K1> void h(Consumer<? super List<K1>> c) {}
    static void u(Consumer<?> c) { h(c); }
}
"#,
        );
        assert_eq!(
            diags,
            [
                (DiagnosticCode::UnusedLocal, "d".to_owned()),
                (DiagnosticCode::TypeMismatch, "c".to_owned()),
                (DiagnosticCode::ArgumentMismatch, "s".to_owned()),
                (DiagnosticCode::ArgumentMismatch, "h".to_owned()),
            ],
        );
    }
}
