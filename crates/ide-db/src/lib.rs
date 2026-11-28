//! IDE 功能共用的设施：数据库实体、符号索引、引用搜索、签名渲染、Javadoc、import 编辑。

pub mod annotations;
pub mod diamond;
pub mod doc_links;
pub mod editorconfig;
pub mod fuzzy;
pub mod imports;
pub mod javadoc;
pub mod overrides;
pub mod render;
pub mod search;
pub mod spring;
pub mod spring_metadata;
pub mod symbol_index;

use std::sync::Arc;

use base_db::{Interner, ParseCache};
use hir::{class_data, ClassKind, Definition, LocalKind, Modifiers};
use syntax::TextRange;

pub use base_db::{self, Db, FileId, LineCol, LineIndex, SourceFile};

/// 整个分析层唯一的具体数据库。
///
/// `clone()` 得到的是共享同一份存储的句柄，用作只读快照；对原句柄的写入会让
/// 所有快照上正在进行的查询取消。
///
#[salsa::db]
#[derive(Clone)]
pub struct RootDatabase {
    storage: salsa::Storage<Self>,
    interner: Arc<Interner>,
    parse_cache: Arc<ParseCache>,
}

impl Default for RootDatabase {
    fn default() -> Self {
        RootDatabase {
            storage: salsa::Storage::new(Some(Box::new(on_salsa_event))),
            interner: Arc::default(),
            parse_cache: Arc::default(),
        }
    }
}

#[salsa::db]
impl salsa::Database for RootDatabase {}

#[salsa::db]
impl Db for RootDatabase {
    fn interner(&self) -> &Interner {
        &self.interner
    }

    fn parse_cache(&self) -> &ParseCache {
        &self.parse_cache
    }

    fn fork_for_thread(&self) -> Option<Box<dyn Db + Send>> {
        Some(Box::new(self.clone()))
    }
}

/// 当前线程上正在记录的查询事件：（真正执行的次数，核对后复用的次数），按查询种类。
type EventLog = rustc_hash::FxHashMap<salsa::IngredientIndex, (usize, usize)>;

thread_local! {
    /// `None` 表示没在记录。
    static EXECUTIONS: std::cell::RefCell<Option<EventLog>> = const { std::cell::RefCell::new(None) };
}

fn on_salsa_event(event: salsa::Event) {
    let (key, executed) = match event.kind {
        salsa::EventKind::WillExecute { database_key } => (database_key, true),
        salsa::EventKind::DidValidateMemoizedValue { database_key } => (database_key, false),
        _ => return,
    };
    EXECUTIONS.with(|log| {
        if let Some(log) = log.borrow_mut().as_mut() {
            let entry = log.entry(key.ingredient_index()).or_default();
            if executed {
                entry.0 += 1;
            } else {
                entry.1 += 1;
            }
        }
    });
}

/// 查询真正执行（没有命中缓存）的次数，按查询名（如 `infer_tracked`）。
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct QueryExecutions(pub rustc_hash::FxHashMap<String, usize>);

impl QueryExecutions {
    /// 某个查询执行了几次。
    pub fn count(&self, query: &str) -> usize {
        self.0.get(query).copied().unwrap_or(0)
    }
}

/// 统计 `f` 在当前线程上让哪些查询真正执行了多少次。用来检查编辑之后的失效范围。
/// 只记录当前线程：`f` 里分到别的线程并行做的查询不计入。
pub fn record_executions<T>(db: &RootDatabase, f: impl FnOnce() -> T) -> (T, QueryExecutions) {
    let (res, executed, _) = record_query_events(db, f);
    (res, executed)
}

/// 和 [`record_executions`] 一样，另外返回编辑之后核对依赖、确认可以复用的缓存个数
/// （每个缓存每个版本最多核对一次，数量大说明这次请求的依赖面很广）。
pub fn record_query_events<T>(
    db: &RootDatabase,
    f: impl FnOnce() -> T,
) -> (T, QueryExecutions, QueryExecutions) {
    let previous = EXECUTIONS.with(|log| log.borrow_mut().replace(Default::default()));
    let res = f();
    let counts = EXECUTIONS
        .with(|log| std::mem::replace(&mut *log.borrow_mut(), previous))
        .unwrap_or_default();
    let mut executed = QueryExecutions::default();
    let mut validated = QueryExecutions::default();
    for (idx, (runs, checks)) in counts {
        let name = salsa::Database::ingredient_debug_name(db, idx).into_owned();
        if runs > 0 {
            *executed.0.entry(name.clone()).or_default() += runs;
        }
        if checks > 0 {
            *validated.0.entry(name).or_default() += checks;
        }
    }
    (res, executed, validated)
}

impl RootDatabase {
    pub fn new() -> RootDatabase {
        let db = RootDatabase::default();
        base_db::init_workspace(&db);
        db
    }
}

impl std::fmt::Debug for RootDatabase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RootDatabase").finish_non_exhaustive()
    }
}

/// 一处文本替换。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextEdit {
    pub range: TextRange,
    pub new_text: String,
}

impl TextEdit {
    pub fn insert(offset: syntax::TextSize, text: impl Into<String>) -> TextEdit {
        TextEdit {
            range: TextRange::empty(offset),
            new_text: text.into(),
        }
    }

    pub fn replace(range: TextRange, text: impl Into<String>) -> TextEdit {
        TextEdit {
            range,
            new_text: text.into(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    Class,
    Interface,
    Enum,
    Record,
    Annotation,
    Field,
    EnumConstant,
    Method,
    Constructor,
    Local,
    Param,
    TypeParam,
    Package,
}

impl SymbolKind {
    pub fn of_class(kind: ClassKind) -> SymbolKind {
        match kind {
            ClassKind::Class => SymbolKind::Class,
            ClassKind::Interface => SymbolKind::Interface,
            ClassKind::Enum => SymbolKind::Enum,
            ClassKind::Record => SymbolKind::Record,
            ClassKind::Annotation => SymbolKind::Annotation,
        }
    }

    pub fn of_definition(db: &dyn Db, def: &Definition) -> SymbolKind {
        match def {
            Definition::Class(class) => {
                class_data(db, *class).map_or(SymbolKind::Class, |d| SymbolKind::of_class(d.kind))
            }
            Definition::Field(field) => {
                let is_constant = class_data(db, field.class)
                    .and_then(|d| {
                        d.fields
                            .get(field.idx as usize)
                            .map(|f| f.is_enum_constant())
                    })
                    .unwrap_or(false);
                if is_constant {
                    SymbolKind::EnumConstant
                } else {
                    SymbolKind::Field
                }
            }
            Definition::Method(method) => {
                let is_constructor = class_data(db, method.class)
                    .and_then(|d| d.methods.get(method.idx as usize).map(|m| m.is_constructor))
                    .unwrap_or(false);
                if is_constructor {
                    SymbolKind::Constructor
                } else {
                    SymbolKind::Method
                }
            }
            Definition::Local(local) => match hir::infer(db, local.body).local(local.id).kind {
                LocalKind::Param | LocalKind::LambdaParam | LocalKind::CatchParam => {
                    SymbolKind::Param
                }
                LocalKind::LocalClassField => SymbolKind::Field,
                LocalKind::LocalClassMethod => SymbolKind::Method,
                _ => SymbolKind::Local,
            },
            Definition::TypeParam(_) => SymbolKind::TypeParam,
            Definition::Package(_) => SymbolKind::Package,
        }
    }
}

/// 定义的修饰符（局部符号、类型参数、包没有）。
pub fn definition_flags(db: &dyn Db, def: &Definition) -> Modifiers {
    let flags = match def {
        Definition::Class(class) => class_data(db, *class).map(|d| d.flags),
        Definition::Field(field) => class_data(db, field.class)
            .and_then(|d| d.fields.get(field.idx as usize).map(|f| f.flags)),
        Definition::Method(method) => class_data(db, method.class)
            .and_then(|d| d.methods.get(method.idx as usize).map(|m| m.flags)),
        _ => None,
    };
    flags.unwrap_or_default()
}
