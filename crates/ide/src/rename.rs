//! 重命名。
//!
//! 收集定义本身、它的全部引用，以及必须跟着一起改名的关联声明：
//! - 方法：整条覆写链上的所有声明；
//! - 类：它的构造器声明，以及与类同名的源文件；
//! - 记录组件：同名的访问器调用；
//! - 字段：Lombok 生成的 getter / setter / wither / 构建器方法的调用，换成按新字段名生成的名字。
//!   反过来，在这些生成的访问器上重命名等于重命名字段（`getName` → `getTitle` 把字段改成 `title`）。
//!
//! 冲突检查是保守的：只拦截确定会出错的情况（名字不合法、同一作用域里已有同名符号、
//! 同一个类里已有参数类型擦除后相同的同名方法、目标在依赖库里）。

use base_db::Db;
use hir::{
    class_data, method_sig, AccessorKind, ClassId, ClassKind, Definition, FieldData, FieldId,
    MethodId, Modifiers, Name, Semantics, Ty,
};
use ide_db::{
    search::{find_references_with_docs, refers_to},
    TextEdit,
};
use rustc_hash::FxHashSet;
use syntax::{ast, TextRange};

use crate::{
    navigation::{all_subclasses, definition_at, position_file, super_methods},
    FileId, FilePosition, RangeInfo,
};

/// 跨文件的一组修改。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceChange {
    /// 每个文件里的文本替换，按起始位置排序、互不重叠
    pub edits: Vec<(FileId, Vec<TextEdit>)>,
    /// 需要改名的文件：`(文件, 新文件名)`，新文件名不含目录
    pub file_renames: Vec<(FileId, String)>,
    /// 需要新建的文件：`(旁边的文件, 新文件名, 内容)`，新文件和"旁边的文件"在同一个目录
    pub file_creates: Vec<(FileId, String, String)>,
}

impl SourceChange {
    pub fn is_empty(&self) -> bool {
        self.edits.is_empty() && self.file_renames.is_empty() && self.file_creates.is_empty()
    }

    pub fn single_file(file_id: FileId, mut edits: Vec<TextEdit>) -> SourceChange {
        edits.sort_by_key(|edit| (edit.range.start(), edit.range.end()));
        SourceChange {
            edits: vec![(file_id, edits)],
            file_renames: Vec::new(),
            file_creates: Vec::new(),
        }
    }

    /// 每一处替换可以有各自的新文本（字段改名时，Lombok 访问器的调用点要换成相应的访问器名）。
    fn from_replacements(mut items: Vec<(FileId, TextRange, String)>) -> SourceChange {
        items.sort_by(|(f1, r1, t1), (f2, r2, t2)| {
            (f1, r1.start(), r1.end(), t1).cmp(&(f2, r2.start(), r2.end(), t2))
        });
        items.dedup();
        let mut edits: Vec<(FileId, Vec<TextEdit>)> = Vec::new();
        for (file_id, range, new_text) in items {
            let edit = TextEdit::replace(range, new_text);
            match edits.last_mut() {
                Some((last, list)) if *last == file_id => list.push(edit),
                _ => edits.push((file_id, vec![edit])),
            }
        }
        SourceChange {
            edits,
            file_renames: Vec::new(),
            file_creates: Vec::new(),
        }
    }
}

/// 是否是合法的、非关键字的 Java 标识符。
pub(crate) fn is_valid_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first.is_alphabetic() || first == '_' || first == '$') {
        return false;
    }
    if !chars.all(|c| c.is_alphanumeric() || c == '_' || c == '$') {
        return false;
    }
    // 借解析器排除关键字：`class <name> {}` 必须能无错误地解析
    ast::CompilationUnit::parse(&format!("class {name} {{}}"))
        .errors()
        .is_empty()
        && !matches!(
            name,
            "var" | "yield" | "record" | "sealed" | "permits" | "_"
        )
}

fn is_constructor(db: &dyn Db, method: MethodId) -> bool {
    class_data(db, method.class)
        .and_then(|d| d.methods.get(method.idx as usize).map(|m| m.is_constructor))
        .unwrap_or(false)
}

/// 构造器上的重命名实际是重命名它的类。
fn rename_target(db: &dyn Db, def: Definition) -> Definition {
    match def {
        Definition::Method(method) if is_constructor(db, method) => Definition::Class(method.class),
        other => other,
    }
}

pub(crate) fn prepare_rename(
    db: &dyn Db,
    position: FilePosition,
) -> Result<RangeInfo<String>, String> {
    let file = position_file(db, position).ok_or(base_db::trs!("未知的文件", "Unknown file"))?;
    let (range, def) = definition_at(db, file, position.offset).ok_or(base_db::trs!(
        "光标处没有可以重命名的符号",
        "No symbol to rename at the cursor"
    ))?;
    let def = rename_target(db, def);
    check_renameable(db, &def)?;
    if let Definition::Method(method) = def {
        check_overridden_renameable(db, method)?;
    }
    let name = def
        .name(db)
        .ok_or(base_db::trs!("这个符号没有名字", "This symbol has no name"))?;
    Ok(RangeInfo {
        range,
        info: name.to_string(),
    })
}

/// 覆写了依赖库里的方法就不能改名。只沿覆写链往上查，比算出整个覆写族（`toString` 这类
/// 方法要扫遍所有子类）便宜得多，`prepareRename` 也能先把它拦下来。
fn check_overridden_renameable(db: &dyn Db, method: MethodId) -> Result<(), String> {
    for sup in super_methods(db, method) {
        check_renameable(db, &Definition::Method(sup)).map_err(|_| {
            base_db::tr!(
                "这个方法覆写了依赖库里的方法，不能重命名",
                "This method overrides a library method and cannot be renamed"
            )
        })?;
    }
    Ok(())
}

fn check_renameable(db: &dyn Db, def: &Definition) -> Result<(), String> {
    match def {
        Definition::Package(_) => Err(base_db::tr!(
            "暂不支持重命名包",
            "Renaming packages is not supported yet"
        )),
        Definition::Local(_) | Definition::TypeParam(_) => Ok(()),
        Definition::Class(_) | Definition::Field(_) | Definition::Method(_) => {
            let class = match def {
                Definition::Class(class) => *class,
                _ => def.container_class().ok_or(base_db::trs!(
                    "找不到所属的类",
                    "Cannot find the enclosing class"
                ))?,
            };
            let is_source = class_data(db, class).is_some_and(|d| d.is_source);
            if !is_source {
                return Err(base_db::tr!(
                    "不能重命名依赖库或 JDK 里的符号",
                    "Cannot rename a symbol from a library or the JDK"
                ));
            }
            let generated = || {
                base_db::tr!(
                    "这个成员是自动生成的，没有可以修改的声明",
                    "This member is generated and has no declaration to edit"
                )
            };
            if def.source(db).is_none() {
                return Err(generated());
            }
            // 合成成员的声明位置指向触发它的字段或类：只有能归到某个字段的访问器
            // 可以重命名（实际改的是字段），其余的（`builder()`、`build()`、日志器字段 …）不行
            match def {
                Definition::Method(method)
                    if is_synthetic_method(db, *method) && !is_constructor(db, *method) =>
                {
                    if accessor_origin(db, *method).is_none() {
                        return Err(generated());
                    }
                }
                Definition::Field(field) => {
                    let synthetic = class_data(db, field.class)
                        .and_then(|d| d.fields.get(field.idx as usize).map(|f| f.flags))
                        .is_some_and(|flags| flags.contains(Modifiers::SYNTHETIC));
                    if synthetic {
                        return Err(generated());
                    }
                }
                _ => {}
            }
            Ok(())
        }
    }
}

fn is_synthetic_method(db: &dyn Db, method: MethodId) -> bool {
    class_data(db, method.class)
        .and_then(|d| d.methods.get(method.idx as usize).map(|m| m.flags))
        .is_some_and(|flags| flags.contains(Modifiers::SYNTHETIC))
}

/// 合成的访问器（Lombok 的 getter / setter / wither / 构建器方法、记录的访问器）
/// 是从哪个字段生成的、属于哪一种。
pub(crate) fn accessor_origin(db: &dyn Db, method: MethodId) -> Option<(FieldId, AccessorKind)> {
    let data = class_data(db, method.class)?;
    let m = data.methods.get(method.idx as usize)?;
    if m.is_constructor || !m.flags.contains(Modifiers::SYNTHETIC) {
        return None;
    }
    let decl = m.decl?;
    // 字段在本类里；构建器类（合成的嵌套类）的方法对应外层类的字段
    let mut owners = vec![method.class];
    if data.flags.contains(Modifiers::SYNTHETIC) {
        if let Some(outer) = hir::outer_class(db, method.class) {
            owners.push(outer);
        }
    }
    owners.into_iter().find_map(|owner| {
        let owner_data = class_data(db, owner)?;
        owner_data
            .fields
            .iter()
            .enumerate()
            .filter(|(_, f)| f.decl == Some(decl))
            .find_map(|(idx, f)| {
                AccessorKind::of(f, m).map(|kind| {
                    (
                        FieldId {
                            class: owner,
                            idx: idx as u32,
                        },
                        kind,
                    )
                })
            })
    })
}

/// 字段的全部合成访问器（包括 Lombok 构建器类上的同名方法）。
pub(crate) fn field_accessors(db: &dyn Db, field: FieldId) -> Vec<(MethodId, AccessorKind)> {
    let Some(data) = class_data(db, field.class) else {
        return Vec::new();
    };
    let Some(field_data) = data.fields.get(field.idx as usize) else {
        return Vec::new();
    };
    let mut classes = vec![field.class];
    classes.extend(hir::nested_class(
        db,
        field.class,
        &format!("{}Builder", data.name),
    ));
    let mut res = Vec::new();
    for class in classes {
        let Some(class_data) = class_data(db, class) else {
            continue;
        };
        for (idx, m) in class_data.methods.iter().enumerate() {
            if m.is_constructor
                || !m.flags.contains(Modifiers::SYNTHETIC)
                || m.decl.is_none()
                || m.decl != field_data.decl
            {
                continue;
            }
            if let Some(kind) = AccessorKind::of(field_data, m) {
                res.push((
                    MethodId {
                        class,
                        idx: idx as u32,
                    },
                    kind,
                ));
            }
        }
    }
    res
}

/// 方法所在的整条覆写链：它覆写的、覆写它的，以及这些方法的其它覆写者。
fn method_family(db: &dyn Db, method: MethodId) -> Vec<MethodId> {
    let target = Definition::Method(method);
    let Some(name) = target.name(db) else {
        return vec![method];
    };
    let mut family: Vec<MethodId> = vec![method];
    family.extend(super_methods(db, method));

    // 链上每个声明类的全部子类里，同一族的方法
    let roots: Vec<ClassId> = family.iter().map(|m| m.class).collect();
    let mut seen: FxHashSet<MethodId> = family.iter().copied().collect();
    for root in roots {
        for sub in all_subclasses(db, root) {
            let Some(data) = class_data(db, sub) else {
                continue;
            };
            for (idx, _) in data.methods_named(&name) {
                let candidate = MethodId { class: sub, idx };
                if seen.contains(&candidate) {
                    continue;
                }
                if refers_to(db, &Definition::Method(candidate), &target) {
                    seen.insert(candidate);
                    family.push(candidate);
                }
            }
        }
    }
    family
}

fn check_conflicts(db: &dyn Db, def: &Definition, new_name: &str) -> Result<(), String> {
    match def {
        Definition::Local(local) => {
            let result = hir::infer(db, local.body);
            let clash = result
                .locals()
                .iter()
                .enumerate()
                .any(|(id, other)| id as u32 != local.id && other.name == new_name);
            if clash {
                return Err(base_db::tr!(
                    "这个方法体里已经有名为 `{new_name}` 的局部符号",
                    "A local symbol named `{new_name}` already exists in this method body"
                ));
            }
        }
        Definition::Field(field) => {
            if class_data(db, field.class).is_some_and(|d| d.field_named(new_name).is_some()) {
                return Err(base_db::tr!(
                    "类里已经有名为 `{new_name}` 的字段",
                    "The class already has a field named `{new_name}`"
                ));
            }
        }
        Definition::Class(class) => {
            let binary_name = class.binary_name(db);
            let sibling = match binary_name.rfind(['/', '$']) {
                Some(idx) => format!("{}{new_name}", &binary_name[..=idx]),
                None => new_name.to_owned(),
            };
            let from = hir::class_decl_file(db, *class);
            if hir::lookup_class_from(db, from, &sibling).is_some() {
                return Err(base_db::tr!(
                    "已经存在名为 `{new_name}` 的类",
                    "A class named `{new_name}` already exists"
                ));
            }
        }
        Definition::Method(method) => {
            // 同一个类里同名、参数类型擦除后相同的方法会变成重复声明；
            // 参数类型解析不出来时按参数个数保守判断
            if let Some(data) = class_data(db, method.class) {
                let erased_params = |idx: u32| -> Vec<Ty> {
                    method_sig(
                        db,
                        MethodId {
                            class: method.class,
                            idx,
                        },
                    )
                    .params
                    .iter()
                    .map(|ty| ty.erasure(db))
                    .collect()
                };
                let own = erased_params(method.idx);
                let clash = data.methods_named(new_name).any(|(idx, other)| {
                    if other.is_constructor || other.params.len() != own.len() {
                        return false;
                    }
                    let theirs = erased_params(idx);
                    own.iter()
                        .zip(&theirs)
                        .all(|(a, b)| a == b || a.contains_unknown() || b.contains_unknown())
                });
                if clash {
                    return Err(base_db::tr!(
                        "类里已经有参数类型相同的方法 `{new_name}`",
                        "The class already has a method `{new_name}` with the same parameter types"
                    ));
                }
            }
        }
        Definition::TypeParam(_) | Definition::Package(_) => {}
    }
    Ok(())
}

pub(crate) fn rename(
    db: &dyn Db,
    position: FilePosition,
    new_name: &str,
) -> Result<SourceChange, String> {
    if !is_valid_identifier(new_name) {
        return Err(base_db::tr!(
            "`{new_name}` 不是合法的 Java 标识符",
            "`{new_name}` is not a valid Java identifier"
        ));
    }
    let file = position_file(db, position).ok_or(base_db::trs!("未知的文件", "Unknown file"))?;
    let (_, def) = definition_at(db, file, position.offset).ok_or(base_db::trs!(
        "光标处没有可以重命名的符号",
        "No symbol to rename at the cursor"
    ))?;
    let def = rename_target(db, def);
    check_renameable(db, &def)?;
    if def.name(db).is_some_and(|old| old == new_name) {
        return Ok(SourceChange::default());
    }
    // 重命名合成的访问器等于重命名它的字段：`getName` → `getTitle` 把字段改成 `title`，
    // 其它访问器跟着字段一起改
    let (def, new_name) = match &def {
        Definition::Method(method) => match accessor_origin(db, *method) {
            Some((field, kind)) => {
                let field_data = class_data(db, field.class)
                    .and_then(|d| d.fields.get(field.idx as usize).cloned())
                    .ok_or(base_db::trs!("找不到字段", "Cannot find the field"))?;
                let field_name = kind
                    .field_name_for(&field_data, new_name)
                    .filter(|name| is_valid_identifier(name))
                    .ok_or_else(|| {
                        base_db::tr!(
                            "`{new_name}` 不是字段 `{}` 生成的访问器能用的名字",
                            "`{new_name}` is not a valid accessor name for the field `{}`",
                            field_data.name
                        )
                    })?;
                (Definition::Field(field), field_name.to_string())
            }
            None => (def, new_name.to_owned()),
        },
        _ => (def, new_name.to_owned()),
    };
    let new_name = new_name.as_str();
    let old_name = def
        .name(db)
        .ok_or(base_db::trs!("这个符号没有名字", "This symbol has no name"))?;
    if old_name == new_name {
        return Ok(SourceChange::default());
    }
    check_conflicts(db, &def, new_name)?;

    let mut items: Vec<(FileId, TextRange, String)> = Vec::new();
    let add_declaration = |def: &Definition, items: &mut Vec<(FileId, TextRange, String)>| {
        if let Some(source) = def.source(db) {
            items.push((
                source.file.file_id(db),
                source.focus_range,
                new_name.to_owned(),
            ));
        }
    };
    let add_references_as =
        |def: &Definition, text: &str, items: &mut Vec<(FileId, TextRange, String)>| {
            items.extend(
                find_references_with_docs(db, def)
                    .into_iter()
                    .map(|r| (r.file_id, r.range, text.to_owned())),
            );
        };
    let add_references = |def: &Definition, items: &mut Vec<(FileId, TextRange, String)>| {
        add_references_as(def, new_name, items);
    };

    let mut file_renames = Vec::new();
    match &def {
        Definition::Method(method) => {
            check_overridden_renameable(db, *method)?;
            let family = method_family(db, *method);
            for member in &family {
                let member_def = Definition::Method(*member);
                check_renameable(db, &member_def).map_err(|_| {
                    base_db::tr!(
                        "这个方法覆写了依赖库里的方法，不能重命名",
                        "This method overrides a library method and cannot be renamed"
                    )
                })?;
                add_declaration(&member_def, &mut items);
            }
            // 菱形匿名类里的覆写（没有登记成类，覆写链里没有它们）
            for (file, member) in crate::navigation::diamond_anonymous_overrides(db, &family) {
                items.push((file.file_id(db), member.name_range, new_name.to_owned()));
            }
            // 引用搜索本身就按覆写链匹配，搜一次即可
            add_references(&def, &mut items);
        }
        Definition::Class(class) => {
            add_declaration(&def, &mut items);
            add_references(&def, &mut items);
            let data = class_data(db, *class).ok_or(base_db::trs!(
                "找不到类的数据",
                "Cannot find the class data"
            ))?;
            for (idx, ctor) in data.constructors() {
                // 隐式构造器的声明位置就是类本身，不重复添加
                if ctor.decl != data.decl {
                    add_declaration(
                        &Definition::Method(MethodId { class: *class, idx }),
                        &mut items,
                    );
                }
            }
            // 顶层类与文件同名时文件也要改名
            if data.outer.is_none() {
                if let Some(source) = def.source(db) {
                    let sema = Semantics::new(db);
                    let cu = sema.parse(source.file);
                    let top_level_count = cu.type_decls().count();
                    let is_public = data.flags.visibility() == hir::Visibility::Public;
                    if is_public || top_level_count == 1 {
                        file_renames.push((source.file.file_id(db), format!("{new_name}.java")));
                    }
                }
            }
        }
        Definition::Field(field) => {
            add_declaration(&def, &mut items);
            add_references(&def, &mut items);
            // Lombok 生成的访问器：调用点换成按新字段名生成的访问器名
            if let Some(field_data) =
                class_data(db, field.class).and_then(|d| d.fields.get(field.idx as usize).cloned())
            {
                let renamed = FieldData {
                    name: Name::new(new_name),
                    ..field_data
                };
                for (accessor, kind) in field_accessors(db, *field) {
                    let accessor_name = kind.name_for(&renamed);
                    add_references_as(&Definition::Method(accessor), &accessor_name, &mut items);
                }
            }
            // 记录组件的访问器与组件同名
            if let Some(data) = class_data(db, field.class) {
                if data.kind == ClassKind::Record {
                    let accessor = data.methods.iter().position(|m| {
                        !m.is_constructor && m.name == old_name && m.params.is_empty()
                    });
                    if let Some(idx) = accessor {
                        let method = Definition::Method(MethodId {
                            class: field.class,
                            idx: idx as u32,
                        });
                        add_references(&method, &mut items);
                    }
                }
            }
        }
        Definition::Local(_) | Definition::TypeParam(_) => {
            add_declaration(&def, &mut items);
            add_references(&def, &mut items);
        }
        Definition::Package(_) => {
            return Err(base_db::tr!(
                "暂不支持重命名包",
                "Renaming packages is not supported yet"
            ))
        }
    }

    let mut change = SourceChange::from_replacements(items);
    change.file_renames = file_renames;
    Ok(change)
}
