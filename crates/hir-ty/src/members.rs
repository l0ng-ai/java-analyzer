//! 成员查找：字段、方法（含继承）、构造器、函数式接口的抽象方法。

use base_db::Db;
use hir_def::{
    class_data, class_header, constructor_indices, field_named, methods_named, ClassId, ClassKind,
    FieldId, GenericOwner, MethodId, Modifiers, Name, TypeParamId,
};

use crate::{
    lower::{field_ty, method_data, method_sig, type_param_bounds},
    subtype::all_super_tys,
    ty::{Subst, Ty},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldCandidate {
    pub id: FieldId,
    /// 按接收者类型代换后的字段类型
    pub ty: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MethodCandidate {
    pub id: MethodId,
    /// 声明该方法的类的类型参数 → 接收者处的实参
    pub subst: Subst,
}

impl MethodCandidate {
    /// 代换后的形参类型。
    pub fn param_tys(&self, db: &dyn Db) -> Vec<Ty> {
        method_sig(db, self.id)
            .params
            .iter()
            .map(|p| p.subst(&self.subst))
            .collect()
    }

    pub fn ret_ty(&self, db: &dyn Db) -> Ty {
        method_sig(db, self.id).ret.subst(&self.subst)
    }
}

/// 在接收者类型及其父类型里找字段。
pub fn lookup_field(db: &dyn Db, receiver: &Ty, name: &str) -> Option<FieldCandidate> {
    for ty in all_super_tys(db, &Subst::capture_receiver(db, receiver)) {
        let Ty::Class(class, args) = &ty else {
            continue;
        };
        if let Some(idx) = field_named(db, *class, name) {
            let id = FieldId { class: *class, idx };
            let subst = Subst::for_member_access(db, *class, args);
            return Some(FieldCandidate {
                id,
                ty: field_ty(db, id).subst(&subst),
            });
        }
    }
    None
}

/// 接收者类型上名为 `name` 的全部方法（含继承来的重载）。被子类覆写的版本不重复出现。
pub fn lookup_methods(db: &dyn Db, receiver: &Ty, name: &str) -> Vec<MethodCandidate> {
    let mut res: Vec<MethodCandidate> = Vec::new();
    // 已经收下的签名 → 在 `res` 里的下标
    let mut seen: Vec<(Vec<Ty>, usize)> = Vec::new();
    for ty in all_super_tys(db, &Subst::capture_receiver(db, receiver)) {
        let Ty::Class(class, args) = &ty else {
            continue;
        };
        let indices = methods_named(db, *class, name);
        if indices.is_empty() {
            continue;
        }
        let subst = Subst::for_member_access(db, *class, args);
        for &idx in indices.iter() {
            let id = MethodId { class: *class, idx };
            let Some(method) = method_data(db, id) else {
                continue;
            };
            if method.flags.is_static() && inherited_interface_static(db, *class, receiver) {
                continue;
            }
            let candidate = MethodCandidate {
                id,
                subst: subst.clone(),
            };
            let params = candidate.param_tys(db);
            let n_type_params = method_sig(db, id).n_type_params;
            let same_signature = |(seen_params, at): &&(Vec<Ty>, usize)| {
                if *seen_params == params {
                    return true;
                }
                // 泛型方法的签名相同要先把类型参数对应起来，上界也相同（JLS §8.4.4）：`Container`
                // 的 `<S> S getSPI(Class<S>)` 覆写接口里的同一个方法，两边的 `S` 是不同的类型参数。
                // 同一个类里的是重载，不是覆写
                let other = res[*at].id;
                if n_type_params == 0
                    || other.class == id.class
                    || method_sig(db, other).n_type_params != n_type_params
                {
                    return false;
                }
                let mut renamed = Subst::empty();
                for idx in 0..n_type_params {
                    renamed.insert(
                        TypeParamId {
                            owner: GenericOwner::Method(id),
                            idx,
                        },
                        Ty::TypeParam(TypeParamId {
                            owner: GenericOwner::Method(other),
                            idx,
                        }),
                    );
                }
                // class 文件里没写上界的类型参数记着 `Object`，和源码里的空上界一样
                let object = Ty::object(db);
                let bounds = |method: MethodId, idx: u32| -> Vec<Ty> {
                    let param = TypeParamId {
                        owner: GenericOwner::Method(method),
                        idx,
                    };
                    type_param_bounds(db, param)
                        .iter()
                        .filter(|b| **b != object)
                        .map(|b| b.subst(&renamed))
                        .collect()
                };
                let bounds_match =
                    (0..n_type_params).all(|idx| bounds(id, idx) == bounds(other, idx));
                bounds_match
                    && params
                        .iter()
                        .map(|p| p.subst(&renamed))
                        .eq(seen_params.iter().cloned())
            };
            if let Some(&(_, at)) = seen.iter().find(same_signature) {
                if inherited_wins(db, &res[at], &candidate) {
                    res[at] = candidate;
                }
                continue;
            }
            seen.push((params, res.len()));
            res.push(candidate);
        }
    }
    res
}

/// 接口的静态方法不会被实现类或子接口继承（JLS §8.4.8、§9.4.1）：只有接收者就是这个接口
/// 本身时才能找到（`Map.of()` 可以，`HashMap.of()` / `Headers.of()` 找到的不是它）。
/// 调用方已经确认方法是静态的。
fn inherited_interface_static(db: &dyn Db, class: ClassId, receiver: &Ty) -> bool {
    receiver.as_class() != Some(class) && class_header(db, class).is_some_and(|d| d.is_interface())
}

/// 同一个签名的方法后找到的 `found` 是否取代先找到的 `existing`。
///
/// 父类的方法压过接口的（见 [`class_method_wins`]）；两个都来自接口时取返回类型更具体的那个
/// （JLS §9.4.1.3）：AWS SDK 的 `PutObjectRequest.Builder` 从 `S3Request.Builder` 继承
/// `S3Request build()`，又从 `SdkBuilder<Builder, PutObjectRequest>` 继承 `PutObjectRequest build()`，
/// 调用得到的是后者。
fn inherited_wins(db: &dyn Db, existing: &MethodCandidate, found: &MethodCandidate) -> bool {
    if class_method_wins(db, existing.id.class, found.id.class) {
        return true;
    }
    let is_interface = |class: ClassId| class_header(db, class).is_some_and(|d| d.is_interface());
    // 先找到的声明在后者的子接口里：它覆写了后者（`Node.OfPrimitive` 的 `T_SPLITR spliterator()`
    // 覆写 `Node` 的 `Spliterator<T> spliterator()`）
    if !is_interface(existing.id.class)
        || !is_interface(found.id.class)
        || hir_def::is_subclass_of(db, existing.id.class, found.id.class)
    {
        return false;
    }
    let existing_ret = existing.ret_ty(db);
    let found_ret = found.ret_ty(db);
    found_ret != existing_ret
        && !found_ret.contains_unknown()
        && !existing_ret.contains_unknown()
        && !matches!(existing_ret, Ty::TypeParam(_))
        && crate::subtype::is_subtype(db, &found_ret, &existing_ret)
}

/// 同一个签名先在接口里、后在父类里找到时，父类的方法才是继承下来的那个（JLS §8.4.8）：
/// `ClassSymbol` 同时从 `Symbol` 继承 `Type asType()`、从 `TypeElement` 继承 `TypeMirror asType()`，
/// 调用得到的是前者。`Object` 的方法不算（接口里重新声明的 `equals` 等保留接口的版本）。
fn class_method_wins(db: &dyn Db, existing: ClassId, found: ClassId) -> bool {
    let is_interface = |class: ClassId| class_header(db, class).is_some_and(|d| d.is_interface());
    is_interface(existing) && !is_interface(found) && found.binary_name(db) != "java/lang/Object"
}

pub fn constructors(db: &dyn Db, class: ClassId, subst: &Subst) -> Vec<MethodCandidate> {
    constructor_indices(db, class)
        .iter()
        .map(|&idx| MethodCandidate {
            id: MethodId { class, idx },
            subst: subst.clone(),
        })
        .collect()
}

/// 接收者类型上所有可见的字段（子类的同名字段遮蔽父类的）。
pub fn all_fields(db: &dyn Db, receiver: &Ty) -> Vec<FieldCandidate> {
    let mut res: Vec<FieldCandidate> = Vec::new();
    let mut seen: Vec<Name> = Vec::new();
    for ty in all_super_tys(db, &Subst::capture_receiver(db, receiver)) {
        let Ty::Class(class, args) = &ty else {
            continue;
        };
        let Some(data) = class_data(db, *class) else {
            continue;
        };
        let subst = Subst::for_member_access(db, *class, args);
        for (idx, field) in data.fields.iter().enumerate() {
            if seen.contains(&field.name) {
                continue;
            }
            seen.push(field.name.clone());
            let id = FieldId {
                class: *class,
                idx: idx as u32,
            };
            res.push(FieldCandidate {
                id,
                ty: field_ty(db, id).subst(&subst),
            });
        }
    }
    res
}

/// 接收者类型上所有的方法（不含构造器），覆写关系已去重。
pub fn all_methods(db: &dyn Db, receiver: &Ty) -> Vec<MethodCandidate> {
    let mut res: Vec<MethodCandidate> = Vec::new();
    let mut seen: Vec<((Name, Vec<Ty>), usize)> = Vec::new();
    for ty in all_super_tys(db, &Subst::capture_receiver(db, receiver)) {
        let Ty::Class(class, args) = &ty else {
            continue;
        };
        let Some(data) = class_data(db, *class) else {
            continue;
        };
        let subst = Subst::for_member_access(db, *class, args);
        for (idx, method) in data.methods.iter().enumerate() {
            if method.is_constructor
                || (data.is_interface()
                    && method.flags.is_static()
                    && receiver.as_class() != Some(*class))
            {
                continue;
            }
            let candidate = MethodCandidate {
                id: MethodId {
                    class: *class,
                    idx: idx as u32,
                },
                subst: subst.clone(),
            };
            let key = (method.name.clone(), candidate.param_tys(db));
            if let Some((_, at)) = seen.iter().find(|(k, _)| *k == key) {
                if inherited_wins(db, &res[*at], &candidate) {
                    res[*at] = candidate;
                }
                continue;
            }
            seen.push((key, res.len()));
            res.push(candidate);
        }
    }
    res
}

const OBJECT_METHODS: &[(&str, usize)] = &[("equals", 1), ("hashCode", 0), ("toString", 0)];

/// 函数式接口的那个唯一的抽象方法（JLS §9.8）。
pub fn functional_method(db: &dyn Db, ty: &Ty) -> Option<MethodCandidate> {
    let class = ty.as_class()?;
    let id = functional_method_id(db, base_db::workspace(db), class)?;
    // 声明它的接口在 `ty` 的父类型里的样子给出类型实参
    let args: Option<std::sync::Arc<[Ty]>> = match ty {
        Ty::Class(_, args) if id.class == class => Some(args.clone()),
        _ => all_super_tys(db, ty).into_iter().find_map(|sup| match sup {
            Ty::Class(c, args) if c == id.class => Some(args),
            _ => None,
        }),
    };
    let args = args.as_deref().unwrap_or(&[]);
    Some(MethodCandidate {
        id,
        subst: Subst::for_class(db, id.class, args),
    })
}

/// 接口（按类判断，和类型实参无关）的那个唯一的抽象方法。
///
/// 按类缓存，并且只看各个接口的签名：用到 lambda 的体依赖它，而不是接口和它的父接口的全部签名。
#[salsa::tracked]
fn functional_method_id(db: &dyn Db, _ws: base_db::Workspace, class: ClassId) -> Option<MethodId> {
    let data = class_data(db, class)?;
    if data.kind != ClassKind::Interface {
        return None;
    }

    let mut found: Option<MethodId> = None;
    let mut found_key: Option<(Name, usize)> = None;
    // 被 default 方法实现掉的抽象方法不算
    let mut implemented: Vec<(Name, usize)> = Vec::new();

    let all_supers = hir_def::all_supers(db, class);
    let supers = std::iter::once(class).chain(all_supers.iter().copied());
    for sup_class in supers {
        let Some(sup_data) = class_data(db, sup_class) else {
            continue;
        };
        if !sup_data.is_interface() {
            continue;
        }
        for (idx, method) in sup_data.methods.iter().enumerate() {
            let key = (method.name.clone(), method.params.len());
            if method.flags.is_static() {
                continue;
            }
            if !method.flags.is_abstract() {
                implemented.push(key);
                continue;
            }
            if OBJECT_METHODS.contains(&(method.name.as_str(), method.params.len()))
                || implemented.contains(&key)
            {
                continue;
            }
            match &found_key {
                Some(existing) if *existing == key => {}
                Some(_) => return None,
                None => {
                    found_key = Some(key);
                    found = Some(MethodId {
                        class: sup_class,
                        idx: idx as u32,
                    });
                }
            }
        }
    }
    found
}

/// 成员是否可以从 `from_class`（及其所在的包）访问。`from_class` 为 `None` 时只看得见 public。
pub fn is_accessible(
    db: &dyn Db,
    flags: Modifiers,
    declaring_class: ClassId,
    from_class: Option<ClassId>,
) -> bool {
    use hir_def::Visibility;
    let Some(from) = from_class else {
        return flags.visibility() == Visibility::Public;
    };
    match flags.visibility() {
        Visibility::Public => true,
        Visibility::Private => outermost_class(db, declaring_class) == outermost_class(db, from),
        Visibility::Package => same_package(db, declaring_class, from),
        Visibility::Protected => {
            same_package(db, declaring_class, from)
                || hir_def::is_subclass_of(db, from, declaring_class)
                || hir_def::is_subclass_of(db, outermost_class(db, from), declaring_class)
        }
    }
}

/// 通过类型为 `receiver` 的表达式访问实例成员时的可访问性。在 [`is_accessible`] 之上多一条
/// protected 的规则（JLS 6.6.2.1）：不在同一个包里时，只能通过"访问发生处的类或其子类"
/// 类型的表达式访问——`Object.clone()` 不能在任意对象上调用。
pub fn is_accessible_via(
    db: &dyn Db,
    flags: Modifiers,
    declaring_class: ClassId,
    from_class: Option<ClassId>,
    receiver: &Ty,
) -> bool {
    if !is_accessible(db, flags, declaring_class, from_class) {
        return false;
    }
    let (Some(from), Ty::Class(receiver, _)) = (from_class, receiver) else {
        return true;
    };
    if flags.visibility() != hir_def::Visibility::Protected
        || flags.is_static()
        || same_package(db, declaring_class, from)
    {
        return true;
    }
    let outer = outermost_class(db, from);
    [from, outer]
        .into_iter()
        .any(|class| *receiver == class || hir_def::is_subclass_of(db, *receiver, class))
}

fn same_package(db: &dyn Db, a: ClassId, b: ClassId) -> bool {
    let a = a.binary_name(db);
    let b = b.binary_name(db);
    a.rsplit_once('/').map(|(p, _)| p) == b.rsplit_once('/').map(|(p, _)| p)
}

fn outermost_class(db: &dyn Db, class: ClassId) -> ClassId {
    hir_def::outermost_class(db, class)
}
