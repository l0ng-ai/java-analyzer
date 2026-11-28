//! 方法覆写关系（JLS §8.4.8.1）：一个方法覆写了祖先里的哪些方法。
//!
//! 非法覆写的检查和重命名时找覆写族都按它判断：父类型的方法按子类看到的类型实参（以及
//! 方法自己的类型参数按位置）代换之后签名相同，或者非泛型的方法等于它的擦除；只算继承得到的
//! 方法（不是私有的，包私有的要在同一个包里，接口的静态方法不算）。

use base_db::Db;
use hir::{
    all_super_tys, class_data, class_header, method_sig, ClassId, GenericOwner, MethodId, Modifiers,
    Subst, Ty, Visibility, Wildcard,
};

/// `method` 覆写（或者以静态方法隐藏）的一个祖先方法。
pub struct OverriddenMethod {
    pub method: MethodId,
    /// 把祖先方法的签名换成 `method` 所在类看到的样子
    pub subst: Subst,
    /// 经由原始类型继承：祖先方法的签名要擦除
    pub erase: bool,
    /// 签名相同（不是靠擦除才覆写等价的）
    pub exact: bool,
}

pub struct Overridden {
    pub methods: Vec<OverriddenMethod>,
    /// 有同名、同参数个数的继承方法因为形参类型解析不出来而判断不了
    pub undecided: bool,
    /// 可能漏掉了被覆写的方法：有父类型读不到成员，或者有同名、同参数个数的继承方法签名
    /// 不同、但其中含没有代换掉的类型参数（菱形匿名类可能丢了推断出的父类型实参）
    pub uncertain: bool,
}

/// `method` 覆写（或者以静态方法隐藏）的祖先方法，按父类型的广度优先顺序。
pub fn overridden_methods(db: &dyn Db, method: MethodId) -> Overridden {
    let mut res = Overridden {
        methods: Vec::new(),
        undecided: false,
        uncertain: false,
    };
    let (Some(decl), Some(data)) = (hir::method_data(db, method), class_header(db, method.class))
    else {
        return res;
    };
    if decl.is_constructor {
        return res;
    }
    let sig = method_sig(db, method);
    // 自己的形参解析不出来时不比较签名，只记下有没有可能被覆写的同名同参数个数的方法
    let own_unknown = sig.params.iter().any(Ty::contains_unknown);
    let own_generic = !decl.type_params.is_empty();
    let raw = raw_inherited_classes(db, method.class);

    for super_ty in all_super_tys(db, &hir::this_ty(db, method.class)) {
        let Ty::Class(owner, args) = &super_ty else {
            continue;
        };
        let owner = *owner;
        if owner == method.class {
            continue;
        }
        let erase = raw.contains(&owner);
        let Some(owner_data) = class_data(db, owner) else {
            res.uncertain = true;
            continue;
        };
        let class_subst = Subst::for_class(db, owner, args);
        for (idx, candidate) in owner_data.methods.iter().enumerate() {
            if candidate.is_constructor
                || candidate.name != decl.name
                || candidate.params.len() != decl.params.len()
            {
                continue;
            }
            // 泛型方法只和类型参数个数相同的泛型方法比较（类型参数按位置对应）；非泛型方法
            // 可以靠擦除覆写泛型方法
            if own_generic && candidate.type_params.len() != decl.type_params.len() {
                continue;
            }
            // 接口的静态方法和私有方法不被继承
            if owner_data.is_interface()
                && (candidate.flags.is_static()
                    || candidate.flags.visibility() == Visibility::Private)
            {
                continue;
            }
            // 私有方法不被继承；包私有的只在同一个包里才被继承
            let super_rank = if owner_data.is_interface() {
                3
            } else {
                visibility_rank(candidate.flags.visibility())
            };
            let same_package = {
                let package = |name: &str| name.rsplit_once('/').map(|(p, _)| p.to_owned());
                package(&owner_data.binary_name) == package(&data.binary_name)
            };
            if super_rank == 0 || (super_rank == 1 && !same_package) {
                continue;
            }
            let candidate_id = MethodId {
                class: owner,
                idx: idx as u32,
            };
            let mut subst = class_subst.clone();
            if own_generic {
                for i in 0..decl.type_params.len() as u32 {
                    subst.set(
                        hir::TypeParamId {
                            owner: GenericOwner::Method(candidate_id),
                            idx: i,
                        },
                        Ty::TypeParam(hir::TypeParamId {
                            owner: GenericOwner::Method(method),
                            idx: i,
                        }),
                    );
                }
            }
            let super_sig = method_sig(db, candidate_id);
            let super_params: Vec<Ty> = super_sig
                .params
                .iter()
                .map(|p| erase_if(db, p.subst(&subst), erase))
                .collect();
            if own_unknown || super_params.iter().any(Ty::contains_unknown) {
                res.undecided = true;
                continue;
            }
            // 签名相同，或者（非泛型的）覆写方法的签名等于被覆写方法签名的擦除
            let exact = sig
                .params
                .iter()
                .zip(&super_params)
                .all(|(own, sup)| same_ty(db, own, sup));
            let by_erasure = !exact
                && !own_generic
                && sig.params.iter().zip(&super_params).all(|(own, sup)| {
                    let erased = sup.erasure(db);
                    !erased.contains_unknown() && same_ty(db, own, &erased)
                });
            if exact || by_erasure {
                res.methods.push(OverriddenMethod {
                    method: candidate_id,
                    subst,
                    erase,
                    exact,
                });
            } else if !candidate.flags.is_static()
                && (sig
                    .params
                    .iter()
                    .chain(&super_params)
                    .any(|p| p.mentions_params_where(&|_| true))
                    || (data.flags.contains(Modifiers::ANONYMOUS)
                        && erase
                        && super_sig
                            .params
                            .iter()
                            .any(|p| p.mentions_params_where(&|_| true))))
            {
                res.uncertain = true;
            }
        }
    }
    res
}

/// 经由原始类型继承来的父类型：某个父类型（或类自己）把它、或它的某个子类型写成了原始类型。
/// 原始类型的成员签名和它的父类型都要擦除（JLS §4.8），不能把类型参数换成 `Object` 了事：
/// `implements Foo` 时 `Supplier<Optional<T>> get()` 的签名是 `Supplier get()`。
pub fn raw_inherited_classes(db: &dyn Db, class: ClassId) -> rustc_hash::FxHashSet<ClassId> {
    let mut raw = rustc_hash::FxHashSet::default();
    for current in std::iter::once(class).chain(hir::all_supers(db, class).iter().copied()) {
        for sup in hir::class_supertypes(db, current).iter() {
            if let Ty::Class(id, _) = sup {
                if is_raw(db, sup) && raw.insert(*id) {
                    raw.extend(hir::all_supers(db, *id).iter().copied());
                }
            }
        }
    }
    raw
}

pub fn erase_if(db: &dyn Db, ty: Ty, erase: bool) -> Ty {
    if erase {
        ty.erasure(db)
    } else {
        ty
    }
}

pub fn visibility_rank(visibility: Visibility) -> u8 {
    match visibility {
        Visibility::Private => 0,
        Visibility::Package => 1,
        Visibility::Protected => 2,
        Visibility::Public => 3,
    }
}

/// 两个类型相同：结构相同，或者不含类型参数时全限定名相同（同名类的两份副本）。
/// 无界通配符 `?` 与 `? extends Object` 也等价。
pub fn same_ty(db: &dyn Db, a: &Ty, b: &Ty) -> bool {
    if a == b
        || (!a.mentions_params_where(&|_| true)
            && !b.mentions_params_where(&|_| true)
            && a.display_qualified(db) == b.display_qualified(db))
    {
        return true;
    }
    // 类型参数 T 代换成 Object 后，`? extends T` 与 `?` 等价。
    match (a, b) {
        (Ty::Wildcard(Wildcard::Unbounded), Ty::Wildcard(Wildcard::Extends(bound)))
        | (Ty::Wildcard(Wildcard::Extends(bound)), Ty::Wildcard(Wildcard::Unbounded)) => {
            same_ty(db, bound, &Ty::object(db))
        }
        (Ty::Class(ac, aa), Ty::Class(bc, ba)) => {
            ac.binary_name(db) == bc.binary_name(db)
                && aa.len() == ba.len()
                && aa.iter().zip(ba.iter()).all(|(a, b)| same_ty(db, a, b))
        }
        (Ty::Array(a), Ty::Array(b))
        | (Ty::Wildcard(Wildcard::Extends(a)), Ty::Wildcard(Wildcard::Extends(b)))
        | (Ty::Wildcard(Wildcard::Super(a)), Ty::Wildcard(Wildcard::Super(b))) => same_ty(db, a, b),
        _ => false,
    }
}

/// 类类型是原始类型（泛型类不带类型实参）。
pub fn is_raw(db: &dyn Db, ty: &Ty) -> bool {
    match ty {
        Ty::Class(class, args) => {
            args.is_empty() && class_header(db, *class).is_some_and(|d| !d.type_params.is_empty())
        }
        Ty::Array(element) => is_raw(db, element),
        _ => false,
    }
}
