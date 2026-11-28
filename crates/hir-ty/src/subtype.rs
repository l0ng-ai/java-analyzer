//! 子类型、可赋值性与父类型遍历（JLS §4.10、§5）。
//!
//! 这里的判断在遇到 `Unknown` 或尚未推断出的类型参数时一律从宽：
//! 宁可漏报，不可误报。

use std::collections::VecDeque;

use base_db::Db;
use hir_def::{ClassId, PrimitiveType};
use rustc_hash::FxHashSet;

use crate::{
    lower::{class_supertypes, type_param_bounds},
    ty::{Subst, Ty, Wildcard},
};

/// `ty` 自身（如果是类类型）及其全部父类型，类型实参已按继承链代换。
/// 广度优先，`Object` 在最后。
pub fn all_super_tys(db: &dyn Db, ty: &Ty) -> Vec<Ty> {
    let mut res = Vec::new();
    let mut seen: FxHashSet<ClassId> = FxHashSet::default();
    let mut queue: VecDeque<Ty> = VecDeque::new();
    queue.push_back(ty.clone());

    while let Some(current) = queue.pop_front() {
        match &current {
            Ty::Class(class, args) => {
                if !seen.insert(*class) {
                    continue;
                }
                let subst = Subst::for_class(db, *class, args);
                for sup in class_supertypes(db, *class).iter() {
                    queue.push_back(sup.subst(&subst));
                }
                res.push(current);
            }
            Ty::TypeParam(param) => {
                for bound in type_param_bounds(db, *param).iter() {
                    queue.push_back(bound.clone());
                }
            }
            Ty::Intersection(parts) => queue.extend(parts.iter().cloned()),
            Ty::Wildcard(_) => queue.push_back(current.upper_bound(db)),
            Ty::Array(_) => {
                queue.push_back(Ty::well_known(db, "java/lang/Cloneable"));
                queue.push_back(Ty::well_known(db, "java/io/Serializable"));
            }
            _ => {}
        }
    }

    // Object 放在最后：接口、类型参数、数组的成员查找都要落到它上面
    let object = Ty::object(db);
    if let Ty::Class(object_id, _) = &object {
        if ty.is_reference() && !matches!(ty, Ty::Null) {
            res.retain(|t| t.as_class() != Some(*object_id));
            res.push(object);
        }
    }
    res
}

/// 类型相容性里的"同一个类"：同一个 id，或者同名类的两份副本。
///
/// javac 在一次编译里只按名字认类：别的模块的签名里出现的同名类和本模块看到的是同一个，
/// 所以副本之间互相赋值不报错（宁可漏报）。
fn same_class(db: &dyn Db, a: ClassId, b: ClassId) -> bool {
    a == b || ((a.is_copy() || b.is_copy()) && a.binary_name(db) == b.binary_name(db))
}

/// `ty` 作为 `target` 的子类型时，`target` 的实例化形式（带代换后的类型实参）。
pub fn find_super(db: &dyn Db, ty: &Ty, target: ClassId) -> Option<Ty> {
    if let Ty::Class(class, _) = ty {
        if same_class(db, *class, target) {
            return Some(ty.clone());
        }
    }
    all_super_tys(db, ty).into_iter().find(|t| {
        t.as_class()
            .is_some_and(|class| same_class(db, class, target))
    })
}

/// 泛型类的原始类型（类型实参为空）。
fn is_raw(db: &dyn Db, class: ClassId, args: &[Ty]) -> bool {
    args.is_empty() && hir_def::class_header(db, class).is_some_and(|d| !d.type_params.is_empty())
}

/// 类型本身是原始类型，或者它的父类型链上经过了原始类型（`class TreeList extends AbstractList`）：
/// 这样的值转换成参数化的父类型要靠未经检查的转换。
pub fn involves_raw(db: &dyn Db, ty: &Ty) -> bool {
    let mut seen: FxHashSet<ClassId> = FxHashSet::default();
    let mut queue: VecDeque<Ty> = VecDeque::new();
    queue.push_back(ty.clone());
    while let Some(current) = queue.pop_front() {
        let Ty::Class(class, args) = &current else {
            continue;
        };
        if is_raw(db, *class, args) {
            return true;
        }
        if !seen.insert(*class) || seen.len() > 64 {
            continue;
        }
        queue.extend(class_supertypes(db, *class).iter().cloned());
    }
    false
}

/// 和 [`find_super`] 一样，但保留原始类型：继承链上经过原始类型时，它的父类型都是擦除后的
/// （JLS §4.8），找到的 `target` 也是原始类型（类型实参为空）。
pub fn find_super_keeping_raw(db: &dyn Db, ty: &Ty, target: ClassId) -> Option<Ty> {
    let mut seen: FxHashSet<ClassId> = FxHashSet::default();
    let mut queue: VecDeque<Ty> = VecDeque::new();
    queue.push_back(ty.clone());
    while let Some(current) = queue.pop_front() {
        match &current {
            Ty::Class(class, args) => {
                if same_class(db, *class, target) {
                    return Some(current);
                }
                if !seen.insert(*class) {
                    continue;
                }
                let raw = is_raw(db, *class, args);
                let subst = Subst::for_class(db, *class, args);
                for sup in class_supertypes(db, *class).iter() {
                    queue.push_back(match sup {
                        Ty::Class(sup_class, _) if raw => Ty::class(*sup_class),
                        _ => sup.subst(&subst),
                    });
                }
            }
            Ty::TypeParam(param) => {
                for bound in type_param_bounds(db, *param).iter() {
                    queue.push_back(bound.clone());
                }
            }
            Ty::Intersection(parts) => queue.extend(parts.iter().cloned()),
            Ty::Wildcard(_) => queue.push_back(current.upper_bound(db)),
            _ => {}
        }
    }
    // 接口、数组、类型变量都以 `Object` 为父类型
    let object = Ty::object(db);
    (object.as_class() == Some(target) && ty.is_reference() && !matches!(ty, Ty::Null))
        .then_some(object)
}

fn primitive_rank(p: PrimitiveType) -> u8 {
    match p {
        PrimitiveType::Boolean => 0,
        PrimitiveType::Byte => 1,
        PrimitiveType::Short | PrimitiveType::Char => 2,
        PrimitiveType::Int => 3,
        PrimitiveType::Long => 4,
        PrimitiveType::Float => 5,
        PrimitiveType::Double => 6,
    }
}

/// 基本类型的拓宽转换（含恒等）。
pub fn primitive_widens(from: PrimitiveType, to: PrimitiveType) -> bool {
    if from == to {
        return true;
    }
    if from == PrimitiveType::Boolean || to == PrimitiveType::Boolean {
        return false;
    }
    // byte / short 不能拓宽到 char，char 也不能到 short
    if to == PrimitiveType::Char || (from == PrimitiveType::Char && to == PrimitiveType::Short) {
        return false;
    }
    primitive_rank(from) < primitive_rank(to)
}

/// 二元数值提升的结果类型。
pub fn binary_numeric_promotion(a: PrimitiveType, b: PrimitiveType) -> PrimitiveType {
    if a == PrimitiveType::Double || b == PrimitiveType::Double {
        PrimitiveType::Double
    } else if a == PrimitiveType::Float || b == PrimitiveType::Float {
        PrimitiveType::Float
    } else if a == PrimitiveType::Long || b == PrimitiveType::Long {
        PrimitiveType::Long
    } else {
        PrimitiveType::Int
    }
}

fn is_object(db: &dyn Db, class: ClassId) -> bool {
    class.binary_name(db) == "java/lang/Object"
}

pub fn is_subtype(db: &dyn Db, sub: &Ty, sup: &Ty) -> bool {
    if sub == sup {
        return true;
    }
    match (sub, sup) {
        (Ty::Unknown, _) | (_, Ty::Unknown) => true,
        (Ty::Void, _) | (_, Ty::Void) => false,
        (Ty::Primitive(a), Ty::Primitive(b)) => primitive_widens(*a, *b),
        (Ty::Primitive(_), _) | (_, Ty::Primitive(_)) => false,
        (Ty::Null, _) => true,
        // 还没推断出来的类型参数：从宽
        (_, Ty::TypeParam(_)) => true,
        (_, Ty::Intersection(parts)) => parts.iter().all(|p| is_subtype(db, sub, p)),
        (_, Ty::Wildcard(Wildcard::Unbounded)) => true,
        (_, Ty::Wildcard(Wildcard::Extends(bound))) => is_subtype(db, sub, bound),
        (_, Ty::Wildcard(Wildcard::Super(bound))) => is_subtype(db, bound, sub),
        (_, Ty::Class(class, _)) if is_object(db, *class) => true,
        (Ty::Array(a), Ty::Array(b)) => {
            if a.is_primitive() || b.is_primitive() {
                a == b
            } else {
                is_subtype(db, a, b)
            }
        }
        (Ty::Array(_), Ty::Class(class, _)) => {
            matches!(
                &*class.binary_name(db),
                "java/lang/Cloneable" | "java/io/Serializable"
            )
        }
        (_, Ty::Class(target, sup_args)) => match find_super_keeping_raw(db, sub, *target) {
            Some(found) => type_args_contained(db, found.type_args(), sup_args),
            None => false,
        },
        _ => false,
    }
}

/// 两个类型相同：结构相同，其中的类可以是同一个类在不同 jar 里的副本（javac 只按名字认类）。
fn same_type(db: &dyn Db, a: &Ty, b: &Ty) -> bool {
    if a == b {
        return true;
    }
    let all_same = |xs: &[Ty], ys: &[Ty]| {
        xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| same_type(db, x, y))
    };
    match (a, b) {
        (Ty::Class(x, xs), Ty::Class(y, ys)) => same_class(db, *x, *y) && all_same(xs, ys),
        (Ty::Array(x), Ty::Array(y)) => same_type(db, x, y),
        (Ty::Wildcard(Wildcard::Extends(x)), Ty::Wildcard(Wildcard::Extends(y)))
        | (Ty::Wildcard(Wildcard::Super(x)), Ty::Wildcard(Wildcard::Super(y))) => {
            same_type(db, x, y)
        }
        (Ty::Intersection(xs), Ty::Intersection(ys)) => all_same(xs, ys),
        _ => false,
    }
}

fn type_args_contained(db: &dyn Db, sub_args: &[Ty], sup_args: &[Ty]) -> bool {
    // 任一侧是原始类型：未经检查的转换，允许
    if sub_args.is_empty() || sup_args.is_empty() || sub_args.len() != sup_args.len() {
        return true;
    }
    sub_args
        .iter()
        .zip(sup_args)
        .all(|(sub, sup)| type_arg_contains(db, sup, sub))
}

/// 类型实参的包含关系（JLS §4.5.1）：`sup` 是否包含 `sub`。
fn type_arg_contains(db: &dyn Db, sup: &Ty, sub: &Ty) -> bool {
    match sup {
        Ty::Unknown | Ty::Wildcard(Wildcard::Unbounded) => true,
        Ty::Wildcard(Wildcard::Extends(bound)) => is_subtype(db, &sub.upper_bound(db), bound),
        Ty::Wildcard(Wildcard::Super(bound)) => match sub {
            Ty::Wildcard(Wildcard::Super(sub_bound)) => is_subtype(db, bound, sub_bound),
            Ty::Wildcard(_) => false,
            _ => is_subtype(db, bound, sub),
        },
        _ => {
            same_type(db, sub, sup)
                || sub.contains_unknown()
                || sup.contains_unknown()
                || matches!(sub, Ty::TypeParam(_))
                || matches!(sup, Ty::TypeParam(_))
        }
    }
}

/// 赋值上下文的相容性：子类型，或经装箱 / 拆箱后相容。
pub fn is_assignable(db: &dyn Db, from: &Ty, to: &Ty) -> bool {
    if is_subtype(db, from, to) {
        return true;
    }
    match (from, to) {
        (Ty::Primitive(_), _) if to.is_reference() => is_subtype(db, &from.boxed(db), to),
        (_, Ty::Primitive(target)) => from
            .unboxed(db)
            .is_some_and(|unboxed| primitive_widens(unboxed, *target)),
        _ => false,
    }
}

/// 两个类型之间"确定不兼容"的判断，用于对参数化类型报类型不匹配。
///
/// 和 [`is_subtype`] 不同，这里的 `true` 必须是确定的。两边的类型要先通过
/// [`is_plain`](Incompatibility::is_plain)：没有原始类型（未经检查的转换只是警告）、交叉类型，
/// 涉及的类的层次结构都可靠（`reliable`）。类型变量只认当前作用域里的（`in_scope`），它们是
/// 确定的类型；推断不出来的部分（`Unknown`、别处的类型参数）只允许出现在类型实参里，
/// 那个位置上不下结论，别的位置照常判断（`Function<Thread, Integer>` 确定不能交给
/// `Function<? super String, ? extends R>`，不管 `R` 是什么）。
pub struct Incompatibility<'a> {
    db: &'a dyn Db,
    reliable: &'a dyn Fn(ClassId) -> bool,
    in_scope: &'a dyn Fn(hir_def::TypeParamId) -> bool,
    inferred: &'a dyn Fn(hir_def::TypeParamId) -> Option<Vec<Ty>>,
}

fn not_inferred(_: hir_def::TypeParamId) -> Option<Vec<Ty>> {
    None
}

impl<'a> Incompatibility<'a> {
    pub fn new(
        db: &'a dyn Db,
        reliable: &'a dyn Fn(ClassId) -> bool,
        in_scope: &'a dyn Fn(hir_def::TypeParamId) -> bool,
    ) -> Self {
        Incompatibility {
            db,
            reliable,
            in_scope,
            inferred: &not_inferred,
        }
    }

    /// 被调用方法的类型变量由这一个实参推断：`inferred` 对这样的变量给出代换后的声明上界，
    /// 拿不准的给空表（不下结论），已经固定的变量给 `None`。只影响捕获变量对 `? super K1` 的判断。
    pub fn with_inferred(
        mut self,
        inferred: &'a dyn Fn(hir_def::TypeParamId) -> Option<Vec<Ty>>,
    ) -> Self {
        self.inferred = inferred;
        self
    }

    /// 类型可以拿来下结论（见类型本身的说明）。
    pub fn is_plain(&self, ty: &Ty) -> bool {
        self.plain(ty, false)
    }

    fn plain(&self, ty: &Ty, in_args: bool) -> bool {
        match ty {
            Ty::Class(class, args) => {
                (self.reliable)(*class)
                    && !is_raw(self.db, *class, args)
                    && hir_def::class_header(self.db, *class)
                        .is_some_and(|d| d.type_params.len() == args.len())
                    && args.iter().all(|a| self.plain(a, true))
            }
            Ty::Array(element) => match &**element {
                Ty::Primitive(_) => true,
                other => self.plain(other, in_args),
            },
            Ty::Wildcard(Wildcard::Unbounded) => in_args,
            Ty::Wildcard(Wildcard::Extends(bound) | Wildcard::Super(bound)) => {
                in_args && self.plain(bound, true)
            }
            Ty::TypeParam(param) => in_args || (self.in_scope)(*param),
            Ty::Unknown => in_args,
            _ => false,
        }
    }

    /// 推断不出来的部分：`Unknown`，或者不在作用域里的类型参数（多半是没推断出来的方法类型参数）。
    fn is_unknown(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Unknown => true,
            Ty::TypeParam(param) => !(self.in_scope)(*param),
            _ => false,
        }
    }

    /// `from` 类型的值确定不能在赋值上下文里交给 `to`。两边都必须是引用类型并且 [`plain`]。
    ///
    /// [`plain`]: Incompatibility::is_plain
    pub fn not_assignable(&self, from: &Ty, to: &Ty) -> bool {
        self.is_plain(from) && self.is_plain(to) && self.not_subtype(from, to, 0)
    }

    /// 类型变量的上界（没写时是 `Object`）。
    fn bounds_of(&self, param: hir_def::TypeParamId) -> Vec<Ty> {
        let bounds = type_param_bounds(self.db, param);
        if bounds.is_empty() {
            vec![Ty::object(self.db)]
        } else {
            bounds.to_vec()
        }
    }

    /// `sub` 确定不是 `sup` 的子类型（两边都已检查过 [`plain`](Incompatibility::is_plain)）。
    fn not_subtype(&self, sub: &Ty, sup: &Ty, depth: u32) -> bool {
        // 递归的类型（`Enum<E extends Enum<E>>` 一类）不深究
        if depth > 8 || self.is_unknown(sub) || self.is_unknown(sup) {
            return false;
        }
        let db = self.db;
        match (sub, sup) {
            (Ty::TypeParam(a), Ty::TypeParam(b)) if a == b => false,
            // 类型变量是它的某个上界的子类型时才可能是 `sup` 的子类型
            (Ty::TypeParam(a), _) => self
                .bounds_of(*a)
                .iter()
                .all(|bound| self.is_plain(bound) && self.not_subtype(bound, sup, depth + 1)),
            // 具体的类型不是任何类型变量的子类型
            (Ty::Class(..) | Ty::Array(_), Ty::TypeParam(_)) => true,
            (Ty::Array(a), Ty::Array(b)) => match (&**a, &**b) {
                (a, b) if self.is_unknown(a) || self.is_unknown(b) => false,
                (Ty::Primitive(x), Ty::Primitive(y)) => x != y,
                (Ty::Primitive(_), _) | (_, Ty::Primitive(_)) => true,
                (a, b) => self.not_subtype(a, b, depth + 1),
            },
            (Ty::Array(_), Ty::Class(class, _)) => !matches!(
                &*class.binary_name(db),
                "java/lang/Object" | "java/lang/Cloneable" | "java/io/Serializable"
            ),
            (Ty::Class(..), Ty::Array(_)) => true,
            (Ty::Class(sub_class, sub_args), Ty::Class(target, sup_args)) => {
                if is_object(db, *target) {
                    return false;
                }
                // 先在泛型形式上找到 `target`，再代换：这样能分辨出哪些实参是由通配符捕获来的
                let generic = crate::lower::this_ty(db, *sub_class);
                let Some(lifted) = find_super_keeping_raw(db, &generic, *target) else {
                    return true;
                };
                if sup_args.is_empty() {
                    return false;
                }
                // 继承链上经过了原始类型
                if lifted.type_args().len() != sup_args.len() {
                    return false;
                }
                let subst = Subst::for_class(db, *sub_class, sub_args);
                let owner = hir_def::GenericOwner::Class(*sub_class);
                lifted
                    .type_args()
                    .iter()
                    .zip(sup_args.iter())
                    .any(|(arg, sup_arg)| {
                        // 直接是被捕获的通配符：当作一个新的类型变量（捕获变量）
                        if let Ty::TypeParam(param) = arg {
                            if param.owner == owner {
                                if let Some(w @ Ty::Wildcard(_)) = sub_args.get(param.idx as usize)
                                {
                                    return self.capture_not_contained(*param, w, sup_arg, depth);
                                }
                            }
                        }
                        // 捕获变量出现在更深的位置（`Map<K, List<V>>` 里的 `V`）：不深究。
                        // 提到别的类的类型参数（内部类的父类型用到外层类的类型参数，具体是哪个
                        // 实例化不知道）也不深究
                        let foreign = arg.mentions_params_where(&|param| {
                            param.owner != owner
                                || matches!(sub_args.get(param.idx as usize), Some(Ty::Wildcard(_)))
                        });
                        let actual = arg.subst(&subst);
                        if foreign || !self.plain(&actual, true) {
                            return false;
                        }
                        self.not_contained(sup_arg, &actual, depth)
                    })
            }
            _ => false,
        }
    }

    /// 类型实参 `sup_arg` 确定不包含（JLS §4.5.1）具体的类型实参 `actual`（不是捕获变量）。
    fn not_contained(&self, sup_arg: &Ty, actual: &Ty, depth: u32) -> bool {
        if self.is_unknown(sup_arg) || self.is_unknown(actual) {
            return false;
        }
        match sup_arg {
            Ty::Wildcard(Wildcard::Unbounded) => false,
            Ty::Wildcard(Wildcard::Extends(bound)) => self.not_subtype(actual, bound, depth + 1),
            Ty::Wildcard(Wildcard::Super(bound)) => self.not_subtype(bound, actual, depth + 1),
            _ => self.certainly_different(sup_arg, actual),
        }
    }

    /// 捕获变量（来自 `sub` 的第 `param` 个类型实参，通配符 `wildcard`）确定不被 `sup_arg` 包含。
    fn capture_not_contained(
        &self,
        param: hir_def::TypeParamId,
        wildcard: &Ty,
        sup_arg: &Ty,
        depth: u32,
    ) -> bool {
        if self.is_unknown(sup_arg) {
            return false;
        }
        match sup_arg {
            Ty::Wildcard(Wildcard::Unbounded) => false,
            // 交叉类型是 `S` 的子类型只要有一个成员是，所以每个上界都确定不是 `S` 的子类型才算
            Ty::Wildcard(Wildcard::Extends(bound)) => {
                self.capture_uppers(param, wildcard).is_some_and(|uppers| {
                    uppers
                        .iter()
                        .all(|upper| self.not_subtype(upper, bound, depth + 1))
                })
            }
            // 只有 `? super L` 捕获出来的变量有下界
            Ty::Wildcard(Wildcard::Super(bound)) => match (wildcard, &**bound) {
                (Ty::Wildcard(Wildcard::Super(lower)), _) => {
                    self.not_subtype(bound, lower, depth + 1)
                }
                // 界是只由这个实参推断的方法类型变量 `K1`：JLS 18.2.3 得到 `K1 <: CAP`，取
                // `K1 = CAP` 就适用，除非捕获变量确定不满足 `K1` 的声明上界（javac 拒绝
                // `<K1 extends String>` 收 `Consumer<?>`）
                (_, Ty::TypeParam(k1)) => match (self.inferred)(*k1) {
                    Some(declared) => self.capture_uppers(param, wildcard).is_some_and(|uppers| {
                        declared.iter().any(|d| {
                            self.is_plain(d)
                                && uppers.iter().all(|u| self.not_subtype(u, d, depth + 1))
                        })
                    }),
                    None => true,
                },
                _ => true,
            },
            // 捕获变量是一个新的类型，不等于任何具体类型。但 javac 把 `? super T` 捕获出来、
            // 上下界相同的变量当成 `T` 本身（`ListCellRenderer<? super Object>` 能赋给
            // `ListCellRenderer<Object>`），这种情形不下结论
            _ => match wildcard {
                Ty::Wildcard(Wildcard::Super(lower)) if **lower == *sup_arg => {
                    match type_param_bounds(self.db, param).as_slice() {
                        [] => lower.as_class().is_some_and(|c| !is_object(self.db, c)),
                        [bound] if self.is_plain(bound) => *bound != **lower,
                        _ => false,
                    }
                }
                _ => true,
            },
        }
    }

    /// 捕获变量的上界：通配符的界和类型参数声明的上界（的交）。上界提到了类型参数
    /// （`T extends Comparable<T>`）时代换出来的是捕获变量，不深究，给 `None`。
    fn capture_uppers(&self, param: hir_def::TypeParamId, wildcard: &Ty) -> Option<Vec<Ty>> {
        let mut uppers: Vec<Ty> = Vec::new();
        if let Ty::Wildcard(Wildcard::Extends(w)) = wildcard {
            uppers.push((**w).clone());
        }
        for declared in type_param_bounds(self.db, param).iter() {
            if crate::method_resolution::mentions_type_param(declared) || !self.is_plain(declared) {
                return None;
            }
            uppers.push(declared.clone());
        }
        if uppers.is_empty() {
            uppers.push(Ty::object(self.db));
        }
        Some(uppers)
    }

    /// 两个具体的类型实参确定不是同一个类型。通配符之间的比较拿不准（`?` 和 `? extends Object`
    /// 等价），只在别的位置能分出不同时下结论。
    fn certainly_different(&self, a: &Ty, b: &Ty) -> bool {
        if self.is_unknown(a) || self.is_unknown(b) {
            return false;
        }
        match (a, b) {
            (Ty::TypeParam(x), Ty::TypeParam(y)) => x != y,
            (Ty::TypeParam(_), Ty::Class(..) | Ty::Array(_) | Ty::Primitive(_))
            | (Ty::Class(..) | Ty::Array(_) | Ty::Primitive(_), Ty::TypeParam(_)) => true,
            (Ty::Class(x, xs), Ty::Class(y, ys)) => {
                !same_class(self.db, *x, *y)
                    || xs.len() == ys.len()
                        && xs.iter().zip(ys.iter()).any(|(p, q)| {
                            !p.is_wildcard() && !q.is_wildcard() && self.certainly_different(p, q)
                        })
            }
            (Ty::Array(x), Ty::Array(y)) => self.certainly_different(x, y),
            (Ty::Primitive(x), Ty::Primitive(y)) => x != y,
            (Ty::Array(_), Ty::Class(..)) | (Ty::Class(..), Ty::Array(_)) => true,
            (Ty::Primitive(_), Ty::Class(..) | Ty::Array(_))
            | (Ty::Class(..) | Ty::Array(_), Ty::Primitive(_)) => true,
            _ => false,
        }
    }
}

/// 几个类型的最小上界（JLS §4.10.4），只在结果确定是单个类型时给出：其中一个是其余所有的
/// 父类型，或者擦除后的公共父类型里只有一个最具体的、并且它不是泛型类（不用推类型实参）。
/// 结果是交集类型、继承链不全、有未知类型时返回 `Unknown`。
pub fn lub(db: &dyn Db, tys: &[Ty]) -> Ty {
    if tys.is_empty() || tys.iter().any(Ty::contains_unknown) {
        return Ty::Unknown;
    }
    if let Some(top) = tys
        .iter()
        .find(|top| tys.iter().all(|ty| is_subtype(db, ty, top)))
    {
        return top.clone();
    }
    let mut classes = Vec::with_capacity(tys.len());
    for ty in tys {
        let Ty::Class(class, _) = ty else {
            return Ty::Unknown;
        };
        classes.push(*class);
    }
    let with_supers = |class: ClassId| {
        let mut res = hir_def::all_supers(db, class).to_vec();
        res.push(class);
        res
    };
    // 继承链上有解析不了的父类型时，公共父类型可能少算
    let resolved = |class: ClassId| {
        hir_def::class_header(db, class).is_some_and(|data| {
            data.superclass.iter().count() + data.interfaces.len()
                == class_supertypes(db, class).len()
        })
    };
    if !classes
        .iter()
        .all(|&class| with_supers(class).into_iter().all(resolved))
    {
        return Ty::Unknown;
    }
    let common: Vec<ClassId> = with_supers(classes[0])
        .into_iter()
        .filter(|&sup| {
            classes
                .iter()
                .all(|&class| hir_def::is_subclass_of(db, class, sup))
        })
        .collect();
    let mut minimal = common.iter().copied().filter(|&sup| {
        !common
            .iter()
            .any(|&other| other != sup && hir_def::is_subclass_of(db, other, sup))
    });
    match (minimal.next(), minimal.next()) {
        (Some(only), None)
            if hir_def::class_header(db, only).is_some_and(|data| data.type_params.is_empty()) =>
        {
            Ty::class(only)
        }
        _ => Ty::Unknown,
    }
}
