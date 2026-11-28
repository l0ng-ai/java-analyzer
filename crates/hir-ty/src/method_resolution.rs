//! 重载决议（JLS §15.12.2）与方法类型参数的推断。
//!
//! 三个阶段依次尝试：严格调用（只允许子类型）→ 宽松调用（允许装箱 / 拆箱）→ 可变参数调用。
//! 某个阶段有适用的候选就在该阶段内选最具体的那个。
//!
//! 类型参数推断只实现了 JLS §18 的常见形态：由实参向形参做结构化的合一，
//! lambda / 方法引用的实参延后处理，最后用期望类型补全返回类型里剩下的变量。
//! 推断不出来的变量变成 `Unknown`，不报错。由实参推出的绑定确定违反声明的上界时，候选不适用。

use std::sync::Arc;

use base_db::Db;
use hir_def::{GenericOwner, MethodId, TypeParamId};

use crate::{
    lower::{method_sig, type_param_bounds, MethodSig},
    members::{functional_method, MethodCandidate},
    subtype::{find_super, find_super_keeping_raw, is_assignable, is_subtype},
    ty::{Subst, Ty},
};

/// 一个实参在重载决议时提供的信息。
#[derive(Clone, Debug)]
pub enum Arg {
    Ty(Ty),
    /// lambda：只知道形参个数和体的形状，类型要等选定方法之后才能推
    Lambda {
        arity: usize,
        /// 形参都没写类型（`x -> ...`）。零个形参的 lambda 按显式类型算
        implicit: bool,
        /// 体可能与 void 的函数类型兼容（语句表达式，或没有 `return 值;` 的块）
        void_compatible: bool,
        /// 体可能与有返回值的函数类型兼容（表达式，或只有 `return 值;` 的块）
        value_compatible: bool,
    },
    /// 方法引用。`arities`：它能匹配的函数类型形参个数 `(n, 可变参数)`，可变参数时不少于 `n`
    /// 的都行；不知道时是 `None`
    MethodRef {
        arities: Option<Vec<(usize, bool)>>,
    },
}

/// 合一的上下文：哪些类型参数是待推断的，以及目前推出的绑定。
#[derive(Clone, Debug)]
pub struct Inference {
    pub owners: Vec<GenericOwner>,
    pub bindings: Subst,
    /// 由通配符实参（`Class<?>`、`List<? extends T>`）近似得到的绑定：真实的类型是捕获变量，
    /// 不能拿来下"违反上界"之类的结论
    pub approximate: Vec<TypeParamId>,
    /// 由原始类型（或父类型链上经过原始类型的类型）的实参得到的绑定：真实的推断里它只是下界，
    /// 目标类型可以把变量定成它的参数化父类型（`T data` 接收 `new TreeList()`，目标要求
    /// `T = List<String>`，靠未经检查的转换适用）
    pub from_raw: Vec<TypeParamId>,
}

impl Inference {
    pub fn new(owners: Vec<GenericOwner>) -> Inference {
        Inference {
            owners,
            bindings: Subst::empty(),
            approximate: Vec::new(),
            from_raw: Vec::new(),
        }
    }

    fn is_inferable(&self, param: TypeParamId) -> bool {
        self.owners.contains(&param.owner) && !self.bindings.contains(param)
    }

    /// 实参给出的绑定能否写入：还没有绑定，或者现有的绑定只是 `Object`
    /// （多半来自 `Class<?>` 这类不带信息的实参）或者还不完整，后面更具体的实参可以覆盖它。
    fn can_bind_from_arg(&self, db: &dyn Db, param: TypeParamId) -> bool {
        self.owners.contains(&param.owner)
            && self
                .bindings
                .get(param)
                .is_none_or(|bound| *bound == Ty::object(db) || bound.contains_unknown())
    }

    /// 让形参类型 `formal` 去匹配实参类型 `actual`，记录由此得到的类型参数绑定。
    pub fn unify(&mut self, db: &dyn Db, formal: &Ty, actual: &Ty) {
        if matches!(actual, Ty::Unknown | Ty::Null) {
            return;
        }
        match formal {
            Ty::TypeParam(param) => {
                if self.can_bind_from_arg(db, *param) {
                    // 类型实参不能是基本类型；通配符取它的界来近似捕获转换
                    self.bindings
                        .set(*param, actual.wildcard_bound(db).boxed(db));
                    if matches!(actual, Ty::Wildcard(_)) {
                        if !self.approximate.contains(param) {
                            self.approximate.push(*param);
                        }
                    } else {
                        self.approximate.retain(|p| p != param);
                    }
                    if crate::subtype::involves_raw(db, actual) {
                        if !self.from_raw.contains(param) {
                            self.from_raw.push(*param);
                        }
                    } else {
                        self.from_raw.retain(|p| p != param);
                    }
                }
            }
            Ty::Wildcard(_) => {
                // `?` 不提供任何信息
                if matches!(actual, Ty::Wildcard(crate::ty::Wildcard::Unbounded)) {
                    return;
                }
                let bound = formal.wildcard_bound(db);
                self.unify(db, &bound, &actual.wildcard_bound(db));
            }
            Ty::Array(formal_element) => {
                if let Ty::Array(actual_element) = actual {
                    self.unify(db, formal_element, actual_element);
                }
            }
            Ty::Class(class, formal_args) if !formal_args.is_empty() => {
                let actual = actual.boxed(db);
                // 经过原始类型才到达 `class`（`List<T>` 收原始的 `ArrayList`）：调用靠未经检查的
                // 转换适用，这个实参不约束类型参数（JLS §18.2.2）。擦除出来的类型实参（`Object`）
                // 不能拿来推断，否则会误判违反上界（`Collections.sort(rawList)`）
                let via_raw = find_super_keeping_raw(db, &actual, *class)
                    .is_some_and(|lifted| lifted.type_args().is_empty());
                if via_raw {
                    return;
                }
                if let Some(found) = find_super(db, &actual, *class) {
                    for (formal_arg, actual_arg) in formal_args.iter().zip(found.type_args()) {
                        self.unify(db, formal_arg, actual_arg);
                    }
                }
            }
            _ => {}
        }
    }

    /// 把已经绑定的类型参数代进它声明的上界，推出只出现在上界里的类型参数：
    /// `<T, F extends Future<T>> Callable<T> decorate(Supplier<F>)` 收
    /// `Supplier<CompletableFuture<String>>` 时，`F` 定下来之后由 `F <: Future<T>` 得出 `T = String`。
    pub fn incorporate_bounds(&mut self, db: &dyn Db, receiver_subst: &Subst) {
        // 上界链（`<A, B extends List<A>, C extends List<B>>`）一轮推出一层
        for _ in 0..3 {
            let bound: Vec<(TypeParamId, Ty)> = self
                .bindings
                .iter()
                .filter(|(id, ty)| self.owners.contains(&id.owner) && !ty.contains_unknown())
                .map(|(id, ty)| (id, ty.clone()))
                .collect();
            let before = self.bindings.clone();
            for (param, binding) in bound {
                for declared in type_param_bounds(db, param).iter() {
                    let declared = declared.subst(receiver_subst);
                    if !self
                        .owners
                        .iter()
                        .any(|owner| declared.mentions_params_of(*owner))
                    {
                        continue;
                    }
                    let known: Vec<TypeParamId> = self.bindings.iter().map(|(id, _)| id).collect();
                    self.unify(db, &declared, &binding);
                    // 由近似的绑定推出来的也是近似的
                    if self.approximate.contains(&param) {
                        for (id, _) in self.bindings.iter() {
                            if !known.contains(&id) && !self.approximate.contains(&id) {
                                self.approximate.push(id);
                            }
                        }
                    }
                }
            }
            if self.bindings == before {
                break;
            }
        }
    }

    /// 绑定成 `ty`、而且来自原始类型实参的类型参数。
    fn raw_bound_by(&self, ty: &Ty) -> Option<TypeParamId> {
        self.from_raw
            .iter()
            .copied()
            .find(|param| self.bindings.get(*param) == Some(ty))
    }

    /// 反方向：用期望类型去确定 `ty`（通常是返回类型）里还没绑定的变量。
    pub fn unify_with_expected(&mut self, db: &dyn Db, ty: &Ty, expected: &Ty) {
        if matches!(expected, Ty::Unknown) {
            return;
        }
        match ty {
            Ty::TypeParam(param) => {
                let bound = expected.wildcard_bound(db);
                if self.is_inferable(*param) && !bound.contains_unknown() {
                    self.bindings.insert(*param, bound.boxed(db));
                }
            }
            // 由原始类型的实参绑定的变量：目标类型是它（擦除后的）父类型时以目标为准
            Ty::Class(..) if self.raw_bound_by(ty).is_some() => {
                let Some(param) = self.raw_bound_by(ty) else {
                    return;
                };
                let bound = expected.wildcard_bound(db);
                if !bound.contains_unknown()
                    && matches!(bound, Ty::Class(..))
                    && is_subtype(db, &ty.erasure(db), &bound.erasure(db))
                {
                    self.bindings.set(param, bound);
                    self.from_raw.retain(|p| *p != param);
                }
            }
            Ty::Array(element) => {
                if let Ty::Array(expected_element) = expected {
                    self.unify_with_expected(db, element, expected_element);
                }
            }
            Ty::Class(class, args) if !args.is_empty() => {
                // 把 `ty` 向上转成期望类型的那个类，再逐个实参对齐。
                // 此时 `ty` 的实参里还带着未绑定的类型参数，代换会原样保留它们。
                if let Ty::Class(expected_class, expected_args) = expected {
                    let lifted = if class == expected_class {
                        Some(ty.clone())
                    } else {
                        find_super(db, ty, *expected_class)
                    };
                    if let Some(lifted) = lifted {
                        for (arg, expected_arg) in
                            lifted.type_args().iter().zip(expected_args.iter())
                        {
                            self.unify_with_expected(db, arg, expected_arg);
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// 重载决议的结果。
#[derive(Clone, Debug)]
pub struct Call {
    pub method: MethodId,
    pub sig: Arc<MethodSig>,
    /// 接收者带来的代换（声明类的类型参数）
    pub receiver_subst: Subst,
    /// 方法（以及菱形构造时的类）的类型参数推断状态
    pub inference: Inference,
    /// 是否按可变参数展开的形式调用
    pub varargs_expanded: bool,
    /// 没有任何候选适用，这是按参数个数挑的"最像"的一个
    pub applicable: bool,
    /// 能确定调用有歧义时，另一个同样适用、又不比选中者更不具体的候选
    pub ambiguous: Option<MethodId>,
}

impl Call {
    /// 第 `arg_idx` 个实参对应的形参类型（已应用目前所有的代换）。
    pub fn param_ty(&self, arg_idx: usize) -> Ty {
        let n = self.sig.params.len();
        if n == 0 {
            return Ty::Unknown;
        }
        let raw = if self.varargs_expanded && arg_idx >= n - 1 {
            match &self.sig.params[n - 1] {
                Ty::Array(element) => (**element).clone(),
                other => other.clone(),
            }
        } else {
            match self.sig.params.get(arg_idx) {
                Some(ty) => ty.clone(),
                None => return Ty::Unknown,
            }
        };
        raw.subst(&self.receiver_subst)
            .subst(&self.inference.bindings)
    }

    /// 和 [`Call::param_ty`] 一样，但由通配符实参近似出来的类型参数代换成通配符本身：
    /// `<T> T getBean(Class<T>)` 收 `Class<? extends Gen>` 时 `T` 记成 `Gen`，形参是 `Class<Gen>`，
    /// 实参不是它的子类型；按捕获转换，`T` 是上界为 `Gen` 的捕获变量，形参看作
    /// `Class<? extends Gen>` 时才对得上。
    pub fn param_ty_capturing(&self, arg_idx: usize) -> Ty {
        let mut bindings = self.inference.bindings.clone();
        for param in &self.inference.approximate {
            if let Some(bound) = bindings.get(*param).cloned() {
                bindings.set(
                    *param,
                    Ty::Wildcard(crate::ty::Wildcard::Extends(Arc::new(bound))),
                );
            }
        }
        raw_param(self, arg_idx)
            .subst(&self.receiver_subst)
            .subst(&bindings)
    }

    /// 第 `arg_idx` 个实参对应的形参类型：只代换接收者带来的类型参数，方法自己的类型参数原样保留。
    pub fn formal_param_ty(&self, arg_idx: usize) -> Ty {
        raw_param(self, arg_idx).subst(&self.receiver_subst)
    }

    /// 第 `arg_idx` 个实参的类型在选定方法之后才变得更精确时，用它重新约束类型参数。
    pub fn refine_arg(&mut self, db: &dyn Db, arg_idx: usize, actual: &Ty) {
        let formal = raw_param(self, arg_idx).subst(&self.receiver_subst);
        self.inference.unify(db, &formal, actual);
    }

    /// 返回类型。`expected` 用来确定只出现在返回类型里的类型参数；仍未确定的变成 `Unknown`。
    pub fn return_ty(&mut self, db: &dyn Db, expected: Option<&Ty>) -> Ty {
        // 实参（lambda 的返回值等）在选定方法之后还可能补充绑定
        self.inference.incorporate_bounds(db, &self.receiver_subst);
        let ret = self.sig.ret.subst(&self.receiver_subst);
        self.finish_ty(db, &ret, expected)
    }

    /// 没有目标类型时的返回类型：还没定下来的方法类型参数取它声明的上界（不是 `Object`、
    /// 也不引用其它没定下来的类型参数时），例如 `<T extends S> T value(...)` 取 `S`。
    /// 只用在结果被当作接收者的地方，让后面的成员查找能继续，不拿它做类型检查。
    pub fn return_ty_by_bounds(&self, db: &dyn Db) -> Option<Ty> {
        let owner = GenericOwner::Method(self.method);
        let mut bindings = self.inference.bindings.clone();
        for idx in 0..self.sig.n_type_params {
            let id = TypeParamId { owner, idx };
            if bindings.contains(id) {
                continue;
            }
            let Some(bound) = type_param_bounds(db, id).first().cloned() else {
                continue;
            };
            let bound = bound
                .subst(&self.receiver_subst)
                .subst(&bindings)
                .upper_bound(db)
                .erase_params_of(owner);
            let is_object = matches!(&bound, Ty::Class(class, _) if class.binary_name(db) == "java/lang/Object");
            if !bound.contains_unknown() && !is_object {
                bindings.insert(id, bound);
            }
        }
        let mut res = self.sig.ret.subst(&self.receiver_subst).subst(&bindings);
        for owner in &self.inference.owners {
            res = res.erase_params_of(*owner);
        }
        (!res.contains_unknown()).then_some(res)
    }

    /// 没有目标类型的调用（结果被当作接收者、作为 `var` 的初始值或者不被使用）里，`ty`
    /// 定下来的类型：和 javac 一样，形参里没出现过（因此只能由目标类型确定）的类型参数取它
    /// 声明的上界，没有上界时取 `Object`（`List.of()` 是 `List<Object>`，`new ArrayList<>()`
    /// 是 `ArrayList<Object>`）。`n_args` 是实参个数，可变参数展开后没有对应实参的形参不算。
    pub fn finish_standalone(&self, db: &dyn Db, ty: &Ty, n_args: usize) -> Ty {
        let mut inference = self.inference.clone();
        inference.incorporate_bounds(db, &self.receiver_subst);
        let mut bindings = inference.bindings;
        let formals: Vec<Ty> = (0..n_args).map(|idx| raw_param(self, idx)).collect();
        for owner in &self.inference.owners {
            for idx in 0..n_type_params_of(db, *owner, &self.sig) {
                let id = TypeParamId { owner: *owner, idx };
                if bindings.contains(id)
                    || formals
                        .iter()
                        .any(|formal| formal.mentions_params_where(&|p| p == id))
                {
                    continue;
                }
                let bounds = type_param_bounds(db, id);
                let mut parts = Vec::new();
                for bound in bounds.iter() {
                    let bound = bound.subst(&self.receiver_subst).subst(&bindings);
                    if bound.contains_unknown()
                        || self
                            .inference
                            .owners
                            .iter()
                            .any(|owner| bound.mentions_params_of(*owner))
                    {
                        parts.clear();
                        break;
                    }
                    parts.push(bound);
                }
                let filled = match (bounds.is_empty(), parts.len()) {
                    (true, _) => Ty::object(db),
                    (false, 0) => continue,
                    (false, 1) => parts.pop().unwrap_or_else(|| Ty::object(db)),
                    (false, _) => Ty::Intersection(parts.into()),
                };
                bindings.insert(id, filled);
            }
        }
        let mut res = ty.subst(&self.receiver_subst).subst(&bindings);
        for owner in &self.inference.owners {
            res = res.erase_params_of(*owner);
        }
        res
    }

    /// 用当前的推断状态把任意一个类型定下来（菱形构造用它来算 `new Foo<>()` 的类型）。
    pub fn finish_ty(&mut self, db: &dyn Db, ty: &Ty, expected: Option<&Ty>) -> Ty {
        if let Some(expected) = expected {
            let partially = ty.subst(&self.inference.bindings);
            self.inference.unify_with_expected(db, &partially, expected);
        }
        let mut res = ty.subst(&self.inference.bindings);
        for owner in &self.inference.owners {
            res = res.erase_params_of(*owner);
        }
        res
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Phase {
    Strict,
    Loose,
    Varargs,
}

struct Scored {
    call: Call,
    phase: Phase,
    /// 代换后的形参类型，用来比较"谁更具体"
    params: Vec<Ty>,
}

/// 在候选里选出要调用的方法。
///
/// - `extra_owners`：除方法自身之外也待推断的类型参数所有者（菱形构造时是被构造的类）。
/// - `explicit_type_args`：`obj.<String>foo()` 里显式给出的类型实参。
pub fn resolve_call(
    db: &dyn Db,
    candidates: &[MethodCandidate],
    args: &[Arg],
    explicit_type_args: &[Ty],
    extra_owners: &[GenericOwner],
) -> Option<Call> {
    let mut scored: Vec<Scored> = Vec::new();
    let mut fallback: Option<Call> = None;
    let mut fallback_arity_matches = false;

    for candidate in candidates {
        let sig = method_sig(db, candidate.id);
        let method_owner = GenericOwner::Method(candidate.id);
        let mut owners = vec![method_owner];
        owners.extend_from_slice(extra_owners);

        let n = sig.params.len();
        let fixed_arity = args.len() == n;
        let variable_arity = sig.varargs && n > 0 && args.len() >= n - 1;

        let make_call = |varargs_expanded: bool| -> Call {
            let mut inference = Inference::new(owners.clone());
            if explicit_type_args.len() == sig.n_type_params as usize {
                for (idx, ty) in explicit_type_args.iter().enumerate() {
                    inference.bindings.insert(
                        TypeParamId {
                            owner: method_owner,
                            idx: idx as u32,
                        },
                        ty.clone(),
                    );
                }
            }
            let mut call = Call {
                method: candidate.id,
                sig: sig.clone(),
                receiver_subst: candidate.subst.clone(),
                inference,
                varargs_expanded,
                applicable: true,
                ambiguous: None,
            };
            for (idx, arg) in args.iter().enumerate() {
                if let Arg::Ty(arg_ty) = arg {
                    let formal = raw_param(&call, idx).subst(&call.receiver_subst);
                    call.inference.unify(db, &formal, arg_ty);
                }
            }
            call.inference.incorporate_bounds(db, &call.receiver_subst);
            call
        };

        // 兜底候选：优先选参数个数对得上的第一个
        let arity_matches = fixed_arity || variable_arity;
        if fallback.is_none() || (arity_matches && !fallback_arity_matches) {
            fallback = Some(make_call(variable_arity && !fixed_arity));
            fallback_arity_matches = arity_matches;
        }

        if fixed_arity {
            let call = make_call(false);
            let bounds_ok = bounds_satisfied(db, &call);
            let strict = bounds_ok && args_applicable(db, &call, args, false);
            let loose = strict || (bounds_ok && args_applicable(db, &call, args, true));
            if loose {
                let params = (0..args.len()).map(|i| call.param_ty(i)).collect();
                let phase = if strict { Phase::Strict } else { Phase::Loose };
                scored.push(Scored {
                    call,
                    phase,
                    params,
                });
                continue;
            }
        }
        if variable_arity {
            let call = make_call(true);
            if bounds_satisfied(db, &call) && args_applicable(db, &call, args, true) {
                let params = (0..args.len().max(n)).map(|i| call.param_ty(i)).collect();
                scored.push(Scored {
                    call,
                    phase: Phase::Varargs,
                    params,
                });
            }
        }
    }

    let best_phase = scored.iter().map(|s| s.phase).min();
    if let Some(best_phase) = best_phase {
        let in_phase: Vec<&Scored> = scored.iter().filter(|s| s.phase == best_phase).collect();
        let most_specific = in_phase.iter().find(|candidate| {
            in_phase.iter().all(|other| {
                std::ptr::eq(**candidate, *other)
                    || candidate.call.method == other.call.method
                    || more_specific(db, candidate, other, args)
            })
        });
        return Some(match most_specific {
            Some(best) => best.call.clone(),
            None => {
                let mut call = in_phase[0].call.clone();
                call.ambiguous = certain_ambiguity(db, &in_phase, args, best_phase);
                if let Some(other) = call.ambiguous {
                    // 报告时把两个互不更具体的候选都点出来：选中的那个得是极大的
                    if let Some(first) = maximal(db, &in_phase, args)
                        .into_iter()
                        .find(|s| s.call.method != other)
                    {
                        call = first.call.clone();
                        call.ambiguous = Some(other);
                    }
                } else {
                    // 实参类型不知道、选不出来时，返回类型不一样的候选之间没法定：结果当作未知，
                    // 免得按随便挑的那个往下报类型不匹配
                    let candidates = maximal(db, &in_phase, args);
                    let rets_differ = candidates.first().is_some_and(|first| {
                        candidates
                            .iter()
                            .any(|s| s.call.sig.ret != first.call.sig.ret)
                    });
                    if rets_differ {
                        let mut sig = (*call.sig).clone();
                        sig.ret = Ty::Unknown;
                        call.sig = Arc::new(sig);
                    }
                }
                call
            }
        });
    }

    // 没有适用的候选：返回参数个数最接近的一个，让跳转、悬停等功能仍然可用
    fallback.map(|call| Call {
        applicable: false,
        ..call
    })
}

pub(crate) fn mentions_type_param(ty: &Ty) -> bool {
    match ty {
        Ty::TypeParam(_) => true,
        Ty::Class(_, args) | Ty::Intersection(args) => args.iter().any(mentions_type_param),
        Ty::Array(element) => mentions_type_param(element),
        Ty::Wildcard(crate::ty::Wildcard::Extends(bound) | crate::ty::Wildcard::Super(bound)) => {
            mentions_type_param(bound)
        }
        _ => false,
    }
}

/// 方法自己的类型参数目前的绑定是否满足声明的上界（`<T extends Number>`）。
///
/// 绑定或上界里有推断不出来的部分、绑定本身是（外层的）类型变量、绑定是由通配符实参近似
/// 得到的时候从宽，视为满足。
fn bounds_satisfied(db: &dyn Db, call: &Call) -> bool {
    bound_violation(db, call).is_none()
}

/// 第一个确定违反上界的类型参数：`(绑定, 代换后的上界)`。
fn bound_violation(db: &dyn Db, call: &Call) -> Option<(Ty, Ty)> {
    let owner = GenericOwner::Method(call.method);
    (0..call.sig.n_type_params).find_map(|idx| {
        let param = TypeParamId { owner, idx };
        if call.inference.approximate.contains(&param) {
            return None;
        }
        let binding = call.inference.bindings.get(param)?;
        if binding.contains_unknown() || mentions_type_param(binding) {
            return None;
        }
        type_param_bounds(db, param).iter().find_map(|bound| {
            let bound = bound
                .subst(&call.receiver_subst)
                .subst(&call.inference.bindings);
            let unclear = bound.contains_unknown()
                || call
                    .inference
                    .owners
                    .iter()
                    .any(|owner| bound.mentions_params_of(*owner));
            (!unclear && !is_subtype(db, binding, &bound)).then(|| (binding.clone(), bound))
        })
    })
}

/// 按实参推出的类型参数确定违反了上界，因而这个候选确定不适用：
/// 参数个数固定且对得上，实参都是已知类型，违反上界的绑定和上界里都没有类型变量。
pub fn certainly_violates_bounds(db: &dyn Db, candidate: &MethodCandidate, args: &[Arg]) -> bool {
    let sig = method_sig(db, candidate.id);
    if sig.n_type_params == 0 || sig.params.len() != args.len() {
        return false;
    }
    let mut call = Call {
        method: candidate.id,
        sig: sig.clone(),
        receiver_subst: candidate.subst.clone(),
        inference: Inference::new(vec![GenericOwner::Method(candidate.id)]),
        varargs_expanded: false,
        applicable: true,
        ambiguous: None,
    };
    for (idx, arg) in args.iter().enumerate() {
        match arg {
            Arg::Ty(ty) if !ty.contains_unknown() && !matches!(ty, Ty::Null) => {
                let formal = raw_param(&call, idx).subst(&call.receiver_subst);
                call.inference.unify(db, &formal, ty);
            }
            _ => return false,
        }
    }
    bound_violation(db, &call).is_some_and(|(binding, bound)| {
        !mentions_type_param(&binding) && !mentions_type_param(&bound)
    })
}

/// 未代换的形参类型（考虑可变参数展开）。
fn raw_param(call: &Call, arg_idx: usize) -> Ty {
    let n = call.sig.params.len();
    if n == 0 {
        return Ty::Unknown;
    }
    if call.varargs_expanded && arg_idx >= n - 1 {
        match &call.sig.params[n - 1] {
            Ty::Array(element) => (**element).clone(),
            other => other.clone(),
        }
    } else {
        call.sig.params.get(arg_idx).cloned().unwrap_or(Ty::Unknown)
    }
}

fn args_applicable(db: &dyn Db, call: &Call, args: &[Arg], allow_boxing: bool) -> bool {
    args.iter().enumerate().all(|(idx, arg)| {
        let param = call.param_ty(idx);
        match arg {
            Arg::Ty(arg_ty) => {
                let fits = |param: &Ty| {
                    if allow_boxing {
                        is_assignable(db, arg_ty, param)
                    } else {
                        is_subtype(db, arg_ty, param)
                    }
                };
                fits(&param)
                    || (!call.inference.approximate.is_empty()
                        && fits(&call.param_ty_capturing(idx)))
            }
            // 潜在兼容（JLS 15.12.2.1）：形参个数相同，体的形状与函数类型的返回值相符
            Arg::Lambda {
                arity,
                void_compatible,
                value_compatible,
                ..
            } => match &param {
                Ty::Class(..) => functional_method(db, &param).is_some_and(|method| {
                    let sig = method_sig(db, method.id);
                    sig.params.len() == *arity
                        && if sig.ret == Ty::Void {
                            *void_compatible
                        } else {
                            *value_compatible
                        }
                }),
                Ty::TypeParam(_) | Ty::Unknown => true,
                _ => false,
            },
            // 潜在兼容（JLS 15.12.2.1）：有候选方法能匹配函数类型的形参个数
            Arg::MethodRef { arities } => match &param {
                Ty::Class(..) => functional_method(db, &param).is_some_and(|method| {
                    let n = method_sig(db, method.id).params.len();
                    arities.as_ref().is_none_or(|arities| {
                        arities
                            .iter()
                            .any(|&(min, varargs)| n == min || (varargs && n > min))
                    })
                }),
                Ty::TypeParam(_) | Ty::Unknown => true,
                _ => false,
            },
        }
    })
}

/// 没有谁比别人都具体的候选里，没有别的候选比它更具体的那些（按方法去重）。
fn maximal<'a>(db: &dyn Db, in_phase: &[&'a Scored], args: &[Arg]) -> Vec<&'a Scored> {
    let mut res: Vec<&Scored> = Vec::new();
    for candidate in in_phase {
        let dominated = in_phase.iter().any(|other| {
            other.call.method != candidate.call.method && more_specific(db, other, candidate, args)
        });
        if !dominated && !res.iter().any(|r| r.call.method == candidate.call.method) {
            res.push(candidate);
        }
    }
    res
}

/// 能确定调用有歧义时，返回第二个极大的候选。
///
/// 只在规则简单、不会误报的情形下判断：没有可变参数展开，实参都是已知类型或隐式类型的 lambda
/// （显式类型的 lambda、方法引用有额外的"更具体"规则），候选都不是泛型方法、形参类型都已知。
/// 形参类型完全相同的两个候选只在都是静态方法、来自互不相关的类（两个静态导入撞名）时才算歧义，
/// 别的情形多半是覆写或者继承来的同一签名。
fn certain_ambiguity(
    db: &dyn Db,
    in_phase: &[&Scored],
    args: &[Arg],
    phase: Phase,
) -> Option<MethodId> {
    if phase == Phase::Varargs {
        return None;
    }
    let args_clear = args.iter().all(|arg| match arg {
        Arg::Ty(ty) => !ty.contains_unknown() && !mentions_type_param(ty),
        Arg::Lambda { implicit, .. } => *implicit,
        Arg::MethodRef { .. } => false,
    });
    let candidates_clear = in_phase.iter().all(|s| {
        !is_generic(s)
            && s.params
                .iter()
                .all(|p| !p.contains_unknown() && !mentions_type_param(p))
    });
    if !args_clear || !candidates_clear {
        return None;
    }
    let maximal = maximal(db, in_phase, args);
    let [first, second, ..] = maximal.as_slice() else {
        return None;
    };
    if first.params != second.params {
        return Some(second.call.method);
    }
    let unrelated_statics =
        maximal.iter().all(|s| {
            crate::lower::method_flags(db, s.call.method).is_some_and(|flags| flags.is_static())
        }) && !hir_def::is_subclass_of(db, first.call.method.class, second.call.method.class)
            && !hir_def::is_subclass_of(db, second.call.method.class, first.call.method.class);
    unrelated_statics.then_some(second.call.method)
}

/// `a` 是否比 `b` 更具体：`a` 的每个形参类型都是 `b` 对应形参类型的子类型。
///
/// 代换后形参完全相同时，非泛型方法比泛型方法更具体：`f(StringBuilder)` 比
/// `<A extends Appendable> f(A)` 更具体，因为后者声明的形参是类型变量，不是前者的子类型。
fn more_specific(db: &dyn Db, a: &Scored, b: &Scored, args: &[Arg]) -> bool {
    if a.params.len() != b.params.len() {
        return false;
    }
    // 类型不知道（类路径缺了这个类）的形参或实参和什么都相容，按子类型比较会得出错的结论：
    // 形参类型不知道的候选不能压过形参类型已知的（`toURI(ICompilationUnit)` 压过 `toURI(String)`），
    // 实参类型不知道的位置上形参不同的两个候选谁也不比谁具体
    let unclear = a
        .params
        .iter()
        .zip(&b.params)
        .enumerate()
        .any(|(idx, (pa, pb))| {
            let arg_unknown = matches!(args.get(idx), Some(Arg::Ty(ty)) if ty.contains_unknown());
            (arg_unknown && pa != pb) || (pa.contains_unknown() && !pb.contains_unknown())
        });
    if unclear {
        return false;
    }
    let (a_generic, b_generic) = (is_generic(a), is_generic(b));
    if a.params != b.params && (a_generic || b_generic) {
        // 有一方是泛型方法时按声明的形参比较（JLS 15.12.2.5、18.5.4）：代换后的形参只说明这次调用
        // 两边都能接受实参。`<T> assertThat(T)` 取 `T = List<Pet>` 之后比
        // `assertThat(List<? extends E>)` 取 `E = Pet` 得到的 `List<? extends Pet>` 还"窄"，
        // 但声明的 `T` 不能传给 `List<? extends E>`，反过来可以，所以后者更具体；
        // `<T> assertThat(T)` 取 `T = Exception` 也不比 `assertThat(Throwable)` 具体
        return declared_more_specific(db, a, b);
    }
    if !a
        .params
        .iter()
        .zip(&b.params)
        .all(|(pa, pb)| is_subtype(db, pa, pb))
    {
        return false;
    }
    if a.params != b.params {
        return true;
    }
    match (a_generic, b_generic) {
        (false, b_generic) => b_generic,
        // 代换后一样（`of(E)` 取 `E = String[]` 和 `of(E...)` 取 `E = String`）：
        // 按声明的形参类型比较（JLS 15.12.2.5）
        (true, true) => declared_more_specific(db, a, b) && !declared_more_specific(db, b, a),
        (true, false) => false,
    }
}

/// 候选按泛型方法看待：方法自己有类型参数，或者是菱形构造器、声明的形参里用到了被构造类的
/// 类型参数（JLS 15.9.3：菱形构造时构造器被看成以类的类型参数为类型参数的泛型方法）。
/// `new Box<>("s")` 里 `Box(T)` 取 `T = String` 之后和 `Box(CharSequence)` 代换后一样宽，
/// 得按声明的 `T` 比较，后者才更具体。
fn is_generic(s: &Scored) -> bool {
    s.call.sig.n_type_params > 0
        || (0..s.params.len()).any(|idx| {
            let formal = s.call.formal_param_ty(idx);
            s.call
                .inference
                .owners
                .iter()
                .any(|owner| formal.mentions_params_of(*owner))
        })
}

/// 所有者声明的类型参数个数。
fn n_type_params_of(db: &dyn Db, owner: GenericOwner, sig: &MethodSig) -> u32 {
    match owner {
        GenericOwner::Method(_) => sig.n_type_params,
        GenericOwner::Class(class) => {
            hir_def::class_header(db, class).map_or(0, |data| data.type_params.len() as u32)
        }
    }
}

/// `b` 能否接受类型为 `a` 的声明形参类型的实参（`b` 的类型参数按这些实参推断，`a` 的保持不动）。
fn declared_more_specific(db: &dyn Db, a: &Scored, b: &Scored) -> bool {
    let n = a.params.len();
    let a_formals: Vec<Ty> = (0..n).map(|i| a.call.formal_param_ty(i)).collect();
    let b_formals: Vec<Ty> = (0..n).map(|i| b.call.formal_param_ty(i)).collect();
    // 菱形构造时被构造类的类型参数也按实参推断
    let mut inference = Inference::new(b.call.inference.owners.clone());
    for (fb, fa) in b_formals.iter().zip(&a_formals) {
        inference.unify(db, fb, fa);
    }
    let fits = a_formals
        .iter()
        .zip(&b_formals)
        .all(|(fa, fb)| is_subtype(db, fa, &fb.subst(&inference.bindings)));
    // 推出来的绑定还得满足 `b` 的类型参数声明的上界：`<T> f(T)` 的 `T` 不能传给
    // `<U extends Comparable<? super U>> f(U)`
    fits && b.call.inference.owners.iter().all(|&owner| {
        (0..n_type_params_of(db, owner, &b.call.sig)).all(|idx| {
            let param = TypeParamId { owner, idx };
            let Some(binding) = inference.bindings.get(param) else {
                return true;
            };
            type_param_bounds(db, param).iter().all(|bound| {
                let bound = bound
                    .subst(&b.call.receiver_subst)
                    .subst(&inference.bindings);
                bound.contains_unknown() || is_subtype(db, binding, &bound)
            })
        })
    })
}
