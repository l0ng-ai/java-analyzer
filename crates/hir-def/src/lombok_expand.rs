//! 需要别的类的签名才能合成的 Lombok 成员。
//!
//! - `@Delegate` 字段：把字段类型（连同它的父类型，`Object` 除外）的公开实例方法转发到本类。
//!
//! （`@SuperBuilder` 的子类构建器直接继承父类的构建器，不需要在这里补成员。）
//!
//! 合成出来的签名里的类型都换成已解析的二进制名（[`TypeRef::Class`]），因为它们来自别的类，
//! 在本类的作用域里按源码写法解析未必能找到。

use std::cell::RefCell;

use base_db::Db;
use rustc_hash::FxHashMap;

use crate::{
    data::{ClassData, MethodData, Modifiers, Name, ParamData, TypeParamData, TypeRef},
    index::{all_supers, class_data, class_decl_file, nested_class, sibling_class},
    resolver::{resolve_type_ref_to_class, TypeScope},
    ClassId, WildcardBound,
};

thread_local! {
    /// 正在展开的类。两个类互相 `@Delegate` 时，后一个不再去取前一个的签名，避免查询循环
    static EXPANDING: RefCell<Vec<ClassId>> = const { RefCell::new(Vec::new()) };
}

/// 这个类是否需要按别的类的签名补成员。
pub(crate) fn needs_expansion(data: &ClassData) -> bool {
    data.fields
        .iter()
        .any(|f| f.flags.contains(Modifiers::LOMBOK_DELEGATE))
}

pub(crate) fn expand(db: &dyn Db, id: ClassId, data: &mut ClassData) {
    let cyclic = EXPANDING.with(|stack| stack.borrow().contains(&id));
    if cyclic {
        return;
    }
    EXPANDING.with(|stack| stack.borrow_mut().push(id));
    // salsa 的取消以 panic 展开，展开时也要出栈
    struct PopOnDrop;
    impl Drop for PopOnDrop {
        fn drop(&mut self) {
            EXPANDING.with(|stack| {
                stack.borrow_mut().pop();
            });
        }
    }
    let _guard = PopOnDrop;
    add_delegates(db, id, data);
}

fn is_expanding(class: ClassId) -> bool {
    EXPANDING.with(|stack| stack.borrow().contains(&class))
}

fn has_method(data: &ClassData, name: &str, arity: usize) -> bool {
    data.methods
        .iter()
        .any(|m| !m.is_constructor && m.name == name && m.params.len() == arity)
}

/// 把类型引用里按作用域解析的部分换成二进制名。
struct Absolutizer<'a> {
    db: &'a dyn Db,
    scope: TypeScope,
    /// 类的类型参数 → 实参（缺省时为 `TypeRef::Error`）
    subst: FxHashMap<Name, TypeRef>,
    /// 方法自己的类型参数：原样保留
    method_params: Vec<Name>,
}

impl Absolutizer<'_> {
    fn type_var(&self, name: &Name) -> Option<TypeRef> {
        if self.method_params.contains(name) {
            return Some(TypeRef::TypeVar(name.clone()));
        }
        self.subst.get(name).cloned()
    }

    fn apply(&self, ty: &TypeRef) -> TypeRef {
        match ty {
            TypeRef::Path(segments) => {
                if let [segment] = segments.as_slice() {
                    if segment.args.is_empty() {
                        if let Some(var) = self.type_var(&segment.name) {
                            return var;
                        }
                    }
                }
                match resolve_type_ref_to_class(self.db, &self.scope, ty) {
                    Some(class) => TypeRef::Class {
                        name: class.binary_name(self.db),
                        args: segments
                            .last()
                            .map(|s| s.args.iter().map(|a| self.apply(a)).collect())
                            .unwrap_or_default(),
                    },
                    None => TypeRef::Error,
                }
            }
            TypeRef::TypeVar(name) => self.type_var(name).unwrap_or(TypeRef::Error),
            TypeRef::Class { name, args } => TypeRef::Class {
                name: name.clone(),
                args: args.iter().map(|a| self.apply(a)).collect(),
            },
            TypeRef::Array(element) => TypeRef::Array(Box::new(self.apply(element))),
            TypeRef::Wildcard(bound) => TypeRef::Wildcard(match bound {
                WildcardBound::Unbounded => WildcardBound::Unbounded,
                WildcardBound::Extends(b) => WildcardBound::Extends(Box::new(self.apply(b))),
                WildcardBound::Super(b) => WildcardBound::Super(Box::new(self.apply(b))),
            }),
            TypeRef::Intersection(list) => {
                TypeRef::Intersection(list.iter().map(|t| self.apply(t)).collect())
            }
            TypeRef::Primitive(_) | TypeRef::Void | TypeRef::Error => ty.clone(),
        }
    }

    /// 把别的类里的方法搬过来：签名里的类型全部解析好。
    fn method(&mut self, method: &MethodData) -> MethodData {
        self.method_params = method.type_params.iter().map(|p| p.name.clone()).collect();
        MethodData {
            name: method.name.clone(),
            is_constructor: false,
            type_params: method
                .type_params
                .iter()
                .map(|p| TypeParamData {
                    name: p.name.clone(),
                    bounds: p.bounds.iter().map(|b| self.apply(b)).collect(),
                })
                .collect(),
            params: method
                .params
                .iter()
                .map(|p| ParamData {
                    name: p.name.clone(),
                    ty: self.apply(&p.ty),
                    nullness: p.nullness,
                })
                .collect(),
            ret: self.apply(&method.ret),
            throws: method.throws.iter().map(|t| self.apply(t)).collect(),
            flags: Modifiers(Modifiers::PUBLIC | Modifiers::SYNTHETIC),
            has_body: true,
            decl: None,
        }
    }
}

/// `@Delegate` 字段转发的方法。
fn add_delegates(db: &dyn Db, id: ClassId, data: &mut ClassData) {
    let delegates: Vec<(TypeRef, Option<u32>)> = data
        .fields
        .iter()
        .filter(|f| f.flags.contains(Modifiers::LOMBOK_DELEGATE))
        .map(|f| (f.ty.clone(), f.decl))
        .collect();
    if delegates.is_empty() {
        return;
    }
    // 在本类的外层作用域里解析字段类型：用本类自己的作用域会在算本类签名的过程中再要本类签名
    let outer_scope = TypeScope {
        file: class_decl_file(db, id),
        class: data
            .outer
            .as_deref()
            .and_then(|outer| sibling_class(db, id, outer)),
        method: None,
        in_class_header: false,
    };
    let own_scope = Absolutizer {
        db,
        scope: outer_scope,
        subst: FxHashMap::default(),
        method_params: Vec::new(),
    };
    for (field_ty, decl) in delegates {
        // 本类的成员类型
        let target = match &field_ty {
            TypeRef::Path(segments)
                if segments.len() == 1 && data.nested.contains(&segments[0].name) =>
            {
                nested_class(db, id, &segments[0].name)
            }
            _ => resolve_type_ref_to_class(db, &outer_scope, &field_ty),
        };
        let Some(target) = target.filter(|t| *t != id && !is_expanding(*t)) else {
            continue;
        };
        let args: Vec<TypeRef> = match &field_ty {
            TypeRef::Path(segments) => segments
                .last()
                .map(|s| s.args.iter().map(|a| own_scope.apply(a)).collect())
                .unwrap_or_default(),
            TypeRef::Class { args, .. } => args.clone(),
            _ => Vec::new(),
        };

        let mut classes = vec![target];
        classes.extend(all_supers(db, target).iter().copied());
        for class in classes {
            let binary = class.binary_name(db);
            if binary == "java/lang/Object" || class == id || is_expanding(class) {
                continue;
            }
            let Some(source) = class_data(db, class) else {
                continue;
            };
            // 只有字段类型自己的类型参数知道实参；父类型的类型参数按未知处理
            let subst = source
                .type_params
                .iter()
                .enumerate()
                .map(|(idx, p)| {
                    let arg = if class == target {
                        args.get(idx).cloned().unwrap_or(TypeRef::Error)
                    } else {
                        TypeRef::Error
                    };
                    (p.name.clone(), arg)
                })
                .collect();
            let mut absolutizer = Absolutizer {
                db,
                scope: TypeScope::class(db, class),
                subst,
                method_params: Vec::new(),
            };
            for method in source.methods.iter() {
                let skip = method.is_constructor
                    || method.flags.is_static()
                    || method.flags.visibility() != crate::Visibility::Public
                    || (method.flags.contains(Modifiers::SYNTHETIC) && !source.is_source)
                    || has_method(data, &method.name, method.params.len());
                if skip {
                    continue;
                }
                let mut forwarded = absolutizer.method(method);
                forwarded.decl = decl;
                data.methods.push(forwarded);
            }
        }
    }
}
