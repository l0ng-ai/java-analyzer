//! 把定义渲染成 Java 风格的签名文本（悬停、补全详情、签名帮助、符号搜索共用）。

use base_db::Db;
use hir::{
    class_data, class_supertypes, field_ty, method_sig, type_param_bounds, ClassId, ClassKind,
    Definition, FieldId, GenericOwner, LocalData, MethodId, Modifiers, Subst, Ty, TypeParamId,
};

fn push_modifiers(out: &mut String, flags: Modifiers) {
    let rendered = flags.render();
    if !rendered.is_empty() {
        out.push_str(&rendered);
        out.push(' ');
    }
}

/// `T extends Comparable<T>`
pub fn type_param_decl(db: &dyn Db, param: TypeParamId) -> String {
    let mut out = hir::type_param_name(db, param);
    let bounds = type_param_bounds(db, param);
    let shown: Vec<String> = bounds
        .iter()
        .map(|b| b.display(db))
        .filter(|b| b != "Object")
        .collect();
    if !shown.is_empty() {
        out.push_str(" extends ");
        out.push_str(&shown.join(" & "));
    }
    out
}

pub fn type_params_decl(db: &dyn Db, owner: GenericOwner, count: usize) -> String {
    if count == 0 {
        return String::new();
    }
    let params: Vec<String> = (0..count)
        .map(|idx| {
            type_param_decl(
                db,
                TypeParamId {
                    owner,
                    idx: idx as u32,
                },
            )
        })
        .collect();
    format!("<{}>", params.join(", "))
}

/// `public final class Foo<T> extends Bar implements Baz`
pub fn class_header(db: &dyn Db, class: ClassId) -> String {
    let Some(data) = class_data(db, class) else {
        return class.qualified_name(db);
    };
    let mut out = String::new();
    let mut flags = data.flags;
    // 接口的 abstract、记录的 final、枚举的 static 都是隐含的，不展示
    match data.kind {
        ClassKind::Interface | ClassKind::Annotation => flags.remove(Modifiers::ABSTRACT),
        ClassKind::Record | ClassKind::Enum => flags.remove(Modifiers::FINAL),
        ClassKind::Class => {}
    }
    push_modifiers(&mut out, flags);
    out.push_str(match data.kind {
        ClassKind::Class => "class ",
        ClassKind::Interface => "interface ",
        ClassKind::Enum => "enum ",
        ClassKind::Record => "record ",
        ClassKind::Annotation => "@interface ",
    });
    out.push_str(&data.name);
    out.push_str(&type_params_decl(
        db,
        GenericOwner::Class(class),
        data.type_params.len(),
    ));

    let supers = class_supertypes(db, class);
    let (mut extends, mut implements): (Vec<String>, Vec<String>) = (Vec::new(), Vec::new());
    for sup in supers.iter() {
        let Some(sup_class) = sup.as_class() else {
            continue;
        };
        let name = sup_class.binary_name(db);
        if matches!(
            &*name,
            "java/lang/Object"
                | "java/lang/Enum"
                | "java/lang/Record"
                | "java/lang/annotation/Annotation"
        ) {
            continue;
        }
        let is_interface = class_data(db, sup_class).is_some_and(|d| d.is_interface());
        if is_interface && !data.is_interface() {
            implements.push(sup.display(db));
        } else {
            extends.push(sup.display(db));
        }
    }
    if !extends.is_empty() {
        out.push_str(" extends ");
        out.push_str(&extends.join(", "));
    }
    if !implements.is_empty() {
        out.push_str(" implements ");
        out.push_str(&implements.join(", "));
    }
    out
}

/// 形参的展示文本，例如 `["int a", "String... rest"]`。
pub fn method_params(db: &dyn Db, method: MethodId, subst: &Subst) -> Vec<String> {
    let sig = method_sig(db, method);
    let last = sig.params.len().saturating_sub(1);
    let names = hir::method_param_names(db, method);
    sig.params
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            let ty = ty.subst(subst);
            let ty_text = match (&ty, sig.varargs && idx == last) {
                (Ty::Array(element), true) => format!("{}...", element.display(db)),
                _ => ty.display(db),
            };
            match names.get(idx).and_then(|name| name.as_ref()) {
                Some(name) => format!("{ty_text} {name}"),
                None => format!("{ty_text} arg{idx}"),
            }
        })
        .collect()
}

/// `public static <T> List<T> of(T... elements) throws IOException`
pub fn method_signature(db: &dyn Db, method: MethodId, subst: &Subst) -> String {
    let Some(data) = class_data(db, method.class) else {
        return String::new();
    };
    let Some(m) = data.methods.get(method.idx as usize) else {
        return String::new();
    };
    let sig = method_sig(db, method);

    let mut out = String::new();
    let mut flags = m.flags;
    flags.remove(Modifiers::VARARGS | Modifiers::SYNTHETIC | Modifiers::DEPRECATED);
    if data.is_interface() {
        flags.remove(Modifiers::ABSTRACT | Modifiers::PUBLIC);
    }
    push_modifiers(&mut out, flags);
    let type_params = type_params_decl(db, GenericOwner::Method(method), m.type_params.len());
    if !type_params.is_empty() {
        out.push_str(&type_params);
        out.push(' ');
    }
    if !m.is_constructor {
        // 捕获的通配符用作返回值时显示其上界，保留类型实参里的通配符。
        out.push_str(&sig.ret.subst(subst).upper_bound(db).display(db));
        out.push(' ');
    }
    out.push_str(&m.name);
    out.push('(');
    out.push_str(&method_params(db, method, subst).join(", "));
    out.push(')');
    if !sig.throws.is_empty() {
        out.push_str(" throws ");
        let throws: Vec<String> = sig
            .throws
            .iter()
            .map(|t| t.subst(subst).display(db))
            .collect();
        out.push_str(&throws.join(", "));
    }
    out
}

/// `private final int count`
pub fn field_signature(db: &dyn Db, field: FieldId, subst: &Subst) -> String {
    let Some(data) = class_data(db, field.class) else {
        return String::new();
    };
    let Some(f) = data.fields.get(field.idx as usize) else {
        return String::new();
    };
    let mut out = String::new();
    if !f.is_enum_constant() {
        let mut flags = f.flags;
        flags.remove(Modifiers::DEPRECATED | Modifiers::SYNTHETIC);
        push_modifiers(&mut out, flags);
    }
    out.push_str(&field_ty(db, field).subst(subst).display(db));
    out.push(' ');
    out.push_str(&f.name);
    out
}

pub fn local_signature(db: &dyn Db, local: &LocalData) -> String {
    format!("{} {}", local.ty.display(db), local.name)
}

/// 定义的一行签名。
pub fn definition_signature(db: &dyn Db, def: &Definition) -> String {
    match def {
        Definition::Class(class) => class_header(db, *class),
        Definition::Field(field) => field_signature(db, *field, &Subst::empty()),
        Definition::Method(method) => method_signature(db, *method, &Subst::empty()),
        Definition::Local(local) => local_signature(db, hir::infer(db, local.body).local(local.id)),
        Definition::TypeParam(param) => type_param_decl(db, *param),
        Definition::Package(package) => format!("package {}", package.replace('/', ".")),
    }
}
