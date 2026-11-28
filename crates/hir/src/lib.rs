//! 语义层对外的门面。
//!
//! IDE 功能只通过这里和语法树打交道：给一个语法节点，问"它是什么"（[`Semantics`]），
//! 或者给一个定义，问"它在哪里声明"（[`Definition::source`]）。

mod consts;
mod definition;
mod semantics;

pub use base_db::{Db, FileId, SourceFile};
pub use hir_def::{
    all_supers, binary_class, binary_module_annotations, binary_null_annotations,
    binary_package_annotations, class_at_decl, class_by_key, class_copies, class_data,
    class_decl_file, class_header, class_in_file, class_origin, class_source_file,
    constructor_indices, decl_header, direct_supers, field_named, file_scope, is_compact_source,
    is_preferred_from, is_subclass_of, is_visible_from, item_tree, library_class_source,
    library_method_source, local_class_owner, lookup_class, lookup_class_from, lower_param_type,
    lower_type, member_type, method_param_names, methods_named, module_graph,
    module_import_candidates, module_imports, nested_class, on_demand_import_candidates,
    outer_class, outermost_class, package_classes, package_exists, package_visible_from,
    param_null_annotation, permitted_subclasses, resolve_qualified_class,
    resolve_qualified_class_from, resolve_qualified_class_visible, resolve_simple_type,
    resolve_type_path, source_class_index, source_map, source_subclasses, subpackages,
    workspace_item_trees, AccessorKind, AnnotationTargets, BinaryAnnotation, ClassData,
    ClassHeader, ClassId, ClassKind, ClassOrigin, FieldData, FieldId, FieldRef, FileScope,
    GenericOwner, Import, ItemTree, MethodData, MethodId, MethodRef, Modifiers, ModuleDeclData,
    ModuleGraph, ModuleInfo, Name, NullAnnotation, ParamData, PrimitiveType, TypeNs, TypeParamId,
    TypeRef, TypeScope, Visibility,
};
pub use hir_ty::{
    all_fields, all_methods, all_super_tys, body_member, body_syntax, body_tree, class_supertypes,
    constructors, field_data, field_flags, field_ty, find_super, find_super_keeping_raw,
    functional_method, infer, is_accessible, is_accessible_via, is_assignable, is_subtype,
    lookup_field, lookup_methods, lower_type_ref, method_data, method_flags, method_sig, this_ty,
    type_param_bounds, type_param_name, BodyId, BodyTree, CallInfo, FieldCandidate,
    InferDiagnostic, InferDiagnosticKind, InferenceResult, LocalData, LocalId, LocalKind,
    MethodCandidate, MethodSig, Resolution, Subst, Ty, Wildcard,
};

pub use crate::{
    consts::{expr_constant, field_constant, local_constant, Constant},
    definition::{DeclSource, Definition, LocalDef},
    semantics::Semantics,
};
