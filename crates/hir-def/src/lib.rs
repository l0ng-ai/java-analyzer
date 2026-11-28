//! 签名层：把源码和 class 文件统一成 [`ClassData`]，建立全局类索引，解析类型名。
//!
//! 这一层完全不看方法体。所有查询的结果只取决于声明的"形状"，
//! 因此在方法体里敲字不会让任何全局结果失效。

mod binary;
mod binary_nullness;
mod data;
mod index;
mod library_decls;
mod library_source;
mod lombok;
mod lombok_expand;
mod lower;
mod modules;
mod resolver;
mod signatures;
mod visibility;

pub use crate::{
    binary::lower_class_file,
    binary_nullness::{
        binary_module_annotations, binary_null_annotations, binary_package_annotations,
        BinaryAnnotation, BinaryMethodAnnotations, BinaryNullAnnotations,
    },
    data::{
        AnnotationTargets, ClassData, ClassId, ClassKind, CopyOrigin, DeclIdx, FieldConstant,
        FieldData, FieldId, GenericOwner, Import, ItemTree, LocalClass, MethodData, MethodId,
        Modifiers, ModuleDeclData, Name, NullAnnotation, ParamData, PathSegment, PrimitiveType,
        TypeParamData, TypeParamId, TypeRef, Visibility, WildcardBound,
    },
    index::{
        all_supers, binary_class, class_by_key, class_copies, class_data, class_decl_file,
        class_in_file, class_in_origin, class_origin, class_source_file, decl_header,
        direct_supers, has_copies, is_subclass_of, item_tree, item_tree_and_map, lookup_class,
        nested_class, outer_class, outermost_class, package_classes, package_exists,
        permitted_subclasses, sibling_class, source_class_index, source_direct_subtypes,
        source_map, source_subclasses, subpackages, workspace_item_trees, ClassOrigin,
        ItemTreeChunk, SourceClassIndex,
    },
    library_source::{
        library_class_source, library_method_source, method_param_names, LibraryClassSource,
        LibraryMethodSource,
    },
    lombok::AccessorKind,
    lower::{
        is_compact_source, lower_file, lower_file_with, lower_param_type, lower_type,
        param_null_annotation, SourceMap,
    },
    modules::{module_graph, module_import_candidates, module_imports, ModuleGraph, ModuleInfo},
    resolver::{
        local_class_owner, lookup_class_in_scope, member_type, on_demand_import_candidates,
        resolve_qualified_class, resolve_qualified_class_from, resolve_qualified_class_visible,
        resolve_simple_type, resolve_type_param, resolve_type_path, resolve_type_ref_to_class,
        TypeNs, TypeScope,
    },
    signatures::{
        class_at_decl, class_decls, class_header, constructor_indices, field_named, file_scope,
        method_type_param, methods_named, ClassHeader, FieldRef, FileScope, MethodRef,
    },
    visibility::{is_preferred_from, is_visible_from, lookup_class_from, package_visible_from},
};
