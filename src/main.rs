// Copyright (c) 2022 Kaushik Kulkarni
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#![feature(box_patterns)]

use codegen::Scope;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use lazy_static::lazy_static;
use std::fs;
use std::iter::zip;
use std::path::Path;

#[derive(Clone, Debug)]
enum CType {
    IslDimType,
    IslError,
    IslFold,
    IslStat,
    IslType(String),
    IslSize,
    IslBool,
    CStr,
    Int,
    Long,
    UInt,
    ULong,
    USize,
    Double,
    MutVoidStar,
    ConstVoidStar,
    FnPointer {
        args: Vec<CType>,
        ret: Option<Box<CType>>,
    },
    Raw(String),
}

impl From<clang::Type<'_>> for CType {
    fn from(type_: clang::Type<'_>) -> CType {
        let name = type_.get_canonical_type().get_display_name();
        if name == "enum isl_dim_type" {
            CType::IslDimType
        } else if name == "enum isl_error" {
            CType::IslError
        } else if name == "enum isl_fold" {
            CType::IslFold
        } else if name == "isl_stat" {
            CType::IslStat
        } else if is_isl_type(&name) {
            CType::IslType(name)
        } else if name == "isl_size" {
            CType::IslSize
        } else if name == "isl_bool" {
            CType::IslBool
        } else if name == "const char *" || name == "char *" {
            CType::CStr
        } else if name == "int" {
            CType::Int
        } else if name == "long" {
            CType::Long
        } else if name == "unsigned int" || name == "uint32_t" {
            CType::UInt
        } else if name == "unsigned long" {
            CType::ULong
        } else if name == "size_t" {
            CType::USize
        } else if name == "double" {
            CType::Double
        } else if name == "void *" {
            CType::MutVoidStar
        } else if name == "const void *" {
            CType::ConstVoidStar
        } else if let Some(pointee) = type_.get_pointee_type() {
            if let (Some(args), Some(ret)) =
                (pointee.get_argument_types(), pointee.get_result_type())
            {
                let args = args.into_iter().map(CType::from).collect();
                let ret = if ret.get_canonical_type().get_display_name() == "void" {
                    None
                } else {
                    Some(Box::new(CType::from(ret)))
                };
                CType::FnPointer { args, ret }
            } else {
                CType::Raw(name)
            }
        } else {
            CType::Raw(name)
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum Mutability {
    Const,
    Mut,
}
use Mutability::*;

#[derive(Clone, PartialEq, Eq, Hash)]
enum RustType {
    UIntPtr,
    Bool,
    I32,
    I64,
    U32,
    U64,
    USize,
    F64,
    CVoid,
    CChar,
    Str,
    DimType,
    Error,
    Fold,
    Stat,
    Ref(Box<RustType>),
    Ptr(Mutability, Box<RustType>),
    FnPointer {
        args: Vec<RustType>,
        ret: Option<Box<RustType>>,
    },
    Raw(String),
}

impl std::fmt::Display for RustType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            RustType::UIntPtr => write!(f, "uintptr_t"),
            RustType::Bool => write!(f, "bool"),
            RustType::I32 => write!(f, "i32"),
            RustType::I64 => write!(f, "i64"),
            RustType::U32 => write!(f, "u32"),
            RustType::U64 => write!(f, "u64"),
            RustType::USize => write!(f, "usize"),
            RustType::F64 => write!(f, "f64"),
            RustType::CVoid => write!(f, "c_void"),
            RustType::CChar => write!(f, "c_char"),
            RustType::Str => write!(f, "str"),
            RustType::DimType => write!(f, "DimType"),
            RustType::Error => write!(f, "Error"),
            RustType::Fold => write!(f, "Fold"),
            RustType::Stat => write!(f, "Stat"),
            RustType::Ref(x) => write!(f, "&{x}"),
            RustType::Ptr(Const, x) => write!(f, "*const {x}"),
            RustType::Ptr(Mut, x) => write!(f, "*mut {x}"),
            RustType::FnPointer { args, ret } => {
                write!(f,
                       "unsafe extern \"C\" fn({}){}",
                       args.iter().format(" "),
                       ret.as_ref()
                          .map(|ret| format!(" -> {ret}"))
                          .unwrap_or_default())
            }
            RustType::Raw(x) => write!(f, "{x}"),
        }
    }
}

lazy_static! {
    static ref C_TO_RS_BINDING: HashMap<&'static str, RustType> =
        HashMap::from([("struct isl_ctx *", RustType::Raw("Context".to_owned())),
                       ("struct isl_space *", RustType::Raw("Space".to_owned())),
                       ("struct isl_local_space *", RustType::Raw("LocalSpace".to_owned())),
                       ("struct isl_id *", RustType::Raw("Id".to_owned())),
                       ("struct isl_id_list *", RustType::Raw("IdList".to_owned())),
                       ("struct isl_val *", RustType::Raw("Val".to_owned())),
                       ("struct isl_val_list *", RustType::Raw("ValList".to_owned())),
                       ("struct isl_point *", RustType::Raw("Point".to_owned())),
                       ("struct isl_mat *", RustType::Raw("Mat".to_owned())),
                       ("struct isl_vec *", RustType::Raw("Vec".to_owned())),
                       ("struct isl_basic_set *", RustType::Raw("BasicSet".to_owned())),
                       ("struct isl_basic_set_list *", RustType::Raw("BasicSetList".to_owned())),
                       ("struct isl_set *", RustType::Raw("Set".to_owned())),
                       ("struct isl_set_list *", RustType::Raw("SetList".to_owned())),
                       ("struct isl_basic_map *", RustType::Raw("BasicMap".to_owned())),
                       ("struct isl_basic_map_list *", RustType::Raw("BasicMapList".to_owned())),
                       ("struct isl_map *", RustType::Raw("Map".to_owned())),
                       ("struct isl_map_list *", RustType::Raw("MapList".to_owned())),
                       ("struct isl_union_set *", RustType::Raw("UnionSet".to_owned())),
                       ("struct isl_union_set_list *", RustType::Raw("UnionSetList".to_owned())),
                       ("struct isl_union_map *", RustType::Raw("UnionMap".to_owned())),
                       ("struct isl_union_map_list *", RustType::Raw("UnionMapList".to_owned())),
                       ("struct isl_constraint *", RustType::Raw("Constraint".to_owned())),
                       ("struct isl_constraint_list *", RustType::Raw("ConstraintList".to_owned())),
                       ("struct isl_aff *", RustType::Raw("Aff".to_owned())),
                       ("struct isl_aff_list *", RustType::Raw("AffList".to_owned())),
                       ("struct isl_term *", RustType::Raw("Term".to_owned())),
                       ("struct isl_qpolynomial *", RustType::Raw("QPolynomial".to_owned())),
                       ("struct isl_qpolynomial_list *", RustType::Raw("QPolynomialList".to_owned())),
                       ("struct isl_qpolynomial_fold *", RustType::Raw("QPolynomialFold".to_owned())),
                       ("struct isl_multi_id *", RustType::Raw("MultiId".to_owned())),
                       ("struct isl_multi_val *", RustType::Raw("MultiVal".to_owned())),
                       ("struct isl_multi_aff *", RustType::Raw("MultiAff".to_owned())),
                       ("struct isl_multi_pw_aff *", RustType::Raw("MultiPwAff".to_owned())),
                       ("struct isl_multi_union_pw_aff *", RustType::Raw("MultiUnionPwAff".to_owned())),
                       ("struct isl_pw_aff *", RustType::Raw("PwAff".to_owned())),
                       ("struct isl_pw_aff_list *", RustType::Raw("PwAffList".to_owned())),
                       ("struct isl_pw_multi_aff *", RustType::Raw("PwMultiAff".to_owned())),
                       ("struct isl_pw_multi_aff_list *", RustType::Raw("PwMultiAffList".to_owned())),
                       ("struct isl_pw_qpolynomial *", RustType::Raw("PwQPolynomial".to_owned())),
                       ("struct isl_pw_qpolynomial_list *", RustType::Raw("PwQPolynomialList".to_owned())),
                       ("struct isl_pw_qpolynomial_fold *", RustType::Raw("PwQPolynomialFold".to_owned())),
                       ("struct isl_pw_qpolynomial_fold_list *", RustType::Raw("PwQPolynomialFoldList".to_owned())),
                       ("struct isl_union_pw_aff *", RustType::Raw("UnionPwAff".to_owned())),
                       ("struct isl_union_pw_aff_list *", RustType::Raw("UnionPwAffList".to_owned())),
                       ("struct isl_union_pw_multi_aff *", RustType::Raw("UnionPwMultiAff".to_owned())),
                       ("struct isl_union_pw_multi_aff_list *", RustType::Raw("UnionPwMultiAffList".to_owned())),
                       ("struct isl_union_pw_qpolynomial *", RustType::Raw("UnionPwQPolynomial".to_owned())),
                       ("struct isl_union_pw_qpolynomial_fold *", RustType::Raw("UnionPwQPolynomialFold".to_owned())),
                       ("struct isl_stride_info *", RustType::Raw("StrideInfo".to_owned())),
                       ("struct isl_fixed_box *", RustType::Raw("FixedBox".to_owned())),
                       ("enum isl_dim_type", RustType::DimType),
                       ("enum isl_error", RustType::Error),
                       ("enum isl_fold", RustType::Fold),
                       ("enum isl_stat", RustType::Stat),
                       ("struct isl_stat", RustType::Stat),
                       ("struct isl_printer *", RustType::Raw("Printer".to_owned()))]);
    static ref ISL_CORE_TYPES: HashSet<&'static str> = HashSet::from(["struct isl_ctx *",
                                                                      "struct isl_space *",
                                                                      "struct isl_local_space *",
                                                                      "struct isl_id *",
                                                                      "struct isl_id_list *",
                                                                      "struct isl_val *",
                                                                      "struct isl_val_list *",
                                                                      "struct isl_point *",
                                                                      "struct isl_mat *",
                                                                      "struct isl_vec *",
                                                                      "struct isl_basic_set *",
                                                                      "struct isl_basic_set_list *",
                                                                      "struct isl_set *",
                                                                      "struct isl_set_list *",
                                                                      "struct isl_basic_map *",
                                                                      "struct isl_basic_map_list *",
                                                                      "struct isl_map *",
                                                                      "struct isl_map_list *",
                                                                      "struct isl_union_set *",
                                                                      "struct isl_union_set_list *",
                                                                      "struct isl_union_map *",
                                                                      "struct isl_union_map_list *",
                                                                      "struct isl_constraint *",
                                                                      "struct isl_constraint_list *",
                                                                      "struct isl_aff *",
                                                                      "struct isl_aff_list *",
                                                                      "struct isl_term *",
                                                                      "struct isl_qpolynomial *",
                                                                      "struct isl_qpolynomial_list *",
                                                                      "struct isl_qpolynomial_fold *",
                                                                      "struct isl_multi_id *",
                                                                      "struct isl_multi_val *",
                                                                      "struct isl_multi_aff *",
                                                                      "struct isl_multi_pw_aff *",
                                                                      "struct isl_multi_union_pw_aff *",
                                                                      "struct isl_pw_aff *",
                                                                      "struct isl_pw_aff_list *",
                                                                      "struct isl_pw_multi_aff *",
                                                                      "struct isl_pw_multi_aff_list *",
                                                                      "struct isl_pw_qpolynomial *",
                                                                      "struct isl_pw_qpolynomial_list *",
                                                                      "struct isl_pw_qpolynomial_fold *",
                                                                      "struct isl_pw_qpolynomial_fold_list *",
                                                                      "struct isl_union_pw_aff *",
                                                                      "struct isl_union_pw_aff_list *",
                                                                      "struct isl_union_pw_multi_aff *",
                                                                      "struct isl_union_pw_multi_aff_list *",
                                                                      "struct isl_union_pw_qpolynomial *",
                                                                      "struct isl_union_pw_qpolynomial_fold *",
                                                                      "struct isl_stride_info *",
                                                                      "struct isl_fixed_box *",
                                                                      "struct isl_printer *",
                                                                      ]);
    static ref ISL_TYPES_RS: HashSet<RustType> =
        HashSet::from_iter(C_TO_RS_BINDING.clone().into_values());
    static ref KEYWORD_TO_IDEN: HashMap<&'static str, &'static str> =
        HashMap::from([("in", "in_"),
                       ("str", "str_"),
                       ("type", "type_"),
                       ("box", "box_"),
                       ("ref", "incref"),
                       ("mod", "mod_"),
                       ("2exp", "to_exp"),
                       ("match", "match_")]);

    // TODO: Once we reduce this set down to 0, we are done!
    static ref UNSUPPORTED_C_TYPES: HashSet<&'static str> =
        HashSet::from(["struct __sFILE *", "const struct __sFILE *",
                       "int *",
                       "const int *",
                       "isl_bool *",
                       "struct isl_args *",
                       "struct isl_options *",
                       "const void *",
        ]);
}

/// Records the properties of a function node in an AST.
#[derive(Clone, Eq, Hash, PartialEq)]
struct Function {
    /// name of the function symbol
    name: String,
    /// Argument names
    arg_names: Vec<String>,
    /// Argument types
    arg_types: Vec<RustType>,
    /// Return type
    ret_type: Option<RustType>,
}

#[derive(Debug, Copy, Clone)]
enum ISLOwnership {
    Keep,
    Take,
}

/// Returns an identifier based on `input` to avoid using a Rust-keyword.
fn guard_identifier(input: impl ToString) -> String {
    let input_str = input.to_string();
    match KEYWORD_TO_IDEN.get(input_str.as_str()) {
        Some(x) => x.to_string(),
        None => input.to_string(),
    }
}

/// Returns `true` only if `c_arg_t` is reference to a core isl object.
/// Note that we do not consider `isl_dim_type`, `isl_error`, `isl_fold`, or
/// `isl_stat` to be core isl objects.
fn is_isl_type(c_arg_t: &str) -> bool {
    let c_arg_t = &c_arg_t.to_string()[..];

    ISL_CORE_TYPES.contains(c_arg_t)
    || c_arg_t.strip_prefix("const ")
              .is_some_and(|c_arg_t| ISL_CORE_TYPES.contains(c_arg_t))
}

/// Returns `true` only if `c_arg_t` is a type not supported by
/// [`isl_bindings_generator`].
fn is_type_not_supported(c_arg_t: &CType) -> bool {
    // TODO this dismisses all callbacks and out pointers
    match c_arg_t {
        CType::Raw(c_arg_t) => {
            UNSUPPORTED_C_TYPES.contains(c_arg_t.as_str()) || c_arg_t.contains("**")
        }
        _ => false,
    }
}

/// Returns the name for `c_arg_t` to use in `extern "C"` block function
/// declarations.
fn to_extern_arg_t(c_arg_t: &CType) -> RustType {
    match c_arg_t {
        CType::IslDimType => C_TO_RS_BINDING["enum isl_dim_type"].clone(),
        CType::IslError => C_TO_RS_BINDING["enum isl_error"].clone(),
        CType::IslFold => C_TO_RS_BINDING["enum isl_fold"].clone(),
        CType::IslStat => C_TO_RS_BINDING["struct isl_stat"].clone(),
        CType::IslType(_) => RustType::UIntPtr,
        CType::IslSize => {
            // FIXME: Add add an assertion for this assumption.
            // KK: Assumption: `# typedef isl_size i32`
            RustType::I32
        }
        CType::IslBool => {
            // Using i32 for isl_bool as it is not a real type.
            // Will panic for -1
            RustType::I32
        }
        CType::CStr => RustType::Ptr(Const, Box::new(RustType::CChar)),
        CType::Int => RustType::I32,
        CType::Long => RustType::I64,
        CType::UInt => RustType::U32,
        CType::ULong => RustType::U64,
        CType::USize => RustType::USize,
        CType::Double => RustType::F64,
        CType::MutVoidStar => RustType::Ptr(Mut, Box::new(RustType::CVoid)),
        CType::ConstVoidStar => RustType::Ptr(Const, Box::new(RustType::CVoid)),
        CType::FnPointer { args, ret } => {
            RustType::FnPointer { args: args.iter().map(to_extern_arg_t).collect(),
                                  ret: ret.as_ref()
                                          .map(|box ret| to_extern_arg_t(ret))
                                          .map(Box::new) }
        }
        CType::Raw(c_arg_t) => {
            panic!("Unexpected type: {}", c_arg_t)
        }
    }
}

/// Returns the name for `c_arg_t` to use in the rust-binding function.
fn to_rust_arg_t(c_arg_t: CType, ownership: Option<ISLOwnership>) -> RustType {
    match c_arg_t {
        CType::IslDimType => C_TO_RS_BINDING["enum isl_dim_type"].clone(),
        CType::IslError => C_TO_RS_BINDING["enum isl_error"].clone(),
        CType::IslFold => C_TO_RS_BINDING["enum isl_fold"].clone(),
        CType::IslStat => C_TO_RS_BINDING["struct isl_stat"].clone(),
        CType::IslType(c_arg_t) => {
            let c_arg_t = c_arg_t.strip_prefix("const ").unwrap_or(&c_arg_t);

            match ownership.unwrap() {
                ISLOwnership::Keep => RustType::Ref(Box::new(C_TO_RS_BINDING[c_arg_t].clone())),
                ISLOwnership::Take => C_TO_RS_BINDING[c_arg_t].clone(),
            }
        }
        CType::IslSize => {
            // FIXME: Add add an assertion for this assumption.
            // KK: Assumption: `# typedef isl_size i32`
            RustType::I32
        }
        CType::IslBool => {
            // Using i32 for isl_bool as it is not a real type.
            // Will panic for -1
            RustType::Bool
        }
        CType::CStr => RustType::Ref(Box::new(RustType::Str)),
        CType::Int => RustType::I32,
        CType::Long => RustType::I64,
        CType::UInt => RustType::U32,
        CType::ULong => RustType::U64,
        CType::USize => RustType::USize,
        CType::Double => RustType::F64,
        CType::MutVoidStar => RustType::Ptr(Mut, Box::new(RustType::CVoid)),
        CType::ConstVoidStar => RustType::Ptr(Const, Box::new(RustType::CVoid)),
        CType::FnPointer { args, ret } => {
            RustType::FnPointer { args: args.into_iter()
                                            .map(|arg| to_extern_arg_t(&arg))
                                            .collect(),
                                  ret: ret.map(|box ret| to_extern_arg_t(&ret)).map(Box::new) }
        }
        CType::Raw(c_arg_t) => {
            panic!("Unexpected type: {}", c_arg_t)
        }
    }
}

/// Imports `ty_name` from the correct path for `scope`.
fn import_type(scope: &mut Scope, ty_name: &RustType) {
    match ty_name {
        RustType::UIntPtr => {
            scope.import("libc", "uintptr_t");
        }
        RustType::I32
        | RustType::U32
        | RustType::Bool
        | RustType::U64
        | RustType::I64
        | RustType::F64
        | RustType::USize => {}
        RustType::Str => {
            scope.import("std::ffi", "CString");
            scope.import("std::ffi", "CStr");
        }
        RustType::CChar => {
            scope.import("std::os::raw", "c_char");
        }
        RustType::CVoid => {
            scope.import("std::os::raw", "c_void");
        }
        RustType::Ref(t) => import_type(scope, t),
        RustType::Ptr(_, t) => import_type(scope, t),
        x if ISL_TYPES_RS.contains(x) => {
            scope.import("crate::bindings", &x.to_string());
        }
        RustType::FnPointer { args, ret } => {
            for arg in args {
                import_type(scope, arg);
            }
            if let Some(ret) = ret {
                import_type(scope, ret);
            }
        }
        RustType::DimType
        | RustType::Error
        | RustType::Fold
        | RustType::Stat
        | RustType::Raw(_) => panic!("Unknown type '{}'.", ty_name),
    };
}

/// Updates `func` by adding a line shadowing the variable `var_name` to pass it
/// legally to an external function.
fn preprocess_var_to_extern_func(func: &mut codegen::Function, rs_ty_name: &RustType,
                                 var_name: impl ToString) {
    let var_name = var_name.to_string();

    match rs_ty_name {
        RustType::UIntPtr
        | RustType::I32
        | RustType::U32
        | RustType::Bool
        | RustType::U64
        | RustType::I64
        | RustType::F64
        | RustType::USize
        | RustType::DimType
        | RustType::Error
        | RustType::Fold
        | RustType::Stat
        | RustType::Ptr(_, box RustType::CVoid)
        | RustType::FnPointer { .. } => {}
        RustType::Ref(box RustType::Str) => {
            func.line(format!("let {} = CString::new({}).unwrap();", var_name, var_name));
            func.line(format!("let {} = {}.as_ptr();", var_name, var_name));
        }
        x if ISL_TYPES_RS.contains(x) => {
            func.line(format!("let mut {} = {};", var_name, var_name));
            func.line(format!("{}.do_not_free_on_drop();", var_name));
            func.line(format!("let {} = {}.ptr;", var_name, var_name));
        }
        RustType::Ref(box ref x) if ISL_TYPES_RS.contains(x) => {
            func.line(format!("let {} = {}.ptr;", var_name, var_name));
        }
        RustType::CVoid
        | RustType::CChar
        | RustType::Str
        | RustType::Ref(_)
        | RustType::Ptr(_, _)
        | RustType::Raw(_) => unimplemented!("{}", rs_ty_name),
    };
}

/// Updates `func` by adding a line shadowing the variable `var_name` to refer
/// it's corresponding type in Rust land.
fn postprocess_var_from_extern_func(func: &mut codegen::Function, rs_ty_name: Option<RustType>,
                                    var_name: impl ToString, can_emit_error_message: bool) {
    match rs_ty_name {
        Some(rs_ty_name) => {
            let var_name = var_name.to_string();

            match rs_ty_name {
                RustType::UIntPtr
                | RustType::I32
                | RustType::U32
                | RustType::U64
                | RustType::I64
                | RustType::F64
                | RustType::USize
                | RustType::DimType
                | RustType::Error
                | RustType::Fold
                | RustType::Stat
                | RustType::Ptr(_, box RustType::CVoid)
                | RustType::FnPointer { .. } => {}
                RustType::Ref(box RustType::Str) => {
                    func.line(format!("let {} = unsafe {{ CStr::from_ptr({}) }};",
                                      var_name, var_name));
                    func.line(format!("let {} = {}.to_str().unwrap();", var_name, var_name));
                }
                RustType::Bool => {
                    func.line(format!("let {} = match {} {{", var_name, var_name));
                    func.line("    0 => false,");
                    func.line("    1 => true,");
                    if can_emit_error_message {
                        func.line("    _ => panic!(\"ISL error: {}\", context_for_error_message.last_error_msg()),");
                    } else {
                        func.line("    _ => panic!(\"ISL error\"),");
                    }
                    func.line("};");
                }
                ref x | RustType::Ref(box ref x) if ISL_TYPES_RS.contains(x) => {
                    func.line(format!("if {} == 0 {{", var_name));
                    if can_emit_error_message {
                        func.line("    panic!(\"ISL error: {}\", context_for_error_message.last_error_msg());");
                    } else {
                        func.line("    panic!(\"ISL error\");");
                    }
                    func.line("}");
                    func.line(format!("let {} = {} {{ ptr: {}, should_free_on_drop: true }};",
                                      var_name, rs_ty_name, var_name));
                }
                RustType::CVoid
                | RustType::CChar
                | RustType::Str
                | RustType::Ref(_)
                | RustType::Ptr(_, _)
                | RustType::Raw(_) => unimplemented!("{}", rs_ty_name),
            };
        }
        None => {
            // Function does not return anything.
        }
    };
}

/// Returns the method name for the binding to generate on the Rust end.
fn get_rust_method_name(func_decl: &clang::Entity, c_struct_t: &CType) -> String {
    let c_name = func_decl.get_name().unwrap();
    let CType::IslType(c_struct_t) = c_struct_t else {
        panic!()
    };
    // Remove the type prefix (For eg. isl_basic_set_read_from_str -> read_from_str)
    let name_in_rust = c_name[c_struct_t.len() + 1..].to_string();
    guard_identifier(name_in_rust)
}

fn get_extern_and_bindings_functions(func_decls: Vec<clang::Entity>, src_t: &CType)
                                     -> HashSet<(Function, Function)> {
    // external_functions: External functions that must be declared.
    // bindings_functions: Rust functions that are to be generated.
    let mut extern_and_bindings_functions: HashSet<(Function, Function)> = HashSet::new();

    for func_decl in func_decls {
        // println!("Traversing {}", func_decl.get_name().unwrap());
        let arguments = func_decl.get_arguments().unwrap();

        // {{{ parse borrowing_rules
        let mut borrowing_rules: Vec<Option<ISLOwnership>> = vec![];
        for arg in arguments.iter() {
            let arg_children = arg.get_children();
            let qualifier =
                arg_children.iter()
                            .find(|entity| entity.get_kind() == clang::EntityKind::AnnotateAttr)
                            .and_then(|entity| entity.get_display_name());
            let borrow_rule = match qualifier.as_deref() {
                Some("isl_take") => Some(ISLOwnership::Take),
                Some("isl_keep") => Some(ISLOwnership::Keep),
                Some("isl_give") => None, // FIXME
                Some(x) => panic!("Unknown ownership rule {} in {}",
                                  x,
                                  func_decl.get_name().unwrap()),
                None => {
                    if arg.get_type()
                          .unwrap()
                          .get_canonical_type()
                          .get_display_name()
                       == "struct isl_ctx *"
                    {
                        // isl_ctx is always kept
                        Some(ISLOwnership::Keep)
                    } else if func_decl.get_name().unwrap().ends_with("_copy") {
                        Some(ISLOwnership::Keep)
                    } else {
                        None
                    }
                }
            };

            borrowing_rules.push(borrow_rule);
        }

        // }}}

        let c_arg_types = arguments.iter()
                                   .map(|x| CType::from(x.get_type().unwrap()))
                                   .collect::<Vec<_>>();
        let ret_type = func_decl.get_result_type()
                                .filter(|x| x.get_display_name() != "void")
                                .map(|x| x)
                                .map(CType::from);

        if c_arg_types.iter().any(|x| is_type_not_supported(x))
           || ret_type.clone()
                      .map_or(false, |x| is_type_not_supported(&x))
        {
            println!("SKIPPING {}", func_decl.get_name().unwrap());
            continue;
        }
        let c_arg_names =
            arguments.iter()
                     .map(|x| x.get_name().unwrap())
                     .map(|x| KEYWORD_TO_IDEN.get(x.as_str()).map_or(x, |y| y.to_string()))
                     .collect::<Vec<_>>();

        let extern_func =
            Function { name: func_decl.get_name().unwrap(),
                       arg_names: c_arg_names.clone(),
                       arg_types: c_arg_types.iter().map(to_extern_arg_t).collect(),
                       ret_type: ret_type.as_ref().map(to_extern_arg_t) };

        let binding_func =
            Function { name: get_rust_method_name(&func_decl, src_t),
                       arg_names: c_arg_names,
                       arg_types: zip(c_arg_types, borrowing_rules).map(|(x, brw)| {
                                                                       to_rust_arg_t(x, brw)
                                                                   })
                                                                   .collect(),
                       ret_type: ret_type.map(|x| to_rust_arg_t(x, Some(ISLOwnership::Take))) };

        extern_and_bindings_functions.insert((extern_func, binding_func));
    }

    extern_and_bindings_functions
}

/// Generates Rust bindings for type `dst_t` from the C-struct `src_t`. Searches
/// for functions within `src_file` and the generated code is written to
/// `dst_file`.
fn implement_bindings(dst_t: &RustType, src_t: &CType, dst_file: &str, src_files: &[&str]) {
    let clang = clang::Clang::new().unwrap();
    let index = clang::Index::new(&clang, false, true);

    let (extern_funcs, binding_funcs): (Vec<_>, Vec<_>) =
        src_files.iter()
                 .map(|src_file| {
                     let t_unit =
                         index.parser(src_file)
                              .arguments(&["-I", "isl/include/", "-I", "/opt/homebrew/opt/llvm/include/c++/v1", "-I", "/opt/homebrew/opt/llvm/lib/clang/20/include", "-isysroot", "/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk", "-D", "__isl_take=[[clang::annotate(\"isl_take\")]]", "-D", "__isl_keep=[[clang::annotate(\"isl_keep\")]]", "-D", "__isl_give=[[clang::annotate(\"isl_give\")]]"])
                              .parse()
                              .unwrap();

                     let CType::IslType(src_t_str) = src_t else { panic!() };

                     // func_decls: Functions for which bindings are to be generated
                     let func_decls: Vec<_> =
                         t_unit.get_entity()
                               .get_children()
                               .into_iter()
                               .filter(|e| {
                                   e.get_kind() == clang::EntityKind::FunctionDecl
                                   && e.get_name().is_some()
                                   && e.get_name().unwrap().starts_with(src_t_str)
                                   // match isl_set, but not isl_set_list
                                   && ! e.get_name().unwrap().starts_with(format!("{}_list", src_t_str).as_str())
                                   && e.get_location().is_some()
                                   && *src_file
                                      == e.get_location().unwrap().get_presumed_location().0
                               })
                               .collect();
                     get_extern_and_bindings_functions(func_decls, src_t)
                 }).concat().into_iter().unzip();

    let mut scope = Scope::new();

    // {{{ Generate `use ...` statements.

    // Always use uintptr_t as dst_t's struct requires it.
    import_type(&mut scope, &RustType::UIntPtr);
    for func in extern_funcs.iter().chain(binding_funcs.iter()) {
        match &func.ret_type {
            Some(x) if x != dst_t && x != &RustType::Ref(Box::new(dst_t.clone())) => {
                import_type(&mut scope, x)
            }
            _ => {}
        };
        for arg_t in func.arg_types.iter() {
            if arg_t != dst_t && arg_t != &RustType::Ref(Box::new(dst_t.clone())) {
                import_type(&mut scope, arg_t);
            }
        }
    }

    // }}}

    // {{{ Generate struct for dst_t

    scope.new_struct(&dst_t.to_string())
         .field("pub ptr", "uintptr_t")
         .field("pub should_free_on_drop", "bool")
         .vis("pub")
         .doc(format!("Wraps `{}`.", match src_t {
                  CType::IslType(t) => t,
                  _ => panic!(),
              }).as_str());

    // }}}

    // {{{ Declare the extern functions

    scope.raw("extern \"C\" {");
    for extern_func in extern_funcs.clone() {
        // TODO: Not ideal to emit raw strings, but `codegen` crate lacks support for
        // function declarations.
        // See https://gitlab.com/IovoslavIovchev/codegen/-/issues/11
        let args_str = zip(extern_func.arg_names, extern_func.arg_types).map(|(name, ty)| {
                                                                            format!("{}: {}",
                                                                                    name, ty)
                                                                        })
                                                                        .collect::<Vec<String>>()
                                                                        .join(", ");
        let ret_str = extern_func.ret_type
                                 .map_or("".to_string(), |x| format!(" -> {}", x));

        scope.raw(format!("    fn {}({}){};", extern_func.name, args_str, ret_str));
    }
    scope.raw("}");

    // }}}

    // {{{ impl Clone for `dst_t`.

    if binding_funcs.iter().any(|Function { name,
                                            arg_names: _,
                                            arg_types,
                                            ret_type, }| {
                                    match (&name[..], &arg_types[..], ret_type) {
                                        ("copy", [arg_type], Some(ret_type)) => {
                                            arg_type == &RustType::Ref(Box::new(dst_t.clone()))
                                            && ret_type == dst_t
                                        }
                                        _ => false,
                                    }
                                })
    {
        let clone_impl = scope.new_impl(&dst_t.to_string());
        clone_impl.impl_trait("Clone");
        clone_impl.new_fn("clone")
                  .arg_ref_self()
                  .ret(&dst_t.to_string())
                  .line("self.copy()");
    }

    // }}}

    // {{{ impl PartialEq, Eq for `dst_t`.

    if binding_funcs.iter().any(|Function { name,
                                            arg_names: _,
                                            arg_types,
                                            ret_type, }| {
                                    matches!((&name[..], &arg_types[..], ret_type),
                                    ("is_equal", [arg1_type, arg2_type], Some(ret_type))
                                        if arg1_type == &RustType::Ref(Box::new(dst_t.clone()))
                                           && arg2_type == &RustType::Ref(Box::new(dst_t.clone()))
                                           && ret_type == &RustType::Bool
                                    )
                                })
    {
        let partial_eq_impl = scope.new_impl(&dst_t.to_string());
        partial_eq_impl.impl_trait("PartialEq");
        partial_eq_impl.new_fn("eq")
                       .arg_ref_self()
                       .arg("other", "&Self")
                       .ret("bool")
                       .line("self.is_equal(other)");

        let eq_impl = scope.new_impl(&dst_t.to_string());
        eq_impl.impl_trait("Eq");
    }

    // }}}

    // {{{ impl FromIterator for `dst_t`.

    if let RustType::Raw(dst_t) = dst_t {
        if let Some(elem_t) = dst_t.strip_suffix("List") {
            let from_iterator_impl = scope.new_impl(dst_t);
            from_iterator_impl.impl_trait(format!("FromIterator<{}>", elem_t));
            from_iterator_impl.new_fn("from_iter")
                              .generic("T")
                              .bound("T", format!("IntoIterator<Item = {}>", elem_t))
                              .arg("iter", "T")
                              .ret("Self")
                              .line("let mut iter = iter.into_iter().peekable();")
                              .line("let ctx = iter.peek().unwrap().get_ctx();")
                              .line("let (size, _) = iter.size_hint();")
                              .line("let mut res = Self::alloc(&ctx, size as _);")
                              .line("for x in iter {")
                              .line("res = res.add(x);")
                              .line("}")
                              .line("res");
        }
    }

    // }}}

    // {{{ impl Arithmetic Ops for `dst_t`.

    for (trait_name, impl_fn_name, fn_name) in [("core::ops::Add", "add", "add"),
                                                ("core::ops::Sub", "sub", "sub"),
                                                ("core::ops::Mul", "mul", "mul"),
                                                ("core::ops::Div", "div", "div"),
                                                ("core::ops::Rem", "rem", "mod_")]
    {
        if binding_funcs.iter().any(|Function { name,
                                                arg_names: _,
                                                arg_types,
                                                ret_type, }| {
                                        matches!((&name[..], &arg_types[..], ret_type),
                                        (fn_name2, [arg1_type, arg2_type], Some(ret_type))
                                            if fn_name == fn_name2
                                               && arg1_type == dst_t
                                               && arg2_type == dst_t
                                               && ret_type == dst_t
                                        )
                                    })
        {
            let trait_impl = scope.new_impl(&dst_t.to_string());
            trait_impl.impl_trait(trait_name);
            trait_impl.associate_type("Output", dst_t.to_string());
            trait_impl.new_fn(impl_fn_name)
                      .arg_self()
                      .arg("rhs", dst_t.to_string())
                      .ret(dst_t.to_string())
                      .line(format!("self.{}(rhs)", fn_name));
        }
    }

    // }}}

    // {{{ Implement the struct 'dst_t'

    let dst_impl = scope.new_impl(&dst_t.to_string());

    // KK: Assumption guarded by assertion. There is a one-to-one mapping between
    // the binding and the external functions
    assert_eq!(extern_funcs.len(), binding_funcs.len());

    for (extern_func, binding_func) in zip(extern_funcs, binding_funcs) {
        let mut impl_fn = dst_impl.new_fn(binding_func.name.as_str())
                                  .vis("pub")
                                  .doc(format!("Wraps `{}`.", extern_func.name).as_str());

        // FIXME: /!\ Big FIXME. This logic doesn't account
        let mut bnd_arg_names: Vec<String> = binding_func.arg_names.clone();
        let mut bnd_arg_types: Vec<RustType> = binding_func.arg_types.clone();
        let mut arg_names_in_fn_body: Vec<String> = vec![];

        // emit first argument to the method
        if bnd_arg_types.first().is_some_and(|bnd_arg_type| {
                                    bnd_arg_type == &RustType::Ref(Box::new(dst_t.clone()))
                                })
        {
            // consume the first argument
            impl_fn = impl_fn.arg_ref_self();
            bnd_arg_names = bnd_arg_names[1..].to_vec();
            bnd_arg_types = bnd_arg_types[1..].to_vec();
            arg_names_in_fn_body.push("self".to_string());
        } else if bnd_arg_types.first()
                               .is_some_and(|bnd_arg_type| bnd_arg_type == dst_t)
        {
            // consume the first argument
            impl_fn = impl_fn.arg_self();
            bnd_arg_names = bnd_arg_names[1..].to_vec();
            bnd_arg_types = bnd_arg_types[1..].to_vec();
            arg_names_in_fn_body.push("self".to_string());
        } else {
            // do nothing
        }

        // add the rest of the arguments
        for (arg_name, arg_t) in zip(bnd_arg_names.iter(), bnd_arg_types.iter()) {
            impl_fn = impl_fn.arg(arg_name, arg_t.to_string());
            arg_names_in_fn_body.push(arg_name.to_string());
        }

        // add the return type
        match binding_func.ret_type.clone() {
            Some(x) => impl_fn.ret(x.to_string()),
            None => impl_fn,
        };

        // Store context in case we need it later for error handling
        let can_emit_error_message = if let Some(rs_ty_name) = &binding_func.ret_type {
            if rs_ty_name != &RustType::Raw("Context".to_owned())
               && arg_names_in_fn_body.first()
                                      .is_some_and(|name| name == "self")
               && (ISL_TYPES_RS.contains(rs_ty_name)
                   || (if let RustType::Ref(t) = rs_ty_name {
                       ISL_TYPES_RS.contains(&**t)
                   } else {
                       false
                   })
                   || rs_ty_name == &RustType::Bool)
            {
                if dst_t == &RustType::Raw("Context".to_owned()) {
                    impl_fn.line("let context_for_error_message = &self;");
                } else {
                    impl_fn.line("let context_for_error_message = self.get_ctx();");
                }
                true
            } else {
                false
            }
        } else {
            false
        };

        // Implement the function
        for (arg_type, (arg_name, arg_name_in_fn_body)) in zip(binding_func.arg_types.iter(),
                                                               zip(binding_func.arg_names.iter(),
                                                                   arg_names_in_fn_body.iter()))
        {
            if arg_name != arg_name_in_fn_body {
                impl_fn.line(format!("let {} = {};", arg_name, arg_name_in_fn_body));
            }

            preprocess_var_to_extern_func(impl_fn, arg_type, arg_name);
        }

        let passed_args_str = binding_func.arg_names.join(", ");

        impl_fn.line(format!("let isl_rs_result = unsafe {{ {}({}) }};",
                             extern_func.name, passed_args_str));

        postprocess_var_from_extern_func(impl_fn,
                                         binding_func.ret_type.clone(),
                                         "isl_rs_result",
                                         can_emit_error_message);

        // {{{ Do not free isl_ctx* if not from isl_ctx_alloc.

        match binding_func.ret_type {
            Some(x)
                if (x == C_TO_RS_BINDING["struct isl_ctx *"]
                    && extern_func.name != "isl_ctx_alloc") =>
            {
                impl_fn.line("let mut isl_rs_result = isl_rs_result;");
                impl_fn.line("isl_rs_result.do_not_free_on_drop();");
            }
            _ => {}
        };

        // }}}

        impl_fn.line("isl_rs_result");
    }

    dst_impl.new_fn("do_not_free_on_drop")
            .vis("pub")
            .doc("Does not call isl_xxx_free() on being dropped. (For internal use only.)")
            .arg_mut_self()
            .line("self.should_free_on_drop = false;");

    // }}}

    // {{{ impl Drop for `dst_t`.

    let drop_impl = scope.new_impl(&dst_t.to_string());
    drop_impl.impl_trait("Drop");
    drop_impl.new_fn("drop")
             .arg_mut_self()
             .line("if self.should_free_on_drop {")
             .line(format!("    unsafe {{ {}_free(self.ptr); }}", match src_t {
                       CType::IslType(t) => t,
                       _ => panic!(),
                   }))
             .line("}");

    // }}}

    // Write the generated code
    fs::write(dst_file,
              format!("// Automatically generated by isl_bindings_generator.\n// LICENSE: MIT\n\n{}", scope.to_string())
              ).unwrap_or_else(|_| panic!("error writing to {} file.", dst_file));
}

/// Generate rust code to define an enum declation in rust and
/// writes the generated to the `dst_file` path. (Touches the file if not
/// already present)
///
/// # Warnings
///  
/// - Overwrites the contents of `dst_file`.
fn define_enum(c_type: &str, prefix: &str, dst_file: &str, src_file: &str) {
    let clang = clang::Clang::new().unwrap();
    let index = clang::Index::new(&clang, false, true);
    let t_unit = index.parser(src_file)
                      .arguments(&["-I", "isl/include/", "-I", "/opt/homebrew/opt/llvm/include/c++/v1", "-I", "/opt/homebrew/opt/llvm/lib/clang/20/include", "-isysroot", "/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk", "-D", "__isl_take=[[clang::annotate(\"isl_take\")]]", "-D", "__isl_keep=[[clang::annotate(\"isl_keep\")]]", "-D", "__isl_give=[[clang::annotate(\"isl_give\")]]"])
                      .detailed_preprocessing_record(true)
                      .parse()
                      .unwrap();

    let c_enum_decl = t_unit.get_entity()
                            .get_children()
                            .into_iter()
                            .find(|e| {
                                e.get_kind() == clang::EntityKind::EnumDecl
                                && e.get_display_name().as_ref().map(String::as_str) == Some(c_type)
                            })
                            .unwrap();

    // KK: Assertion to guard assumption
    assert!(c_enum_decl.get_children()
                       .into_iter()
                       .all(|x| x.get_kind() == clang::EntityKind::EnumConstantDecl));

    let mut c_variant_names = vec![];
    let mut c_synonyms = vec![];

    for variant in c_enum_decl.get_children() {
        let name = variant.get_display_name().unwrap();
        if let Some(synonym) = variant.get_children()
                                      .pop()
                                      .and_then(|x| x.get_display_name())
        {
            c_synonyms.push((name, synonym));
        } else {
            let value = variant.get_children().pop().and_then(|x| x.evaluate());
            c_variant_names.push((name, value));
        }
    }

    // KK: Assertion to guard assumption
    assert!(c_variant_names.iter().all(|(x, _)| x.starts_with(prefix)));

    let rs_type = C_TO_RS_BINDING[format!("enum {}", c_type).as_str()].clone();

    let mut scope = Scope::new();
    let rs_enum_decl = scope.new_enum(rs_type.to_string())
                            .vis("pub")
                            .repr("C")
                            .derive("Clone")
                            .derive("Copy")
                            .derive("Debug");
    for (c_variant_name, c_variant_value) in c_variant_names {
        let name_in_rust = c_variant_name[prefix.len()..].to_string();
        // convert variant name to camel case
        let name_in_rust = format!("{}{}",
                                   &name_in_rust[..1].to_uppercase(),
                                   &name_in_rust[1..]);
        let name_in_rust = match c_variant_value {
            Some(clang::EvaluationResult::SignedInteger(x)) => {
                format!("{name_in_rust} = {x}")
            }
            Some(clang::EvaluationResult::UnsignedInteger(x)) => {
                format!("{name_in_rust} = {x}")
            }
            Some(_) | None => name_in_rust,
        };
        rs_enum_decl.new_variant(guard_identifier(name_in_rust));
    }

    let rs_enum_impl = scope.new_impl(&rs_type.to_string());
    for (c_synonym_name, c_synonym_value) in c_synonyms {
        let name_in_rust = c_synonym_name[prefix.len()..].to_string();
        // convert variant name to camel case
        let name_in_rust = format!("{}{}",
                                   &name_in_rust[..1].to_uppercase(),
                                   &name_in_rust[1..]);
        let value_in_rust = c_synonym_value[prefix.len()..].to_string();
        // convert variant name to camel case
        let value_in_rust = format!("{}{}",
                                    &value_in_rust[..1].to_uppercase(),
                                    &value_in_rust[1..]);
        rs_enum_impl.associate_const(guard_identifier(name_in_rust),
                                     rs_type.to_string(),
                                     format!("{rs_type}::{}", &guard_identifier(value_in_rust)),
                                     "pub");
    }

    // Write the generated code
    fs::write(dst_file,
              format!("// Automatically generated by isl_bindings_generator.\n// LICENSE: MIT\n{}", scope.to_string())
              ).expect("error writing to enum file");
}

/// Populates `src/bindings/mod.rs` with isl types.
fn generate_bindings_mod(dst_file: &str) {
    let mut scope = Scope::new();

    scope.raw("mod dim_type;");
    scope.raw("mod error;");
    scope.raw("mod fold;");
    scope.raw("mod stat;");
    scope.raw("mod fixed_box;");
    scope.raw("mod stride_info;");
    scope.raw("mod context;");
    scope.raw("mod space;");
    scope.raw("mod local_space;");
    scope.raw("mod id;");
    scope.raw("mod id_list;");
    scope.raw("mod multi_id;");
    scope.raw("mod val;");
    scope.raw("mod val_list;");
    scope.raw("mod multi_val;");
    scope.raw("mod point;");
    scope.raw("mod mat;");
    scope.raw("mod vec;");
    scope.raw("mod bset;");
    scope.raw("mod bset_list;");
    scope.raw("mod set;");
    scope.raw("mod set_list;");
    scope.raw("mod bmap;");
    scope.raw("mod bmap_list;");
    scope.raw("mod map;");
    scope.raw("mod map_list;");
    scope.raw("mod union_set;");
    scope.raw("mod union_set_list;");
    scope.raw("mod union_map;");
    scope.raw("mod union_map_list;");
    scope.raw("mod constraint;");
    scope.raw("mod constraint_list;");
    scope.raw("mod aff;");
    scope.raw("mod aff_list;");
    scope.raw("mod term;");
    scope.raw("mod qpolynomial;");
    scope.raw("mod qpolynomial_list;");
    scope.raw("mod qpolynomial_fold;");
    scope.raw("mod multi_aff;");
    scope.raw("mod multi_pw_aff;");
    scope.raw("mod multi_union_pw_aff;");
    scope.raw("mod pw_aff;");
    scope.raw("mod pw_aff_list;");
    scope.raw("mod pw_multi_aff;");
    scope.raw("mod pw_multi_aff_list;");
    scope.raw("mod pw_qpolynomial;");
    scope.raw("mod pw_qpolynomial_list;");
    scope.raw("mod pw_qpolynomial_fold;");
    scope.raw("mod pw_qpolynomial_fold_list;");
    scope.raw("mod union_pw_aff;");
    scope.raw("mod union_pw_aff_list;");
    scope.raw("mod union_pw_multi_aff;");
    scope.raw("mod union_pw_multi_aff_list;");
    scope.raw("mod union_pw_qpolynomial;");
    scope.raw("mod union_pw_qpolynomial_fold;");
    scope.raw("mod printer;");

    scope.raw("pub use dim_type::DimType;");
    scope.raw("pub use error::Error;");
    scope.raw("pub use fold::Fold;");
    scope.raw("pub use stat::Stat;");
    scope.raw("pub use fixed_box::FixedBox;");
    scope.raw("pub use stride_info::StrideInfo;");

    scope.raw("pub use context::Context;");
    scope.raw("pub use space::Space;");
    scope.raw("pub use local_space::LocalSpace;");
    scope.raw("pub use id::Id;");
    scope.raw("pub use id_list::IdList;");
    scope.raw("pub use multi_id::MultiId;");
    scope.raw("pub use val::Val;");
    scope.raw("pub use val_list::ValList;");
    scope.raw("pub use multi_val::MultiVal;");
    scope.raw("pub use point::Point;");
    scope.raw("pub use mat::Mat;");
    scope.raw("pub use vec::Vec;");
    scope.raw("pub use bset::BasicSet;");
    scope.raw("pub use bset_list::BasicSetList;");
    scope.raw("pub use set::Set;");
    scope.raw("pub use set_list::SetList;");
    scope.raw("pub use bmap::BasicMap;");
    scope.raw("pub use bmap_list::BasicMapList;");
    scope.raw("pub use map::Map;");
    scope.raw("pub use map_list::MapList;");
    scope.raw("pub use union_set::UnionSet;");
    scope.raw("pub use union_set_list::UnionSetList;");
    scope.raw("pub use union_map::UnionMap;");
    scope.raw("pub use union_map_list::UnionMapList;");
    scope.raw("pub use constraint::Constraint;");
    scope.raw("pub use constraint_list::ConstraintList;");
    scope.raw("pub use aff::Aff;");
    scope.raw("pub use aff_list::AffList;");
    scope.raw("pub use term::Term;");
    scope.raw("pub use qpolynomial::QPolynomial;");
    scope.raw("pub use qpolynomial_list::QPolynomialList;");
    scope.raw("pub use qpolynomial_fold::QPolynomialFold;");
    scope.raw("pub use multi_aff::MultiAff;");
    scope.raw("pub use multi_pw_aff::MultiPwAff;");
    scope.raw("pub use multi_union_pw_aff::MultiUnionPwAff;");
    scope.raw("pub use pw_aff::PwAff;");
    scope.raw("pub use pw_aff_list::PwAffList;");
    scope.raw("pub use pw_multi_aff::PwMultiAff;");
    scope.raw("pub use pw_multi_aff_list::PwMultiAffList;");
    scope.raw("pub use pw_qpolynomial::PwQPolynomial;");
    scope.raw("pub use pw_qpolynomial_list::PwQPolynomialList;");
    scope.raw("pub use pw_qpolynomial_fold::PwQPolynomialFold;");
    scope.raw("pub use pw_qpolynomial_fold_list::PwQPolynomialFoldList;");
    scope.raw("pub use union_pw_aff::UnionPwAff;");
    scope.raw("pub use union_pw_aff_list::UnionPwAffList;");
    scope.raw("pub use union_pw_multi_aff::UnionPwMultiAff;");
    scope.raw("pub use union_pw_multi_aff_list::UnionPwMultiAffList;");
    scope.raw("pub use union_pw_qpolynomial::UnionPwQPolynomial;");
    scope.raw("pub use union_pw_qpolynomial_fold::UnionPwQPolynomialFold;");
    scope.raw("pub use printer::Printer;");

    // Write the generated code
    fs::write(dst_file, scope.to_string()).expect("error writing to lib file");
}

fn main() {
    if Path::new("src/bindings/").is_dir() {
        fs::remove_dir_all("src/bindings/").expect("Removing `src/bindings` failed.");
    }

    fs::create_dir("src/bindings/").unwrap();

    define_enum("isl_dim_type",
                "isl_dim_",
                "src/bindings/dim_type.rs",
                "isl/include/isl/space_type.h");

    define_enum("isl_error",
                "isl_error_",
                "src/bindings/error.rs",
                "isl/include/isl/ctx.h");

    define_enum("isl_fold",
                "isl_fold_",
                "src/bindings/fold.rs",
                "isl/include/isl/polynomial_type.h");

    define_enum("isl_stat",
                "isl_stat_",
                "src/bindings/stat.rs",
                "isl/include/isl/ctx.h");

    // {{{ emit bindings for primitive types

    implement_bindings(&RustType::Raw("Context".to_owned()),
                       &CType::IslType("isl_ctx".to_owned()),
                       "src/bindings/context.rs",
                       &["isl/include/isl/ctx.h"]);
    implement_bindings(&RustType::Raw("Space".to_owned()),
                       &CType::IslType("isl_space".to_owned()),
                       "src/bindings/space.rs",
                       &["isl/include/isl/space.h"]);
    implement_bindings(&RustType::Raw("LocalSpace".to_owned()),
                       &CType::IslType("isl_local_space".to_owned()),
                       "src/bindings/local_space.rs",
                       &["isl/include/isl/local_space.h"]);
    implement_bindings(&RustType::Raw("Id".to_owned()),
                       &CType::IslType("isl_id".to_owned()),
                       "src/bindings/id.rs",
                       &["isl/include/isl/id.h"]);
    implement_bindings(&RustType::Raw("IdList".to_owned()),
                       &CType::IslType("isl_id_list".to_owned()),
                       "src/bindings/id_list.rs",
                       &["isl/include/isl/id.h"]);
    implement_bindings(&RustType::Raw("MultiId".to_owned()),
                       &CType::IslType("isl_multi_id".to_owned()),
                       "src/bindings/multi_id.rs",
                       &["isl/include/isl/id.h"]);
    implement_bindings(&RustType::Raw("Val".to_owned()),
                       &CType::IslType("isl_val".to_owned()),
                       "src/bindings/val.rs",
                       &["isl/include/isl/val.h"]);
    implement_bindings(&RustType::Raw("ValList".to_owned()),
                       &CType::IslType("isl_val_list".to_owned()),
                       "src/bindings/val_list.rs",
                       &["isl/include/isl/val.h"]);
    implement_bindings(&RustType::Raw("MultiVal".to_owned()),
                       &CType::IslType("isl_multi_val".to_owned()),
                       "src/bindings/multi_val.rs",
                       &["isl/include/isl/val.h"]);
    implement_bindings(&RustType::Raw("Point".to_owned()),
                       &CType::IslType("isl_point".to_owned()),
                       "src/bindings/point.rs",
                       &["isl/include/isl/point.h"]);
    implement_bindings(&RustType::Raw("Mat".to_owned()),
                       &CType::IslType("isl_mat".to_owned()),
                       "src/bindings/mat.rs",
                       &["isl/include/isl/mat.h"]);
    implement_bindings(&RustType::Raw("Vec".to_owned()),
                       &CType::IslType("isl_vec".to_owned()),
                       "src/bindings/vec.rs",
                       &["isl/include/isl/vec.h"]);
    implement_bindings(&RustType::Raw("BasicSet".to_owned()),
                       &CType::IslType("isl_basic_set".to_owned()),
                       "src/bindings/bset.rs",
                       &["isl/include/isl/set.h", "isl/include/isl/constraint.h"]);
    implement_bindings(&RustType::Raw("BasicSetList".to_owned()),
                       &CType::IslType("isl_basic_set_list".to_owned()),
                       "src/bindings/bset_list.rs",
                       &["isl/include/isl/map_type.h", "isl/include/isl/set.h"]);
    implement_bindings(&RustType::Raw("Set".to_owned()),
                       &CType::IslType("isl_set".to_owned()),
                       "src/bindings/set.rs",
                       &["isl/include/isl/set.h", "isl/include/isl/constraint.h"]);
    implement_bindings(&RustType::Raw("SetList".to_owned()),
                       &CType::IslType("isl_set_list".to_owned()),
                       "src/bindings/set_list.rs",
                       &["isl/include/isl/map_type.h", "isl/include/isl/set.h"]);
    implement_bindings(&RustType::Raw("BasicMap".to_owned()),
                       &CType::IslType("isl_basic_map".to_owned()),
                       "src/bindings/bmap.rs",
                       &["isl/include/isl/map.h", "isl/include/isl/constraint.h"]);
    implement_bindings(&RustType::Raw("BasicMapList".to_owned()),
                       &CType::IslType("isl_basic_map_list".to_owned()),
                       "src/bindings/bmap_list.rs",
                       &["isl/include/isl/map_type.h", "isl/include/isl/map.h"]);
    implement_bindings(&RustType::Raw("Map".to_owned()),
                       &CType::IslType("isl_map".to_owned()),
                       "src/bindings/map.rs",
                       &["isl/include/isl/map.h", "isl/include/isl/constraint.h"]);
    implement_bindings(&RustType::Raw("MapList".to_owned()),
                       &CType::IslType("isl_map_list".to_owned()),
                       "src/bindings/map_list.rs",
                       &["isl/include/isl/map_type.h", "isl/include/isl/map.h"]);
    implement_bindings(&RustType::Raw("UnionSet".to_owned()),
                       &CType::IslType("isl_union_set".to_owned()),
                       "src/bindings/union_set.rs",
                       &["isl/include/isl/union_set_type.h",
                         "isl/include/isl/union_set.h"]);
    implement_bindings(&RustType::Raw("UnionSetList".to_owned()),
                       &CType::IslType("isl_union_set_list".to_owned()),
                       "src/bindings/union_set_list.rs",
                       &["isl/include/isl/union_set_type.h",
                         "isl/include/isl/union_set.h"]);
    implement_bindings(&RustType::Raw("UnionMap".to_owned()),
                       &CType::IslType("isl_union_map".to_owned()),
                       "src/bindings/union_map.rs",
                       &["isl/include/isl/union_map_type.h",
                         "isl/include/isl/union_map.h"]);
    implement_bindings(&RustType::Raw("UnionMapList".to_owned()),
                       &CType::IslType("isl_union_map_list".to_owned()),
                       "src/bindings/union_map_list.rs",
                       &["isl/include/isl/union_map_type.h",
                         "isl/include/isl/union_map.h"]);
    implement_bindings(&RustType::Raw("Constraint".to_owned()),
                       &CType::IslType("isl_constraint".to_owned()),
                       "src/bindings/constraint.rs",
                       &["isl/include/isl/constraint.h"]);
    implement_bindings(&RustType::Raw("ConstraintList".to_owned()),
                       &CType::IslType("isl_constraint_list".to_owned()),
                       "src/bindings/constraint_list.rs",
                       &["isl/include/isl/constraint.h"]);
    implement_bindings(&RustType::Raw("Aff".to_owned()),
                       &CType::IslType("isl_aff".to_owned()),
                       "src/bindings/aff.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("AffList".to_owned()),
                       &CType::IslType("isl_aff_list".to_owned()),
                       "src/bindings/aff_list.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("Term".to_owned()),
                       &CType::IslType("isl_term".to_owned()),
                       "src/bindings/term.rs",
                       &["isl/include/isl/polynomial.h"]);
    implement_bindings(&RustType::Raw("QPolynomial".to_owned()),
                       &CType::IslType("isl_qpolynomial".to_owned()),
                       "src/bindings/qpolynomial.rs",
                       &["isl/include/isl/polynomial.h"]);
    implement_bindings(&RustType::Raw("QPolynomialList".to_owned()),
                       &CType::IslType("isl_qpolynomial_list".to_owned()),
                       "src/bindings/qpolynomial_list.rs",
                       &["isl/include/isl/polynomial.h"]);
    implement_bindings(&RustType::Raw("QPolynomialFold".to_owned()),
                       &CType::IslType("isl_qpolynomial_fold".to_owned()),
                       "src/bindings/qpolynomial_fold.rs",
                       &["isl/include/isl/polynomial.h"]);
    implement_bindings(&RustType::Raw("MultiAff".to_owned()),
                       &CType::IslType("isl_multi_aff".to_owned()),
                       "src/bindings/multi_aff.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("MultiPwAff".to_owned()),
                       &CType::IslType("isl_multi_pw_aff".to_owned()),
                       "src/bindings/multi_pw_aff.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("MultiUnionPwAff".to_owned()),
                       &CType::IslType("isl_multi_union_pw_aff".to_owned()),
                       "src/bindings/multi_union_pw_aff.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("PwAff".to_owned()),
                       &CType::IslType("isl_pw_aff".to_owned()),
                       "src/bindings/pw_aff.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("PwAffList".to_owned()),
                       &CType::IslType("isl_pw_aff_list".to_owned()),
                       "src/bindings/pw_aff_list.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("PwMultiAff".to_owned()),
                       &CType::IslType("isl_pw_multi_aff".to_owned()),
                       "src/bindings/pw_multi_aff.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("PwMultiAffList".to_owned()),
                       &CType::IslType("isl_pw_multi_aff_list".to_owned()),
                       "src/bindings/pw_multi_aff_list.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("PwQPolynomial".to_owned()),
                       &CType::IslType("isl_pw_qpolynomial".to_owned()),
                       "src/bindings/pw_qpolynomial.rs",
                       &["isl/include/isl/polynomial.h"]);
    implement_bindings(&RustType::Raw("PwQPolynomialList".to_owned()),
                       &CType::IslType("isl_pw_qpolynomial_list".to_owned()),
                       "src/bindings/pw_qpolynomial_list.rs",
                       &["isl/include/isl/polynomial.h"]);
    implement_bindings(&RustType::Raw("PwQPolynomialFold".to_owned()),
                       &CType::IslType("isl_pw_qpolynomial_fold".to_owned()),
                       "src/bindings/pw_qpolynomial_fold.rs",
                       &["isl/include/isl/polynomial.h"]);
    implement_bindings(&RustType::Raw("PwQPolynomialFoldList".to_owned()),
                       &CType::IslType("isl_pw_qpolynomial_fold_list".to_owned()),
                       "src/bindings/pw_qpolynomial_fold_list.rs",
                       &["isl/include/isl/polynomial.h"]);
    implement_bindings(&RustType::Raw("UnionPwAff".to_owned()),
                       &CType::IslType("isl_union_pw_aff".to_owned()),
                       "src/bindings/union_pw_aff.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("UnionPwAffList".to_owned()),
                       &CType::IslType("isl_union_pw_aff_list".to_owned()),
                       "src/bindings/union_pw_aff_list.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("UnionPwMultiAff".to_owned()),
                       &CType::IslType("isl_union_pw_multi_aff".to_owned()),
                       "src/bindings/union_pw_multi_aff.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("UnionPwMultiAffList".to_owned()),
                       &CType::IslType("isl_union_pw_multi_aff_list".to_owned()),
                       "src/bindings/union_pw_multi_aff_list.rs",
                       &["isl/include/isl/aff.h"]);
    implement_bindings(&RustType::Raw("UnionPwQPolynomial".to_owned()),
                       &CType::IslType("isl_union_pw_qpolynomial".to_owned()),
                       "src/bindings/union_pw_qpolynomial.rs",
                       &["isl/include/isl/polynomial.h"]);
    implement_bindings(&RustType::Raw("UnionPwQPolynomialFold".to_owned()),
                       &CType::IslType("isl_union_pw_qpolynomial_fold".to_owned()),
                       "src/bindings/union_pw_qpolynomial_fold.rs",
                       &["isl/include/isl/polynomial.h"]);
    implement_bindings(&RustType::Raw("StrideInfo".to_owned()),
                       &CType::IslType("isl_stride_info".to_owned()),
                       "src/bindings/stride_info.rs",
                       &["isl/include/isl/stride_info.h"]);
    implement_bindings(&RustType::Raw("FixedBox".to_owned()),
                       &CType::IslType("isl_fixed_box".to_owned()),
                       "src/bindings/fixed_box.rs",
                       &["isl/include/isl/fixed_box.h"]);
    implement_bindings(&RustType::Raw("Printer".to_owned()),
                       &CType::IslType("isl_printer".to_owned()),
                       "src/bindings/printer.rs",
                       &["isl/include/isl/printer.h",
                         "isl/include/isl/val.h",
                         "isl/include/isl/set.h",
                         "isl/include/isl/map.h",
                         "isl/include/isl/union_set.h",
                         "isl/include/isl/union_map.h",
                         "isl/include/isl/id.h",
                         "isl/include/isl/aff.h",
                         "isl/include/isl/polynomial.h"]);

    // }}}

    // add `uses` to src/bindings/mod.rs
    generate_bindings_mod("src/bindings/mod.rs");
}

// vim:fdm=marker
