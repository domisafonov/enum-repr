#![cfg_attr(feature = "nightly", warn(clippy::pedantic))]

#![recursion_limit = "128"]

//! Generate enum repr conversions compatible with type aliases.
//!
//! Generate with `#[EnumRepr(type = "TYPE")]`.
//!
//! Functions generated are
//! ```ignore
//! fn repr(&self) -> EnumReprType
//! fn from_repr(x: EnumReprType) -> Option<Self>
//! ```
//! The real enum discriminant is usually forced to be `#[repr(isize)]`.
//! If `u*` or `i*` types are used for the discriminant, the actual enum
//! representation is made to be `#[repr(that_type_specified)]`.
//! The list of types recognized as `u*` and `i*` currently is as follows:
//! `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128`.
//! If the type is specified through a type alias, `#[repr(isize)]` is used.
//! Inability to specify type aliases as enum representations is this crate's
//! reason to exist.
//!
//! The code generated does not require std.
//!
//! # Examples
//! ```
//! extern crate enum_repr;
//! extern crate libc;
//!
//! use libc::*;
//!
//! use enum_repr::EnumRepr;
//!
//! #[EnumRepr(type = "c_int")]
//! #[derive(Debug, PartialEq)]
//! pub enum IpProto {
//!     IP = IPPROTO_IP,
//!     IPv6 = IPPROTO_IPV6,
//!     // …
//! }
//!
//! fn main() {
//!     assert_eq!(IpProto::IP.repr(), IPPROTO_IP);
//!     assert_eq!(IpProto::from_repr(IPPROTO_IPV6), Some(IpProto::IPv6));
//!     assert!(IpProto::from_repr(12345).is_none());
//! }
//! ```
//!
//! ```
//! # extern crate enum_repr;
//! # extern crate libc;
//! #
//! # use libc::*;
//! #
//! # use enum_repr::EnumRepr;
//! #
//! #[EnumRepr(type = "c_int")]
//! # #[derive(Debug, Eq, Hash, PartialEq)]
//! pub enum InetDomain {
//!     Inet = 2,
//!     // …
//! }
//!
//! #[EnumRepr(type = "c_int")]
//! # #[derive(Debug, Eq, Hash, PartialEq)]
//! pub enum SocketType {
//!     Stream = 1,
//!     // …
//! }
//!
//! // …
//!
//! # fn main() { unsafe {
//! assert!(
//!    socket(InetDomain::Inet.repr(), SocketType::Stream.repr(), 0) != -1
//! );
//! # }}
//! ```
//!
//! ```no_run
//! # extern crate enum_repr;
//! # extern crate libc;
//! #
//! # use libc::*;
//! #
//! # use enum_repr::EnumRepr;
//! #
//! // compatible with documentation and other attributes
//!
//! /// Represents a layer 3 network protocol.
//! #[EnumRepr(type = "c_int")]
//! #[derive(Debug, PartialEq)]
//! pub enum IpProto {
//!     IP = IPPROTO_IP,
//!     IPv6 = IPPROTO_IPV6,
//!     // …
//! }
//! #
//! # fn main() {}
//! ```
//!
//! Out of bound discriminants fail to compile:
//! ```compile_fail
//! # #![deny(overflowing_literals)]
//! # extern crate enum_repr;
//! #
//! # use enum_repr::EnumRepr;
//! #
//! #[EnumRepr(type = "u8")]
//! enum Test {
//!     A = 256
//! }
//! #
//! # fn main() {}
//! ```
//!
//! Discriminants of a wrong type fail to compile as well:
//! ```compile_fail
//! # #![deny(overflowing_literals)]
//! # extern crate enum_repr;
//! #
//! # use enum_repr::EnumRepr;
//! #
//! const C: u16 = 256;
//!
//! #[EnumRepr(type = "u8")]
//! enum Test {
//!     A = C
//! }
//! #
//! # fn main() {}
//! ```
//!
//! Using the actual enum discriminant representation:
//! ```
//! # extern crate enum_repr;
//! #
//! # use std::mem::size_of;
//! #
//! # use enum_repr::EnumRepr;
//! #
//! #[EnumRepr(type = "u8")]
//! #[derive(Debug, PartialEq)]
//! enum Test {
//!     A = 1
//! }
//!
//! fn main() {
//!     assert_eq!(size_of::<u8>(), size_of::<Test>());
//! }
//! ```

extern crate proc_macro;
extern crate proc_macro2;
#[macro_use] extern crate quote;
extern crate syn;

use std::iter;

use proc_macro2::Span;
use proc_macro::TokenStream;
use quote::ToTokens;
use syn::*;

/// The code generator
#[allow(non_snake_case)]
#[proc_macro_attribute]
pub fn EnumRepr(
    args: TokenStream,
    input: TokenStream
) -> TokenStream {
    let input = syn::parse::<ItemEnum>(input)
        .expect("#[EnumRepr] must only be used on enums");
    validate(&input.variants);

    let repr_ty = get_repr_type(args);
    let compiler_repr_ty = match repr_ty.to_string().as_str() {
        "i8" | "i16" | "i32" | "i64" | "i128"
        | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" => repr_ty.clone(),
        _ => Ident::new(&"isize", Span::call_site())
    };

    let new_enum = convert_enum(&input, compiler_repr_ty);
    let mut ret: TokenStream = new_enum.clone().into_token_stream().into();

    let gen = generate_code(&new_enum, repr_ty);
    ret.extend(gen);
    ret
}

fn generate_code(input: &ItemEnum, repr_ty: Ident) -> TokenStream {
    let ty = input.ident.clone();
    let vis = input.vis.clone();
    let (names, discrs) = extract_variants(input);
    let vars_len = input.variants.len();

    let (names2, discrs2, discrs3) =
        (names.clone(), discrs.clone(), discrs.clone());
    let repr_ty2 = repr_ty.clone();
    let repr_ty3 = repr_ty.clone();
    let ty_repeat = iter::repeat(ty.clone()).take(vars_len);
    let ty_repeat2 = ty_repeat.clone();
    let repr_ty_repeat = iter::repeat(repr_ty.clone()).take(vars_len);
    let repr_ty_repeat2 = repr_ty_repeat.clone();
    let repr_ty_repeat3 = repr_ty_repeat.clone();

    let (impl_generics, ty_generics, where_clause) =
        input.generics.split_for_impl();

    let ret: TokenStream = quote! {
        impl #impl_generics #ty #ty_generics #where_clause {
            #vis fn repr(&self) -> #repr_ty2 {
                match self {
                    #( #ty_repeat2::#names2 => #discrs2 as #repr_ty_repeat ),*
                }
            }

            #vis fn from_repr(x: #repr_ty3) -> Option<#ty> {
                match x {
                    #( x if x == #discrs as #repr_ty_repeat2 => Some(#ty_repeat::#names), )*
                    _ => None
                }
            }

            #[doc(hidden)]
            #[allow(dead_code)]
            fn _enum_repr_typecheck() {
                #( let _x: #repr_ty_repeat3 = #discrs3; )*
                panic!("don't call me!")
            }
        }
    }.into();
    ret
}

fn extract_variants(input: &ItemEnum) -> (Vec<Ident>, Vec<Expr>) {
    let (names, discrs): (Vec<_>, Vec<_>) = input.variants.iter()
        .map(|x| (
            x.ident.clone(),
            x.discriminant.as_ref()
                .expect("no discriminant for a variant").1.clone()
        )).unzip();
    (names, discrs)
}

fn get_repr_type(args: TokenStream) -> Ident {
    let args = syn::parse::<Meta>(args).expect("specify repr type in format \
            \"#[EnumRepr]\"");
    match args {
        Meta::NameValue(MetaNameValue {
            ident, lit: Lit::Str(repr_ty), ..
        }) => {
            if ident.to_string() != "type" {
                panic!("#[EnumRepr] accepts one argument named \"type\"")
            }
            Ident::new(
                &repr_ty.value(),
                Span::call_site()
            )
        },
        _ => panic!("specify repr type in format \
            \"#[EnumRepr(type = \"TYPE\")]\"")
    }
}

fn validate(vars: &punctuated::Punctuated<Variant, token::Comma>) {
    for i in vars {
        match i.fields {
            Fields::Named(_) | Fields::Unnamed(_) =>
                panic!("the enum's fields must \
                    be in the \"ident = discriminant\" form"),
            Fields::Unit => ()
        }
    }
}

fn convert_enum(input: &ItemEnum, compiler_repr_ty: Ident) -> ItemEnum {
    let mut variants = input.variants.clone();

    let mut prev_expr: Expr = parse_quote!( 0 as #compiler_repr_ty );
    variants.iter_mut().for_each(|ref mut var| {
        let discr_opt = var.discriminant.clone();
        let (eq, new_expr): (syn::token::Eq, Expr) = match discr_opt {
            Some(discr) => {
                let expr = discr.1.into_token_stream();
                ( discr.0,
                    parse_quote!( (#expr) as #compiler_repr_ty ) )
            },
            None => {
                let expr = prev_expr.clone();
                ( syn::token::Eq { spans: [Span::call_site(),] },
                    parse_quote!( (1 + (#expr)) as #compiler_repr_ty ) )
            },
        };
        prev_expr = new_expr.clone();
        var.discriminant = Some((eq, new_expr));
    });

    let mut attrs = input.attrs.clone();
    attrs.push(parse_quote!( #[repr(#compiler_repr_ty)] ));

    let ret = input.clone();
    ItemEnum {
        variants,
        attrs,
        .. ret
    }
}
