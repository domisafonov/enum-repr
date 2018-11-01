#![warn(clippy::pedantic)]

#![recursion_limit = "128"]

//! Derive enum repr conversions compatible with type aliases.
//!
//! Derive with `#[derive(EnumRepr)]`.  The repr type is set
//! by `#[EnumReprType = "..."]`.
//!
//! Functions `fn repr(&self) -> EnumReprType`
//! and `fn from_repr(x: EnumReprType) -> Option<Self>` are generated.
//! The real enum discriminant still remains `isize`.
//!
//! The code generated does not require std.
//!
//! # Examples
//! ```
//! #[macro_use] extern crate enum_repr;
//! extern crate libc;
//!
//! use libc::*;
//!
//! #[derive(Debug, PartialEq)]
//! #[derive(EnumRepr)]
//! #[EnumReprType = "c_int"]
//! pub enum IpProto {
//!     IP = IPPROTO_IP as isize,
//!     IPv6 = IPPROTO_IPV6 as isize,
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
//! # #[macro_use] extern crate enum_repr;
//! # extern crate libc;
//! #
//! # use libc::*;
//! #
//! # #[derive(Debug, Eq, Hash, PartialEq)]
//! #[derive(EnumRepr)]
//! #[EnumReprType = "c_int"]
//! pub enum InetDomain {
//!     Inet = 2,
//!     // …
//! }
//!
//! # #[derive(Debug, Eq, Hash, PartialEq)]
//! #[derive(EnumRepr)]
//! #[EnumReprType = "c_int"]
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
//! ```
//! # #[macro_use] extern crate enum_repr;
//! # extern crate libc;
//! #
//! # use libc::*;
//! #
//! // compatible with documentation and other attributes
//!
//! /// Represents a layer 3 network protocol.
//! #[derive(Debug, PartialEq)]
//! #[derive(EnumRepr)]
//! #[EnumReprType = "c_int"]
//! pub enum IpProto {
//!     IP = IPPROTO_IP as isize,
//!     IPv6 = IPPROTO_IPV6 as isize,
//!     // …
//! }
//! #
//! # fn main() {}
//! ```
//!
//! # Limitations
//! No warnings are produced if out-of-bounds integer literals are specified.
//! E.g, a variant like `A = 65537` would compile with `EnumReprType = "u16"`
//! silently:
//! ```
//! # #[macro_use] extern crate enum_repr;
//! #
//! #[derive(PartialEq)]
//! #[derive(EnumRepr)]
//! #[EnumReprType = "u16"]
//! enum En {
//!     A = 65537
//! }
//! #
//! # fn main() {}
//! ```
//!
//! The solution is to use the `A = 65537u16 as isize` form or
//! a named constant.  E.g.,
//! ```rust,compile_fail
//! #![deny(overflowing_literals)]
//!
//! # #[macro_use] extern crate enum_repr;
//! #
//! #[derive(PartialEq)]
//! #[derive(EnumRepr)]
//! #[EnumReprType = "u16"]
//! enum En {
//!     A = 65537u16 as isize
//! }
//! #
//! # fn main() {}
//! ```
//! fails to compile.

extern crate proc_macro;
extern crate proc_macro2;
#[macro_use] extern crate quote;
extern crate syn;

use std::iter;

use proc_macro2::*;
use syn::*;

/// The derivation function
#[proc_macro_derive(EnumRepr, attributes(EnumReprType))]
pub fn enum_repr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derive = syn::parse::<DeriveInput>(input)
        .expect("#[derive(EnumRepr)] could not parse input");

    let repr_ty = get_repr_type(&derive);
    let vars = get_vars(&derive);

    validate(&vars);

    let ty = derive.ident;
    let vis = derive.vis;

    let (names, discrs): (Vec<_>, Vec<_>) = vars.iter()
        .map(|x| (
            x.ident.clone(),
            x.discriminant.as_ref().unwrap().1.clone()
        )).unzip();

    let vars_len = vars.len();

    let (names2, discrs2) = (names.clone(), discrs.clone());
    let repr_ty2 = repr_ty.clone();
    let repr_ty3 = repr_ty.clone();

    let ty_repeat = iter::repeat(ty.clone()).take(vars_len);
    let repr_ty_repeat = iter::repeat(repr_ty.clone()).take(vars_len);
    let repr_ty_repeat2 = iter::repeat(repr_ty.clone()).take(vars_len);

    let (impl_generics, ty_generics, where_clause) =
        derive.generics.split_for_impl();

    let gen = quote! {
        impl #impl_generics #ty #ty_generics #where_clause {
            #vis fn repr(&self) -> #repr_ty2 {
                use #ty::*;
                match self {
                    #( #names2 => #discrs2 as #repr_ty_repeat ),*
                }
            }

            #vis fn from_repr(x: #repr_ty3) -> Option<#ty> {
                match x {
                    #( x if x == #discrs as #repr_ty_repeat2 => Some(#ty_repeat :: #names),)*
                    _ => None,
                }
            }
        }
    };

    gen.into()
}

fn get_repr_type(derive: &DeriveInput) -> Ident {
    let mut found_ident = None;
    for attr in &derive.attrs {
        if let Some(Meta::NameValue(MetaNameValue {
            ident,
            lit: Lit::Str(repr_ty),
            ..
        })) = attr.interpret_meta()
        {
            if ident == "EnumReprType" {
                if found_ident.is_some() {
                    panic!("specify #[EnumReprType = \"...\"] exactly once for an enum");
                }
                found_ident = Some(Ident::new(&repr_ty.value(), Span::call_site()));
            }
        }
    }
    if let Some(found_ident) = found_ident {
        found_ident
    } else {
        panic!("specify #[EnumReprType = \"...\"] exactly once for an enum");
    }
}

fn get_vars(
    derive: &DeriveInput
) -> punctuated::Punctuated<Variant, token::Comma> {
    match derive.data {
        Data::Enum(ref en) => en.variants.clone(),
        _ => panic!("#[derive(EnumRepr)] is only implemented for enums")
    }
}

fn validate(vars: &punctuated::Punctuated<Variant, token::Comma>) {
    for i in vars {
        match i.fields {
            Fields::Named(_) | Fields::Unnamed(_) =>
                panic!("the enum's fields must \
                    be in the \"ident = number literal\" form"),
            Fields::Unit => ()
        }
    }
}
