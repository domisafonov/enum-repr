#![cfg_attr(feature = "nightly", warn(clippy::pedantic))]

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

use proc_macro2::Span;
use proc_macro::TokenStream;
use quote::ToTokens;
use syn::*;

/// The derivation function
#[allow(non_snake_case)]
#[proc_macro_attribute]
pub fn EnumRepr(
    args: TokenStream,
    input: TokenStream
) -> TokenStream {
    let input = syn::parse::<ItemEnum>(input)
        .expect("#[EnumRepr] must only be used on enums");

    let repr_ty = get_repr_type(args);

    validate(&input.variants);

    let ty = input.ident.clone();
    let vis = input.vis.clone();

    let (names, discrs): (Vec<_>, Vec<_>) = input.variants.iter()
        .map(|x| (
            x.ident.clone(),
            x.discriminant.as_ref()
                .expect("no discriminant for a variant").1.clone()
        )).unzip();

    let vars_len = input.variants.len();

    let (names2, discrs2, discrs3) =
        (names.clone(), discrs.clone(), discrs.clone());
    let repr_ty2 = repr_ty.clone();
    let repr_ty3 = repr_ty.clone();

    let ty_repeat = iter::repeat(ty.clone()).take(vars_len);
    let ty_repeat2 = ty_repeat.clone();
    let repr_ty_repeat = iter::repeat(repr_ty.clone()).take(vars_len);
    let repr_ty_repeat2 = iter::repeat(repr_ty.clone()).take(vars_len);
    let repr_ty_repeat3 = iter::repeat(repr_ty.clone()).take(vars_len);

    let (impl_generics, ty_generics, where_clause) =
        input.generics.split_for_impl();

    let mut ret: TokenStream = convert_variants(&input).into_token_stream().into();
    let gen: TokenStream = { quote! {
        impl #impl_generics #ty #ty_generics #where_clause {
            #vis fn repr(&self) -> #repr_ty2 {
                match self {
                    #( #ty_repeat2::#names2 => #discrs2 as #repr_ty_repeat ),*
                }
            }

            #vis fn from_repr(x: #repr_ty3) -> Option<#ty> {
                match x {
                    #( x if x == #discrs as #repr_ty_repeat2 => Some(#ty_repeat :: #names), )*
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
    }}.into();
    ret.extend(gen);

    ret
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

fn convert_variants(input: &ItemEnum) -> ItemEnum {
    let mut variants = input.variants.clone();

    variants.iter_mut().for_each(|ref mut var| {
        let discr = var.discriminant.clone().unwrap();
        let expr = discr.1.into_token_stream();
        let new_expr = parse_quote!( (#expr) as isize );
        var.discriminant = Some((discr.0, new_expr));
    });

    let ret = input.clone();
    ItemEnum {
        variants,
        .. ret
    }
}
