#![allow(dead_code)]
#![no_std]

extern crate enum_repr;

use enum_repr::EnumRepr;

type T = u8;

#[EnumRepr(type = "T")]
enum En {
    A = 1,
    B = 2
}

#[EnumRepr(type = "T")]
pub enum PubEn {
    A = 1,
    B = 2
}
