#![allow(dead_code)]
#![no_std]

#[macro_use] extern crate enum_repr;

type T = u8;

#[derive(Clone, EnumRepr, PartialEq)]
#[EnumReprType = "T"]
enum En {
    A = 1u8 as isize,
    B = 2u8 as isize
}

#[derive(Clone, EnumRepr, PartialEq)]
#[EnumReprType = "T"]
pub enum PubEn {
    A = 1u8 as isize,
    B = 2u8 as isize
}
