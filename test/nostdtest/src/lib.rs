// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

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
