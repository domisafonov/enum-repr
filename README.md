# enum-repr

[![Build Status](https://travis-ci.org/dmnsafonov/enum-repr.svg?branch=master)](https://travis-ci.org/dmnsafonov/enum-repr)
[![Crates.io](https://img.shields.io/crates/v/enum-repr.svg)](https://crates.io/crates/enum-repr)
[![Documentation](https://docs.rs/enum-repr/badge.svg)](https://docs.rs/enum-repr)

Derive enum repr conversions compatible with type aliases.

`EnumRepr` proc macro takes an `EnumReprType` argument and defines
two functions for the enum derived on: `fn repr(&self) -> EnumReprType`
and `fn from_repr(x: EnumReprType) -> Option<Self>`.  The real enum
discriminant still remains `isize`.

```rust
#[macro_use] extern crate enum_repr;
extern crate libc;

use libc::*;

#[derive(Clone, Debug, PartialEq)]
#[derive(EnumRepr)]
#[EnumReprType = "c_int"]
pub enum IpProto {
    IP = IPPROTO_IP as isize,
    IPv6 = IPPROTO_IPV6 as isize,
    // …
}

fn main() {
    assert_eq!(IpProto::IP.repr(), IPPROTO_IP);
    assert_eq!(IpProto::from_repr(IPPROTO_IPV6), Some(IpProto::IPv6));
    assert!(IpProto::from_repr(12345).is_none());
}
```
