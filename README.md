# enum-repr

[![Build Status](https://travis-ci.org/dmnsafonov/enum-repr.svg?branch=master)](https://travis-ci.org/dmnsafonov/enum-repr)
[![Crates.io](https://img.shields.io/crates/v/enum-repr.svg)](https://crates.io/crates/enum-repr)
[![Documentation](https://docs.rs/enum-repr/badge.svg)](https://docs.rs/enum-repr)

Generate enum repr conversions compatible with type aliases.  Works on `no_std`.

`EnumRepr` proc macro takes an `type` argument and defines two functions
for the enum used on:
```
fn repr(&self) -> EnumReprType
fn from_repr(x: EnumReprType) -> Option<Self>
```
The real enum discriminant still remains `isize`.

```rust
extern crate enum_repr;
extern crate libc;

use libc::*;

use enum_repr::EnumRepr;

#[EnumRepr(type = "c_int")]
#[derive(Debug, PartialEq)]
pub enum IpProto {
    IP = IPPROTO_IP,
    IPv6 = IPPROTO_IPV6,
    // …
}

fn main() {
    assert_eq!(IpProto::IP.repr(), IPPROTO_IP);
    assert_eq!(IpProto::from_repr(IPPROTO_IPV6), Some(IpProto::IPv6));
    assert!(IpProto::from_repr(12345).is_none());
}
```

# License

This project is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or
   http://opensource.org/licenses/MIT)

at your option.
