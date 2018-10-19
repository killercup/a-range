# A Range

> **Write quick and explict ranges in Rust**

[![Build Status](https://travis-ci.com/killercup/a-range.svg?branch=master)](https://travis-ci.com/killercup/a-range)
[![crates.io](https://img.shields.io/crates/v/a-range.svg)](https://crates.io/crates/a-range)
[![docs](https://img.shields.io/badge/api_docs-latest-blue.svg)](https://docs.rs/a-range)

Create ranges in a very explicit manner

Start with the [`from()`] function and build up a range using [`From::up_to`] or
[`From::down_to`].

# Examples

```rust
extern crate a_range;

let x = a_range::from(5).up_to(7);
assert_eq!(x.to_vec(), vec![5, 6, 7]);

let x = a_range::from(3).down_to(1);
assert_eq!(x.to_vec(), vec![3, 2, 1]);
```

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
