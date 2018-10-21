# A Range

> **Write quick and explict ranges in Rust**

[![Build Status](https://travis-ci.com/killercup/a-range.svg?branch=master)](https://travis-ci.com/killercup/a-range)
[![crates.io](https://img.shields.io/crates/v/a-range.svg)](https://crates.io/crates/a-range)
[![docs](https://img.shields.io/badge/api_docs-latest-blue.svg)](https://docs.rs/a-range)

## Example

```rust
extern crate a_range;

// Create upward-counting inclusive ranges
let days_of_xmas = a_range::from(1).up_to(12);
let expected = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
assert_eq!(days_of_xmas.to_vec(), expected);

// Just as easily count backwards
let apollo_countdown = a_range::from(100).down_to(0);
let expected: Vec<i32> = (0..101).rev().collect();
assert_eq!(apollo_countdown.to_vec(), expected);

// Infinite ranges are also fun
let naturals = a_range::from(0).up_to_infinity();
let until_four: Vec<i32> = naturals.into_iter().take(5).collect();
assert_eq!(until_four, vec![0, 1, 2, 3, 4]);
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
