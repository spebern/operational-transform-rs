# operational-transform

[![Crates.io][crates-badge]][crates-url]
[![docs.rs docs][docs-badge]][docs-url]
[![ci][ci-badge]][ci-url]

[crates-badge]: https://img.shields.io/crates/v/operational-transform.svg
[crates-url]: https://crates.io/crates/operational-transform

[docs-badge]: https://img.shields.io/badge/docs-latest-blue.svg
[docs-url]: https://docs.rs/operational-transform

[ci-badge]: https://github.com/spebern/operational-transform-rs/workflows/Rust/badge.svg
[ci-url]: https://github.com/spebern/operational-transform-rs/actions

A library for Operational Transformation

Operational transformation (OT) is a technology for supporting a range of
collaboration functionalities in advanced collaborative software systems.
[[1]](https://en.wikipedia.org/wiki/Operational_transformation)

When working on the same document over the internet concurrent operations
from multiple users might be in conflict. **Operational Transform** can help
to resolve conflicts in such a way that documents stay in sync.

The basic operations that are supported are:
- Retain(n): Move the cursor `n` positions forward
- Delete(n): Delete `n` characters at the current position
- Insert(s): Insert the string `s` at the current position

This library can be  used to...

... compose sequences of operations:
```rust
use operational_transform::OperationSeq;

let mut a = OperationSeq::default();
a.insert("abc");
let mut b = OperationSeq::default();
b.retain(3);
b.insert("def");
let after_a = a.apply("").unwrap();
let after_b = b.apply(&after_a).unwrap();
let c = a.compose(&b).unwrap();
let after_ab = a.compose(&b).unwrap().apply("").unwrap();
assert_eq!(after_ab, after_b);
```

... transform sequences of operations
```rust
use operational_transform::OperationSeq;

let s = "abc";
let mut a = OperationSeq::default();
a.retain(3);
a.insert("def");
let mut b = OperationSeq::default();
b.retain(3);
b.insert("ghi");
let (a_prime, b_prime) = a.transform(&b).unwrap();
let ab_prime = a.compose(&b_prime).unwrap();
let ba_prime = b.compose(&a_prime).unwrap();
let after_ab_prime = ab_prime.apply(s).unwrap();
let after_ba_prime = ba_prime.apply(s).unwrap();
assert_eq!(ab_prime, ba_prime);
assert_eq!(after_ab_prime, after_ba_prime);
```

... invert sequences of operations
```rust
use operational_transform::OperationSeq;

let s = "abc";
let mut o = OperationSeq::default();
o.retain(3);
o.insert("def");
let p = o.invert(s);
assert_eq!(p.apply(&o.apply(s).unwrap()).unwrap(), s);
```

### Features

Serialisation is supporeted by using the `serde` feature.

- Delete(n) will be serialized to -n
- Insert(s) will be serialized to "{s}"
- Retain(n) will be serailized to n

```rust
use operational_transform::OperationSeq;
use serde_json;

let o: OperationSeq = serde_json::from_str("[1,-1,\"abc\"]").unwrap();
let mut o_exp = OperationSeq::default();
o_exp.retain(1);
o_exp.delete(1);
o_exp.insert("abc");
assert_eq!(o, o_exp);
```

### Acknowledgement
In the current state the code is ported from
[here](https://github.com/Operational-Transformation/ot.js/). It might
change in the future as there is much room for optimisation and also
usability.
