# Succinct on-disk data structures in Rust

![](https://github.com/triblespace/jerky/actions/workflows/preflight.yml/badge.svg)
[![Documentation](https://docs.rs/jerky/badge.svg)](https://docs.rs/jerky)
[![Crates.io](https://img.shields.io/crates/v/jerky.svg)](https://crates.io/crates/jerky)

Jerky provides some [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure) written in Rust.

## Documentation

https://docs.rs/jerky/

## Limitation

This library is designed to run on 64-bit machines.

## Build docs

The document can be compiled with the following command:

```console
RUSTDOCFLAGS="--html-in-header katex.html" cargo doc --no-deps
```

## Zero-copy bit vectors

`BitVectorBuilder` can build a bit vector whose underlying `BitVectorData`
is backed by `anybytes::View`. The data can be serialized with
`BitVectorData::to_bytes` and reconstructed using `BitVectorData::from_bytes`,
allowing zero-copy loading from an mmap or any other source by passing the
byte region to `Bytes::from_source`.

## Usage example

The snippet below shows how to build a bit vector with a rank/select index and
perform a few basic queries:

```rust
use jerky::bit_vector::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut builder = BitVectorBuilder::new();
    builder.extend_bits([true, false, true, false, true]);
    let bv = builder.freeze::<Rank9SelIndex>();

    assert_eq!(bv.num_bits(), 5);
    assert_eq!(bv.rank1(4), Some(2));
    assert_eq!(bv.select1(1), Some(2));
    Ok(())
}
```

## Licensing

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
