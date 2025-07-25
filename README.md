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
`DacsByte` sequences support a similar interface with `to_bytes` returning
metadata alongside the byte slice and `from_bytes` rebuilding the sequence
using that metadata.

```text
Bytes layout from `DacsByte::to_bytes`:

| flag[0] words | flag[1] words | ... | flag[n-2] words | level[0] data | level[1] data | ... | level[n-1] data |

The flag vectors come first and store native-endian `usize` words. The level
data immediately follows without any padding.
```

## Examples

See the [examples](examples/) directory for runnable usage demos, including
`bit_vector`, `wavelet_matrix`, and `compact_vector`.

## Licensing

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
