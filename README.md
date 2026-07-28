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
is backed by `anybytes::View`. Metadata describing a stored sequence includes
[`SectionHandle`](anybytes::area::SectionHandle)s so the raw
`Bytes` returned by `ByteArea::freeze` can be handed to
`BitVectorData::from_bytes` with its `BitVectorDataMeta` for zero‑copy reconstruction.

Types following this pattern implement the [`Serializable`](src/serialization.rs) trait,
which exposes a `metadata` accessor and a `from_bytes` constructor.

`DacsByte` sequences expose a `metadata` method returning a descriptor with a
handle to a slice of per-level handles. Each entry stores the flag bitvector
handle (if any), its bit length, and the payload byte handle. `from_bytes`
rebuilds the sequence using that metadata.

```text
Bytes layout for a `DacsByte` sequence (current builders place sections
contiguously, though layout is fully described by the stored handles):

| flag[0] words | flag[1] words | ... | flag[n-2] words | level[0] data | level[1] data | ... | level[n-1] data |

The flag vectors come first and store native-endian `usize` words. The level
data immediately follows without any padding.
```

`CompactVector` and `WaveletMatrix` provide the same pattern: call `metadata`
to obtain a descriptor with the required `SectionHandle`s, then hand both the
metadata and the full `Bytes` region to `from_bytes`.

For a wavelet matrix the metadata stores a handle to a slice of per-layer
handles. Each handle in that slice points to the native-endian `u64` words
forming a single layer. Layers may reside anywhere in the arena and no longer
need to be contiguous.

Rank/select indexes can be persisted separately from those raw bit-vector
words. `Rank9SelIndex::persist` writes its native-`usize` representation
directly into a `SectionWriter`, while `from_bytes_for_data` attaches it only
after validating every directory entry and select hint against the supplied
`BitVectorData`. `WaveletMatrix::persist_layer_indexes` writes one such section
per layer in MSB-to-LSB order, and
`WaveletMatrix::from_bytes_with_persisted_indexes` reconstructs a matrix from
the original metadata plus exactly that many checked index payloads. This
separates immutable raw data from derived query indexes without silently
trusting a semantically incompatible sidecar.

```rust
use anybytes::ByteArea;
use jerky::int_vectors::{CompactVector, CompactVectorBuilder};

let mut area = ByteArea::new()?;
let mut sections = area.sections();
let mut builder = CompactVectorBuilder::with_capacity(3, 3, &mut sections)?;
builder.set_ints(0..3, [7, 2, 5])?;
let cv = builder.freeze();
let meta = cv.metadata();
let bytes = area.freeze()?;
let view = CompactVector::from_bytes(meta, bytes.clone())?;
assert_eq!(view.get_int(1), Some(2));
```

## GPU batch queries (feature `gpu`)

The optional `gpu` feature adds [`jerky::gpu::GpuWaveletMatrix`](src/gpu.rs)
(cubecl/wgpu — Metal, Vulkan, DX12): upload a frozen `WaveletMatrix` to the
GPU once, then answer *batches* of access/rank/select/quantile queries with
one dispatch and one host↔device sync per batch. Wavelet queries are
latency-bound chains of dependent scattered loads, so GPU thread
oversubscription pays off at scale: at 1M-query batches an M4 Max runs
24–72× over one CPU core and 2.2–4.9× over all 16 threads, with break-even
around 16k–65k queries per batch. Use it for large analytic batches; keep
point lookups on the CPU form. Run the honest comparison on your hardware:

For multi-kernel query execution, `DeviceU32Buffer` plus the resident
WaveletMatrix access/rank methods keep inputs and outputs on the device.
`GpuBitVector` provides the same fixed and device-length seam for raw-data
rank1/select1. Downstream CubeCL kernels consume typed array arguments, with a
single `DeviceU32Buffer::read` at the end of the pipeline; slice-based methods
remain the host convenience path. Structures built from clones of one
`GpuContext` safely share resident buffers. Host-known lengths use
`GpuContext::static_batch_dispatch` for a checked direct launch with no device
allocation or upload. For device-compacted frontiers, `DeviceBatchMeta` stores
`[logical_len, capacity]` separately from the persistent/exclusive
`DeviceDispatch`; dynamic kernels use tight 2-D indirect dispatch while still
guarding every probe by the device logical length.

```console
cargo run --release --features gpu --example gpu_bench
```

Note that the `gpu` feature requires a recent stable toolchain (cubecl's
MSRV) and, for its tests, a working GPU.

## Examples

See the [examples](examples/) directory for runnable usage demos, including
`bit_vector`, `compact_vector`, `dacs_byte`, and `wavelet_matrix`.

## Licensing

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
