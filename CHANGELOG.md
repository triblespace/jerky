# Changelog

## Unreleased
- Added `WaveletMatrix::to_bytes` and `WaveletMatrix::from_bytes` returning metadata and bytes for zero-copy persistence.
- Documented the serialized `WaveletMatrix` layout with ASCII art.
- Added `CompactVector::to_bytes` and `from_bytes` for zero-copy serialization.
- Made `DacsByte` generic over its flag index type with a default of `Rank9SelIndex`.
- `DacsByte::from_slice` now accepts a generic index type, removing `from_slice_with_index`.
- Added `BitVectorBuilder` and zero-copy `BitVectorData` backed by `anybytes::View`.
- Introduced `IndexBuilder` trait with a `Built` type and adjusted serialization helpers.
- `Rank9SelIndex` now stores its serialized bytes internally and `to_bytes` returns this buffer.
- Rename crate to `succdisk` to reflect on-disk succinct data structures.
- Rename crate from `succdisk` to `jerky`.
- Replaced the old `BitVector` with the generic `BitVector<I>` and renamed the
  mutable variant to `RawBitVector`.
- Extended `BitVectorBuilder` with `push_bits` and `set_bit` APIs.
- Added `from_bit` constructor on `BitVectorBuilder` for repeating a single bit.
- `DacsByte` now stores level data as zero-copy `View<[u8]>` values.
- Added `to_bytes` and `from_bytes` on `DacsByte` for zero-copy serialization.
- Documented the byte layout produced by `DacsByte::to_bytes` with ASCII art.
- Flags are serialized before level data to eliminate padding.
- `DacsByte` stores all flags and levels in one contiguous byte buffer and `to_bytes` simply clones this buffer.
- Added `get_bits` methods to `BitVectorData` and `BitVector`.
- Removed deprecated `size_in_bytes` helpers.
- Added `scripts/devtest.sh` and `scripts/preflight.sh` for testing and
  verification workflows.
- Simplified CI workflow to run `scripts/preflight.sh` on pull requests.
- Fixed `scripts/preflight.sh` to install `rustfmt` when `cargo-fmt` is missing.
- `Rank9Sel` now stores a `BitVector<Rank9SelIndex>` built via `BitVectorBuilder`.
- Replaced `DArrayFullIndex` with new `DArrayIndex` that uses const generics
  to optionally include `select1` and `select0` support.
- Introduced `CompactVectorBuilder` mutable APIs `push_int`, `set_int`, and `extend`.
- Simplified bit vector imports by re-exporting `BitVectorBuilder` and `Rank9SelIndex` and updating examples.
- Moved the `bit_vector::bit_vector` module contents directly into `bit_vector` for cleaner paths.
- Added README usage example demonstrating basic bit vector operations.
- Removed `bit_vector::prelude`; import traits directly with `use jerky::bit_vector::*`.
- Added `freeze()` on `CompactVectorBuilder` yielding an immutable `CompactVector` backed by `BitVector<NoIndex>`.
- `CompactVector::new` and `with_capacity` now return builders; other constructors build via the builder pattern.
- Wavelet matrix and DACs builders now use `BitVectorBuilder` for temporary bit
  vectors, storing only immutable `BitVector` data after construction.
- Removed obsolete `RawBitVector` type.
- Removed the `Rank9Sel` wrapper; use `BitVector<Rank9SelIndex>` directly.
- Removed the `DArray` wrapper; use `BitVector<darray::inner::DArrayIndex>` instead.
- Dropped the dense array implementation and all benchmarks referencing `DArrayIndex`.
- Removed the `Build` trait for bit vectors; construct indexes via `BitVectorBuilder` and `IndexBuilder`.
- Removed index builders in favor of parameterized index types constructed with `build`.
- Simplified benchmark code by importing index types and relying on type inference.
- Added `INVENTORY.md` for tracking pending work and ideas.
- Clarified inventory instructions in `AGENTS.md`.
- Removed the `## Completed Work` section from `INVENTORY.md`.
- Consolidated module layout by moving `WORD_LEN` into `bit_vectors::data` and
  adopting directory-based `mod.rs` files.
- Unified bit vector implementation under `bit_vector.rs` and removed the
  redundant `data` module.
- Renamed the `bit_vectors` module to `bit_vector` and updated imports.
- Updated benchmarks to use `jerky::bit_vector` imports.
- Removed the WaveletMatrix iterator caching TODO and inventory entry after
  benchmarking showed only a 3% performance gain.
- Fixed a stale doc link referencing the old `bit_vectors` module.
- Removed completed documentation cleanup tasks from `INVENTORY.md`.
- Fixed a typo in `bench/README.md`.
- Added iterators and `to_vec` helpers for inspecting built vectors.
- Split inspection tests so each assertion stands alone.
- Documented `WaveletMatrix` usage in `README.md`.
- Moved README usage examples to runnable files in `examples/`.
- Added `compact_vector` example showing construction and retrieval.
- WaveletMatrix now stores its serialized word buffer for zero-copy access and preallocates building memory.
