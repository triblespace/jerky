# Changelog

## Unreleased
- Added `BitVectorBuilder` and zero-copy `BitVectorData` backed by `anybytes::View`.
- Introduced `IndexBuilder` trait with a `Built` type and adjusted serialization helpers.
- Rename crate to `succdisk` to reflect on-disk succinct data structures.
- Rename crate from `succdisk` to `jerky`.
- Replaced the old `BitVector` with the generic `BitVector<I>` and renamed the
  mutable variant to `RawBitVector`.
- Extended `BitVectorBuilder` with `push_bits` and `set_bit` APIs.
- Added `get_bits` methods to `BitVectorData` and `BitVector`.
- Added `scripts/devtest.sh` and `scripts/preflight.sh` for testing and
  verification workflows.
- Index builders now provide `from_data` constructors operating on `BitVectorData`.
- Simplified CI workflow to run `scripts/preflight.sh` on pull requests.
- Fixed `scripts/preflight.sh` to install `rustfmt` when `cargo-fmt` is missing.
- `Rank9Sel` now stores a `BitVector<Rank9SelIndex>` built via `BitVectorBuilder`.
- Added `DArrayFullIndex` wrapping `DArrayIndex<true>` and `DArrayIndex<false>`
  for unified 0/1 select queries.
- Introduced `CompactVectorBuilder` mutable APIs `push_int`, `set_int`, and `extend`.
- Added `freeze()` on `CompactVectorBuilder` yielding an immutable `CompactVector` backed by `BitVector<NoIndex>`.
- `CompactVector::new` and `with_capacity` now return builders; other constructors build via the builder pattern.
- Wavelet matrix and DACs builders now use `BitVectorBuilder` for temporary bit
  vectors, storing only immutable `BitVector` data after construction.
- Removed obsolete `RawBitVector` type.
- Removed the `Rank9Sel` wrapper; use `BitVector<Rank9SelIndex>` directly.
