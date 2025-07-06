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
