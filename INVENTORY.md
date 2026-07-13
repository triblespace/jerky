# Inventory

## Potential Removals
- None at the moment.

## Desired Functionality
- Device-resident query adapter in triblespace's `SuccinctArchive`: produce
  rank inputs and consume `DeviceU32Buffer` results in CubeCL so an entire
  frontier transition needs one final readback rather than one sync per
  clause. Jerky's fixed and device-length/indirect resident rank launches are
  ready; scan/compact and scheduling live in triblespace.
- Extend the device-resident launch API to access/select/quantile; the shared
  `GpuContext` already lets those future kernels reuse typed buffers safely
  across several `GpuWaveletMatrix` instances on the same device.
- GPU forms for more ops/structures: `rank_range`/`intersect` on
  `GpuWaveletMatrix`, and a batched rank/select kernel for a standalone
  `BitVector<Rank9SelIndex>`.
- Persistent single-workgroup kernel variant for latency-bound query chains
  under GPU contention (a single dispatch is immune to per-dispatch scheduler
  gaps; measured to win under load in prior probes).
- Wire triblespace's `SuccinctRollup::merge` onto the new `WaveletMatrix`
  merge APIs. Note the alphabet gap: archive segments carry per-segment value
  domains, so codes are remapped during a merge — the structural
  `merge_interleaved` applies only once segments share a code space; until
  then the adapter path is `to_vec` + remap + `from_iter` (which already
  avoids the sort).
- Provide more usage examples and documentation.
- Evaluate additional succinct data structures to include.
- Investigate alternative dense-select index strategies to replace removed `DArrayIndex`.
- Explore additional index implementations leveraging the new generic `DacsByte<I>`.
- Demonstrate the generic `from_slice` usage in examples and docs.
- Apply `with_capacity` constructors across builders to avoid intermediate reallocations.
- Transition builders to fixed-size APIs, removing growable variants.
- Refactor builders and serializers to operate on `ByteArea` sections, enabling
  zero-copy persistence across all structures.
- Move `DacsByte` metadata arrays into the arena and store per-level handles
  similar to `WaveletMatrixMeta`.
- Add slice-based range setters for integer builders to minimize manual index
  tracking during construction.
- Provide bulk bit setters like `set_bits_from_slice` for `BitVectorBuilder`
  to copy from packed data efficiently.
- Provide convenience helpers to manage `ByteArea` and `SectionWriter` setup for
  common builder use cases.
- Audit remaining constructors for zero-capacity variants and decide whether to
  offer explicit `empty` helpers instead of `with_capacity(0)`.
- Evaluate introducing more structured error types per module now that
  `anyhow` has been removed, ensuring diagnostics remain precise without
  relying on free-form strings.
- Allocate temporary wavelet-matrix buffers from `ByteArea` to avoid
  intermediate `Vec` copies and ensure fully contiguous construction.
- Provide a derive or macro to reduce boilerplate when implementing the
  `Serializable` trait.
- Consider a slice-based `WaveletMatrix` constructor to avoid requiring
  cloneable iterators.
 - Benchmark the cycle-based partitioning in `WaveletMatrixBuilder::freeze`
   and explore more efficient permutation strategies.
- Explore specialized rotation helpers for `BitVectorBuilder` to speed up
  recursive partitioning without extra buffers.
- Explore using `BitVectorBuilder` for other temporary bitmaps to reduce
  scattered `Vec<bool>` allocations.
- Review documentation examples across modules and convert remaining ignored
  snippets into runnable doctests.
- Explore iterating layer indices instead of reversing `remaining` to avoid
  the upfront `reverse` cost in `WaveletMatrixBuilder::freeze`.
- Audit integer-vector constructors for opportunities to allocate directly
  from `SectionWriter` without temporary `Vec`s.
- Document the fixed 64-bit word assumption across structures now that bit
  vectors use `u64` internally.
- Provide helpers on `SectionHandle` to derive typed sub-handles, reducing
  manual offset math in complex `from_bytes` implementations like `DacsByte`.
- Investigate slimming `DacsByte` per-level metadata to avoid storing unused
  flag handles for the last level.
- Provide a derive macro for the new `Metadata` trait to simplify implementing
  zero-copy metadata structs.
## Discovered Issues
- Upstream checked `SectionHandle::bytes`/`view` slicing to AnyBytes 0.20.x.
  `view` returns a `Result`, but both paths currently compute `offset + len` and
  slice before validation, so overflow or out-of-bounds handles can panic and
  every caller must preflight ranges manually.
- `katex.html` performs manual string replacements; consider DOM-based manipulation.
- Revisit zero-copy storage strategy: avoid extra copies when storing serialized bytes in structures.
- Enforce that `DacsByte` always retains at least one level instead of relying on defensive length checks.
