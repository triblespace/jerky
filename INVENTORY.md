# Inventory

## Potential Removals
- None at the moment.

## Desired Functionality
- Provide more usage examples and documentation.
- Evaluate additional succinct data structures to include.
- Investigate alternative dense-select index strategies to replace removed `DArrayIndex`.
- Explore additional index implementations leveraging the new generic `DacsByte<I>`.
- Demonstrate the generic `from_slice` usage in examples and docs.
- Showcase `DacsByte` byte serialization in an example.
- Provide serialization helpers for additional structures beyond `WaveletMatrix`.
- Show `CompactVector::to_bytes` and `from_bytes` in examples.

## Discovered Issues
- `katex.html` performs manual string replacements; consider DOM-based manipulation.
