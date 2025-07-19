# Inventory

## Potential Removals
- None at the moment.

## Desired Functionality
- Expose utilities for inspecting and debugging built vectors.
- Provide more usage examples and documentation.
- Evaluate additional succinct data structures to include.
- Investigate alternative dense-select index strategies to replace removed `DArrayIndex`.
- Audit documentation for broken module links after recent restructuring.
- Ensure README and examples reference the new `bit_vector` module name.

## Discovered Issues
- `katex.html` performs manual string replacements; consider DOM-based manipulation.
- Benchmarks still used the old `jerky::bit_vectors` path, breaking compilation.
