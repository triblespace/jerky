# Inventory

## Potential Removals
- None at the moment.

## Desired Functionality
- Provide more usage examples and documentation.
- Evaluate additional succinct data structures to include.
- Investigate alternative dense-select index strategies to replace removed `DArrayIndex`.

## Discovered Issues
- `katex.html` performs manual string replacements; consider DOM-based manipulation.
- bit_vector prelude lacks common types like `BitVectorBuilder` and `Rank9SelIndex`,
  forcing verbose imports in examples.
- Import paths for `BitVectorBuilder` include a redundant `bit_vector` module
  segment, e.g. `jerky::bit_vector::bit_vector::BitVectorBuilder`.
  Cleanup the module layout so examples only need `jerky::bit_vector`.
