//! Constants for bit vector operations.

/// The number of bits in a machine word.
pub const WORD_LEN: usize = std::mem::size_of::<usize>() * 8;
