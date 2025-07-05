//! Top module for integer vectors.
//!
//! # Introduction
//!
//! Integer sequences consisting of many small values can be stored in compressed space
//! using *compressed integer vectors*.
//!
//! Let $`A = (a_0, a_1, \dots, a_{n-1})`$ be a sequence of $`n`$ unsigned integers.
//! Our integer vectors support the following queries:
//!
//! - $`\textrm{Access}(i)`$ returns $`a_i`$ (implemented by [`Access`]).
//! - $`\textrm{Update}(i, x)`$ modifies $`a_i \gets x`$.
//!
//! Note that they are not limited depending on data structures.
//!
//! # Data structures
//!
//! The implementations provided in this crate are summarized below:
//!
//! | Implementation | [Access](Access) | Update | Memory (bits) |
//! | --- | :-: | :-: | :-: |
//! | [`CompactVector`] | $`O(1)`$ | $`O(1)`$  | $`n \lceil \lg u \rceil`$ |
//! | [`DacsByte`] | $`O(\ell(a_i) / b)`$ | -- | $`\textrm{DAC}_\textrm{Byte}(A) + o(\textrm{DAC}_\textrm{Byte}(A)/b) + O(\lg u)`$ |
//!
//! The parameters are introduced below.
//!
//! ## Plain format without index
//!
//! [`CompactVector`] is a simple data structure in which each integer is represented in a fixed number of bits.
//! Assuming $`u`$ is the maximum value in $`A`$ plus 1,
//! each integer is stored in $`\lceil \lg u \rceil`$ bits of space.
//!
//! This is the only updatable data structure and will be the fastest due to its simplicity.
//! However, the compression performance is poor, especially when $`A`$ contains at least one large value.
//!
//!
//! ## Compressed format with Directly Addressable Codes
//!
//! [`DacsByte`] is a compressed data structure using Directly Addressable Codes (DACs),
//! a randomly-accessible variant of the VByte encoding scheme.
//!
//! Let
//!
//!  - $`\ell(a)`$ be the length in bits of the binary representation of an integer $`a`$,
//!  - $`b`$ be the length in bits assigned for each level with DACs, and
//!  - $`\textrm{DAC}(A)`$ be the length in bits of the encoded sequence from $`A`$ with DACs.
//!
//! The complexities are as shown in the table.
//! (For simplicity, we assume all levels have the same bit length $`b`$.)
//!
//! # Examples
//!
//! This module provides several traits for essential behaviors,
//! allowing to compare our integer vectors as components in your data structures.
//! [`prelude`] allows you to import them easily.
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use jerky::int_vectors::{DacsByte, prelude::*};
//!
//! let seq = DacsByte::build_from_slice(&[5, 0, 100000, 334])?;
//!
//! assert_eq!(seq.num_vals(), 4);
//!
//! assert_eq!(seq.access(3), Some(334));
//! assert_eq!(seq.access(4), None);
//! # Ok(())
//! # }
//! ```
pub mod compact_vector;
pub mod dacs_byte;

pub mod prelude;

pub use compact_vector::CompactVector;
pub use dacs_byte::DacsByte;

use anyhow::Result;
use num_traits::ToPrimitive;

/// Interface for building integer vectors.
pub trait Build {
    /// Creates a new vector from a slice of integers `vals`.
    ///
    /// # Arguments
    ///
    ///  - `vals`: Slice of integers to be stored.
    ///
    /// # Errors
    ///
    /// An error is returned if `vals` contains an integer that cannot be cast to [`usize`].
    fn build_from_slice<T>(vals: &[T]) -> Result<Self>
    where
        T: ToPrimitive,
        Self: Sized;
}

/// Interface for reporting basic statistics of integer vectors.
pub trait NumVals {
    /// Returns the number of integers stored.
    fn num_vals(&self) -> usize;
}

/// Interface for accessing elements on integer vectors.
pub trait Access {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    fn access(&self, pos: usize) -> Option<usize>;
}
