//! Top module for character sequences.
//!
//! # Introduction
//!
//! *Character sequences* are a generalization of [bit vectors](crate::bit_vector),
//! whose elements are drawn from an alphabet $`\Sigma = \{ 0,1,\dots,\sigma - 1 \}`$.
//!
//! Let $`(c_0, c_1, \dots, c_{n-1}) \in \Sigma^{n} `$ be a sequence of $`n`$ characters.
//! Our sequences support the following queries:
//!
//! - $`\textrm{Access}(i)`$ returns $`c_i`$.
//! - $`\textrm{Rank}(i,c)`$ returns the number of occurrences of character $`c`$ for $`c_0,c_1,\dots,c_{i-1}`$.
//! - $`\textrm{Select}(k,c)`$ returns the occurrence position of the $`k`$-th character $`c`$.
//!
//! Note that they are not limited depending on data structures.
//!
//! # Data structures
//!
//! The implementations provided in this crate are summarized below:
//!
//! | Implementation | Access | Rank | Select | Memory (bits) |
//! | --- | :-: | :-: | :-: | :-: |
//! | [`WaveletMatrix`] | $`O(\lg \sigma)`$ | $`O(\lg \sigma)`$ | $`O(\lg \sigma)`$ | $`O(n \lg \sigma )`$ |
//!
//! Since there is only one implementation, we do not provide traits for the queries.
//!
//! ## Wavelet trees
//!
//! [`WaveletMatrix`] is a practical variant of Wavelet trees that are functional character sequences.
//! In addition to the basic queires listed above, this provides several range queries
//! such as [`quantile`](WaveletMatrix::quantile) or [`intersect`](WaveletMatrix::intersect).
//!
//! Its complexities are related to those of a [bit vector](crate::bit_vector) used internally.
//! For simplicity, the above table assumes constant-time and linear-space implementation.
pub mod wavelet_matrix;

pub use wavelet_matrix::WaveletMatrix;
