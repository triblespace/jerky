//! The prelude for bit vectors.
//!
//! The purpose of this module is to alleviate imports of many common traits for bit vectors.
//!
//! ```
//! # #![allow(unused_imports)]
//! use jerky::bit_vectors::prelude::*;
//! ```
pub use crate::bit_vectors::{Access, Build, NumBits, Rank, Select};
