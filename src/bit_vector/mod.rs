//! Top module for bit vectors.
//!
//! # Introduction
//!
//! Bit vectors and operations on them are fundamental to succinct data structures.
//!
//! Let $`S \subseteq \{ 0,1,\dots,u-1 \}`$ be a set of positions
//! at which bits are set in a bit vector of length $`u`$.
//! Our bit vectors support the following queries:
//!
//! - $`\textrm{Access}(i)`$ returns `true` if $`i \in S`$ or `false` otherwise (implemented by [`Access`]).
//! - $`\textrm{Rank}(i)`$ returns the cardinality of $`\{ x \in S \mid x < i \}`$ (implemented by [`Rank`]).
//! - $`\textrm{Select}(k)`$ returns the $`k`$-th smallest position in $`S`$ (implemented by [`Select`]).
//! - $`\textrm{Update}(i)`$ inserts/removes $`i`$ to/from $`S`$.
//!
//! Note that they are not limited depending on data structures.
//!
//! # Data structures
//!
//! Let $`n`$ be the number of positions (i.e., $`n = |S|`$).
//! The implementations provided in this crate are summarized below:
//!
//! | Implementations | [Access](Access) | [Rank](Rank) | [Select](Select) | Update | Memory (bits) |
//! | --- | :-: | :-: | :-: | :-: | :-: |
//! | [`BitVector`] | $`O(1)`$  | $`O(u)`$ | $`O(u)`$ | $`O(1)`$ | $`u`$ |
//! | [`BitVector<rank9sel::inner::Rank9SelIndex>`] | $`O(1)`$ | $`O(1)`$ | $`O(\lg u)`$ | -- | $`u + o(u)`$ |
//!
//! ## Plain bit vectors without index
//!
//! [`BitVector`] is a plain format without index and the only mutable data structure.
//!
//! All search queries are performed by linear scan in $`O(u)`$ time,
//! although they are quickly computed in word units using bit-parallelism techniques.
//!
//! ## Plain bit vectors with index
//!
//! [`BitVector<rank9sel::inner::Rank9SelIndex>`] is an index structure for faster queries built on [`BitVector`].
//!
//! [`BitVector<rank9sel::inner::Rank9SelIndex>`] is an implementation of Vigna's Rank9 and hinted selection techniques, supporting
//! constant-time Rank and logarithmic-time Select queries.
//!
//! # Examples
//!
//! This module provides several traits for essential behaviors,
//! allowing you to compare our bit vectors as components in your data
//! structures. Import them all with `use jerky::bit_vector::*;`.
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use jerky::bit_vector::*;
//!
//! let mut builder = BitVectorBuilder::new();
//! builder.extend_bits([true, false, false, true]);
//! let bv = builder.freeze::<Rank9SelIndex>();
//!
//! assert_eq!(bv.num_bits(), 4);
//! assert_eq!(bv.num_ones(), 2);
//!
//! assert_eq!(bv.access(1), Some(false));
//!
//! assert_eq!(bv.rank1(1), Some(1));
//! assert_eq!(bv.rank0(1), Some(0));
//!
//! assert_eq!(bv.select1(1), Some(3));
//! assert_eq!(bv.select0(0), Some(1));
//! # Ok(())
//! # }
//! ```
pub mod rank9sel;

/// Interface for building a bit vector with rank/select queries.

/// Interface for reporting basic statistics in a bit vector.
pub trait NumBits {
    /// Returns the number of bits stored.
    fn num_bits(&self) -> usize;

    /// Returns the number of bits set.
    fn num_ones(&self) -> usize;

    /// Returns the number of bits unset.
    #[inline(always)]
    fn num_zeros(&self) -> usize {
        self.num_bits() - self.num_ones()
    }
}

/// Interface for accessing elements on bit arrays.
pub trait Access {
    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    fn access(&self, pos: usize) -> Option<bool>;
}

/// Interface for rank queries on bit vectors.
///
/// Let $`S \subseteq \{ 0,1,\dots,u-1 \}`$ be a set of positions
/// at which bits are set in a bit vector of length $`u`$.
pub trait Rank {
    /// Returns the cardinality of $`\{ x \in S \mid x < i \}`$,
    /// or [`None`] if $`u < x`$.
    fn rank1(&self, x: usize) -> Option<usize>;

    /// Returns the cardinality of $`\{ x \not\in S \mid 0 \leq x < i \}`$,
    /// or [`None`] if $`u < x`$.
    fn rank0(&self, x: usize) -> Option<usize>;
}

/// Interface for select queries on bit vectors.
///
/// Let $`S \subseteq \{ 0,1,\dots,u-1 \}`$ be a set of positions
/// at which bits are set in a bit vector of length $`u`$.
pub trait Select {
    /// Returns the $`k`$-th smallest position in $`S`$, or
    /// [`None`] if out of bounds.
    fn select1(&self, k: usize) -> Option<usize>;

    /// Returns the $`k`$-th smallest integer $`x`$ such that $`x \not\in S`$ and $`0 \leq x < u`$, or
    /// [`None`] if out of bounds.
    fn select0(&self, k: usize) -> Option<usize>;
}

/// The number of bits in a machine word.
pub const WORD_LEN: usize = core::mem::size_of::<usize>() * 8;

use anybytes::{Bytes, View};
use anyhow::{anyhow, Result};

/// Builder that collects raw bits into a zero-copy [`BitVector`].
#[derive(Debug, Default, Clone)]
pub struct BitVectorBuilder {
    words: Vec<usize>,
    len: usize,
}

impl BitVectorBuilder {
    /// Creates an empty builder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Pushes a single bit.
    pub fn push_bit(&mut self, bit: bool) {
        let pos_in_word = self.len % WORD_LEN;
        if pos_in_word == 0 {
            self.words.push(bit as usize);
        } else {
            let cur = self.words.last_mut().unwrap();
            *cur |= (bit as usize) << pos_in_word;
        }
        self.len += 1;
    }

    /// Pushes `len` bits from `bits` at the end.
    ///
    /// Bits outside the lowest `len` bits are truncated.
    pub fn push_bits(&mut self, bits: usize, len: usize) -> Result<()> {
        if WORD_LEN < len {
            return Err(anyhow!(
                "len must be no greater than {WORD_LEN}, but got {len}."
            ));
        }
        if len == 0 {
            return Ok(());
        }

        let mask = if len < WORD_LEN {
            (1 << len) - 1
        } else {
            usize::MAX
        };
        let bits = bits & mask;

        let pos_in_word = self.len % WORD_LEN;
        if pos_in_word == 0 {
            self.words.push(bits);
        } else {
            let cur = self.words.last_mut().unwrap();
            *cur |= bits << pos_in_word;
            if len > WORD_LEN - pos_in_word {
                self.words.push(bits >> (WORD_LEN - pos_in_word));
            }
        }
        self.len += len;
        Ok(())
    }

    /// Sets the `pos`-th bit to `bit`.
    pub fn set_bit(&mut self, pos: usize, bit: bool) -> Result<()> {
        if self.len <= pos {
            return Err(anyhow!(
                "pos must be no greater than self.len()={}, but got {pos}.",
                self.len
            ));
        }
        let word = pos / WORD_LEN;
        let pos_in_word = pos % WORD_LEN;
        self.words[word] &= !(1 << pos_in_word);
        self.words[word] |= (bit as usize) << pos_in_word;
        Ok(())
    }

    /// Extends the builder from an iterator of bits.
    pub fn extend_bits<I: IntoIterator<Item = bool>>(&mut self, bits: I) {
        bits.into_iter().for_each(|b| self.push_bit(b));
    }

    fn into_data(self) -> BitVectorData {
        let words = Bytes::from_source(self.words).view::<[usize]>().unwrap();
        BitVectorData {
            words,
            len: self.len,
        }
    }

    /// Finalizes the builder into a [`BitVector`].
    pub fn freeze<I: BitVectorIndex>(self) -> BitVector<I> {
        let data = self.into_data();
        let index = I::build(&data);
        BitVector::new(data, index)
    }

    /// Serializes the builder contents into a [`Bytes`] buffer.
    pub fn into_bytes(self) -> (usize, Bytes) {
        (self.len, Bytes::from_source(self.words))
    }
}

/// Immutable bit vector data without auxiliary indexes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitVectorData {
    /// Underlying machine words storing bit data.
    pub words: View<[usize]>,
    /// Number of valid bits in `words`.
    pub len: usize,
}

impl Default for BitVectorData {
    fn default() -> Self {
        Self {
            words: Bytes::empty().view::<[usize]>().unwrap(),
            len: 0,
        }
    }
}

impl BitVectorData {
    /// Creates bit vector data from a bit iterator.
    pub fn from_bits<I: IntoIterator<Item = bool>>(bits: I) -> Self {
        let mut builder = BitVectorBuilder::new();
        builder.extend_bits(bits);
        builder.into_data()
    }

    /// Reconstructs the data from zero-copy [`Bytes`].
    pub fn from_bytes(len: usize, bytes: Bytes) -> Result<Self> {
        let words = bytes.view::<[usize]>().map_err(|e| anyhow::anyhow!(e))?;
        Ok(Self { words, len })
    }

    /// Returns the number of bits stored.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns the raw word slice.
    pub fn words(&self) -> &[usize] {
        self.words.as_ref()
    }

    /// Returns the number of words stored.
    pub fn num_words(&self) -> usize {
        self.words.len()
    }

    /// Returns `len` bits starting at position `pos`.
    pub fn get_bits(&self, pos: usize, len: usize) -> Option<usize> {
        if WORD_LEN < len || self.len() < pos + len {
            return None;
        }
        if len == 0 {
            return Some(0);
        }
        let block = pos / WORD_LEN;
        let shift = pos % WORD_LEN;
        let mask = if len < WORD_LEN {
            (1 << len) - 1
        } else {
            usize::MAX
        };
        let bits = if shift + len <= WORD_LEN {
            (self.words[block] >> shift) & mask
        } else {
            (self.words[block] >> shift) | ((self.words[block + 1] << (WORD_LEN - shift)) & mask)
        };
        Some(bits)
    }

    /// Returns the number of bytes required for the old copy-based serialization.
    pub fn size_in_bytes(&self) -> usize {
        std::mem::size_of::<usize>() * (self.words.len() + 2)
    }

    /// Serializes the data into a [`Bytes`] buffer.
    pub fn to_bytes(&self) -> (usize, Bytes) {
        (self.len, self.words.clone().bytes())
    }
}

impl From<BitVectorData> for BitVector<NoIndex> {
    fn from(data: BitVectorData) -> Self {
        BitVector::new(data, NoIndex)
    }
}

impl Access for BitVectorData {
    fn access(&self, pos: usize) -> Option<bool> {
        if pos < self.len {
            let block = pos / WORD_LEN;
            let shift = pos % WORD_LEN;
            Some((self.words[block] >> shift) & 1 == 1)
        } else {
            None
        }
    }
}

/// Index trait for bit vector data.
pub trait BitVectorIndex: Sized {
    /// Constructs an index from bit vector data.
    fn build(data: &BitVectorData) -> Self;

    /// Counts set bits in the data.
    fn num_ones(&self, data: &BitVectorData) -> usize;

    /// Counts unset bits in the data.
    fn num_zeros(&self, data: &BitVectorData) -> usize {
        data.len() - self.num_ones(data)
    }

    /// Rank query for ones.
    fn rank1(&self, data: &BitVectorData, pos: usize) -> Option<usize>;

    /// Rank query for zeros.
    fn rank0(&self, data: &BitVectorData, pos: usize) -> Option<usize> {
        Some(pos - self.rank1(data, pos)?)
    }

    /// Select query for ones.
    fn select1(&self, data: &BitVectorData, k: usize) -> Option<usize>;

    /// Select query for zeros.
    fn select0(&self, data: &BitVectorData, k: usize) -> Option<usize>;
}

/// Placeholder index that performs linear scans over the data.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NoIndex;

impl BitVectorIndex for NoIndex {
    fn build(_: &BitVectorData) -> Self {
        NoIndex
    }

    fn num_ones(&self, data: &BitVectorData) -> usize {
        data.words
            .iter()
            .map(|&w| crate::broadword::popcount(w))
            .sum()
    }

    fn rank1(&self, data: &BitVectorData, pos: usize) -> Option<usize> {
        if data.len() < pos {
            return None;
        }
        let mut r = 0;
        let (wpos, left) = (pos / WORD_LEN, pos % WORD_LEN);
        for &w in &data.words[..wpos] {
            r += crate::broadword::popcount(w);
        }
        if left != 0 {
            r += crate::broadword::popcount(data.words[wpos] << (WORD_LEN - left));
        }
        Some(r)
    }

    fn select1(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        let mut wpos = 0;
        let mut cur_rank = 0;
        while wpos < data.words.len() {
            let cnt = crate::broadword::popcount(data.words[wpos]);
            if k < cur_rank + cnt {
                break;
            }
            wpos += 1;
            cur_rank += cnt;
        }
        if wpos == data.words.len() {
            return None;
        }
        let sel = wpos * WORD_LEN
            + crate::broadword::select_in_word(data.words[wpos], k - cur_rank).unwrap();
        Some(sel)
    }

    fn select0(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        let mut wpos = 0;
        let mut cur_rank = 0;
        while wpos < data.words.len() {
            let cnt = crate::broadword::popcount(!data.words[wpos]);
            if k < cur_rank + cnt {
                break;
            }
            wpos += 1;
            cur_rank += cnt;
        }
        if wpos == data.words.len() {
            return None;
        }
        let sel = wpos * WORD_LEN
            + crate::broadword::select_in_word(!data.words[wpos], k - cur_rank).unwrap();
        if sel < data.len() {
            Some(sel)
        } else {
            None
        }
    }
}

/// Immutable bit vector data combined with an auxiliary index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitVector<I> {
    /// Raw data bits.
    pub data: BitVectorData,
    /// Associated index.
    pub index: I,
}

/// Iterator over bits in a [`BitVector`].
pub struct Iter<'a, I> {
    bv: &'a BitVector<I>,
    pos: usize,
}

impl<'a, I> Iter<'a, I> {
    /// Creates a new iterator.
    pub const fn new(bv: &'a BitVector<I>) -> Self {
        Self { bv, pos: 0 }
    }
}

impl<I> Iterator for Iter<'_, I> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.bv.len() {
            let bit = self.bv.access(self.pos).unwrap();
            self.pos += 1;
            Some(bit)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.bv.len(), Some(self.bv.len()))
    }
}

impl<I> BitVector<I> {
    /// Creates a new wrapper from data and index.
    pub const fn new(data: BitVectorData, index: I) -> Self {
        Self { data, index }
    }

    /// Returns the number of bits stored.
    pub const fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns the `len` bits starting at `pos`, or [`None`] if out of bounds.
    pub fn get_bits(&self, pos: usize, len: usize) -> Option<usize> {
        self.data.get_bits(pos, len)
    }

    /// Creates an iterator over all bits.
    pub const fn iter(&self) -> Iter<I> {
        Iter { bv: self, pos: 0 }
    }

    /// Collects all bits into a `Vec<bool>` for inspection.
    pub fn to_vec(&self) -> Vec<bool> {
        self.iter().collect()
    }
}

impl<I: BitVectorIndex> NumBits for BitVector<I> {
    fn num_bits(&self) -> usize {
        self.data.len()
    }

    fn num_ones(&self) -> usize {
        self.index.num_ones(&self.data)
    }
}

impl<I> Access for BitVector<I> {
    fn access(&self, pos: usize) -> Option<bool> {
        self.data.access(pos)
    }
}

impl<I: BitVectorIndex> Rank for BitVector<I> {
    fn rank1(&self, pos: usize) -> Option<usize> {
        self.index.rank1(&self.data, pos)
    }

    fn rank0(&self, pos: usize) -> Option<usize> {
        self.index.rank0(&self.data, pos)
    }
}

impl<I: BitVectorIndex> Select for BitVector<I> {
    fn select1(&self, k: usize) -> Option<usize> {
        self.index.select1(&self.data, k)
    }

    fn select0(&self, k: usize) -> Option<usize> {
        self.index.select0(&self.data, k)
    }
}

pub use rank9sel::Rank9SelIndex;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_index_wrapper() {
        let data = BitVectorData::from_bits([true, false, false, true]);
        let bv = BitVector::new(data, NoIndex);

        assert_eq!(bv.num_bits(), 4);
        assert_eq!(bv.num_ones(), 2);
        assert_eq!(bv.access(0), Some(true));
        assert_eq!(bv.rank1(4), Some(2));
        assert_eq!(bv.select1(1), Some(3));
        assert_eq!(bv.select0(0), Some(1));
    }

    #[test]
    fn builder_freeze() {
        let mut builder = BitVectorBuilder::new();
        builder.extend_bits([true, false]);
        builder.push_bits(0b10, 2).unwrap();
        builder.set_bit(1, true).unwrap();
        let bv: BitVector<NoIndex> = builder.freeze::<NoIndex>();
        assert_eq!(bv.len(), 4);
        assert_eq!(bv.get_bits(0, 4), Some(0b1011));
    }

    #[test]
    fn from_bytes_roundtrip() {
        let mut builder = BitVectorBuilder::new();
        builder.extend_bits([true, false, true, true, false]);
        let expected: BitVector<NoIndex> = builder.clone().freeze::<NoIndex>();
        let (len, bytes) = builder.into_bytes();

        let data = BitVectorData::from_bytes(len, bytes).unwrap();
        let other: BitVector<NoIndex> = data.into();
        assert_eq!(expected, other);
    }

    #[test]
    fn get_bits_wrapper() {
        let data = BitVectorData::from_bits([true, false, true, true, false]);
        let bv = BitVector::new(data.clone(), NoIndex);
        assert_eq!(data.get_bits(1, 3), Some(0b110));
        assert_eq!(data.get_bits(2, 4), None);
        assert_eq!(bv.get_bits(1, 3), Some(0b110));
        assert_eq!(bv.get_bits(2, 4), None);
    }

    #[test]
    fn builder_push_bits_across_word() {
        let mut builder = BitVectorBuilder::new();
        builder.extend_bits(core::iter::repeat(false).take(62));
        builder.push_bits(0b011111, 6).unwrap();
        let bv: BitVector<NoIndex> = builder.freeze::<NoIndex>();
        assert_eq!(bv.data.get_bits(61, 7).unwrap(), 0b0111110);
    }

    #[test]
    fn iter_collects() {
        let data = BitVectorData::from_bits([true, false, true]);
        let bv = BitVector::new(data, NoIndex);
        let collected: Vec<bool> = bv.iter().collect();
        assert_eq!(collected, vec![true, false, true]);
    }

    #[test]
    fn to_vec_collects() {
        let data = BitVectorData::from_bits([true, false, true]);
        let bv = BitVector::new(data, NoIndex);
        assert_eq!(bv.to_vec(), vec![true, false, true]);
    }
}
