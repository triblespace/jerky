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
//! use anybytes::ByteArea;
//! let mut area = ByteArea::new()?;
//! let mut sections = area.sections();
//! let mut builder = BitVectorBuilder::with_capacity(4, &mut sections)?;
//! builder.set_bit(0, true)?;
//! builder.set_bit(3, true)?;
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
pub const WORD_LEN: usize = core::mem::size_of::<u64>() * 8;

use crate::serialization::Serializable;
use anybytes::area::ByteArea;
use anybytes::area::Section;
use anybytes::area::SectionHandle;
use anybytes::area::SectionWriter;
use anybytes::Bytes;
use anybytes::View;

use crate::error::{Error, Result};

/// Builder that collects raw bits into a zero-copy [`BitVector`].

#[derive(Debug)]
pub struct BitVectorBuilder<'a> {
    words: Section<'a, u64>,
    len: usize,
}

impl<'a> BitVectorBuilder<'a> {
    /// Creates a builder storing `len` zero bits.
    pub fn with_capacity(len: usize, writer: &mut SectionWriter<'a>) -> Result<Self> {
        let num_words = (len + WORD_LEN - 1) / WORD_LEN;
        let mut words = writer.reserve::<u64>(num_words)?;
        words.as_mut_slice().fill(0);
        Ok(Self { words, len })
    }

    /// Creates a builder that stores `len` copies of `bit`.
    pub fn from_bit(bit: bool, len: usize, writer: &mut SectionWriter<'a>) -> Result<Self> {
        if len == 0 {
            return Self::with_capacity(0, writer);
        }
        let word = if bit { u64::MAX } else { 0 };
        let num_words = (len + WORD_LEN - 1) / WORD_LEN;
        let mut words = writer.reserve::<u64>(num_words)?;
        words.as_mut_slice().fill(word);
        let shift = len % WORD_LEN;
        if shift != 0 {
            let mask = (1u64 << shift) - 1;
            *words.as_mut_slice().last_mut().unwrap() &= mask;
        }
        Ok(Self { words, len })
    }

    /// Fills the entire builder with `bit`.
    pub fn fill(&mut self, bit: bool) {
        let word = if bit { u64::MAX } else { 0 };
        self.words.as_mut_slice().fill(word);
        if bit {
            let shift = self.len % WORD_LEN;
            if shift != 0 {
                let mask = (1u64 << shift) - 1;
                if let Some(last) = self.words.as_mut_slice().last_mut() {
                    *last &= mask;
                }
            }
        }
    }

    /// Returns the `pos`-th bit.
    pub fn get_bit(&self, pos: usize) -> Result<bool> {
        if self.len <= pos {
            return Err(Error::invalid_argument(format!(
                "pos must be no greater than self.len()={}, but got {pos}.",
                self.len
            )));
        }
        let word = pos / WORD_LEN;
        let pos_in_word = pos % WORD_LEN;
        Ok(((self.words[word] >> pos_in_word) & 1u64) == 1)
    }

    /// Sets the `pos`-th bit to `bit`.
    pub fn set_bit(&mut self, pos: usize, bit: bool) -> Result<()> {
        if self.len <= pos {
            return Err(Error::invalid_argument(format!(
                "pos must be no greater than self.len()={}, but got {pos}.",
                self.len
            )));
        }
        let word = pos / WORD_LEN;
        let pos_in_word = pos % WORD_LEN;
        self.words[word] &= !(1u64 << pos_in_word);
        self.words[word] |= (bit as u64) << pos_in_word;
        Ok(())
    }

    /// Sets all bits in `range` to `bit`.
    pub fn set_bits(&mut self, range: std::ops::Range<usize>, bit: bool) -> Result<()> {
        if range.end > self.len {
            return Err(Error::invalid_argument(format!(
                "range end must be no greater than self.len()={}, but got {}.",
                self.len, range.end
            )));
        }
        if range.is_empty() {
            return Ok(());
        }
        let mut pos = range.start;
        while pos < range.end {
            let word = pos / WORD_LEN;
            let pos_in_word = pos % WORD_LEN;
            let remaining = range.end - pos;
            let take = remaining.min(WORD_LEN - pos_in_word);
            let mask = if take == WORD_LEN {
                u64::MAX
            } else {
                ((1u64 << take) - 1) << pos_in_word
            };
            if bit {
                self.words[word] |= mask;
            } else {
                self.words[word] &= !mask;
            }
            pos += take;
        }
        Ok(())
    }

    /// Swaps bits at positions `a` and `b`.
    pub fn swap_bits(&mut self, a: usize, b: usize) -> Result<()> {
        if a >= self.len || b >= self.len {
            return Err(Error::invalid_argument(format!(
                "positions must be less than self.len()={}, but got {a} and {b}.",
                self.len
            )));
        }
        if a == b {
            return Ok(());
        }
        let wa = a / WORD_LEN;
        let wb = b / WORD_LEN;
        let ba = a % WORD_LEN;
        let bb = b % WORD_LEN;
        let ma = 1u64 << ba;
        let mb = 1u64 << bb;
        let bit_a = (self.words[wa] & ma) != 0;
        let bit_b = (self.words[wb] & mb) != 0;
        if bit_a != bit_b {
            self.words[wa] ^= ma;
            self.words[wb] ^= mb;
        }
        Ok(())
    }

    /// Sets bits starting at `start` from the provided iterator.
    ///
    /// Bits are written sequentially from `start` until either the iterator is
    /// exhausted or the builder capacity is reached. Returns the number of bits
    /// written. The iterator is taken by mutable reference so that any
    /// unconsumed items remain available to the caller.
    pub fn set_bits_from_iter<I>(&mut self, start: usize, bits: &mut I) -> Result<usize>
    where
        I: Iterator<Item = bool>,
    {
        if start > self.len {
            return Err(Error::invalid_argument(format!(
                "start must be no greater than self.len()={}, but got {}.",
                self.len, start
            )));
        }
        let mut pos = start;
        while pos < self.len {
            match bits.next() {
                Some(bit) => {
                    self.set_bit(pos, bit)?;
                    pos += 1;
                }
                None => break,
            }
        }
        Ok(pos - start)
    }

    fn into_data(self) -> BitVectorData {
        let handle = self.words.handle();
        let words_bytes = self.words.freeze().expect("freeze section");
        let words = words_bytes.view::<[u64]>().unwrap();
        BitVectorData {
            words,
            len: self.len,
            handle: Some(handle),
        }
    }

    /// Finalizes the builder into a [`BitVector`].
    pub fn freeze<I: BitVectorIndex>(self) -> BitVector<I> {
        let data = self.into_data();
        let index = I::build(&data);
        BitVector::new(data, index)
    }

    /// Returns a handle to the backing words section.
    pub fn handle(&self) -> SectionHandle<u64> {
        self.words.handle()
    }
}

/// Immutable bit vector data without auxiliary indexes.
#[derive(Debug, Clone)]
pub struct BitVectorData {
    /// Underlying machine words storing bit data.
    pub words: View<[u64]>,
    /// Number of valid bits in `words`.
    pub len: usize,
    /// Handle to the backing words section, if available.
    pub handle: Option<SectionHandle<u64>>,
}

impl PartialEq for BitVectorData {
    fn eq(&self, other: &Self) -> bool {
        self.words == other.words && self.len == other.len
    }
}

impl Eq for BitVectorData {}

/// Metadata describing a [`BitVectorData`] stored in a [`ByteArea`].
#[derive(Debug, Clone, Copy, zerocopy::FromBytes, zerocopy::KnownLayout, zerocopy::Immutable)]
#[repr(C)]
pub struct BitVectorDataMeta {
    /// Number of bits stored.
    pub len: usize,
    /// Handle to the raw `u64` words backing the vector.
    pub handle: SectionHandle<u64>,
}

impl Default for BitVectorData {
    fn default() -> Self {
        Self {
            words: Bytes::empty().view::<[u64]>().unwrap(),
            len: 0,
            handle: None,
        }
    }
}

impl BitVectorData {
    /// Creates bit vector data from a bit iterator.
    pub fn from_bits<I: IntoIterator<Item = bool>>(bits: I) -> Self {
        let vec: Vec<bool> = bits.into_iter().collect();
        let mut area = ByteArea::new().expect("byte area");
        let mut sections = area.sections();
        let mut builder = BitVectorBuilder::with_capacity(vec.len(), &mut sections).unwrap();
        for (i, b) in vec.into_iter().enumerate() {
            builder.set_bit(i, b).unwrap();
        }
        builder.into_data()
    }

    /// Serializes the data into a [`Bytes`] buffer and accompanying metadata.
    /// Returns metadata describing this data.
    pub fn metadata(&self) -> BitVectorDataMeta {
        BitVectorDataMeta {
            len: self.len,
            handle: self.handle.expect("missing handle"),
        }
    }

    /// Reconstructs the data from zero-copy [`Bytes`] and its metadata.
    pub fn from_bytes(meta: BitVectorDataMeta, bytes: Bytes) -> Result<Self> {
        let words = meta.handle.view(&bytes)?;
        let capacity_bits = words
            .as_ref()
            .len()
            .checked_mul(WORD_LEN)
            .ok_or_else(|| Error::invalid_metadata("bit vector capacity overflow"))?;
        if meta.len > capacity_bits {
            return Err(Error::invalid_metadata(format!(
                "bit vector length {} exceeds capacity {}",
                meta.len, capacity_bits
            )));
        }
        Ok(Self {
            words,
            len: meta.len,
            handle: Some(meta.handle),
        })
    }

    /// Returns the number of bits stored.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns the raw word slice.
    pub fn words(&self) -> &[u64] {
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
            (1u64 << len) - 1
        } else {
            u64::MAX
        };
        let bits = if shift + len <= WORD_LEN {
            (self.words[block] >> shift) & mask
        } else {
            (self.words[block] >> shift) | ((self.words[block + 1] << (WORD_LEN - shift)) & mask)
        };
        Some(bits as usize)
    }
}

impl Serializable for BitVectorData {
    type Meta = BitVectorDataMeta;
    type Error = Error;

    fn metadata(&self) -> Self::Meta {
        BitVectorData::metadata(self)
    }

    fn from_bytes(meta: Self::Meta, bytes: Bytes) -> Result<Self> {
        BitVectorData::from_bytes(meta, bytes)
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
            Some((self.words[block] >> shift) & 1u64 == 1)
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
#[derive(Debug, Clone)]
pub struct BitVector<I> {
    /// Raw data bits.
    pub data: BitVectorData,
    /// Associated index.
    pub index: I,
}

impl<I: PartialEq> PartialEq for BitVector<I> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data && self.index == other.index
    }
}

impl<I: Eq> Eq for BitVector<I> {}

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
    pub const fn iter(&'_ self) -> Iter<'_, I> {
        Iter { bv: self, pos: 0 }
    }

    /// Collects all bits into a `Vec<bool>` for inspection.
    pub fn to_vec(&self) -> Vec<bool> {
        self.iter().collect()
    }

    /// Returns the handle to the backing words section, if available.
    pub fn handle(&self) -> Option<SectionHandle<u64>> {
        self.data.handle
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

impl<I: BitVectorIndex> BitVector<I> {
    /// Serializes the vector into a [`Bytes`] buffer and accompanying metadata.
    /// Returns metadata describing this vector's data.
    pub fn metadata(&self) -> BitVectorDataMeta {
        <Self as Serializable>::metadata(self)
    }

    /// Reconstructs the vector from zero-copy [`Bytes`] and its metadata.
    pub fn from_bytes(meta: BitVectorDataMeta, bytes: Bytes) -> Result<Self> {
        <Self as Serializable>::from_bytes(meta, bytes)
    }
}

impl<I: BitVectorIndex> Serializable for BitVector<I> {
    type Meta = BitVectorDataMeta;
    type Error = Error;

    fn metadata(&self) -> Self::Meta {
        self.data.metadata()
    }

    fn from_bytes(meta: Self::Meta, bytes: Bytes) -> Result<Self> {
        let data = BitVectorData::from_bytes(meta, bytes)?;
        let index = I::build(&data);
        Ok(BitVector::new(data, index))
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
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder = BitVectorBuilder::with_capacity(4, &mut sections).unwrap();
        builder.set_bit(0, true).unwrap();
        builder.set_bit(1, true).unwrap();
        builder.set_bit(3, true).unwrap();
        let bv: BitVector<NoIndex> = builder.freeze::<NoIndex>();
        assert_eq!(bv.len(), 4);
        assert_eq!(bv.get_bits(0, 4), Some(0b1011));
    }

    #[test]
    fn from_bytes_roundtrip() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder = BitVectorBuilder::with_capacity(5, &mut sections).unwrap();
        builder.set_bit(0, true).unwrap();
        builder.set_bit(2, true).unwrap();
        builder.set_bit(3, true).unwrap();
        let expected: BitVector<NoIndex> =
            BitVectorData::from_bits([true, false, true, true, false]).into();
        let bv: BitVector<NoIndex> = builder.freeze::<NoIndex>();
        let meta = bv.metadata();
        let bytes = area.freeze().unwrap();
        let other: BitVector<NoIndex> = BitVector::from_bytes(meta, bytes).unwrap();
        assert_eq!(expected, other);
    }

    #[test]
    fn from_bytes_rejects_metadata_len_overflow() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let builder = BitVectorBuilder::with_capacity(WORD_LEN, &mut sections).unwrap();
        let data = builder.into_data();
        let mut meta = data.metadata();
        let capacity_bits = data.num_words() * WORD_LEN;
        meta.len = capacity_bits + 1;
        drop(data);
        drop(sections);
        let bytes = area.freeze().unwrap();

        let err = BitVectorData::from_bytes(meta, bytes).unwrap_err();
        assert!(matches!(err, Error::InvalidMetadata(_)));
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
    fn builder_set_bits_across_word() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder = BitVectorBuilder::with_capacity(68, &mut sections).unwrap();
        builder.set_bits(0..68, false).unwrap();
        builder.set_bits(62..68, true).unwrap();
        builder.set_bit(67, false).unwrap();
        let bv: BitVector<NoIndex> = builder.freeze::<NoIndex>();
        assert_eq!(bv.data.get_bits(61, 7).unwrap(), 0b0111110);
    }

    #[test]
    fn builder_from_bit() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let builder = BitVectorBuilder::from_bit(true, 5, &mut sections).unwrap();
        let bv: BitVector<NoIndex> = builder.freeze::<NoIndex>();
        assert_eq!(bv.len(), 5);
        assert_eq!(bv.num_ones(), 5);
    }

    #[test]
    fn builder_capacity_limit() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder = BitVectorBuilder::with_capacity(3, &mut sections).unwrap();
        assert!(builder.set_bit(3, true).is_err());
    }

    #[test]
    fn builder_set_bits_from_iter() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder = BitVectorBuilder::with_capacity(4, &mut sections).unwrap();
        let mut iter = [true, false, true, true].iter().copied();
        let written = builder.set_bits_from_iter(0, &mut iter).unwrap();
        assert_eq!(written, 4);
        let bv: BitVector<NoIndex> = builder.freeze::<NoIndex>();
        assert_eq!(bv.data.get_bits(0, 4).unwrap(), 0b1101);
    }

    #[test]
    fn builder_set_bits_from_iter_leaves_unconsumed() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder = BitVectorBuilder::with_capacity(2, &mut sections).unwrap();
        let mut iter = [true, false, true].iter().copied();
        let written = builder.set_bits_from_iter(0, &mut iter).unwrap();
        assert_eq!(written, 2);
        let remaining: Vec<bool> = iter.collect();
        assert_eq!(remaining, vec![true]);
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
