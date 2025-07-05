//! Raw storage types and generic wrapper for bit vectors.
//!
//! The [`BitVectorBuilder`] allows collecting bits and freezing them into
//! [`BitVector`] backed by zero-copy [`BitVectorData`]. Data can also be
//! reconstructed directly from [`anybytes::Bytes`] obtained via an mmap
//! wrapper like `Bytes::from_source`.

use crate::bit_vectors::bit_vector::BitVector as RawBitVector;
use crate::bit_vectors::bit_vector::WORD_LEN;
use crate::bit_vectors::{Access, NumBits, Rank, Select};
use anybytes::{Bytes, View};
use anyhow::Result;

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
    pub fn freeze<B: IndexBuilder>(self) -> BitVector<B::Built> {
        let data = self.into_data();
        let index = B::build(&data);
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

    /// Returns the number of bytes required for the old copy-based serialization.
    pub fn size_in_bytes(&self) -> usize {
        std::mem::size_of::<usize>() * (self.words.len() + 2)
    }

    /// Serializes the data into a [`Bytes`] buffer.
    pub fn to_bytes(&self) -> (usize, Bytes) {
        (self.len, self.words.clone().bytes())
    }
}

impl From<RawBitVector> for BitVectorData {
    fn from(bv: RawBitVector) -> Self {
        let words = Bytes::from_source(bv.words().to_vec())
            .view::<[usize]>()
            .unwrap();
        Self {
            words,
            len: bv.len(),
        }
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
pub trait BitVectorIndex {
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

/// Helper trait for constructing indexes from [`BitVectorData`].
pub trait IndexBuilder {
    /// Output index type constructed by this builder.
    type Built: BitVectorIndex;

    /// Builds an index from the given data.
    fn build(data: &BitVectorData) -> Self::Built;
}

/// Placeholder index that performs linear scans over the data.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NoIndex;

impl BitVectorIndex for NoIndex {
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

impl IndexBuilder for NoIndex {
    type Built = NoIndex;

    fn build(_: &BitVectorData) -> Self::Built {
        NoIndex
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

impl<I> BitVector<I> {
    /// Creates a new wrapper from data and index.
    pub const fn new(data: BitVectorData, index: I) -> Self {
        Self { data, index }
    }

    /// Returns the number of bits stored.
    pub const fn len(&self) -> usize {
        self.data.len()
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
        builder.extend_bits([true, false, true, false]);
        let bv: BitVector<NoIndex> = builder.freeze::<NoIndex>();
        assert_eq!(bv.len(), 4);
        assert_eq!(bv.access(2), Some(true));
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
}
