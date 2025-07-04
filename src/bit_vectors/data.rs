//! Raw storage types and generic wrapper for bit vectors.

use crate::bit_vectors::bit_vector::BitVector as RawBitVector;
use crate::bit_vectors::bit_vector::WORD_LEN;
use crate::bit_vectors::{Access, NumBits, Rank, Select};

/// Immutable bit vector data without auxiliary indexes.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BitVectorData {
    /// Underlying machine words storing bit data.
    pub words: Vec<usize>,
    /// Number of valid bits in `words`.
    pub len: usize,
}

impl BitVectorData {
    /// Creates bit vector data from a bit iterator.
    pub fn from_bits<I: IntoIterator<Item = bool>>(bits: I) -> Self {
        let mut words = Vec::new();
        let mut len = 0usize;
        let mut cur = 0usize;
        let mut shift = 0usize;
        for b in bits {
            if shift == usize::BITS as usize {
                words.push(cur);
                cur = 0;
                shift = 0;
            }
            if b {
                cur |= 1usize << shift;
            }
            shift += 1;
            len += 1;
        }
        if shift != 0 {
            words.push(cur);
        }
        Self { words, len }
    }

    /// Returns the number of bits stored.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns the raw word slice.
    pub fn words(&self) -> &[usize] {
        &self.words
    }

    /// Returns the number of words stored.
    pub fn num_words(&self) -> usize {
        self.words.len()
    }

    /// Returns the number of bytes required for the old copy-based serialization.
    pub fn size_in_bytes(&self) -> usize {
        std::mem::size_of::<usize>() * (self.words.len() + 2)
    }
}

impl From<RawBitVector> for BitVectorData {
    fn from(bv: RawBitVector) -> Self {
        Self {
            words: bv.words().to_vec(),
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
}
