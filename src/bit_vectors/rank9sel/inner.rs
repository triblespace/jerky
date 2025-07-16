//! Internal index structure for [`BitVector<Rank9SelIndex>`](crate::bit_vectors::BitVector).
#![cfg(target_pointer_width = "64")]

use anybytes::{Bytes, View};

use anyhow::Result;

use crate::bit_vectors::data::BitVectorData;
use crate::broadword;

const BLOCK_LEN: usize = 8;
const SELECT_ONES_PER_HINT: usize = 64 * BLOCK_LEN * 2;
const SELECT_ZEROS_PER_HINT: usize = SELECT_ONES_PER_HINT;

/// The index implementation separated from the bit vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rank9SelIndex<const SELECT1: bool = true, const SELECT0: bool = true> {
    len: usize,
    block_rank_pairs: View<[usize]>,
    select1_hints: Option<View<[usize]>>,
    select0_hints: Option<View<[usize]>>,
}

/// Internal builder for [`Rank9SelIndex`].
#[derive(Default, Debug, Clone)]
struct Rank9SelIndexBuilder<const SELECT1: bool, const SELECT0: bool> {
    len: usize,
    block_rank_pairs: Vec<usize>,
    select1_hints: Option<Vec<usize>>,
    select0_hints: Option<Vec<usize>>,
}

impl<const SELECT1: bool, const SELECT0: bool> Rank9SelIndexBuilder<SELECT1, SELECT0> {
    /// Creates a builder from the given bit vector data.
    pub fn new(data: &BitVectorData) -> Self {
        Self::build_rank(data)
    }

    /// Builds an index for faster `select1` queries.
    pub fn select1_hints(self) -> Self {
        self.build_select1()
    }

    /// Builds an index for faster `select0` queries.
    pub fn select0_hints(self) -> Self {
        self.build_select0()
    }

    /// Freezes and returns [`Rank9SelIndex`].
    pub fn build(self) -> Rank9SelIndex<SELECT1, SELECT0> {
        let block_rank_pairs = Bytes::from_source(self.block_rank_pairs)
            .view::<[usize]>()
            .unwrap();
        let select1_hints = self
            .select1_hints
            .map(|v| Bytes::from_source(v).view::<[usize]>().unwrap());
        let select0_hints = self
            .select0_hints
            .map(|v| Bytes::from_source(v).view::<[usize]>().unwrap());
        Rank9SelIndex::<SELECT1, SELECT0> {
            len: self.len,
            block_rank_pairs,
            select1_hints,
            select0_hints,
        }
    }

    fn build_rank(data: &BitVectorData) -> Self {
        let mut next_rank = 0;
        let mut cur_subrank = 0;
        let mut subranks = 0;

        let mut block_rank_pairs = vec![next_rank];

        let words = data.words();
        for (i, &word) in words.iter().enumerate() {
            let word_pop = broadword::popcount(word);

            let shift = i % BLOCK_LEN;
            if shift != 0 {
                subranks <<= 9;
                subranks |= cur_subrank;
            }

            next_rank += word_pop;
            cur_subrank += word_pop;

            if shift == BLOCK_LEN - 1 {
                block_rank_pairs.push(subranks);
                block_rank_pairs.push(next_rank);
                subranks = 0;
                cur_subrank = 0;
            }
        }

        let left = BLOCK_LEN - (data.num_words() % BLOCK_LEN);
        for _ in 0..left {
            subranks <<= 9;
            subranks |= cur_subrank;
        }
        block_rank_pairs.push(subranks);

        if data.num_words() % BLOCK_LEN != 0 {
            block_rank_pairs.push(next_rank);
            block_rank_pairs.push(0);
        }
        block_rank_pairs.shrink_to_fit();

        Self {
            len: data.len(),
            block_rank_pairs,
            select1_hints: None,
            select0_hints: None,
        }
    }

    fn build_select1(mut self) -> Self {
        let mut select1_hints = vec![];
        let mut cur_ones_threshold = SELECT_ONES_PER_HINT;
        for i in 0..self.num_blocks() {
            if self.block_rank(i + 1) > cur_ones_threshold {
                select1_hints.push(i);
                cur_ones_threshold += SELECT_ONES_PER_HINT;
            }
        }
        select1_hints.push(self.num_blocks());
        select1_hints.shrink_to_fit();

        self.select1_hints = Some(select1_hints);
        self
    }

    fn build_select0(mut self) -> Self {
        let mut select0_hints = vec![];
        let mut cur_zeros_threshold = SELECT_ZEROS_PER_HINT;
        for i in 0..self.num_blocks() {
            if self.block_rank0(i + 1) > cur_zeros_threshold {
                select0_hints.push(i);
                cur_zeros_threshold += SELECT_ZEROS_PER_HINT;
            }
        }
        select0_hints.push(self.num_blocks());
        select0_hints.shrink_to_fit();

        self.select0_hints = Some(select0_hints);
        self
    }

    #[inline(always)]
    fn num_blocks(&self) -> usize {
        self.block_rank_pairs.len() / 2 - 1
    }

    #[inline(always)]
    fn block_rank(&self, block: usize) -> usize {
        self.block_rank_pairs[block * 2]
    }

    #[inline(always)]
    fn block_rank0(&self, block: usize) -> usize {
        block * BLOCK_LEN * 64 - self.block_rank(block)
    }
}

impl<const SELECT1: bool, const SELECT0: bool> Rank9SelIndex<SELECT1, SELECT0> {
    /// Creates a new index from the given bit vector data.
    pub fn new(data: &BitVectorData) -> Self {
        let mut builder = Rank9SelIndexBuilder::<SELECT1, SELECT0>::new(data);
        if SELECT1 {
            builder = builder.select1_hints();
        }
        if SELECT0 {
            builder = builder.select0_hints();
        }
        builder.build()
    }

    /// Gets the number of bits set.
    #[inline(always)]
    pub fn num_ones(&self) -> usize {
        self.block_rank_pairs[self.block_rank_pairs.len() - 2]
    }

    /// Gets the number of bits unset.
    #[inline(always)]
    pub fn num_zeros(&self) -> usize {
        self.len - self.num_ones()
    }

    #[inline(always)]
    fn num_blocks(&self) -> usize {
        self.block_rank_pairs.len() / 2 - 1
    }

    #[inline(always)]
    fn block_rank(&self, block: usize) -> usize {
        self.block_rank_pairs[block * 2]
    }

    #[inline(always)]
    fn sub_block_rank(&self, sub_bpos: usize) -> usize {
        let (block, left) = (sub_bpos / BLOCK_LEN, sub_bpos % BLOCK_LEN);
        self.block_rank(block) + ((self.sub_block_ranks(block) >> ((7 - left) * 9)) & 0x1FF)
    }

    #[inline(always)]
    fn sub_block_ranks(&self, block: usize) -> usize {
        self.block_rank_pairs[block * 2 + 1]
    }

    #[inline(always)]
    fn block_rank0(&self, block: usize) -> usize {
        block * BLOCK_LEN * 64 - self.block_rank(block)
    }

    /// Returns the number of ones from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `bv.len() < pos`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Bit vector used in construction.
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Safety
    ///
    /// `bv` must be the one used in construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use jerky::bit_vectors::rank9sel::inner::Rank9SelIndex;
    /// use jerky::bit_vectors::BitVectorData;
    ///
    /// let data = BitVectorData::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndex::<true, true>::new(&data);

    /// assert_eq!(idx.rank1(&data, 1), Some(1));
    /// assert_eq!(idx.rank1(&data, 2), Some(1));
    /// assert_eq!(idx.rank1(&data, 3), Some(1));
    /// assert_eq!(idx.rank1(&data, 4), Some(2));
    /// assert_eq!(idx.rank1(&data, 5), None);
    /// ```
    pub fn rank1(&self, data: &BitVectorData, pos: usize) -> Option<usize> {
        if data.len() < pos {
            return None;
        }
        if pos == data.len() {
            return Some(self.num_ones());
        }
        let (sub_bpos, sub_left) = (pos / 64, pos % 64);
        let mut r = self.sub_block_rank(sub_bpos);
        if sub_left != 0 {
            r += broadword::popcount(data.words()[sub_bpos] << (64 - sub_left));
        }
        Some(r)
    }

    /// Returns the number of zeros from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `bv.len() < pos`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Bit vector used in construction.
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Safety
    ///
    /// `bv` must be the one used in construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use jerky::bit_vectors::rank9sel::inner::Rank9SelIndex;
    /// use jerky::bit_vectors::BitVectorData;
    /// let data = BitVectorData::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndex::<true, true>::new(&data);
    /// assert_eq!(idx.rank0(&data, 2), Some(1));
    /// assert_eq!(idx.rank0(&data, 3), Some(2));
    /// assert_eq!(idx.rank0(&data, 4), Some(2));
    /// assert_eq!(idx.rank0(&data, 5), None);
    /// ```
    pub fn rank0(&self, data: &BitVectorData, pos: usize) -> Option<usize> {
        Some(pos - self.rank1(data, pos)?)
    }

    /// Searches the position of the `k`-th bit set, or
    /// [`None`] if `self.num_ones() <= k`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Bit vector used in construction.
    /// - `k`: Select query.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Safety
    ///
    /// `bv` must be the one used in construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use jerky::bit_vectors::rank9sel::inner::Rank9SelIndex;
    /// use jerky::bit_vectors::BitVectorData;
    /// let data = BitVectorData::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndex::<true, false>::new(&data);
    ///
    /// assert_eq!(idx.select1(&data, 0), Some(0));
    /// assert_eq!(idx.select1(&data, 1), Some(3));
    /// assert_eq!(idx.select1(&data, 2), None);
    /// ```
    pub fn select1(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        if self.num_ones() <= k {
            return None;
        }

        let block = {
            let (mut a, mut b) = (0, self.num_blocks());
            if let Some(select1_hints) = self.select1_hints.as_ref() {
                let chunk = k / SELECT_ONES_PER_HINT;
                if chunk != 0 {
                    a = select1_hints[chunk - 1];
                }
                b = select1_hints[chunk] + 1;
            }
            while b - a > 1 {
                let mid = a + (b - a) / 2;
                let x = self.block_rank(mid);
                if x <= k {
                    a = mid;
                } else {
                    b = mid;
                }
            }
            a
        };

        debug_assert!(block < self.num_blocks());
        let block_offset = block * BLOCK_LEN;
        let mut cur_rank = self.block_rank(block);
        debug_assert!(cur_rank <= k);

        let rank_in_block_parallel = (k - cur_rank) * broadword::ONES_STEP_9;
        let sub_ranks = self.sub_block_ranks(block);
        let sub_block_offset = (broadword::uleq_step_9(sub_ranks, rank_in_block_parallel)
            .wrapping_mul(broadword::ONES_STEP_9)
            >> 54)
            & 0x7;
        cur_rank += (sub_ranks >> (7 - sub_block_offset).wrapping_mul(9)) & 0x1FF;
        debug_assert!(cur_rank <= k);

        let word_offset = block_offset + sub_block_offset;
        let sel = word_offset * 64
            + broadword::select_in_word(data.words()[word_offset], k - cur_rank).unwrap();
        Some(sel)
    }

    /// Searches the position of the `k`-th bit unset, or
    /// [`None`] if `self.num_zeros() <= k`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Bit vector used in construction.
    /// - `k`: Select query.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Safety
    ///
    /// `bv` must be the one used in construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use jerky::bit_vectors::rank9sel::inner::Rank9SelIndex;
    /// use jerky::bit_vectors::BitVectorData;
    /// let data = BitVectorData::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndex::<false, true>::new(&data);
    /// assert_eq!(idx.select0(&data, 0), Some(1));
    /// assert_eq!(idx.select0(&data, 1), Some(2));
    /// assert_eq!(idx.select0(&data, 2), None);
    /// ```
    pub fn select0(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        if self.num_zeros() <= k {
            return None;
        }

        let block = {
            let (mut a, mut b) = (0, self.num_blocks());
            if let Some(select0_hints) = self.select0_hints.as_ref() {
                let chunk = k / SELECT_ZEROS_PER_HINT;
                if chunk != 0 {
                    a = select0_hints[chunk - 1];
                }
                b = select0_hints[chunk] + 1;
            }
            while b - a > 1 {
                let mid = a + (b - a) / 2;
                let x = self.block_rank0(mid);
                if x <= k {
                    a = mid;
                } else {
                    b = mid;
                }
            }
            a
        };

        debug_assert!(block < self.num_blocks());
        let block_offset = block * BLOCK_LEN;
        let mut cur_rank = self.block_rank0(block);
        debug_assert!(cur_rank <= k);

        let rank_in_block_parallel = (k - cur_rank) * broadword::ONES_STEP_9;
        let sub_ranks = 64 * broadword::INV_COUNT_STEP_9 - self.sub_block_ranks(block);
        let sub_block_offset = (broadword::uleq_step_9(sub_ranks, rank_in_block_parallel)
            .wrapping_mul(broadword::ONES_STEP_9)
            >> 54)
            & 0x7;
        cur_rank += (sub_ranks >> (7 - sub_block_offset).wrapping_mul(9)) & 0x1FF;
        debug_assert!(cur_rank <= k);

        let word_offset = block_offset + sub_block_offset;
        let sel = word_offset * 64
            + broadword::select_in_word(!data.words()[word_offset], k - cur_rank).unwrap();
        Some(sel)
    }
}

impl<const SELECT1: bool, const SELECT0: bool> Rank9SelIndex<SELECT1, SELECT0> {
    /// Reconstructs the index from zero-copy [`Bytes`].
    pub fn from_bytes(mut bytes: Bytes) -> Result<Self> {
        let len = *bytes
            .view_prefix::<usize>()
            .map_err(|e| anyhow::anyhow!(e))?;
        let brp_len = *bytes
            .view_prefix::<usize>()
            .map_err(|e| anyhow::anyhow!(e))?;
        let block_rank_pairs = bytes
            .view_prefix_with_elems::<[usize]>(brp_len)
            .map_err(|e| anyhow::anyhow!(e))?;
        let has_select1 = *bytes
            .view_prefix::<usize>()
            .map_err(|e| anyhow::anyhow!(e))?
            != 0;
        let select1_hints = if has_select1 {
            let l = *bytes
                .view_prefix::<usize>()
                .map_err(|e| anyhow::anyhow!(e))?;
            Some(
                bytes
                    .view_prefix_with_elems::<[usize]>(l)
                    .map_err(|e| anyhow::anyhow!(e))?,
            )
        } else {
            None
        };
        let has_select0 = *bytes
            .view_prefix::<usize>()
            .map_err(|e| anyhow::anyhow!(e))?
            != 0;
        let select0_hints = if has_select0 {
            let l = *bytes
                .view_prefix::<usize>()
                .map_err(|e| anyhow::anyhow!(e))?;
            Some(
                bytes
                    .view_prefix_with_elems::<[usize]>(l)
                    .map_err(|e| anyhow::anyhow!(e))?,
            )
        } else {
            None
        };
        if has_select1 != SELECT1 || has_select0 != SELECT0 {
            return Err(anyhow::anyhow!("mismatched hint flags"));
        }
        Ok(Self {
            len,
            block_rank_pairs,
            select1_hints,
            select0_hints,
        })
    }

    /// Serializes the index metadata and data into a [`Bytes`] buffer.
    pub fn to_bytes(&self) -> Bytes {
        let mut store: Vec<usize> = Vec::new();
        store.push(self.len);
        store.push(self.block_rank_pairs.len());
        store.extend_from_slice(self.block_rank_pairs.as_ref());
        if let Some(ref v) = self.select1_hints {
            store.push(1);
            store.push(v.len());
            store.extend_from_slice(v.as_ref());
        } else {
            store.push(0);
        }
        if let Some(ref v) = self.select0_hints {
            store.push(1);
            store.push(v.len());
            store.extend_from_slice(v.as_ref());
        } else {
            store.push(0);
        }
        Bytes::from_source(store)
    }

    /// Returns the number of bytes required for the old copy-based serialization.
    pub fn size_in_bytes(&self) -> usize {
        let mut mem = std::mem::size_of::<usize>() * 2;
        mem += std::mem::size_of::<usize>() * self.block_rank_pairs.len();
        mem += std::mem::size_of::<bool>();
        if let Some(hints) = &self.select1_hints {
            mem += std::mem::size_of::<usize>();
            mem += std::mem::size_of::<usize>() * hints.len();
        }
        mem += std::mem::size_of::<bool>();
        if let Some(hints) = &self.select0_hints {
            mem += std::mem::size_of::<usize>();
            mem += std::mem::size_of::<usize>() * hints.len();
        }
        mem
    }
}

impl<const SELECT1: bool, const SELECT0: bool> crate::bit_vectors::data::BitVectorIndex
    for Rank9SelIndex<SELECT1, SELECT0>
{
    fn build(data: &BitVectorData) -> Self {
        let mut builder = Rank9SelIndexBuilder::<SELECT1, SELECT0>::new(data);
        if SELECT1 {
            builder = builder.select1_hints();
        }
        if SELECT0 {
            builder = builder.select0_hints();
        }
        builder.build()
    }

    fn num_ones(&self, _data: &BitVectorData) -> usize {
        self.num_ones()
    }

    fn rank1(&self, data: &BitVectorData, pos: usize) -> Option<usize> {
        Rank9SelIndex::rank1(self, data, pos)
    }

    fn select1(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        Rank9SelIndex::select1(self, data, k)
    }

    fn select0(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        Rank9SelIndex::select0(self, data, k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_copy_from_to_bytes() {
        let data = BitVectorData::from_bits([false, true, true, false, true]);
        let idx = Rank9SelIndex::<true, true>::new(&data);
        let bytes = idx.to_bytes();
        let other = Rank9SelIndex::<true, true>::from_bytes(bytes).unwrap();
        assert_eq!(idx, other);
    }

    #[test]
    fn test_builder_new_equivalence() {
        let data = BitVectorData::from_bits([true, false, true, false]);
        let idx1 = Rank9SelIndex::<true, true>::new(&data);
        let idx2 = Rank9SelIndex::<true, true>::new(&data);
        assert_eq!(idx1, idx2);
    }
}
