//! Internal index structure of [`Rank9Sel`](super::Rank9Sel).
#![cfg(target_pointer_width = "64")]

use anybytes::{Bytes, View};

use anyhow::Result;

use crate::bit_vectors::BitVector;
use crate::bit_vectors::NumBits;
use crate::broadword;

const BLOCK_LEN: usize = 8;
const SELECT_ONES_PER_HINT: usize = 64 * BLOCK_LEN * 2;
const SELECT_ZEROS_PER_HINT: usize = SELECT_ONES_PER_HINT;

/// The index implementation of [`Rank9Sel`](super::Rank9Sel) separated from the bit vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rank9SelIndex {
    len: usize,
    block_rank_pairs: View<[usize]>,
    select1_hints: Option<View<[usize]>>,
    select0_hints: Option<View<[usize]>>,
}

/// Builder for [`Rank9SelIndex`].
#[derive(Default, Debug, Clone)]
pub struct Rank9SelIndexBuilder<const SELECT1: bool = false, const SELECT0: bool = false> {
    len: usize,
    block_rank_pairs: Vec<usize>,
    select1_hints: Option<Vec<usize>>,
    select0_hints: Option<Vec<usize>>,
    // streaming fields
    next_rank: usize,
    cur_subrank: usize,
    subranks: usize,
    cur_word_pop: usize,
    bits_in_word: usize,
    num_words: usize,
    cur_ones_threshold: usize,
    cur_zeros_threshold: usize,
}

impl Rank9SelIndexBuilder {
    /// Creates a streaming builder without select hints.
    pub fn new() -> Self {
        Rank9SelIndexBuilder::<false, false>::new_stream()
    }

    /// Creates a builder from the given bit vector without select hints.
    pub fn from_bits(bv: &BitVector) -> Self {
        Rank9SelIndexBuilder::<false, false>::new_generic(bv)
    }
}

impl<const SELECT1: bool, const SELECT0: bool> Rank9SelIndexBuilder<SELECT1, SELECT0> {
    /// Creates an empty streaming builder.
    pub fn new_stream() -> Self {
        Self {
            len: 0,
            block_rank_pairs: vec![0],
            select1_hints: if SELECT1 { Some(Vec::new()) } else { None },
            select0_hints: if SELECT0 { Some(Vec::new()) } else { None },
            next_rank: 0,
            cur_subrank: 0,
            subranks: 0,
            cur_word_pop: 0,
            bits_in_word: 0,
            num_words: 0,
            cur_ones_threshold: SELECT_ONES_PER_HINT,
            cur_zeros_threshold: SELECT_ZEROS_PER_HINT,
        }
    }

    /// Creates a builder from the given bit vector.
    pub fn new_generic(bv: &BitVector) -> Self {
        let mut this = Self::new_stream();
        this.extend(bv.iter());
        this
    }

    /// Freezes and returns [`Rank9SelIndex`].
    pub fn build(mut self) -> Rank9SelIndex {
        self.finalize();
        let block_rank_pairs = Bytes::from_source(self.block_rank_pairs)
            .view::<[usize]>()
            .unwrap();
        let select1_hints = self
            .select1_hints
            .map(|v| Bytes::from_source(v).view::<[usize]>().unwrap());
        let select0_hints = self
            .select0_hints
            .map(|v| Bytes::from_source(v).view::<[usize]>().unwrap());
        Rank9SelIndex {
            len: self.len,
            block_rank_pairs,
            select1_hints,
            select0_hints,
        }
    }

    fn build_rank(bv: &BitVector) -> Self {
        let mut this = Self::new_stream();
        this.extend(bv.iter());
        this
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

    /// Pushes a bit for streaming construction.
    pub fn push_bit(&mut self, bit: bool) {
        self.len += 1;
        if bit {
            self.cur_word_pop += 1;
        }
        self.bits_in_word += 1;
        if self.bits_in_word == 64 {
            self.finalize_word();
        }
    }

    /// Extends bits from an iterator.
    pub fn extend<I>(&mut self, bits: I)
    where
        I: IntoIterator<Item = bool>,
    {
        for b in bits {
            self.push_bit(b);
        }
    }

    fn finalize_word(&mut self) {
        let shift = self.num_words % BLOCK_LEN;
        if shift != 0 {
            self.subranks <<= 9;
            self.subranks |= self.cur_subrank;
        }
        self.next_rank += self.cur_word_pop;
        self.cur_subrank += self.cur_word_pop;
        self.num_words += 1;
        if shift == BLOCK_LEN - 1 {
            self.block_rank_pairs.push(self.subranks);
            self.block_rank_pairs.push(self.next_rank);
            self.subranks = 0;
            self.cur_subrank = 0;
            let block_idx = self.num_words / BLOCK_LEN - 1;
            if let Some(ref mut v) = self.select1_hints {
                while self.next_rank > self.cur_ones_threshold {
                    v.push(block_idx);
                    self.cur_ones_threshold += SELECT_ONES_PER_HINT;
                }
            }
            if let Some(ref mut v) = self.select0_hints {
                while self.num_words * 64 - self.next_rank > self.cur_zeros_threshold {
                    v.push(block_idx);
                    self.cur_zeros_threshold += SELECT_ZEROS_PER_HINT;
                }
            }
        }
        self.cur_word_pop = 0;
        self.bits_in_word = 0;
    }

    fn finalize(&mut self) {
        if self.bits_in_word > 0 {
            self.finalize_word();
        }
        let left = BLOCK_LEN - (self.num_words % BLOCK_LEN);
        for _ in 0..left {
            self.subranks <<= 9;
            self.subranks |= self.cur_subrank;
        }
        self.block_rank_pairs.push(self.subranks);
        if self.num_words % BLOCK_LEN != 0 {
            self.block_rank_pairs.push(self.next_rank);
            self.block_rank_pairs.push(0);
        }
        let nb = self.num_blocks();
        if let Some(ref mut v) = self.select1_hints {
            v.push(nb);
        }
        if let Some(ref mut v) = self.select0_hints {
            v.push(nb);
        }
        self.block_rank_pairs.shrink_to_fit();
        if let Some(ref mut v) = self.select1_hints {
            v.shrink_to_fit();
        }
        if let Some(ref mut v) = self.select0_hints {
            v.shrink_to_fit();
        }
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

impl Rank9SelIndex {
    /// Creates a new vector from input bit vector `bv`.
    pub fn new(bv: &BitVector) -> Self {
        Rank9SelIndexBuilder::from_bits(bv).build()
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
    /// use sucds::bit_vectors::{BitVector, rank9sel::inner::{Rank9SelIndex, Rank9SelIndexBuilder}};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndex::new(&bv);
    ///
    /// unsafe {
    ///     assert_eq!(idx.rank1(&bv, 1), Some(1));
    ///     assert_eq!(idx.rank1(&bv, 2), Some(1));
    ///     assert_eq!(idx.rank1(&bv, 3), Some(1));
    ///     assert_eq!(idx.rank1(&bv, 4), Some(2));
    ///     assert_eq!(idx.rank1(&bv, 5), None);
    /// }
    /// ```
    pub unsafe fn rank1(&self, bv: &BitVector, pos: usize) -> Option<usize> {
        if bv.num_bits() < pos {
            return None;
        }
        if pos == bv.num_bits() {
            return Some(self.num_ones());
        }
        let (sub_bpos, sub_left) = (pos / 64, pos % 64);
        let mut r = self.sub_block_rank(sub_bpos);
        if sub_left != 0 {
            r += broadword::popcount(bv.words()[sub_bpos] << (64 - sub_left));
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
    /// use sucds::bit_vectors::{BitVector, rank9sel::inner::{Rank9SelIndex, Rank9SelIndexBuilder}};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndex::new(&bv);
    ///
    /// unsafe {
    ///     assert_eq!(idx.rank0(&bv, 1), Some(0));
    ///     assert_eq!(idx.rank0(&bv, 2), Some(1));
    ///     assert_eq!(idx.rank0(&bv, 3), Some(2));
    ///     assert_eq!(idx.rank0(&bv, 4), Some(2));
    ///     assert_eq!(idx.rank0(&bv, 5), None);
    /// }
    /// ```
    pub unsafe fn rank0(&self, bv: &BitVector, pos: usize) -> Option<usize> {
        Some(pos - self.rank1(bv, pos)?)
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
    /// use sucds::bit_vectors::{BitVector, rank9sel::inner::{Rank9SelIndex, Rank9SelIndexBuilder}};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndexBuilder::<true, false>::new_generic(&bv).build();
    ///
    /// unsafe {
    ///     assert_eq!(idx.select1(&bv, 0), Some(0));
    ///     assert_eq!(idx.select1(&bv, 1), Some(3));
    ///     assert_eq!(idx.select1(&bv, 2), None);
    /// }
    /// ```
    pub unsafe fn select1(&self, bv: &BitVector, k: usize) -> Option<usize> {
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
            + broadword::select_in_word(bv.words()[word_offset], k - cur_rank).unwrap();
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
    /// use sucds::bit_vectors::{BitVector, rank9sel::inner::{Rank9SelIndex, Rank9SelIndexBuilder}};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndexBuilder::<false, true>::new_generic(&bv).build();
    ///
    /// unsafe {
    ///     assert_eq!(idx.select0(&bv, 0), Some(1));
    ///     assert_eq!(idx.select0(&bv, 1), Some(2));
    ///     assert_eq!(idx.select0(&bv, 2), None);
    /// }
    /// ```
    pub unsafe fn select0(&self, bv: &BitVector, k: usize) -> Option<usize> {
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
            + broadword::select_in_word(!bv.words()[word_offset], k - cur_rank).unwrap();
        Some(sel)
    }
}

impl Rank9SelIndex {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_copy_from_to_bytes() {
        let bv = BitVector::from_bits([false, true, true, false, true]);
        let idx = Rank9SelIndexBuilder::<true, true>::new_generic(&bv).build();
        let bytes = idx.to_bytes();
        let other = Rank9SelIndex::from_bytes(bytes).unwrap();
        assert_eq!(idx, other);
    }
}
