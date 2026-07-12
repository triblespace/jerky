//! Internal index structure for [`BitVector<Rank9SelIndex>`](crate::bit_vector::BitVector).
#![cfg(target_pointer_width = "64")]

use anybytes::area::{SectionHandle, SectionWriter};
use anybytes::Bytes;
use anybytes::View;

use crate::bit_vector::BitVectorData;
use crate::broadword;
use crate::error::{Error, Result};

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
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::bit_vector::BitVectorData;
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
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::bit_vector::BitVectorData;
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
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::bit_vector::BitVectorData;
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

        let rank_in_block_parallel = (k - cur_rank) as u64 * broadword::ONES_STEP_9;
        let sub_ranks = self.sub_block_ranks(block) as u64;
        let sub_block_offset = ((broadword::uleq_step_9(sub_ranks, rank_in_block_parallel)
            .wrapping_mul(broadword::ONES_STEP_9)
            >> 54)
            & 0x7) as usize;
        cur_rank += ((sub_ranks >> (7 - sub_block_offset).wrapping_mul(9)) & 0x1FF) as usize;
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
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::bit_vector::BitVectorData;
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

        let rank_in_block_parallel = (k - cur_rank) as u64 * broadword::ONES_STEP_9;
        let sub_ranks = 64u64 * broadword::INV_COUNT_STEP_9 - self.sub_block_ranks(block) as u64;
        let sub_block_offset = ((broadword::uleq_step_9(sub_ranks, rank_in_block_parallel)
            .wrapping_mul(broadword::ONES_STEP_9)
            >> 54)
            & 0x7) as usize;
        cur_rank += ((sub_ranks >> (7 - sub_block_offset).wrapping_mul(9)) & 0x1FF) as usize;
        debug_assert!(cur_rank <= k);

        let word_offset = block_offset + sub_block_offset;
        let sel = word_offset * 64
            + broadword::select_in_word(!data.words()[word_offset], k - cur_rank).unwrap();
        Some(sel)
    }
}

impl<const SELECT1: bool, const SELECT0: bool> Rank9SelIndex<SELECT1, SELECT0> {
    fn parse(mut bytes: Bytes, strict_framing: bool) -> Result<Self> {
        let len = *bytes.view_prefix::<usize>()?;
        let brp_len = *bytes.view_prefix::<usize>()?;
        let block_rank_pairs = bytes.view_prefix_with_elems::<[usize]>(brp_len)?;
        let select1_flag = *bytes.view_prefix::<usize>()?;
        if strict_framing && select1_flag > 1 {
            return Err(Error::invalid_metadata("invalid select1 hint flag"));
        }
        let has_select1 = select1_flag != 0;
        let select1_hints = if has_select1 {
            let l = *bytes.view_prefix::<usize>()?;
            Some(bytes.view_prefix_with_elems::<[usize]>(l)?)
        } else {
            None
        };
        let select0_flag = *bytes.view_prefix::<usize>()?;
        if strict_framing && select0_flag > 1 {
            return Err(Error::invalid_metadata("invalid select0 hint flag"));
        }
        let has_select0 = select0_flag != 0;
        let select0_hints = if has_select0 {
            let l = *bytes.view_prefix::<usize>()?;
            Some(bytes.view_prefix_with_elems::<[usize]>(l)?)
        } else {
            None
        };
        if has_select1 != SELECT1 || has_select0 != SELECT0 {
            return Err(Error::MismatchedHintFlags);
        }
        if strict_framing && !bytes.is_empty() {
            return Err(Error::invalid_metadata(
                "trailing bytes after Rank9/select index",
            ));
        }
        Ok(Self {
            len,
            block_rank_pairs,
            select1_hints,
            select0_hints,
        })
    }

    /// Reconstructs an index from its legacy native-`usize` byte format.
    ///
    /// This constructor checks the serialized framing and const-generic hint
    /// flags, but cannot prove that the index was derived from a particular bit
    /// vector. For compatibility with the original parser, any nonzero hint
    /// flag is accepted as enabled and trailing bytes are ignored. Prefer
    /// [`Self::from_bytes_for_data`] when attaching persisted data to a bit
    /// vector; that path requires canonical flags and exact framing.
    pub fn from_bytes(bytes: Bytes) -> Result<Self> {
        Self::parse(bytes, false)
    }

    /// Reconstructs and validates a persisted index for `data`.
    ///
    /// Validation is allocation-free and linear in the bit vector size. Every
    /// rank directory entry and deterministic select hint is checked against
    /// the raw words, including the unused tail bits of the final word. Thus a
    /// successfully attached index has the same query semantics as one rebuilt
    /// with [`Self::new`].
    pub fn from_bytes_for_data(data: &BitVectorData, bytes: Bytes) -> Result<Self> {
        let index = Self::parse(bytes, true)?;
        index.validate_for(data)?;
        Ok(index)
    }

    /// Validates that this index is exactly the index derived from `data`.
    ///
    /// This performs no allocation and does not retain `data`.
    pub fn validate_for(&self, data: &BitVectorData) -> Result<()> {
        if self.len != data.len() {
            return Err(Error::invalid_metadata(format!(
                "Rank9/select length {} does not match bit-vector length {}",
                self.len,
                data.len()
            )));
        }

        Self::validate_data_shape(data)?;

        let num_blocks = (data.num_words() + BLOCK_LEN - 1) / BLOCK_LEN;
        let expected_pairs = num_blocks
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(|| Error::invalid_metadata("Rank9 directory length overflow"))?;
        if self.block_rank_pairs.len() != expected_pairs {
            return Err(Error::invalid_metadata(format!(
                "Rank9 directory has {} words, expected {expected_pairs}",
                self.block_rank_pairs.len()
            )));
        }

        let mut rank = 0usize;
        for (block, words) in data.words().chunks(BLOCK_LEN).enumerate() {
            if self.block_rank_pairs[block * 2] != rank {
                return Err(Error::invalid_metadata(format!(
                    "Rank9 block {block} has an incorrect base rank"
                )));
            }

            let mut subrank = 0usize;
            let mut packed_subranks = 0usize;
            for (word, &bits) in words.iter().enumerate() {
                if word != 0 {
                    packed_subranks <<= 9;
                    packed_subranks |= subrank;
                }
                let count = broadword::popcount(bits);
                rank += count;
                subrank += count;
            }
            for _ in words.len()..BLOCK_LEN {
                packed_subranks <<= 9;
                packed_subranks |= subrank;
            }
            if self.block_rank_pairs[block * 2 + 1] != packed_subranks {
                return Err(Error::invalid_metadata(format!(
                    "Rank9 block {block} has incorrect subranks"
                )));
            }
        }
        if self.block_rank_pairs[num_blocks * 2] != rank
            || self.block_rank_pairs[num_blocks * 2 + 1] != 0
        {
            return Err(Error::invalid_metadata(
                "Rank9 terminal rank pair does not match the bit vector",
            ));
        }

        self.validate_hints(self.select1_hints.as_deref(), true)?;
        self.validate_hints(self.select0_hints.as_deref(), false)?;
        Ok(())
    }

    fn validate_data_shape(data: &BitVectorData) -> Result<()> {
        let expected_words = data
            .len()
            .checked_add(63)
            .ok_or_else(|| Error::invalid_metadata("bit-vector word count overflow"))?
            / 64;
        if data.num_words() != expected_words {
            return Err(Error::invalid_metadata(format!(
                "bit vector stores {} words, expected {expected_words}",
                data.num_words()
            )));
        }
        if let Some(&last) = data.words().last() {
            let tail = data.len() % 64;
            if tail != 0 && last >> tail != 0 {
                return Err(Error::invalid_metadata(
                    "bit vector has set bits beyond its declared length",
                ));
            }
        }
        Ok(())
    }

    fn validate_hints(&self, hints: Option<&[usize]>, ones: bool) -> Result<()> {
        let enabled = if ones { SELECT1 } else { SELECT0 };
        if hints.is_some() != enabled {
            return Err(Error::MismatchedHintFlags);
        }
        let hints = match hints {
            Some(hints) => hints,
            None => return Ok(()),
        };

        let per_hint = if ones {
            SELECT_ONES_PER_HINT
        } else {
            SELECT_ZEROS_PER_HINT
        };
        let mut threshold = per_hint;
        let mut actual = hints.iter().copied();
        for block in 0..self.num_blocks() {
            let rank = if ones {
                self.block_rank(block + 1)
            } else {
                self.block_rank0(block + 1)
            };
            if rank > threshold {
                if actual.next() != Some(block) {
                    return Err(Error::invalid_metadata(if ones {
                        "select1 hints do not match the rank directory"
                    } else {
                        "select0 hints do not match the rank directory"
                    }));
                }
                threshold += per_hint;
            }
        }
        if actual.next() != Some(self.num_blocks()) || actual.next().is_some() {
            return Err(Error::invalid_metadata(if ones {
                "select1 hints have an incorrect terminal entry"
            } else {
                "select0 hints have an incorrect terminal entry"
            }));
        }
        Ok(())
    }

    fn serialized_words(&self) -> Result<usize> {
        let mut words = 2usize
            .checked_add(self.block_rank_pairs.len())
            .ok_or_else(|| Error::invalid_metadata("Rank9 index size overflow"))?;
        for hints in [&self.select1_hints, &self.select0_hints] {
            words = words
                .checked_add(1)
                .and_then(|n| match hints {
                    Some(hints) => n.checked_add(1)?.checked_add(hints.len()),
                    None => Some(n),
                })
                .ok_or_else(|| Error::invalid_metadata("Rank9 index size overflow"))?;
        }
        Ok(words)
    }

    /// Persists the existing native-`usize` byte format directly into a new
    /// arena section.
    ///
    /// The returned handle identifies the complete serialized index. No
    /// second index-sized buffer is allocated while writing.
    pub fn persist(&self, writer: &mut SectionWriter<'_>) -> Result<SectionHandle<usize>> {
        let mut section = writer.reserve::<usize>(self.serialized_words()?)?;
        let out = section.as_mut_slice();
        let mut pos = 0usize;
        out[pos] = self.len;
        pos += 1;
        out[pos] = self.block_rank_pairs.len();
        pos += 1;
        out[pos..pos + self.block_rank_pairs.len()].copy_from_slice(self.block_rank_pairs.as_ref());
        pos += self.block_rank_pairs.len();

        for hints in [&self.select1_hints, &self.select0_hints] {
            match hints {
                Some(hints) => {
                    out[pos] = 1;
                    out[pos + 1] = hints.len();
                    pos += 2;
                    out[pos..pos + hints.len()].copy_from_slice(hints.as_ref());
                    pos += hints.len();
                }
                None => {
                    out[pos] = 0;
                    pos += 1;
                }
            }
        }
        debug_assert_eq!(pos, out.len());
        let handle = section.handle();
        section.freeze()?;
        Ok(handle)
    }

    /// Builds an index for `data` and persists it without a second
    /// index-sized serialization allocation.
    pub fn build_and_persist(
        data: &BitVectorData,
        writer: &mut SectionWriter<'_>,
    ) -> Result<(Self, SectionHandle<usize>)> {
        Self::validate_data_shape(data)?;
        let index = Self::new(data);
        let handle = index.persist(writer)?;
        Ok((index, handle))
    }
}

impl<const SELECT1: bool, const SELECT0: bool> crate::bit_vector::BitVectorIndex
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
    use crate::bit_vector::{Access, Rank, Select};
    use anybytes::ByteArea;

    fn serialized_words<const SELECT1: bool, const SELECT0: bool>(
        index: &Rank9SelIndex<SELECT1, SELECT0>,
    ) -> Vec<usize> {
        let mut words = vec![index.len, index.block_rank_pairs.len()];
        words.extend_from_slice(index.block_rank_pairs.as_ref());
        for hints in [&index.select1_hints, &index.select0_hints] {
            match hints {
                Some(hints) => {
                    words.push(1);
                    words.push(hints.len());
                    words.extend_from_slice(hints.as_ref());
                }
                None => words.push(0),
            }
        }
        words
    }

    fn persisted_bytes<const SELECT1: bool, const SELECT0: bool>(
        index: &Rank9SelIndex<SELECT1, SELECT0>,
    ) -> Bytes {
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        let handle = index.persist(&mut writer).unwrap();
        let bytes = area.freeze().unwrap();
        handle.bytes(&bytes)
    }

    #[test]
    fn test_builder_new_equivalence() {
        let data = BitVectorData::from_bits([true, false, true, false]);
        let idx1 = Rank9SelIndex::<true, true>::new(&data);
        let idx2 = Rank9SelIndex::<true, true>::new(&data);
        assert_eq!(idx1, idx2);
    }

    #[test]
    fn persisted_format_matches_legacy_encoding() {
        let data = BitVectorData::from_bits((0..4097).map(|i| i % 3 == 0 || i % 11 == 0));
        let index = Rank9SelIndex::<true, true>::new(&data);
        let persisted = persisted_bytes(&index);
        let expected = Bytes::from_source(serialized_words(&index));
        assert_eq!(persisted.as_ref(), expected.as_ref());

        let attached = Rank9SelIndex::<true, true>::from_bytes_for_data(&data, persisted).unwrap();
        assert_eq!(attached, index);
    }

    #[test]
    fn build_and_persist_roundtrips_without_rebuild_on_attach() {
        let data = BitVectorData::from_bits((0..1777).map(|i| (i * 17) % 29 < 13));
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        let (built, handle) =
            Rank9SelIndex::<true, false>::build_and_persist(&data, &mut writer).unwrap();
        let bytes = area.freeze().unwrap();
        let attached =
            Rank9SelIndex::<true, false>::from_bytes_for_data(&data, handle.bytes(&bytes)).unwrap();
        assert_eq!(attached, built);
    }

    fn assert_boundary_roundtrip<const SELECT1: bool, const SELECT0: bool>(bits: &[bool]) {
        let data = BitVectorData::from_bits(bits.iter().copied());
        let index = Rank9SelIndex::<SELECT1, SELECT0>::new(&data);
        let attached =
            Rank9SelIndex::<SELECT1, SELECT0>::from_bytes_for_data(&data, persisted_bytes(&index))
                .unwrap();
        assert_eq!(attached, index);
    }

    #[test]
    fn all_hint_modes_roundtrip_at_word_and_block_boundaries() {
        for &len in &[0usize, 63, 64, 65, 511, 512, 513, 1023, 1024, 1025] {
            let bits: Vec<bool> = (0..len).map(|i| i % 5 == 0 || i % 7 == 3).collect();
            assert_boundary_roundtrip::<true, true>(&bits);
            assert_boundary_roundtrip::<true, false>(&bits);
            assert_boundary_roundtrip::<false, true>(&bits);
            assert_boundary_roundtrip::<false, false>(&bits);
        }
    }

    #[test]
    fn legacy_parser_remains_permissive_but_checked_attach_is_strict() {
        let data = BitVectorData::from_bits((0..1500).map(|i| i % 5 == 0));
        let index = Rank9SelIndex::<true, true>::new(&data);
        let mut words = serialized_words(&index);
        let select1_flag = 2 + words[1];
        words[select1_flag] = 2;
        words.push(0x0BAD_51DE);

        assert_eq!(
            Rank9SelIndex::<true, true>::from_bytes(Bytes::from_source(words.clone())).unwrap(),
            index
        );
        assert!(
            Rank9SelIndex::<true, true>::from_bytes_for_data(&data, Bytes::from_source(words),)
                .is_err()
        );
    }

    #[test]
    fn exhaustive_small_persisted_rank_select_parity() {
        for len in 0..=12 {
            for pattern in 0usize..(1usize << len) {
                let bits: Vec<bool> = (0..len).map(|bit| (pattern >> bit) & 1 != 0).collect();
                let data = BitVectorData::from_bits(bits.iter().copied());
                let index = Rank9SelIndex::<true, true>::new(&data);
                let attached = Rank9SelIndex::<true, true>::from_bytes_for_data(
                    &data,
                    Bytes::from_source(serialized_words(&index)),
                )
                .unwrap();
                let vector = crate::bit_vector::BitVector::new(data, attached);

                for pos in 0..=len {
                    let ones = bits[..pos].iter().filter(|&&bit| bit).count();
                    assert_eq!(vector.rank1(pos), Some(ones));
                    assert_eq!(vector.rank0(pos), Some(pos - ones));
                }
                let ones: Vec<usize> = bits
                    .iter()
                    .enumerate()
                    .filter_map(|(pos, &bit)| if bit { Some(pos) } else { None })
                    .collect();
                let zeros: Vec<usize> = bits
                    .iter()
                    .enumerate()
                    .filter_map(|(pos, &bit)| if bit { None } else { Some(pos) })
                    .collect();
                for k in 0..=ones.len() {
                    assert_eq!(vector.select1(k), ones.get(k).copied());
                }
                for k in 0..=zeros.len() {
                    assert_eq!(vector.select0(k), zeros.get(k).copied());
                }
                for (pos, &bit) in bits.iter().enumerate() {
                    assert_eq!(vector.access(pos), Some(bit));
                }
            }
        }
    }

    #[test]
    fn strict_attach_rejects_malformed_or_incompatible_sidecars() {
        let bits: Vec<bool> = (0..4096).map(|i| i % 3 == 0).collect();
        let data = BitVectorData::from_bits(bits.iter().copied());
        let index = Rank9SelIndex::<true, true>::new(&data);
        let original = serialized_words(&index);
        let brp_len = original[1];

        let rejects = |words: Vec<usize>| {
            Rank9SelIndex::<true, true>::from_bytes_for_data(&data, Bytes::from_source(words))
                .is_err()
        };

        let mut wrong_len = original.clone();
        wrong_len[0] += 1;
        assert!(rejects(wrong_len));

        let mut wrong_rank = original.clone();
        wrong_rank[2 + brp_len - 2] ^= 1;
        assert!(rejects(wrong_rank));

        let mut wrong_subranks = original.clone();
        wrong_subranks[3] ^= 1;
        assert!(rejects(wrong_subranks));

        let select1_flag = 2 + brp_len;
        let mut invalid_flag = original.clone();
        invalid_flag[select1_flag] = 2;
        assert!(rejects(invalid_flag));

        let select1_len = original[select1_flag + 1];
        let select0_flag = select1_flag + 2 + select1_len;
        let select0_len = original[select0_flag + 1];
        assert!(select1_len > 1);
        assert!(select0_len > 1);

        let mut wrong_select1 = original.clone();
        wrong_select1[select1_flag + 2] ^= 1;
        assert!(rejects(wrong_select1));

        let mut wrong_select0 = original.clone();
        wrong_select0[select0_flag + 2] ^= 1;
        assert!(rejects(wrong_select0));

        let mut trailing = original.clone();
        trailing.push(0);
        assert!(rejects(trailing));

        let mut truncated = original.clone();
        truncated.pop();
        assert!(rejects(truncated));

        let unrelated = BitVectorData::from_bits(bits.iter().map(|bit| !bit));
        assert!(Rank9SelIndex::<true, true>::from_bytes_for_data(
            &unrelated,
            Bytes::from_source(original),
        )
        .is_err());
    }

    #[test]
    fn strict_attach_rejects_set_tail_bits() {
        let clean = BitVectorData::from_bits([true]);
        let bytes = persisted_bytes(&Rank9SelIndex::<true, true>::new(&clean));
        let dirty = BitVectorData {
            words: Bytes::from_source(vec![3u64]).view::<[u64]>().unwrap(),
            len: 1,
            handle: None,
        };
        assert!(Rank9SelIndex::<true, true>::from_bytes_for_data(&dirty, bytes).is_err());
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        assert!(Rank9SelIndex::<true, true>::build_and_persist(&dirty, &mut writer).is_err());

        let surplus = BitVectorData {
            words: Bytes::from_source(vec![1u64, 0]).view::<[u64]>().unwrap(),
            len: 1,
            handle: None,
        };
        let surplus_index = Rank9SelIndex::<true, true>::new(&surplus);
        assert!(Rank9SelIndex::<true, true>::from_bytes_for_data(
            &surplus,
            persisted_bytes(&surplus_index),
        )
        .is_err());
        assert!(Rank9SelIndex::<true, true>::build_and_persist(&surplus, &mut writer).is_err());
    }
}
