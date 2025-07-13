//! Internal index structure for the dense array bit-vector technique.
#![cfg(target_pointer_width = "64")]

use anybytes::{Bytes, View};

use anyhow::Result;

use crate::bit_vectors::data::BitVectorData;
use crate::bit_vectors::Access;
use crate::broadword;

const BLOCK_LEN: usize = 1024;
const SUBBLOCK_LEN: usize = 32;
const MAX_IN_BLOCK_DISTANCE: usize = 1 << 16;

/// The index implementation separated from the [`BitVector`] data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DArrayIndex<const OVER_ONE: bool> {
    block_inventory: View<[isize]>,
    subblock_inventory: View<[u16]>,
    overflow_positions: View<[usize]>,
    num_positions: usize,
}

/// Builder for [`DArrayIndex`].
#[derive(Default, Debug, Clone)]
struct DArrayIndexBuilder<const OVER_ONE: bool> {
    block_inventory: Vec<isize>,
    subblock_inventory: Vec<u16>,
    overflow_positions: Vec<usize>,
    num_positions: usize,
}

impl<const OVER_ONE: bool> Default for DArrayIndex<OVER_ONE> {
    fn default() -> Self {
        DArrayIndexBuilder::<OVER_ONE>::default().build()
    }
}

/// Index type that supports both `select1` and `select0` by wrapping
/// [`DArrayIndex<true>`] and [`DArrayIndex<false>`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DArrayFullIndex {
    s1: DArrayIndex<true>,
    s0: DArrayIndex<false>,
}

/// Builder for [`DArrayFullIndex`].
#[derive(Default, Debug, Clone)]
struct DArrayFullIndexBuilder {
    s1: DArrayIndexBuilder<true>,
    s0: DArrayIndexBuilder<false>,
}

impl Default for DArrayFullIndex {
    fn default() -> Self {
        DArrayFullIndexBuilder::default().build()
    }
}

impl DArrayFullIndexBuilder {
    /// Creates a builder from the given bit vector data.
    pub fn new(data: &BitVectorData) -> Self {
        Self {
            s1: DArrayIndexBuilder::<true>::from_data(data),
            s0: DArrayIndexBuilder::<false>::from_data(data),
        }
    }

    /// Creates a builder from the given [`BitVectorData`].
    pub fn from_data(data: &BitVectorData) -> Self {
        Self::new(data)
    }

    /// Freezes and returns [`DArrayFullIndex`].
    pub fn build(self) -> DArrayFullIndex {
        DArrayFullIndex {
            s1: self.s1.build(),
            s0: self.s0.build(),
        }
    }
}

impl DArrayFullIndex {
    /// Creates a new [`DArrayFullIndex`] from bit vector data.
    pub fn new(data: &BitVectorData) -> Self {
        DArrayFullIndexBuilder::new(data).build()
    }

    /// Returns the number of integers set to one.
    #[inline(always)]
    pub fn num_ones(&self) -> usize {
        self.s1.num_ones()
    }

    /// Returns the number of bytes required for the old copy-based serialization.
    pub fn size_in_bytes(&self) -> usize {
        self.s1.size_in_bytes() + self.s0.size_in_bytes()
    }
}

impl crate::bit_vectors::data::BitVectorIndex for DArrayFullIndex {
    fn build(data: &BitVectorData) -> Self {
        DArrayFullIndex::new(data)
    }

    fn num_ones(&self, _data: &BitVectorData) -> usize {
        self.num_ones()
    }

    fn rank1(&self, data: &BitVectorData, pos: usize) -> Option<usize> {
        // rank is not supported; fall back to scanning via s1
        crate::bit_vectors::data::BitVectorIndex::rank1(&self.s1, data, pos)
    }

    fn select1(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        crate::bit_vectors::data::BitVectorIndex::select1(&self.s1, data, k)
    }

    fn select0(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        crate::bit_vectors::data::BitVectorIndex::select0(&self.s0, data, k)
    }
}

impl<const OVER_ONE: bool> DArrayIndexBuilder<OVER_ONE> {
    /// Creates a builder from the given bit vector data.
    pub fn new(data: &BitVectorData) -> Self {
        let mut cur_block_positions = vec![];
        let mut block_inventory = vec![];
        let mut subblock_inventory = vec![];
        let mut overflow_positions = vec![];
        let mut num_positions = 0;

        for (word_idx, &word) in data.words().iter().enumerate() {
            let mut cur_pos = word_idx * 64;
            let mut cur_word = if OVER_ONE { word } else { !word };

            while let Some(l) = broadword::lsb(cur_word) {
                cur_pos += l;
                cur_word >>= l;
                if cur_pos >= data.len() {
                    break;
                }

                cur_block_positions.push(cur_pos);
                if cur_block_positions.len() == BLOCK_LEN {
                    DArrayIndex::<OVER_ONE>::flush_cur_block(
                        &mut cur_block_positions,
                        &mut block_inventory,
                        &mut subblock_inventory,
                        &mut overflow_positions,
                    );
                }

                cur_word >>= 1;
                cur_pos += 1;
                num_positions += 1;
            }
        }

        if !cur_block_positions.is_empty() {
            DArrayIndex::<OVER_ONE>::flush_cur_block(
                &mut cur_block_positions,
                &mut block_inventory,
                &mut subblock_inventory,
                &mut overflow_positions,
            );
        }

        block_inventory.shrink_to_fit();
        subblock_inventory.shrink_to_fit();
        overflow_positions.shrink_to_fit();

        Self {
            block_inventory,
            subblock_inventory,
            overflow_positions,
            num_positions,
        }
    }

    /// Creates a builder from the given [`BitVectorData`].
    pub fn from_data(data: &BitVectorData) -> Self {
        Self::new(data)
    }

    /// Freezes and returns [`DArrayIndex`].
    pub fn build(self) -> DArrayIndex<OVER_ONE> {
        let block_inventory = Bytes::from_source(self.block_inventory)
            .view::<[isize]>()
            .unwrap();
        let subblock_inventory = Bytes::from_source(self.subblock_inventory)
            .view::<[u16]>()
            .unwrap();
        let overflow_positions = Bytes::from_source(self.overflow_positions)
            .view::<[usize]>()
            .unwrap();
        DArrayIndex::<OVER_ONE> {
            block_inventory,
            subblock_inventory,
            overflow_positions,
            num_positions: self.num_positions,
        }
    }
}

impl<const OVER_ONE: bool> DArrayIndex<OVER_ONE> {
    /// Creates a new [`DArrayIndex`] from input bit vector `bv`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Input bit vector.
    pub fn new(data: &BitVectorData) -> Self {
        DArrayIndexBuilder::<OVER_ONE>::new(data).build()
    }

    /// Searches the `k`-th iteger.
    ///
    /// # Arguments
    ///
    /// - `bv`: Bit vector used in construction.
    /// - `k`: Select query.
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
    /// use jerky::bit_vectors::{darray::inner::DArrayIndex, BitVectorData};
    ///
    /// let data = BitVectorData::from_bits([true, false, false, true]);
    /// let da = DArrayIndex::<true>::new(&data);
    /// assert_eq!(da.select(&data, 0), Some(0));
    /// assert_eq!(da.select(&data, 1), Some(3));
    /// assert_eq!(da.select(&data, 2), None);
    /// ```
    ///
    /// You can perform selections over unset bits by specifying
    /// `DArrayIndex::<false>::new(&data)`.
    ///
    /// ```
    /// use jerky::bit_vectors::{darray::inner::DArrayIndex, BitVectorData};
    ///
    /// let data = BitVectorData::from_bits([true, false, false, true]);
    /// let da = DArrayIndex::<false>::new(&data);
    /// assert_eq!(da.select(&data, 0), Some(1));
    /// assert_eq!(da.select(&data, 1), Some(2));
    /// assert_eq!(da.select(&data, 2), None);
    /// ```
    #[inline(always)]
    pub fn select(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        if self.num_ones() <= k {
            return None;
        }

        let block = k / BLOCK_LEN;
        let block_pos = self.block_inventory[block];

        if block_pos < 0 {
            let overflow_pos = (-block_pos - 1) as usize;
            return Some(self.overflow_positions[overflow_pos + (k % BLOCK_LEN)]);
        }

        let subblock = k / SUBBLOCK_LEN;
        let mut reminder = k % SUBBLOCK_LEN;
        let start_pos = block_pos as usize + self.subblock_inventory[subblock] as usize;

        let sel = if reminder == 0 {
            start_pos
        } else {
            let w = if OVER_ONE {
                Self::get_word_over_one
            } else {
                Self::get_word_over_zero
            };

            let mut word_idx = start_pos / 64;
            let word_shift = start_pos % 64;
            let mut word = w(data, word_idx) & (usize::MAX << word_shift);

            loop {
                let popcnt = broadword::popcount(word);
                if reminder < popcnt {
                    break;
                }
                reminder -= popcnt;
                word_idx += 1;
                word = w(data, word_idx);
            }

            64 * word_idx + broadword::select_in_word(word, reminder).unwrap()
        };
        Some(sel)
    }

    /// Gets the number of integers.
    #[inline(always)]
    pub const fn num_ones(&self) -> usize {
        self.num_positions
    }

    /// Reconstructs the index from zero-copy [`Bytes`].
    pub fn from_bytes(mut bytes: Bytes) -> Result<Self> {
        let bi_len = *bytes
            .view_prefix::<usize>()
            .map_err(|e| anyhow::anyhow!(e))?;
        let op_len = *bytes
            .view_prefix::<usize>()
            .map_err(|e| anyhow::anyhow!(e))?;
        let si_len = *bytes
            .view_prefix::<usize>()
            .map_err(|e| anyhow::anyhow!(e))?;
        let num_positions = *bytes
            .view_prefix::<usize>()
            .map_err(|e| anyhow::anyhow!(e))?;
        let over_one = *bytes
            .view_prefix::<usize>()
            .map_err(|e| anyhow::anyhow!(e))?
            != 0;
        if over_one != OVER_ONE {
            return Err(anyhow::anyhow!("mismatched OVER_ONE"));
        }

        let block_inventory = bytes
            .view_prefix_with_elems::<[isize]>(bi_len)
            .map_err(|e| anyhow::anyhow!(e))?;
        let overflow_positions = bytes
            .view_prefix_with_elems::<[usize]>(op_len)
            .map_err(|e| anyhow::anyhow!(e))?;
        let subblock_inventory = bytes
            .view_prefix_with_elems::<[u16]>(si_len)
            .map_err(|e| anyhow::anyhow!(e))?;

        Ok(Self {
            block_inventory,
            subblock_inventory,
            overflow_positions,
            num_positions,
        })
    }

    /// Serializes the index metadata and data into a [`Bytes`] buffer.
    pub fn to_bytes(&self) -> Bytes {
        use core::ops::Deref;
        use zerocopy::IntoBytes;

        let mut store: Vec<u8> = Vec::new();
        store.extend_from_slice(&self.block_inventory.len().to_ne_bytes());
        store.extend_from_slice(&self.overflow_positions.len().to_ne_bytes());
        store.extend_from_slice(&self.subblock_inventory.len().to_ne_bytes());
        store.extend_from_slice(&self.num_positions.to_ne_bytes());
        store.extend_from_slice(&(OVER_ONE as usize).to_ne_bytes());
        store.extend_from_slice(IntoBytes::as_bytes(self.block_inventory.deref()));
        store.extend_from_slice(IntoBytes::as_bytes(self.overflow_positions.deref()));
        store.extend_from_slice(IntoBytes::as_bytes(self.subblock_inventory.deref()));
        Bytes::from_source(store)
    }

    fn flush_cur_block(
        cur_block_positions: &mut Vec<usize>,
        block_inventory: &mut Vec<isize>,
        subblock_inventory: &mut Vec<u16>,
        overflow_positions: &mut Vec<usize>,
    ) {
        let &first = cur_block_positions.first().unwrap();
        let &last = cur_block_positions.last().unwrap();
        if last - first < MAX_IN_BLOCK_DISTANCE {
            block_inventory.push(first as isize);
            for i in (0..cur_block_positions.len()).step_by(SUBBLOCK_LEN) {
                subblock_inventory.push((cur_block_positions[i] - first) as u16);
            }
        } else {
            block_inventory.push(-((overflow_positions.len() + 1) as isize));
            for &x in cur_block_positions.iter() {
                overflow_positions.push(x);
            }
            for _ in (0..cur_block_positions.len()).step_by(SUBBLOCK_LEN) {
                subblock_inventory.push(u16::MAX);
            }
        }
        cur_block_positions.clear();
    }

    fn get_word_over_one(data: &BitVectorData, word_idx: usize) -> usize {
        data.words()[word_idx]
    }

    fn get_word_over_zero(data: &BitVectorData, word_idx: usize) -> usize {
        !data.words()[word_idx]
    }
}

impl<const OVER_ONE: bool> DArrayIndex<OVER_ONE> {
    /// Returns the number of bytes required for the old copy-based serialization.
    pub fn size_in_bytes(&self) -> usize {
        std::mem::size_of::<usize>()
            + std::mem::size_of::<isize>() * self.block_inventory.len()
            + std::mem::size_of::<usize>()
            + std::mem::size_of::<u16>() * self.subblock_inventory.len()
            + std::mem::size_of::<usize>()
            + std::mem::size_of::<usize>() * self.overflow_positions.len()
            + std::mem::size_of::<usize>()
            + std::mem::size_of::<bool>()
    }
}

impl<const OVER_ONE: bool> crate::bit_vectors::data::BitVectorIndex for DArrayIndex<OVER_ONE> {
    fn build(data: &BitVectorData) -> Self {
        DArrayIndex::new(data)
    }
    fn num_ones(&self, _data: &BitVectorData) -> usize {
        self.num_ones()
    }

    fn rank1(&self, data: &BitVectorData, pos: usize) -> Option<usize> {
        // DArrayIndex alone does not support rank; fall back to scanning.
        let mut cnt = 0;
        for i in 0..pos {
            if data.access(i).unwrap() == OVER_ONE {
                cnt += 1;
            }
        }
        Some(cnt)
    }

    fn select1(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        if OVER_ONE {
            self.select(data, k)
        } else {
            // select1 on complement requires scanning
            let mut cnt = 0;
            for i in 0..data.len() {
                if data.access(i).unwrap() {
                    if cnt == k {
                        return Some(i);
                    }
                    cnt += 1;
                }
            }
            None
        }
    }

    fn select0(&self, data: &BitVectorData, k: usize) -> Option<usize> {
        if OVER_ONE {
            // complement selection
            let mut cnt = 0;
            for i in 0..data.len() {
                if !data.access(i).unwrap() {
                    if cnt == k {
                        return Some(i);
                    }
                    cnt += 1;
                }
            }
            None
        } else {
            self.select(data, k)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_zeros_index() {
        let data = BitVectorData::from_bits([false, false, false]);
        let da = DArrayIndex::<true>::new(&data);
        assert_eq!(da.select(&data, 0), None);
    }

    #[test]
    fn test_all_ones_index() {
        let data = BitVectorData::from_bits([true, true, true]);
        let da = DArrayIndex::<false>::new(&data);
        assert_eq!(da.select(&data, 0), None);
    }

    #[test]
    fn test_zero_copy_from_to_bytes() {
        let data = BitVectorData::from_bits([true, false, true, false, true]);
        let idx = DArrayIndex::<true>::new(&data);
        let bytes = idx.to_bytes();
        let other = DArrayIndex::from_bytes(bytes).unwrap();
        assert_eq!(idx, other);
    }

    #[test]
    fn test_builder_roundtrip() {
        let data = BitVectorData::from_bits([true, false, true, true, false, false]);
        let idx = DArrayIndex::<true>::new(&data);
        let bytes = idx.to_bytes();
        let from = DArrayIndex::<true>::from_bytes(bytes).unwrap();
        assert_eq!(idx, from);
    }

    #[test]
    fn test_builder_from_data() {
        let data = BitVectorData::from_bits([true, false, false, true]);
        let idx_from_data = DArrayIndex::<true>::new(&data);
        let idx_from_new = DArrayIndex::<true>::new(&data);
        assert_eq!(idx_from_data, idx_from_new);
    }
}
