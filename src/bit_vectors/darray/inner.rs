//! Internal index structure of [`DArray`](super::DArray).
#![cfg(target_pointer_width = "64")]

use anybytes::{Bytes, View};

use anyhow::Result;

use crate::bit_vectors::BitVector;
use crate::bit_vectors::NumBits;
use crate::broadword;

const BLOCK_LEN: usize = 1024;
const SUBBLOCK_LEN: usize = 32;
const MAX_IN_BLOCK_DISTANCE: usize = 1 << 16;

/// The index implementation of [`DArray`](super::DArray) separated from the bit vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DArrayIndex<const OVER_ONE: bool> {
    block_inventory: View<[isize]>,
    subblock_inventory: View<[u16]>,
    overflow_positions: View<[usize]>,
    num_positions: usize,
}

/// Builder for [`DArrayIndex`].
#[derive(Default, Debug, Clone)]
pub struct DArrayIndexBuilder<const OVER_ONE: bool> {
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

impl<const OVER_ONE: bool> DArrayIndexBuilder<OVER_ONE> {
    /// Creates a builder from the given bit vector.
    pub fn new(bv: &BitVector) -> Self {
        let mut cur_block_positions = vec![];
        let mut block_inventory = vec![];
        let mut subblock_inventory = vec![];
        let mut overflow_positions = vec![];
        let mut num_positions = 0;

        let w = if OVER_ONE {
            DArrayIndex::<OVER_ONE>::get_word_over_one
        } else {
            DArrayIndex::<OVER_ONE>::get_word_over_zero
        };

        for word_idx in 0..bv.num_words() {
            let mut cur_pos = word_idx * 64;
            let mut cur_word = w(bv, word_idx);

            while let Some(l) = broadword::lsb(cur_word) {
                cur_pos += l;
                cur_word >>= l;
                if cur_pos >= bv.num_bits() {
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
    pub fn new(bv: &BitVector) -> Self {
        DArrayIndexBuilder::<OVER_ONE>::new(bv).build()
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
    /// use sucds::bit_vectors::{BitVector, darray::inner::DArrayIndex};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let da = DArrayIndex::<true>::new(&bv);
    ///
    /// unsafe {
    ///     assert_eq!(da.select(&bv, 0), Some(0));
    ///     assert_eq!(da.select(&bv, 1), Some(3));
    ///     assert_eq!(da.select(&bv, 2), None);
    /// }
    /// ```
    ///
    /// You can perform selections over unset bits by specifying
    /// `DArrayIndex::<false>::new(&bv)`.
    ///
    /// ```
    /// use sucds::bit_vectors::{BitVector, darray::inner::DArrayIndex};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let da = DArrayIndex::<false>::new(&bv);
    ///
    /// unsafe {
    ///     assert_eq!(da.select(&bv, 0), Some(1));
    ///     assert_eq!(da.select(&bv, 1), Some(2));
    ///     assert_eq!(da.select(&bv, 2), None);
    /// }
    /// ```
    #[inline(always)]
    pub unsafe fn select(&self, bv: &BitVector, k: usize) -> Option<usize> {
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
            let mut word = w(bv, word_idx) & (usize::MAX << word_shift);

            loop {
                let popcnt = broadword::popcount(word);
                if reminder < popcnt {
                    break;
                }
                reminder -= popcnt;
                word_idx += 1;
                word = w(bv, word_idx);
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

    fn get_word_over_one(bv: &BitVector, word_idx: usize) -> usize {
        bv.words()[word_idx]
    }

    fn get_word_over_zero(bv: &BitVector, word_idx: usize) -> usize {
        !bv.words()[word_idx]
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_zeros_index() {
        let bv = BitVector::from_bit(false, 3);
        let da = DArrayIndex::<true>::new(&bv);
        unsafe {
            assert_eq!(da.select(&bv, 0), None);
        }
    }

    #[test]
    fn test_all_ones_index() {
        let bv = BitVector::from_bit(true, 3);
        let da = DArrayIndex::<false>::new(&bv);
        unsafe {
            assert_eq!(da.select(&bv, 0), None);
        }
    }

    #[test]
    fn test_zero_copy_from_to_bytes() {
        let bv = BitVector::from_bits([true, false, true, false, true]);
        let idx = DArrayIndex::<true>::new(&bv);
        let bytes = idx.to_bytes();
        let other = DArrayIndex::from_bytes(bytes).unwrap();
        assert_eq!(idx, other);
    }

    #[test]
    fn test_builder_roundtrip() {
        let bv = BitVector::from_bits([true, false, true, true, false, false]);
        let builder = DArrayIndexBuilder::<true>::new(&bv);
        let idx = builder.clone().build();
        let bytes = builder.build().to_bytes();
        let from = DArrayIndex::from_bytes(bytes).unwrap();
        assert_eq!(idx, from);
    }
}
