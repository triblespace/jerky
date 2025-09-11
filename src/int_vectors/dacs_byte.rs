//! Compressed integer sequence using Directly Addressable Codes (DACs) in a simple bytewise scheme.
#![cfg(target_pointer_width = "64")]

use std::convert::TryFrom;

use anyhow::{anyhow, Result};
use num_traits::ToPrimitive;

use crate::bit_vector::{self, BitVector, BitVectorBuilder, BitVectorIndex, Rank, Rank9SelIndex};
use crate::int_vectors::{Access, Build, NumVals};
use crate::serialization::Serializable;
use crate::utils;
use anybytes::{area::SectionHandle, ByteArea, Bytes, SectionWriter, View};
use zerocopy::{FromBytes, Immutable, KnownLayout};

const LEVEL_WIDTH: usize = 8;
const LEVEL_MASK: usize = (1 << LEVEL_WIDTH) - 1;
/// Maximum possible number of levels for a [`usize`] value.
const MAX_LEVELS: usize = (usize::BITS as usize + LEVEL_WIDTH - 1) / LEVEL_WIDTH;

/// Compressed integer sequence using Directly Addressable Codes (DACs) in a simple bytewise scheme.
///
/// DACs are a compact representation of an integer sequence consisting of many small values.
/// [`DacsByte`] stores each level as a zero-copy [`View<[u8]>`] to avoid extra copying.
/// The generic parameter `I` chooses the [`BitVectorIndex`](crate::bit_vector::BitVectorIndex)
/// used for the internal flag vectors. It defaults to [`Rank9SelIndex`], so most
/// code can omit the parameter.
///
/// # Memory complexity
///
/// $`\textrm{DAC}(A) + o(\textrm{DAC}(A)/b) + O(\lg u)`$ bits where
///
/// - $`u`$ is the maximum value plus 1,
/// - $`b`$ is the length in bits assigned for each level with DACs (here $`b = 8`$), and
/// - $`\textrm{DAC}(A)`$ is the length in bits of the encoded sequence from an original sequence $`A`$ with DACs.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use anybytes::ByteArea;
/// use jerky::int_vectors::{Access, DacsByte};
/// use jerky::bit_vector::rank9sel::Rank9SelIndex;
/// let mut area = ByteArea::new()?;
/// let mut writer = area.sections();
/// let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 0, 100000, 334], &mut writer)?;
/// let meta = seq.metadata();
/// let bytes = area.freeze()?; // finalize arena
/// let other = DacsByte::<Rank9SelIndex>::from_bytes(meta, bytes.clone())?;
/// assert_eq!(seq, other);
/// assert_eq!(other.access(2), Some(100000));
///
/// assert_eq!(other.len(), 4);
/// assert_eq!(other.num_levels(), 3);
/// # Ok(())
/// # }
/// ```
///
/// # References
///
/// - N. R. Brisaboa, S. Ladra, and G. Navarro, "DACs: Bringing direct access to variable-length
///   codes." Information Processing & Management, 49(1), 392-404, 2013.
#[derive(Clone)]
pub struct DacsByte<I = Rank9SelIndex> {
    data: Vec<View<[u8]>>,
    flags: Vec<BitVector<I>>,
    handles: SectionHandle<LevelMeta>,
}

impl<I: PartialEq> PartialEq for DacsByte<I> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
            && self.flags == other.flags
            && self.handles.offset == other.handles.offset
            && self.handles.len == other.handles.len
    }
}

impl<I: Eq> Eq for DacsByte<I> {}

/// Per-level metadata storing handles for payload bytes and flag bit vectors.
#[derive(Debug, Clone, Copy, FromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct LevelMeta {
    /// Handle to the level's payload bytes.
    pub level: SectionHandle<u8>,
    /// Handle to the flag bit vector words (empty for last level).
    pub flag: SectionHandle<u64>,
    /// Number of bits stored in the flag bit vector.
    pub flag_bits: usize,
}

/// Metadata required to reconstruct a `DacsByte` from bytes.
#[derive(Debug, Clone, Copy, FromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct DacsByteMeta {
    /// Number of valid levels stored.
    pub num_levels: usize,
    /// Handle to a slice of per-level [`LevelMeta`] structures.
    pub levels: SectionHandle<LevelMeta>,
}

impl<I: BitVectorIndex> DacsByte<I> {
    /// Builds DACs by assigning 8 bits to represent each level.
    ///
    /// # Arguments
    ///
    /// - `vals`: Slice of integers to be stored.
    /// - `writer`: Memory allocator used for all internal buffers.
    ///
    /// # Errors
    ///
    /// An error is returned if `vals` contains an integer that cannot be cast to [`usize`].
    pub fn from_slice<'a, T>(vals: &[T], writer: &mut SectionWriter<'a>) -> Result<Self>
    where
        T: ToPrimitive,
    {
        if vals.is_empty() {
            let data_sec = writer.reserve::<u8>(0)?;
            let data_handle = data_sec.handle();
            let flag_sec = writer.reserve::<u64>(0)?;
            let flag_handle = flag_sec.handle();
            let mut infos = writer.reserve::<LevelMeta>(1)?;
            infos[0] = LevelMeta {
                level: data_handle,
                flag: flag_handle,
                flag_bits: 0,
            };
            let handles = infos.handle();
            infos.freeze()?;
            flag_sec.freeze()?;
            data_sec.freeze()?;
            return Ok(Self {
                data: vec![Bytes::empty().view::<[u8]>().unwrap()],
                flags: vec![],
                handles,
            });
        }

        // Determine the number of levels by scanning for the maximum value.
        let mut maxv = 0;
        for x in vals {
            maxv =
                maxv.max(x.to_usize().ok_or_else(|| {
                    anyhow!("vals must consist only of values castable into usize.")
                })?);
        }
        let num_bits = utils::needed_bits(maxv);
        let num_levels = utils::ceiled_divide(num_bits, LEVEL_WIDTH);
        assert_ne!(num_levels, 0);

        // Single-level case: just reserve the bytes and return.
        if num_levels == 1 {
            let mut section = writer.reserve::<u8>(vals.len())?;
            let slice = section.as_mut_slice();
            for (i, x) in vals.iter().enumerate() {
                slice[i] = u8::try_from(x.to_usize().unwrap()).unwrap();
            }
            let level_handle = section.handle();
            let flag_sec = writer.reserve::<u64>(0)?;
            let flag_handle = flag_sec.handle();
            let mut infos = writer.reserve::<LevelMeta>(1)?;
            infos[0] = LevelMeta {
                level: level_handle,
                flag: flag_handle,
                flag_bits: 0,
            };
            let handles = infos.handle();
            infos.freeze()?;
            flag_sec.freeze()?;
            let data = section.freeze()?.view::<[u8]>()?;
            return Ok(Self {
                data: vec![data],
                flags: vec![],
                handles,
            });
        }

        // First pass: count flags per level and determine payload lengths.
        let mut flag_counts = vec![0usize; num_levels - 1];
        let mut level_lens = vec![0usize; num_levels];
        for val in vals {
            let mut x = val
                .to_usize()
                .ok_or_else(|| anyhow!("vals must consist only of values castable into usize."))?;
            let mut j = 0;
            loop {
                level_lens[j] += 1;
                if j == num_levels - 1 {
                    break;
                }
                x >>= LEVEL_WIDTH;
                flag_counts[j] += 1;
                if x == 0 {
                    break;
                }
                j += 1;
            }
        }
        // Allocate metadata table, level sections, flag builders, and a dummy flag handle.
        let mut infos = writer.reserve::<LevelMeta>(num_levels)?;
        let mut flags: Vec<BitVectorBuilder> = flag_counts
            .iter()
            .map(|&c| BitVectorBuilder::with_capacity(c, writer))
            .collect::<Result<_, _>>()?;
        let dummy_flag_sec = writer.reserve::<u64>(0)?;
        let dummy_flag_handle = dummy_flag_sec.handle();
        let mut levels: Vec<_> = level_lens
            .iter()
            .map(|&len| writer.reserve::<u8>(len))
            .collect::<Result<_, _>>()?;
        for j in 0..num_levels {
            let mut meta = LevelMeta {
                level: levels[j].handle(),
                flag: dummy_flag_handle,
                flag_bits: 0,
            };
            if j + 1 < num_levels {
                meta.flag = flags[j].handle();
                meta.flag_bits = flag_counts[j];
            }
            infos[j] = meta;
        }
        dummy_flag_sec.freeze()?;

        // Offsets for writing into levels and flags.
        let mut level_offs = vec![0usize; num_levels];
        let mut flag_offs = vec![0usize; num_levels - 1];

        // Second pass: populate levels and flags in place.
        for val in vals {
            let mut x = val.to_usize().unwrap();
            for j in 0..num_levels {
                levels[j].as_mut_slice()[level_offs[j]] = u8::try_from(x & LEVEL_MASK).unwrap();
                level_offs[j] += 1;
                x >>= LEVEL_WIDTH;
                if j == num_levels - 1 {
                    assert_eq!(x, 0);
                    break;
                } else if x == 0 {
                    flags[j].set_bit(flag_offs[j], false)?;
                    flag_offs[j] += 1;
                    break;
                } else {
                    flags[j].set_bit(flag_offs[j], true)?;
                    flag_offs[j] += 1;
                }
            }
        }

        // Freeze level sections, flag builders, and metadata table.
        let data = levels
            .into_iter()
            .map(|sec| sec.freeze()?.view::<[u8]>().map_err(|e| anyhow!(e)))
            .collect::<Result<Vec<_>>>()?;
        let flags = flags.into_iter().map(|bvb| bvb.freeze::<I>()).collect();
        let handles = infos.handle();
        infos.freeze()?;

        Ok(Self {
            data,
            flags,
            handles,
        })
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use anybytes::ByteArea;
    /// use jerky::bit_vector::rank9sel::Rank9SelIndex;
    /// use jerky::int_vectors::DacsByte;
    ///
    /// let mut area = ByteArea::new()?;
    /// let mut writer = area.sections();
    /// let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 0, 100000, 334], &mut writer)?;
    /// area.freeze()?;
    /// let mut it = seq.iter();
    ///
    /// assert_eq!(it.next(), Some(5));
    /// assert_eq!(it.next(), Some(0));
    /// assert_eq!(it.next(), Some(100000));
    /// assert_eq!(it.next(), Some(334));
    /// assert_eq!(it.next(), None);
    /// # Ok(())
    /// # }
    /// ```
    pub const fn iter(&'_ self) -> Iter<'_, I> {
        Iter::new(self)
    }

    /// Collects all integers into a `Vec<usize>` for inspection.
    pub fn to_vec(&self) -> Vec<usize> {
        self.iter().collect()
    }

    /// Gets the number of integers.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.data.first().map_or(0, |lvl| lvl.len())
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the number of levels.
    #[inline(always)]
    pub fn num_levels(&self) -> usize {
        self.data.len()
    }

    /// Gets the number of bits for each level.
    #[inline(always)]
    pub fn widths(&self) -> Vec<usize> {
        self.data.iter().map(|_| LEVEL_WIDTH).collect()
    }

    /// Returns metadata describing this sequence.
    pub fn metadata(&self) -> DacsByteMeta {
        <Self as Serializable>::metadata(self)
    }

    /// Reconstructs the sequence from zero-copy [`Bytes`].
    pub fn from_bytes(meta: DacsByteMeta, bytes: Bytes) -> Result<Self> {
        <Self as Serializable>::from_bytes(meta, bytes)
    }
}

impl<I: BitVectorIndex> Serializable for DacsByte<I> {
    type Meta = DacsByteMeta;

    fn metadata(&self) -> Self::Meta {
        DacsByteMeta {
            num_levels: self.data.len(),
            levels: self.handles,
        }
    }

    fn from_bytes(meta: Self::Meta, bytes: Bytes) -> Result<Self> {
        if meta.num_levels == 0 || meta.num_levels > MAX_LEVELS {
            return Err(anyhow!("invalid metadata"));
        }

        let infos = meta.levels.view(&bytes).map_err(anyhow::Error::from)?;
        if infos.as_ref().len() != meta.num_levels {
            return Err(anyhow!("invalid metadata"));
        }

        let mut flags = Vec::with_capacity(meta.num_levels.saturating_sub(1));
        let mut data = Vec::with_capacity(meta.num_levels);
        for (idx, info) in infos.as_ref().iter().enumerate() {
            if idx + 1 < meta.num_levels {
                let bv_data = bit_vector::BitVectorData::from_bytes(
                    bit_vector::BitVectorDataMeta {
                        len: info.flag_bits,
                        handle: info.flag,
                    },
                    bytes.clone(),
                )?;
                let index = I::build(&bv_data);
                flags.push(bit_vector::BitVector::new(bv_data, index));
            }
            let lvl_view = info.level.view(&bytes).map_err(anyhow::Error::from)?;
            data.push(lvl_view);
        }

        Ok(Self {
            data,
            flags,
            handles: meta.levels,
        })
    }
}

impl<I: BitVectorIndex> Default for DacsByte<I> {
    fn default() -> Self {
        let mut area = ByteArea::new().expect("byte area");
        let mut writer = area.sections();
        let data_sec = writer.reserve::<u8>(0).expect("reserve section");
        let data_handle = data_sec.handle();
        let flag_sec = writer.reserve::<u64>(0).expect("reserve flag");
        let flag_handle = flag_sec.handle();
        let mut infos = writer.reserve::<LevelMeta>(1).expect("reserve level meta");
        infos[0] = LevelMeta {
            level: data_handle,
            flag: flag_handle,
            flag_bits: 0,
        };
        let handles = infos.handle();
        infos.freeze().expect("freeze level meta");
        flag_sec.freeze().expect("freeze flag");
        data_sec.freeze().expect("freeze section");
        Self {
            data: vec![Bytes::empty().view::<[u8]>().unwrap()],
            flags: vec![],
            handles,
        }
    }
}

impl<I: BitVectorIndex> Build for DacsByte<I> {
    /// Creates a new vector from a slice of integers `vals`.
    ///
    /// This just calls [`Self::from_slice()`]. See the documentation.
    fn build_from_slice<T>(vals: &[T]) -> Result<Self>
    where
        T: ToPrimitive,
        Self: Sized,
    {
        let mut area = ByteArea::new()?;
        let mut writer = area.sections();
        let seq = Self::from_slice(vals, &mut writer)?;
        // Ensure the area is sealed so the bytes become immutable.
        area.freeze()?;
        Ok(seq)
    }
}

impl<I: BitVectorIndex> NumVals for DacsByte<I> {
    /// Returns the number of integers stored (just wrapping [`Self::len()`]).
    fn num_vals(&self) -> usize {
        self.len()
    }
}

impl<I: BitVectorIndex> Access for DacsByte<I> {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// $`O( \ell_{pos} )`$ where $`\ell_{pos}`$ is the number of levels corresponding to
    /// the `pos`-th integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use anybytes::ByteArea;
    /// use jerky::bit_vector::rank9sel::Rank9SelIndex;
    /// use jerky::int_vectors::{DacsByte, Access};
    ///
    /// let mut area = ByteArea::new()?;
    /// let mut writer = area.sections();
    /// let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 999, 334], &mut writer)?;
    /// area.freeze()?;
    ///
    /// assert_eq!(seq.access(0), Some(5));
    /// assert_eq!(seq.access(1), Some(999));
    /// assert_eq!(seq.access(2), Some(334));
    /// assert_eq!(seq.access(3), None);
    /// # Ok(())
    /// # }
    /// ```
    fn access(&self, mut pos: usize) -> Option<usize> {
        if self.len() <= pos {
            return None;
        }
        let mut x = 0;
        for j in 0..self.num_levels() {
            x |= usize::from(self.data[j][pos]) << (j * LEVEL_WIDTH);
            if j == self.num_levels() - 1
                || !bit_vector::Access::access(&self.flags[j], pos).unwrap()
            {
                break;
            }
            pos = self.flags[j].rank1(pos).unwrap();
        }
        Some(x)
    }
}

/// Iterator for enumerating integers, created by [`DacsByte::iter()`].
pub struct Iter<'a, I> {
    seq: &'a DacsByte<I>,
    pos: usize,
}

impl<'a, I> Iter<'a, I> {
    /// Creates a new iterator.
    pub const fn new(seq: &'a DacsByte<I>) -> Self {
        Self { seq, pos: 0 }
    }
}

impl<I: BitVectorIndex> std::fmt::Debug for DacsByte<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DacsByte")
            .field("ints", &self.to_vec())
            .field("len", &self.len())
            .field("num_levels", &self.num_levels())
            .finish()
    }
}

impl<I: BitVectorIndex> Iterator for Iter<'_, I> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.seq.len() {
            let x = self.seq.access(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.seq.len(), Some(self.seq.len()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anybytes::{ByteArea, Bytes};

    #[test]
    fn test_basic() {
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        let seq =
            DacsByte::<Rank9SelIndex>::from_slice(&[0xFFFF, 0xFF, 0xF, 0xFFFFF, 0xF], &mut writer)
                .unwrap();
        area.freeze().unwrap();

        let expected = vec![
            Bytes::from_source(vec![0xFFu8, 0xFF, 0xF, 0xFF, 0xF])
                .view::<[u8]>()
                .unwrap(),
            Bytes::from_source(vec![0xFFu8, 0xFF])
                .view::<[u8]>()
                .unwrap(),
            Bytes::from_source(vec![0xFu8]).view::<[u8]>().unwrap(),
        ];
        assert_eq!(seq.data, expected);

        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut b = BitVectorBuilder::with_capacity(5, &mut sections).unwrap();
        b.set_bit(0, true).unwrap();
        b.set_bit(3, true).unwrap();
        let f0 = b.freeze::<Rank9SelIndex<true, true>>();
        let mut b = BitVectorBuilder::with_capacity(2, &mut sections).unwrap();
        b.set_bit(1, true).unwrap();
        let f1 = b.freeze::<Rank9SelIndex<true, true>>();
        assert_eq!(seq.flags, vec![f0, f1]);

        assert!(!seq.is_empty());
        assert_eq!(seq.len(), 5);
        assert_eq!(seq.num_levels(), 3);
        assert_eq!(seq.widths(), vec![LEVEL_WIDTH, LEVEL_WIDTH, LEVEL_WIDTH]);

        assert_eq!(seq.access(0), Some(0xFFFF));
        assert_eq!(seq.access(1), Some(0xFF));
        assert_eq!(seq.access(2), Some(0xF));
        assert_eq!(seq.access(3), Some(0xFFFFF));
        assert_eq!(seq.access(4), Some(0xF));
    }

    #[test]
    fn test_empty() {
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        let seq = DacsByte::<Rank9SelIndex>::from_slice::<usize>(&[], &mut writer).unwrap();
        area.freeze().unwrap();
        assert!(seq.is_empty());
        assert_eq!(seq.len(), 0);
        assert_eq!(seq.num_levels(), 1);
        assert_eq!(seq.widths(), vec![LEVEL_WIDTH]);
    }

    #[test]
    fn test_all_zeros() {
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        let seq = DacsByte::<Rank9SelIndex>::from_slice(&[0, 0, 0, 0], &mut writer).unwrap();
        area.freeze().unwrap();
        assert!(!seq.is_empty());
        assert_eq!(seq.len(), 4);
        assert_eq!(seq.num_levels(), 1);
        assert_eq!(seq.widths(), vec![LEVEL_WIDTH]);
        assert_eq!(seq.access(0), Some(0));
        assert_eq!(seq.access(1), Some(0));
        assert_eq!(seq.access(2), Some(0));
        assert_eq!(seq.access(3), Some(0));
    }

    #[test]
    fn iter_collects() {
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 7], &mut writer).unwrap();
        area.freeze().unwrap();
        let collected: Vec<usize> = seq.iter().collect();
        assert_eq!(collected, vec![5, 7]);
    }

    #[test]
    fn to_vec_collects() {
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 7], &mut writer).unwrap();
        area.freeze().unwrap();
        assert_eq!(seq.to_vec(), vec![5, 7]);
    }

    #[test]
    fn bytes_roundtrip() {
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 0, 100000, 334], &mut writer).unwrap();
        let bytes = area.freeze().unwrap();
        let meta = seq.metadata();
        let other = DacsByte::<Rank9SelIndex>::from_bytes(meta, bytes).unwrap();
        assert_eq!(seq, other);
    }

    #[test]
    fn test_from_slice_uncastable() {
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        let e = DacsByte::<Rank9SelIndex>::from_slice(&[u128::MAX], &mut writer);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("vals must consist only of values castable into usize.".to_string())
        );
    }
}
