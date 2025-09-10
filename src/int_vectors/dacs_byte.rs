//! Compressed integer sequence using Directly Addressable Codes (DACs) in a simple bytewise scheme.
#![cfg(target_pointer_width = "64")]

use std::convert::TryFrom;

use anyhow::anyhow;
use anyhow::Result;
use num_traits::ToPrimitive;

use crate::bit_vector::BitVector;
use crate::bit_vector::BitVectorBuilder;
use crate::bit_vector::BitVectorIndex;
use crate::bit_vector::Rank;
use crate::bit_vector::Rank9SelIndex;
use crate::bit_vector::{self};
use crate::int_vectors::Access;
use crate::int_vectors::Build;
use crate::int_vectors::NumVals;
use crate::utils;
use anybytes::Bytes;
use anybytes::View;

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
/// use jerky::int_vectors::{DacsByte, Access};
///
/// use jerky::bit_vector::rank9sel::Rank9SelIndex;
/// let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 0, 100000, 334])?;
///
/// assert_eq!(seq.access(0), Some(5));
/// assert_eq!(seq.access(1), Some(0));
/// assert_eq!(seq.access(2), Some(100000));
/// assert_eq!(seq.access(3), Some(334));
///
/// assert_eq!(seq.len(), 4);
/// assert_eq!(seq.num_levels(), 3);
/// # Ok(())
/// # }
/// ```
///
/// # References
///
/// - N. R. Brisaboa, S. Ladra, and G. Navarro, "DACs: Bringing direct access to variable-length
///   codes." Information Processing & Management, 49(1), 392-404, 2013.
#[derive(Clone, PartialEq, Eq)]
pub struct DacsByte<I = Rank9SelIndex> {
    data: Vec<View<[u8]>>,
    flags: Vec<BitVector<I>>,
}

/// Metadata required to reconstruct a `DacsByte` from bytes.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DacsByteMeta {
    /// Number of valid levels stored.
    pub num_levels: usize,
    /// Byte length for each level in order.
    pub level_lens: Vec<usize>,
    /// Metadata for each flag bit vector between levels.
    pub flag_meta: Vec<FlagMeta>,
}

/// Metadata describing a flag bit vector stored inside a `DacsByte`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FlagMeta {
    /// Number of bits stored in the bit vector.
    pub len_bits: usize,
    /// Number of machine words used to hold the bits.
    pub num_words: usize,
}

impl<I: BitVectorIndex> DacsByte<I> {
    /// Builds DACs by assigning 8 bits to represent each level.
    ///
    /// # Arguments
    ///
    /// - `vals`: Slice of integers to be stored.
    ///
    /// # Errors
    ///
    /// An error is returned if `vals` contains an integer that cannot be cast to [`usize`].
    pub fn from_slice<T>(vals: &[T]) -> Result<Self>
    where
        T: ToPrimitive,
    {
        if vals.is_empty() {
            return Ok(Self::default());
        }

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

        if num_levels == 1 {
            let data: Vec<_> = vals
                .iter()
                .map(|x| u8::try_from(x.to_usize().unwrap()).unwrap())
                .collect();
            return Ok(Self {
                data: vec![Bytes::from_source(data).view::<[u8]>().unwrap()],
                flags: vec![],
            });
        }

        let mut data = vec![vec![]; num_levels];
        let mut flags = vec![BitVectorBuilder::new(); num_levels - 1];

        for x in vals {
            let mut x = x.to_usize().unwrap();
            for j in 0..num_levels {
                data[j].push(u8::try_from(x & LEVEL_MASK).unwrap());
                x >>= LEVEL_WIDTH;
                if j == num_levels - 1 {
                    assert_eq!(x, 0);
                    break;
                } else if x == 0 {
                    flags[j].push_bit(false);
                    break;
                }
                flags[j].push_bit(true);
            }
        }

        let flags = flags.into_iter().map(|bvb| bvb.freeze::<I>()).collect();
        let data = data
            .into_iter()
            .map(|v| Bytes::from_source(v).view::<[u8]>().unwrap())
            .collect();
        Ok(Self { data, flags })
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::bit_vector::rank9sel::Rank9SelIndex;
    /// use jerky::int_vectors::DacsByte;
    ///
    /// let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 0, 100000, 334])?;
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
    pub const fn iter(&self) -> Iter<I> {
        Iter::new(self)
    }

    /// Collects all integers into a `Vec<usize>` for inspection.
    pub fn to_vec(&self) -> Vec<usize> {
        self.iter().collect()
    }

    /// Gets the number of integers.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.data[0].len()
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

    /// Serializes the sequence into a [`Bytes`] buffer.
    ///
    /// Returns the metadata necessary for [`from_bytes`].
    pub fn to_bytes(&self) -> (DacsByteMeta, Bytes) {
        let level_lens = self.data.iter().map(|v| v.len()).collect::<Vec<_>>();
        let flag_meta = self
            .flags
            .iter()
            .map(|f| FlagMeta {
                len_bits: f.data.len,
                num_words: f.data.num_words(),
            })
            .collect::<Vec<_>>();

        let mut buf: Vec<u8> = Vec::new();
        for flag in &self.flags {
            for &word in flag.data.words.as_ref() {
                buf.extend_from_slice(&word.to_ne_bytes());
            }
        }

        for level in &self.data {
            buf.extend_from_slice(level.as_ref());
        }

        (
            DacsByteMeta {
                num_levels: self.data.len(),
                level_lens,
                flag_meta,
            },
            Bytes::from_source(buf),
        )
    }

    /// Reconstructs the sequence from zero-copy [`Bytes`].
    ///
    /// The `meta` argument should come from [`to_bytes`].
    pub fn from_bytes(meta: DacsByteMeta, bytes: Bytes) -> Result<Self> {
        use std::mem::size_of;

        let usize_size = size_of::<usize>();
        let mut cursor = 0;
        let slice = bytes.as_ref();

        if meta.num_levels == 0
            || meta.num_levels > MAX_LEVELS
            || meta.level_lens.len() != meta.num_levels
            || meta.flag_meta.len() != meta.num_levels.saturating_sub(1)
        {
            return Err(anyhow!("invalid metadata"));
        }

        let mut flags = Vec::with_capacity(meta.flag_meta.len());
        for fm in &meta.flag_meta {
            let bytes_len = fm.num_words * usize_size;
            if cursor + bytes_len > slice.len() {
                return Err(anyhow!("insufficient bytes"));
            }
            let words_view = bytes
                .slice_to_bytes(&slice[cursor..cursor + bytes_len])
                .ok_or_else(|| anyhow!("invalid slice"))?
                .view::<[usize]>()
                .map_err(|e| anyhow!(e))?;
            cursor += bytes_len;
            let data = bit_vector::BitVectorData {
                words: words_view,
                len: fm.len_bits,
            };
            let index = I::build(&data);
            flags.push(bit_vector::BitVector { data, index });
        }

        let mut data = Vec::with_capacity(meta.num_levels);
        for &len in &meta.level_lens {
            if cursor + len > slice.len() {
                return Err(anyhow!("insufficient bytes"));
            }
            let view_bytes = bytes
                .slice_to_bytes(&slice[cursor..cursor + len])
                .ok_or_else(|| anyhow!("invalid slice"))?;
            let view = view_bytes.view::<[u8]>().map_err(|e| anyhow!(e))?;
            data.push(view);
            cursor += len;
        }

        Ok(Self { data, flags })
    }
}

impl<I: BitVectorIndex> Default for DacsByte<I> {
    fn default() -> Self {
        Self {
            // Needs a single level at least.
            data: vec![Bytes::empty().view::<[u8]>().unwrap()],
            flags: vec![],
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
        Self::from_slice(vals)
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
    /// use jerky::bit_vector::rank9sel::Rank9SelIndex;
    /// use jerky::int_vectors::{DacsByte, Access};
    ///
    /// let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 999, 334])?;
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
    use anybytes::Bytes;

    #[test]
    fn test_basic() {
        let seq =
            DacsByte::<Rank9SelIndex>::from_slice(&[0xFFFF, 0xFF, 0xF, 0xFFFFF, 0xF]).unwrap();

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

        let mut b = BitVectorBuilder::new();
        b.extend_bits([true, false, false, true, false]);
        let f0 = b.freeze::<Rank9SelIndex<true, true>>();
        let mut b = BitVectorBuilder::new();
        b.extend_bits([false, true]);
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
        let seq = DacsByte::<Rank9SelIndex>::from_slice::<usize>(&[]).unwrap();
        assert!(seq.is_empty());
        assert_eq!(seq.len(), 0);
        assert_eq!(seq.num_levels(), 1);
        assert_eq!(seq.widths(), vec![LEVEL_WIDTH]);
    }

    #[test]
    fn test_all_zeros() {
        let seq = DacsByte::<Rank9SelIndex>::from_slice(&[0, 0, 0, 0]).unwrap();
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
        let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 7]).unwrap();
        let collected: Vec<usize> = seq.iter().collect();
        assert_eq!(collected, vec![5, 7]);
    }

    #[test]
    fn to_vec_collects() {
        let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 7]).unwrap();
        assert_eq!(seq.to_vec(), vec![5, 7]);
    }

    #[test]
    fn bytes_roundtrip() {
        let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 0, 100000, 334]).unwrap();
        let (meta, bytes) = seq.to_bytes();
        let other = DacsByte::<Rank9SelIndex>::from_bytes(meta, bytes).unwrap();
        assert_eq!(seq, other);
    }

    #[test]
    fn test_from_slice_uncastable() {
        let e = DacsByte::<Rank9SelIndex>::from_slice(&[u128::MAX]);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("vals must consist only of values castable into usize.".to_string())
        );
    }
}
