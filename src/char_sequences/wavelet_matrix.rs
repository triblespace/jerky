//! Time- and space-efficient data structure for a sequence of integers,
//! supporting some queries such as ranking, selection, and intersection.
#![cfg(target_pointer_width = "64")]

use std::iter::ExactSizeIterator;
use std::ops::Range;

use anybytes::area::ByteArea;
use anybytes::area::Section;
use anybytes::area::SectionHandle;
use anybytes::area::SectionWriter;
use anybytes::Bytes;

use crate::error::{Error, Result};

use crate::bit_vector::Access;
use crate::bit_vector::BitVector;
use crate::bit_vector::BitVectorBuilder;
use crate::bit_vector::BitVectorData;
use crate::bit_vector::BitVectorDataMeta;
use crate::bit_vector::BitVectorIndex;
use crate::bit_vector::NumBits;
use crate::bit_vector::Rank;
use crate::bit_vector::Select;
use crate::serialization::Serializable;
use crate::utils;

/// Time- and space-efficient data structure for a sequence of integers,
/// supporting some queries such as ranking, selection, and intersection.
///
/// [`WaveletMatrix`] stores a sequence of integers and provides myriad operations on the sequence.
/// When a sequence stores $`n`$ integers from $`[0, \sigma)`$,
/// most of the operations run in $`O(\lg \sigma)`$ time, using  $`O(n \lg \sigma )`$ bits of memory
/// (assuming bit vectors in constant-time and linear-space).
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use jerky::bit_vector::Rank9SelIndex;
/// use jerky::char_sequences::WaveletMatrix;
/// use anybytes::ByteArea;
///
/// let text = "banana";
/// let alph_size = ('n' as usize) + 1;
/// let len = text.len();
/// let mut area = ByteArea::new()?;
/// let mut sections = area.sections();
/// let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
///     alph_size,
///     text.bytes().map(|b| b as usize),
///     &mut sections,
/// )?;
///
/// assert_eq!(wm.len(), len);
/// assert_eq!(wm.alph_size(), alph_size);
/// assert_eq!(wm.alph_width(), 7);
///
/// assert_eq!(wm.access(2), Some('n' as usize));
/// assert_eq!(wm.rank(3, 'a' as usize), Some(1));
/// assert_eq!(wm.select(1, 'n' as usize), Some(4));
/// # Ok(())
/// # }
/// ```
///
/// # Credits
///
/// This is a yet another Rust port of [hillbig's waveletMatrix](https://github.com/hillbig/waveletTree/blob/master/waveletMatrix.go).
///
/// # References
///
/// - F. Claude, and G. Navarro, "The Wavelet Matrix," In SPIRE 2012.
#[derive(Debug, Clone)]
pub struct WaveletMatrix<I> {
    layers: Vec<BitVector<I>>,
    alph_size: usize,
    layers_handle: SectionHandle<SectionHandle<u64>>,
}

impl<I: PartialEq> PartialEq for WaveletMatrix<I> {
    fn eq(&self, other: &Self) -> bool {
        self.layers == other.layers
            && self.alph_size == other.alph_size
            && self.layers_handle.offset == other.layers_handle.offset
            && self.layers_handle.len == other.layers_handle.len
    }
}

impl<I: Eq> Eq for WaveletMatrix<I> {}

/// Metadata describing the serialized form of a [`WaveletMatrix`].
#[derive(Debug, Clone, Copy, zerocopy::FromBytes, zerocopy::KnownLayout, zerocopy::Immutable)]
#[repr(C)]
pub struct WaveletMatrixMeta {
    /// Maximum value + 1 stored in the matrix.
    pub alph_size: usize,
    /// Number of bit vector layers in the matrix.
    pub alph_width: usize,
    /// Number of integers stored.
    pub len: usize,
    /// Handle to a slice of per-layer [`SectionHandle`]s stored in the byte arena.
    pub layers: SectionHandle<SectionHandle<u64>>,
}

/// Builder for [`WaveletMatrix`].
pub struct WaveletMatrixBuilder<'a> {
    alph_size: usize,
    len: usize,
    alph_width: usize,
    layers: Vec<BitVectorBuilder<'a>>,
    handles: Section<'a, SectionHandle<u64>>,
}

impl<'a> WaveletMatrixBuilder<'a> {
    /// Creates a builder for a sequence of `len` integers in `0..alph_size`.
    pub fn with_capacity(
        alph_size: usize,
        len: usize,
        writer: &mut SectionWriter<'a>,
    ) -> Result<Self> {
        if len == 0 {
            return Err(Error::invalid_argument("seq must not be empty."));
        }
        let alph_width = utils::needed_bits(alph_size);
        let mut handles = writer.reserve::<SectionHandle<u64>>(alph_width)?;
        let mut layers = Vec::with_capacity(alph_width);
        for idx in 0..alph_width {
            let builder = BitVectorBuilder::with_capacity(len, writer)?;
            handles[idx] = builder.handle();
            layers.push(builder);
        }
        Ok(Self {
            alph_size,
            len,
            alph_width,
            layers,
            handles,
        })
    }

    /// Sets the `pos`-th integer to `val`.
    pub fn set_int(&mut self, pos: usize, val: usize) -> Result<()> {
        if self.len <= pos {
            return Err(Error::invalid_argument(format!(
                "pos must be no greater than self.len()={}, but got {pos}.",
                self.len
            )));
        }
        if val >= self.alph_size {
            return Err(Error::invalid_argument(format!(
                "value {} out of range 0..{}",
                val, self.alph_size
            )));
        }
        for (layer_idx, layer) in self.layers.iter_mut().enumerate() {
            let shift = self.alph_width - 1 - layer_idx;
            let bit = ((val >> shift) & 1) == 1;
            layer.set_bit(pos, bit)?;
        }
        Ok(())
    }

    /// Writes integers from `ints` starting at `start`.
    ///
    /// Returns the number of integers written.
    pub fn set_ints_from_iter<I>(&mut self, start: usize, ints: &mut I) -> Result<usize>
    where
        I: Iterator<Item = usize>,
    {
        if start > self.len {
            return Err(Error::invalid_argument(format!(
                "start must be no greater than self.len()={}, but got {}.",
                self.len, start
            )));
        }
        let mut pos = start;
        while pos < self.len {
            match ints.next() {
                Some(x) => {
                    self.set_int(pos, x)?;
                    pos += 1;
                }
                None => break,
            }
        }
        Ok(pos - start)
    }

    /// Finalizes the builder into a [`WaveletMatrix`].
    ///
    /// Layers are frozen from most significant to least significant bit.
    /// After freezing the current layer, the permutation induced by its bits is
    /// applied in place to all remaining (deeper) layers using cycle
    /// rotations.  A single scratch `visited` bitmap tracks processed
    /// positions, ensuring $`O(n)`$ extra bits overall.
    pub fn freeze<Ix: BitVectorIndex>(self) -> Result<WaveletMatrix<Ix>> {
        // Builders for yet-unfrozen layers. Reverse so popping yields the next
        // layer without shifting the entire vector each iteration.
        let mut remaining = self.layers;
        remaining.reverse();
        let mut layers = Vec::with_capacity(self.alph_width);
        let mut scratch = ByteArea::new()?;
        let mut scratch_sections = scratch.sections();
        let mut visited = BitVectorBuilder::with_capacity(self.len, &mut scratch_sections)?;
        let handles = self.handles;

        for _ in 0..self.alph_width {
            // Freeze the next layer and obtain its index for rank/select queries.
            let builder = remaining.pop().expect("layer available");
            let layer = builder.freeze::<Ix>();
            let zeros = layer.num_zeros();

            if !remaining.is_empty() {
                // Apply the permutation induced by this layer to all deeper
                // levels. Only the minority side needs to start cycles.
                visited.fill(false);
                let ones = self.len - zeros;
                let iterate_zeros = zeros <= ones;
                let count = if iterate_zeros { zeros } else { ones };

                for t in 0..count {
                    let start = if iterate_zeros {
                        layer.select0(t).expect("select0 in range")
                    } else {
                        layer.select1(t).expect("select1 in range")
                    };
                    if visited.get_bit(start)? {
                        continue;
                    }
                    rotate_cycle_over_lower_levels(
                        &layer,
                        zeros,
                        start,
                        &mut remaining,
                        &mut visited,
                    )?;
                }
            }

            layers.push(layer);
        }

        let layers_handle = handles.handle();
        handles.freeze()?;
        Ok(WaveletMatrix {
            layers,
            alph_size: self.alph_size,
            layers_handle,
        })
    }
}

/// Rotates a permutation cycle for all deeper layers during freezing.
///
/// The cycle starts at `start` and follows the permutation induced by the
/// already-frozen layer `layer`. Bits on levels below `layer` are moved in
/// place without any additional buffers.
fn rotate_cycle_over_lower_levels<Ix: BitVectorIndex>(
    layer: &BitVector<Ix>,
    zeros: usize,
    start: usize,
    lower: &mut [BitVectorBuilder<'_>],
    visited: &mut BitVectorBuilder<'_>,
) -> Result<()> {
    debug_assert!(lower.len() <= usize::BITS as usize);
    let mut carry: usize = 0;
    for (offset, b) in lower.iter().enumerate() {
        if b.get_bit(start)? {
            carry |= 1usize << offset;
        }
    }
    let mut p = start;
    loop {
        visited.set_bit(p, true)?;
        let bit = layer.access(p).expect("access within bounds");
        let q = if !bit {
            layer.rank0(p).expect("rank0 within bounds")
        } else {
            zeros + layer.rank1(p).expect("rank1 within bounds")
        };
        for (offset, b) in lower.iter_mut().enumerate() {
            let tmp = b.get_bit(q)?;
            let bit = (carry >> offset) & 1 == 1;
            b.set_bit(q, bit)?;
            carry = (carry & !(1usize << offset)) | ((tmp as usize) << offset);
        }
        p = q;
        if visited.get_bit(p)? {
            break;
        }
    }
    Ok(())
}

impl<I> WaveletMatrix<I>
where
    I: BitVectorIndex,
{
    /// Builds a [`WaveletMatrix`] from a single exact-size iterator.
    pub fn from_iter<'a, J>(
        alph_size: usize,
        ints: J,
        writer: &mut SectionWriter<'a>,
    ) -> Result<Self>
    where
        J: ExactSizeIterator<Item = usize>,
    {
        let len = ints.len();
        let mut builder = WaveletMatrixBuilder::with_capacity(alph_size, len, writer)?;
        for (i, x) in ints.enumerate() {
            builder.set_int(i, x)?;
        }
        builder.freeze()
    }
}

impl<I> WaveletMatrix<I>
where
    I: BitVectorIndex,
{
    /// Returns the `pos`-th integer, or [`None`] if `self.len() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Position to access.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::char_sequences::WaveletMatrix;
    /// use anybytes::ByteArea;
    ///
    /// let text = "banana";
    /// let alph_size = ('n' as usize) + 1;
    /// let mut area = ByteArea::new()?;
    /// let mut sections = area.sections();
    /// let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
    ///     alph_size,
    ///     text.bytes().map(|b| b as usize),
    ///     &mut sections,
    /// )?;
    ///
    /// assert_eq!(wm.access(2), Some('n' as usize));
    /// assert_eq!(wm.access(5), Some('a' as usize));
    /// assert_eq!(wm.access(6), None);
    /// # Ok(())
    /// # }
    /// ```
    // NOTE(kampersanda): We should not use `get()` because it has been already used in most std
    // containers with different type annotations.
    #[inline(always)]
    pub fn access(&self, mut pos: usize) -> Option<usize> {
        if self.len() <= pos {
            return None;
        }
        let mut val = 0;
        for layer in &self.layers {
            val <<= 1;
            if layer.access(pos).unwrap() {
                val |= 1;
                pos = layer.rank1(pos).unwrap() + layer.num_zeros();
            } else {
                pos = layer.rank0(pos).unwrap();
            }
        }
        Some(val)
    }

    /// Returns the number of occurrence of `val` in the range `0..pos`,
    /// or [`None`] if `self.len() < pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Position to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::char_sequences::WaveletMatrix;
    /// use anybytes::ByteArea;
    ///
    /// let text = "banana";
    /// let alph_size = ('n' as usize) + 1;
    /// let mut area = ByteArea::new()?;
    /// let mut sections = area.sections();
    /// let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
    ///     alph_size,
    ///     text.bytes().map(|b| b as usize),
    ///     &mut sections,
    /// )?;
    ///
    /// assert_eq!(wm.rank(3, 'a' as usize), Some(1));
    /// assert_eq!(wm.rank(5, 'c' as usize), Some(0));
    /// assert_eq!(wm.rank(7, 'b' as usize), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn rank(&self, pos: usize, val: usize) -> Option<usize> {
        self.rank_range(0..pos, val)
    }

    /// Returns the number of occurrence of `val` in the given `range`,
    /// or [`None`] if `range` is out of bounds.
    ///
    /// # Arguments
    ///
    /// - `range`: Position range to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::char_sequences::WaveletMatrix;
    /// use anybytes::ByteArea;
    ///
    /// let text = "banana";
    /// let alph_size = ('n' as usize) + 1;
    /// let mut area = ByteArea::new()?;
    /// let mut sections = area.sections();
    /// let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
    ///     alph_size,
    ///     text.bytes().map(|b| b as usize),
    ///     &mut sections,
    /// )?;
    ///
    /// assert_eq!(wm.rank_range(1..4, 'a' as usize), Some(2));
    /// assert_eq!(wm.rank_range(2..4, 'c' as usize), Some(0));
    /// assert_eq!(wm.rank_range(4..7, 'b' as usize), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn rank_range(&self, range: Range<usize>, val: usize) -> Option<usize> {
        if range.is_empty() {
            return Some(0);
        }
        if self.len() < range.end {
            return None;
        }

        let mut start_pos = range.start;
        let mut end_pos = range.end;

        // NOTE(kampersanda): rank should be safe because of the precheck.
        for (depth, layer) in self.layers.iter().enumerate() {
            let bit = Self::get_msb(val, depth, self.alph_width());
            if bit {
                start_pos = layer.rank1(start_pos).unwrap() + layer.num_zeros();
                end_pos = layer.rank1(end_pos).unwrap() + layer.num_zeros();
            } else {
                start_pos = layer.rank0(start_pos).unwrap();
                end_pos = layer.rank0(end_pos).unwrap();
            }
        }
        Some((start_pos..end_pos).len())
    }

    /// Returns the occurrence position of `k`-th `val`,
    /// or [`None`] if there is no such an occurrence.
    ///
    /// # Arguments
    ///
    /// - `k`: Rank to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::char_sequences::WaveletMatrix;
    /// use anybytes::ByteArea;
    ///
    /// let text = "banana";
    /// let alph_size = ('n' as usize) + 1;
    /// let mut area = ByteArea::new()?;
    /// let mut sections = area.sections();
    /// let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
    ///     alph_size,
    ///     text.bytes().map(|b| b as usize),
    ///     &mut sections,
    /// )?;
    ///
    /// assert_eq!(wm.select(1, 'a' as usize), Some(3));
    /// assert_eq!(wm.select(0, 'c' as usize), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn select(&self, k: usize, val: usize) -> Option<usize> {
        self.select_helper(k, val, 0, 0)
    }

    #[inline]
    fn select_helper(
        &self,
        mut k: usize,
        val: usize,
        mut pos: usize,
        depth: usize,
    ) -> Option<usize> {
        if depth == self.alph_width() {
            return Some(pos + k);
        }
        let bit = Self::get_msb(val, depth, self.alph_width());
        let layer = &self.layers[depth];
        if bit {
            let zeros = layer.num_zeros();
            // NOTE(kampersanda): rank should be safe.
            pos = layer.rank1(pos).unwrap() + zeros;
            k = self.select_helper(k, val, pos, depth + 1)?;
            layer.select1(k - zeros)
        } else {
            // NOTE(kampersanda): rank should be safe.
            pos = layer.rank0(pos).unwrap();
            k = self.select_helper(k, val, pos, depth + 1)?;
            layer.select0(k)
        }
    }

    /// Returns `k`-th smallest value in the given `range`,
    /// or [`None`] if `range.len() <= k` or `range` is out of bounds.
    ///
    /// # Arguments
    ///
    /// - `range`: Position range to be searched.
    /// - `k`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::char_sequences::WaveletMatrix;
    /// use anybytes::ByteArea;
    ///
    /// let text = "banana";
    /// let alph_size = ('n' as usize) + 1;
    /// let mut area = ByteArea::new()?;
    /// let mut sections = area.sections();
    /// let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
    ///     alph_size,
    ///     text.bytes().map(|b| b as usize),
    ///     &mut sections,
    /// )?;
    ///
    /// assert_eq!(wm.quantile(1..4, 0), Some('a' as usize)); // The 0th in "ana" should be "a"
    /// assert_eq!(wm.quantile(1..4, 1), Some('a' as usize)); // The 1st in "ana" should be "a"
    /// assert_eq!(wm.quantile(1..4, 2), Some('n' as usize)); // The 1st in "ana" should be "n"
    /// assert_eq!(wm.quantile(1..4, 3), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn quantile(&self, range: Range<usize>, mut k: usize) -> Option<usize> {
        if range.len() <= k {
            return None;
        }
        if self.len() < range.end {
            return None;
        }

        let mut val = 0;
        let mut start_pos = range.start;
        let mut end_pos = range.end;

        for layer in &self.layers {
            val <<= 1;
            // NOTE(kampersanda): rank should be safe because of the precheck.
            let zero_start_pos = layer.rank0(start_pos).unwrap();
            let zero_end_pos = layer.rank0(end_pos).unwrap();
            let zeros = zero_end_pos - zero_start_pos;
            if k < zeros {
                start_pos = zero_start_pos;
                end_pos = zero_end_pos;
            } else {
                k -= zeros;
                val |= 1;
                start_pos = layer.num_zeros() + start_pos - zero_start_pos;
                end_pos = layer.num_zeros() + end_pos - zero_end_pos;
            }
        }
        Some(val)
    }

    /// Returns the all integers co-occurred more than `k` times in given `ranges`,
    /// or [`None`] if any range in `ranges` is out of bounds.
    ///
    /// Note that `Some(vec![])`, not [`None`], will be returned if there is no occurrence.
    ///
    /// # Arguments
    ///
    /// - `ranges`: Ranges to be searched.
    /// - `k`: Occurrence threshold.
    ///
    /// # Complexity
    ///
    /// $`O( \min(\sigma, j_1 - i_1, \dots, j_r - i_r ) )`$ for `ranges` is $`[(i_1,j_1),\dots,(i_r,j_r)]`$.[^intersect]
    ///
    /// [^intersect]: A tighter bound is analyzed in the paper: Gagie, Travis, Gonzalo Navarro, and Simon J. Puglisi.
    /// "New algorithms on wavelet trees and applications to information retrieval." Theoretical Computer Science 426 (2012): 25-41.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::char_sequences::WaveletMatrix;
    /// use anybytes::ByteArea;
    ///
    /// let text = "banana";
    /// let alph_size = ('n' as usize) + 1;
    /// let mut area = ByteArea::new()?;
    /// let mut sections = area.sections();
    /// let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
    ///     alph_size,
    ///     text.bytes().map(|b| b as usize),
    ///     &mut sections,
    /// )?;
    ///
    /// // Intersections among "ana", "na", and "ba".
    /// assert_eq!(
    ///     wm.intersect(&[1..4, 4..6, 0..2], 0),
    ///     Some(vec!['a' as usize, 'b' as usize, 'n' as usize])
    /// );
    /// assert_eq!(
    ///     wm.intersect(&[1..4, 4..6, 0..2], 1),
    ///     Some(vec!['a' as usize, 'n' as usize])
    /// );
    /// assert_eq!(
    ///     wm.intersect(&[1..4, 4..6, 0..2], 2),
    ///     Some(vec!['a' as usize])
    /// );
    /// assert_eq!(
    ///     wm.intersect(&[1..4, 4..6, 0..2], 3),
    ///     Some(vec![])
    /// );
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn intersect(&self, ranges: &[Range<usize>], k: usize) -> Option<Vec<usize>> {
        self.intersect_helper(ranges, k, 0, 0)
    }

    #[inline]
    fn intersect_helper(
        &self,
        ranges: &[Range<usize>],
        k: usize,
        depth: usize,
        prefix: usize,
    ) -> Option<Vec<usize>> {
        if depth == self.alph_width() {
            return Some(vec![prefix]);
        }

        let mut zero_ranges = vec![];
        let mut one_ranges = vec![];

        let layer = &self.layers[depth];
        for range in ranges {
            if layer.num_bits() < range.end {
                return None;
            }
            // NOTE(kampersanda): An empty range should be skipped because it is never co-occurred.
            if range.is_empty() {
                continue;
            }

            let start_pos = range.start;
            let end_pos = range.end;

            // NOTE(kampersanda): rank should be safe because of the precheck.
            let zero_start_pos = layer.rank0(start_pos).unwrap();
            let zero_end_pos = layer.rank0(end_pos).unwrap();
            let one_start_pos = layer.num_zeros() + start_pos - zero_start_pos;
            let one_end_pos = layer.num_zeros() + end_pos - zero_end_pos;

            if zero_end_pos - zero_start_pos > 0 {
                zero_ranges.push(zero_start_pos..zero_end_pos)
            }
            if one_end_pos - one_start_pos > 0 {
                one_ranges.push(one_start_pos..one_end_pos)
            }
        }

        let mut ret = vec![];
        if zero_ranges.len() > k {
            ret.extend_from_slice(&self.intersect_helper(
                &zero_ranges,
                k,
                depth + 1,
                prefix << 1,
            )?);
        }
        if one_ranges.len() > k {
            ret.extend_from_slice(&self.intersect_helper(
                &one_ranges,
                k,
                depth + 1,
                (prefix << 1) | 1,
            )?);
        }
        Some(ret)
    }

    #[inline(always)]
    const fn get_msb(val: usize, pos: usize, width: usize) -> bool {
        ((val >> (width - pos - 1)) & 1) == 1
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::bit_vector::Rank9SelIndex;
    /// use jerky::char_sequences::WaveletMatrix;
    /// use anybytes::ByteArea;
    ///
    /// let text = "ban";
    /// let alph_size = ('n' as usize) + 1;
    /// let mut area = ByteArea::new()?;
    /// let mut sections = area.sections();
    /// let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
    ///     alph_size,
    ///     text.bytes().map(|b| b as usize),
    ///     &mut sections,
    /// )?;
    ///
    /// let mut it = wm.iter();
    /// assert_eq!(it.next(), Some('b' as usize));
    /// assert_eq!(it.next(), Some('a' as usize));
    /// assert_eq!(it.next(), Some('n' as usize));
    /// assert_eq!(it.next(), None);
    /// # Ok(())
    /// # }
    /// ```
    pub const fn iter(&'_ self) -> Iter<'_, I> {
        Iter::new(self)
    }

    /// Returns the number of values stored.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.layers.first().map(|l| l.num_bits()).unwrap_or(0)
    }

    /// Checks if the sequence is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the maximum value + 1 in the sequence, i.e., $`\sigma`$.
    #[inline(always)]
    pub const fn alph_size(&self) -> usize {
        self.alph_size
    }

    /// Returns $`\lceil \log_2{\sigma} \rceil`$, which is the number of layers in the matrix.
    #[inline(always)]
    pub fn alph_width(&self) -> usize {
        self.layers.len()
    }

    /// Returns metadata describing this matrix.
    pub fn metadata(&self) -> WaveletMatrixMeta {
        <Self as Serializable>::metadata(self)
    }

    /// Reconstructs the sequence from metadata and a zero-copy [`Bytes`] buffer.
    pub fn from_bytes(meta: WaveletMatrixMeta, bytes: Bytes) -> Result<Self> {
        <Self as Serializable>::from_bytes(meta, bytes)
    }
}

impl<I: BitVectorIndex> Serializable for WaveletMatrix<I> {
    type Meta = WaveletMatrixMeta;
    type Error = Error;

    fn metadata(&self) -> Self::Meta {
        WaveletMatrixMeta {
            alph_size: self.alph_size,
            alph_width: self.alph_width(),
            len: self.len(),
            layers: self.layers_handle,
        }
    }

    fn from_bytes(meta: Self::Meta, bytes: Bytes) -> Result<Self> {
        let handles_view = meta.layers.view(&bytes)?;
        let mut layers = Vec::with_capacity(meta.alph_width);
        for h in handles_view.as_ref() {
            let data = BitVectorData::from_bytes(
                BitVectorDataMeta {
                    len: meta.len,
                    handle: *h,
                },
                bytes.clone(),
            )?;
            let index = I::build(&data);
            layers.push(BitVector::new(data, index));
        }
        Ok(Self {
            layers,
            alph_size: meta.alph_size,
            layers_handle: meta.layers,
        })
    }
}

/// Iterator for enumerating integers, created by [`WaveletMatrix::iter()`].
pub struct Iter<'a, I> {
    wm: &'a WaveletMatrix<I>,
    pos: usize,
}

impl<'a, I> Iter<'a, I> {
    /// Creates a new iterator.
    pub const fn new(wm: &'a WaveletMatrix<I>) -> Self {
        Self { wm, pos: 0 }
    }
}

impl<I> Iterator for Iter<'_, I>
where
    I: BitVectorIndex,
{
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.wm.len() {
            let x = self.wm.access(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.wm.len(), Some(self.wm.len()))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::bit_vector::rank9sel::inner::Rank9SelIndex;
    use std::iter;

    #[test]
    fn test_empty_seq() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let e = WaveletMatrix::<Rank9SelIndex>::from_iter(1, iter::empty(), &mut sections);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("seq must not be empty.".to_string())
        );
    }

    #[test]
    fn test_navarro_book() {
        // This test example is from G. Navarro's "Compact Data Structures" P130
        let text = "tobeornottobethatisthequestion";
        let len = text.len();

        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let alph_size = ('u' as usize) + 1;
        let ints: Vec<usize> = text.bytes().map(|b| b as usize).collect();
        let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
            alph_size,
            ints.iter().copied(),
            &mut sections,
        )
        .unwrap();

        assert_eq!(wm.len(), len);
        assert_eq!(wm.alph_size(), ('u' as usize) + 1);
        assert_eq!(wm.alph_width(), 7);

        assert_eq!(wm.access(20), Some('h' as usize));
        assert_eq!(wm.rank(22, 'o' as usize), Some(4));
        assert_eq!(wm.select(2, 't' as usize), Some(9));

        assert_eq!(wm.quantile(0..len, 0), Some('a' as usize)); // min
        assert_eq!(wm.quantile(0..len, len / 2), Some('o' as usize)); // median
        assert_eq!(wm.quantile(0..len, len - 1), Some('u' as usize)); // max
        assert_eq!(wm.quantile(0..3, 0), Some('b' as usize)); // zero-th in "tob" should be "b"

        let ranges = vec![0..3, 3..6];
        assert_eq!(wm.intersect(&ranges, 1), Some(vec!['o' as usize]));
    }

    #[test]
    fn builder_sets_ints() {
        let text = "banana";
        let alph_size = ('n' as usize) + 1;
        let ints: Vec<usize> = text.bytes().map(|b| b as usize).collect();
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder =
            WaveletMatrixBuilder::with_capacity(alph_size, ints.len(), &mut sections).unwrap();
        for (i, &x) in ints.iter().enumerate() {
            builder.set_int(i, x).unwrap();
        }
        let wm = builder.freeze::<Rank9SelIndex>().unwrap();
        assert_eq!(wm.len(), text.len());
        assert_eq!(wm.access(2), Some('n' as usize));
    }

    #[test]
    fn from_bytes_roundtrip() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let text = "banana";
        let alph_size = ('n' as usize) + 1;
        let ints: Vec<usize> = text.bytes().map(|b| b as usize).collect();
        let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
            alph_size,
            ints.iter().copied(),
            &mut sections,
        )
        .unwrap();
        let bytes = area.freeze().unwrap();
        let meta = wm.metadata();
        let other = WaveletMatrix::<Rank9SelIndex>::from_bytes(meta, bytes).unwrap();
        assert_eq!(wm, other);
    }
}
