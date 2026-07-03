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
        let handles = self.handles;

        let mut scratch = ByteArea::new()?;
        let mut scratch_sections = scratch.sections();
        let mut visited = BitVectorBuilder::with_capacity(self.len, &mut scratch_sections)?;

        while let Some(builder) = remaining.pop() {
            // Freeze the next layer and obtain its index for rank/select queries.
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

    /// Merges already-built wavelet matrices into one, given the exact
    /// interleaving of their sequences.
    ///
    /// `origins` spells out, for each position of the merged sequence, which
    /// input that element comes from; within each input, elements are taken
    /// in their stored order. The result is identical to building a matrix
    /// from scratch over the interleaved sequence, but is computed
    /// *structurally*: because a stable bit-partition preserves each input's
    /// internal order, layer $`d`$ of the merged matrix is exactly the
    /// interleave of the inputs' layer-$`d`$ bit-planes under an origin
    /// vector that is itself re-partitioned per layer. No values are
    /// decoded, no sort is performed, and no freeze permutation is needed —
    /// just $`O(n \lg \sigma)`$ sequential bit reads/writes followed by the
    /// per-layer rank/select index builds. The returned matrix is complete
    /// and queryable (bit-planes plus indexes).
    ///
    /// This is the LSMT-compaction primitive: use it to replace several
    /// index segments by one merged segment in linear time, instead of
    /// decoding them into a flat vector, re-sorting, and rebuilding. The
    /// caller supplies `origins` from its own merge of the segments' sort
    /// keys (see [`Self::merge_sorted`] for the self-keyed case where the
    /// stored sequences themselves are the sorted runs).
    ///
    /// All inputs must share one alphabet width (the same number of
    /// layers); the merged alphabet size is the maximum of the inputs'. If
    /// the merge re-codes values (e.g. the alphabets are per-segment value
    /// domains that get unioned), the layer structure changes and this
    /// structural merge does not apply: decode with
    /// [`WaveletMatrix::to_vec`], remap, and rebuild with
    /// [`Self::from_iter`] instead.
    ///
    /// # Errors
    ///
    /// An error is returned if `inputs` is empty, if the inputs disagree on
    /// alphabet width, or if `origins` does not reference each input exactly
    /// `len()` times.
    pub fn merge_interleaved<J, T>(
        inputs: &[&WaveletMatrix<J>],
        origins: T,
        writer: &mut SectionWriter<'_>,
    ) -> Result<Self>
    where
        J: BitVectorIndex,
        T: IntoIterator<Item = usize>,
    {
        if inputs.is_empty() {
            return Err(Error::invalid_argument(
                "inputs must contain at least one matrix",
            ));
        }
        let alph_width = inputs[0].alph_width();
        for (j, wm) in inputs.iter().enumerate() {
            if wm.alph_width() != alph_width {
                return Err(Error::invalid_argument(format!(
                    "all inputs must share one alphabet width: \
                     inputs[0] has {alph_width} layers, inputs[{j}] has {}",
                    wm.alph_width()
                )));
            }
        }
        let alph_size = inputs.iter().map(|wm| wm.alph_size()).max().unwrap();
        let len: usize = inputs.iter().map(|wm| wm.len()).sum();

        // Materialize and validate the interleaving.
        let mut origins: Vec<u32> = {
            let iter = origins.into_iter();
            let mut vec = Vec::with_capacity(len);
            let mut counts = vec![0usize; inputs.len()];
            for src in iter {
                if inputs.len() <= src {
                    return Err(Error::invalid_argument(format!(
                        "origin {src} out of range for {} inputs",
                        inputs.len()
                    )));
                }
                counts[src] += 1;
                vec.push(src as u32);
            }
            for (j, (&count, wm)) in counts.iter().zip(inputs).enumerate() {
                if count != wm.len() {
                    return Err(Error::invalid_argument(format!(
                        "origins references inputs[{j}] {count} times, \
                         but it stores {} values",
                        wm.len()
                    )));
                }
            }
            vec
        };

        // Mirror WaveletMatrixBuilder's section layout: one handles section,
        // then one words section per layer.
        let mut handles = writer.reserve::<SectionHandle<u64>>(alph_width)?;
        let mut layers = Vec::with_capacity(alph_width);
        let mut cursors = vec![0usize; inputs.len()];
        let mut zeros_buf: Vec<u32> = Vec::with_capacity(len);
        let mut ones_buf: Vec<u32> = Vec::with_capacity(len);

        for depth in 0..alph_width {
            let mut builder = BitVectorBuilder::with_capacity(len, writer)?;
            handles[depth] = builder.handle();
            {
                let out_words = builder.words_mut();
                let planes: Vec<&[u64]> = inputs
                    .iter()
                    .map(|wm| wm.layers[depth].data.words())
                    .collect();
                cursors.iter_mut().for_each(|c| *c = 0);
                zeros_buf.clear();
                ones_buf.clear();
                let mut word = 0u64;
                for (pos, &src) in origins.iter().enumerate() {
                    let s = src as usize;
                    let cur = cursors[s];
                    cursors[s] = cur + 1;
                    let bit = (planes[s][cur / 64] >> (cur % 64)) & 1;
                    word |= bit << (pos % 64);
                    if pos % 64 == 63 {
                        out_words[pos / 64] = word;
                        word = 0;
                    }
                    if bit == 0 {
                        zeros_buf.push(src);
                    } else {
                        ones_buf.push(src);
                    }
                }
                if len % 64 != 0 {
                    out_words[len / 64] = word;
                }
            }
            layers.push(builder.freeze::<I>());
            // The next layer's order is this layer's stable partition.
            origins.clear();
            origins.extend_from_slice(&zeros_buf);
            origins.extend_from_slice(&ones_buf);
        }

        let layers_handle = handles.handle();
        handles.freeze()?;
        Ok(WaveletMatrix {
            layers,
            alph_size,
            layers_handle,
        })
    }

    /// Merges wavelet matrices whose stored sequences are each sorted
    /// (non-decreasing) into the matrix over the globally sorted merged
    /// sequence, in linear time.
    ///
    /// This is [`Self::merge_interleaved`] for the self-keyed case: each
    /// input is a sorted key run (an LSMT index segment), and the
    /// interleaving is computed here by a multi-way merge of the decoded
    /// runs. Equal values are taken from the lower input index first, and
    /// duplicates across runs are all kept (multiset merge) — deduplicate in
    /// the caller if segments may overlap. Total cost is
    /// $`O(n (\lg \sigma + k))`$ for `k` inputs, all sequential passes; the
    /// $`O(n \lg n)`$ comparison sort that a decode-concatenate-rebuild pays
    /// is avoided entirely, as is the freeze permutation.
    ///
    /// # Errors
    ///
    /// An error is returned if `inputs` is empty, if the inputs disagree on
    /// alphabet width, or if any input's sequence is not non-decreasing.
    pub fn merge_sorted<J>(
        inputs: &[&WaveletMatrix<J>],
        writer: &mut SectionWriter<'_>,
    ) -> Result<Self>
    where
        J: BitVectorIndex,
    {
        let runs: Vec<Vec<usize>> = inputs.iter().map(|wm| wm.to_vec()).collect();
        for (j, run) in runs.iter().enumerate() {
            if run.windows(2).any(|w| w[0] > w[1]) {
                return Err(Error::invalid_argument(format!(
                    "inputs[{j}] does not store a sorted (non-decreasing) sequence"
                )));
            }
        }
        let len = runs.iter().map(Vec::len).sum();
        let mut origins = Vec::with_capacity(len);
        let mut heads = vec![0usize; runs.len()];
        loop {
            let mut best: Option<(usize, usize)> = None;
            for (j, run) in runs.iter().enumerate() {
                if heads[j] < run.len() {
                    let val = run[heads[j]];
                    if best.map_or(true, |(best_val, _)| val < best_val) {
                        best = Some((val, j));
                    }
                }
            }
            match best {
                Some((_, j)) => {
                    heads[j] += 1;
                    origins.push(j);
                }
                None => break,
            }
        }
        Self::merge_interleaved(inputs, origins, writer)
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

    /// Decodes the whole stored sequence into a `Vec<usize>`, in original
    /// order, using one sequential pass per layer.
    ///
    /// This inverts the wavelet freeze: per layer, elements are stably
    /// scattered into the zero/one halves while the layer's bit is shifted
    /// into each element's value accumulator. All reads and (per region)
    /// writes are sequential, so it runs in $`O(n \lg \sigma)`$ time with
    /// streaming memory access — much faster than `iter()`, which pays
    /// $`O(\lg \sigma)`$ *random* rank queries per element.
    ///
    /// Use this when you need the full sequence back, e.g. to re-code and
    /// rebuild a matrix whose alphabet changes during a segment merge.
    pub fn to_vec(&self) -> Vec<usize> {
        let n = self.len();
        if n == 0 {
            return Vec::new();
        }
        // `vals[p]` accumulates the bits of the element currently at
        // position `p` in the running layer order; `idx[p]` remembers that
        // element's original (top-layer) position.
        let mut vals = vec![0usize; n];
        let mut next_vals = vec![0usize; n];
        let mut idx: Vec<usize> = (0..n).collect();
        let mut next_idx = vec![0usize; n];
        for layer in &self.layers {
            let words = layer.data.words();
            let zeros = layer.num_zeros();
            let mut z = 0;
            let mut o = zeros;
            for p in 0..n {
                let bit = (words[p / 64] >> (p % 64)) & 1;
                let val = (vals[p] << 1) | bit as usize;
                if bit == 0 {
                    next_vals[z] = val;
                    next_idx[z] = idx[p];
                    z += 1;
                } else {
                    next_vals[o] = val;
                    next_idx[o] = idx[p];
                    o += 1;
                }
            }
            std::mem::swap(&mut vals, &mut next_vals);
            std::mem::swap(&mut idx, &mut next_idx);
        }
        let mut out = vec![0usize; n];
        for p in 0..n {
            out[idx[p]] = vals[p];
        }
        out
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
        let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(1, iter::empty(), &mut sections)
            .expect("empty iterator should build successfully");
        assert_eq!(wm.len(), 0);
        assert!(wm.is_empty());
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

    /// Deterministic PRNG (splitmix64) for randomized tests without deps.
    fn sm(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn random_ints(seed: u64, len: usize, alph_size: usize) -> Vec<usize> {
        let mut st = seed;
        (0..len).map(|_| sm(&mut st) as usize % alph_size).collect()
    }

    fn build_wm(alph_size: usize, ints: &[usize]) -> (ByteArea, WaveletMatrix<Rank9SelIndex>) {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
            alph_size,
            ints.iter().copied(),
            &mut sections,
        )
        .unwrap();
        (area, wm)
    }

    #[test]
    fn to_vec_roundtrips_random_sequences() {
        let mut seed = 0xA11C_E000;
        for &(len, alph_size) in &[
            (0usize, 1usize),
            (1, 1),
            (1, 300),
            (7, 2),
            (64, 5),
            (65, 1000),
            (1000, 3),
            (1000, 941), // non-power-of-two alphabet
            (4096, 65536),
        ] {
            seed += 1;
            let ints = random_ints(seed, len, alph_size);
            let (_area, wm) = build_wm(alph_size, &ints);
            assert_eq!(wm.to_vec(), ints, "len={len} alph_size={alph_size}");
        }
    }

    /// Asserts that `merged` is exactly the matrix `reference` built from
    /// scratch: same shape, same layer bit-planes, and the same answers for
    /// access/rank/select/quantile on a random sample.
    fn assert_matrix_equivalence(
        merged: &WaveletMatrix<Rank9SelIndex>,
        reference: &WaveletMatrix<Rank9SelIndex>,
        expected: &[usize],
        seed: u64,
    ) {
        assert_eq!(merged.len(), reference.len());
        assert_eq!(merged.alph_size(), reference.alph_size());
        assert_eq!(merged.alph_width(), reference.alph_width());
        for (depth, (m, r)) in merged.layers.iter().zip(&reference.layers).enumerate() {
            assert_eq!(m.data.words(), r.data.words(), "bit-plane {depth} differs");
            assert_eq!(m.data.len(), r.data.len(), "plane {depth} length differs");
        }
        assert_eq!(merged.to_vec(), expected);

        let n = merged.len();
        let mut st = seed;
        for (pos, &val) in expected.iter().enumerate() {
            assert_eq!(merged.access(pos), Some(val), "access({pos})");
        }
        for _ in 0..200.min(n) {
            let pos = sm(&mut st) as usize % (n + 1);
            let val = if n == 0 {
                0
            } else {
                expected[sm(&mut st) as usize % n]
            };
            assert_eq!(
                merged.rank(pos, val),
                reference.rank(pos, val),
                "rank({pos}, {val})"
            );
            let k = sm(&mut st) as usize % (n.max(1));
            assert_eq!(
                merged.select(k, val),
                reference.select(k, val),
                "select({k}, {val})"
            );
            let mut lo = sm(&mut st) as usize % n;
            let mut hi = sm(&mut st) as usize % n;
            if hi < lo {
                std::mem::swap(&mut lo, &mut hi);
            }
            hi += 1;
            let q = sm(&mut st) as usize % (hi - lo);
            assert_eq!(
                merged.quantile(lo..hi, q),
                reference.quantile(lo..hi, q),
                "quantile({lo}..{hi}, {q})"
            );
        }
    }

    #[test]
    fn merge_sorted_equals_rebuild_random_runs() {
        let mut seed = 0x5EED_0001;
        for &(num_runs, max_len, alph_size) in &[
            (1usize, 50usize, 16usize),
            (2, 0, 4), // empty runs
            (2, 100, 300),
            (3, 64, 941),
            (4, 200, 2),
            (5, 333, 65536),
            (2, 1000, 1000),
        ] {
            seed += 1;
            let mut st = seed as u64;
            let runs: Vec<Vec<usize>> = (0..num_runs)
                .map(|_| {
                    let len = if max_len == 0 {
                        0
                    } else {
                        sm(&mut st) as usize % (max_len + 1)
                    };
                    let mut run = random_ints(sm(&mut st), len, alph_size);
                    run.sort_unstable();
                    run
                })
                .collect();
            let built: Vec<(ByteArea, WaveletMatrix<Rank9SelIndex>)> =
                runs.iter().map(|run| build_wm(alph_size, run)).collect();
            let inputs: Vec<&WaveletMatrix<Rank9SelIndex>> =
                built.iter().map(|(_, wm)| wm).collect();

            let mut area = ByteArea::new().unwrap();
            let mut sections = area.sections();
            let merged =
                WaveletMatrix::<Rank9SelIndex>::merge_sorted(&inputs, &mut sections).unwrap();

            // Reference: flatten, sort, rebuild from scratch — the baseline
            // the merge replaces.
            let mut expected: Vec<usize> = runs.iter().flatten().copied().collect();
            expected.sort_unstable();
            let (_ref_area, reference) = build_wm(alph_size, &expected);

            assert_matrix_equivalence(&merged, &reference, &expected, seed as u64 ^ 0xFACE);
        }
    }

    #[test]
    fn merge_interleaved_equals_rebuild_random_interleavings() {
        // The general (externally keyed) case: arbitrary interleavings of
        // arbitrary (unsorted) sequences.
        let mut seed = 0x1EAF_0001;
        for &(num_inputs, max_len, alph_size) in &[
            (1usize, 40usize, 8usize),
            (2, 128, 300),
            (3, 100, 941),
            (4, 77, 65536),
        ] {
            seed += 1;
            let mut st = seed as u64;
            let seqs: Vec<Vec<usize>> = (0..num_inputs)
                .map(|_| {
                    let len = sm(&mut st) as usize % (max_len + 1);
                    random_ints(sm(&mut st), len, alph_size)
                })
                .collect();
            let built: Vec<(ByteArea, WaveletMatrix<Rank9SelIndex>)> =
                seqs.iter().map(|s| build_wm(alph_size, s)).collect();
            let inputs: Vec<&WaveletMatrix<Rank9SelIndex>> =
                built.iter().map(|(_, wm)| wm).collect();

            // A random valid interleaving: a shuffled multiset of source ids.
            let mut origins: Vec<usize> = seqs
                .iter()
                .enumerate()
                .flat_map(|(j, s)| std::iter::repeat(j).take(s.len()))
                .collect();
            for i in (1..origins.len()).rev() {
                origins.swap(i, sm(&mut st) as usize % (i + 1));
            }

            let mut cursors = vec![0usize; num_inputs];
            let expected: Vec<usize> = origins
                .iter()
                .map(|&j| {
                    let v = seqs[j][cursors[j]];
                    cursors[j] += 1;
                    v
                })
                .collect();

            let mut area = ByteArea::new().unwrap();
            let mut sections = area.sections();
            let merged = WaveletMatrix::<Rank9SelIndex>::merge_interleaved(
                &inputs,
                origins.iter().copied(),
                &mut sections,
            )
            .unwrap();
            let (_ref_area, reference) = build_wm(alph_size, &expected);

            assert_matrix_equivalence(&merged, &reference, &expected, seed as u64 ^ 0xBEEF);
        }
    }

    #[test]
    fn merged_matrix_serializes_and_reloads() {
        let a = vec![1usize, 3, 3, 7, 200];
        let b = vec![0usize, 3, 100, 255];
        let (_area_a, wm_a) = build_wm(256, &a);
        let (_area_b, wm_b) = build_wm(256, &b);

        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let merged =
            WaveletMatrix::<Rank9SelIndex>::merge_sorted(&[&wm_a, &wm_b], &mut sections).unwrap();
        let meta = merged.metadata();
        let bytes = area.freeze().unwrap();
        let reloaded = WaveletMatrix::<Rank9SelIndex>::from_bytes(meta, bytes).unwrap();
        assert_eq!(merged, reloaded);

        let mut expected: Vec<usize> = a.iter().chain(&b).copied().collect();
        expected.sort_unstable();
        assert_eq!(reloaded.to_vec(), expected);
    }

    #[test]
    fn merge_rejects_invalid_inputs() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        // Empty input list.
        assert!(
            WaveletMatrix::<Rank9SelIndex>::merge_sorted::<Rank9SelIndex>(&[], &mut sections)
                .is_err()
        );

        // Mismatched alphabet widths.
        let (_a1, narrow) = build_wm(4, &[0, 1, 2]);
        let (_a2, wide) = build_wm(256, &[0, 1, 2]);
        assert!(
            WaveletMatrix::<Rank9SelIndex>::merge_sorted(&[&narrow, &wide], &mut sections).is_err()
        );

        // Unsorted input for merge_sorted.
        let (_a3, unsorted) = build_wm(4, &[2, 0, 1]);
        let (_a4, sorted) = build_wm(4, &[0, 1, 2]);
        assert!(
            WaveletMatrix::<Rank9SelIndex>::merge_sorted(&[&sorted, &unsorted], &mut sections)
                .is_err()
        );

        // Bad interleavings: out-of-range source, wrong multiplicity.
        assert!(WaveletMatrix::<Rank9SelIndex>::merge_interleaved(
            &[&sorted],
            [0usize, 1, 0].iter().copied(),
            &mut sections
        )
        .is_err());
        assert!(WaveletMatrix::<Rank9SelIndex>::merge_interleaved(
            &[&sorted],
            [0usize, 0].iter().copied(),
            &mut sections
        )
        .is_err());
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
