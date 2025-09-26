//! Updatable compact vector in which each integer is represented in a fixed number of bits.
#![cfg(target_pointer_width = "64")]

use num_traits::ToPrimitive;
use std::iter::ExactSizeIterator;

use crate::bit_vector::{BitVector, BitVectorBuilder, BitVectorData, BitVectorDataMeta, NoIndex};
use crate::error::{Error, Result};
use crate::int_vectors::prelude::*;
use crate::serialization::Serializable;
use crate::utils;
use anybytes::{area::SectionHandle, ByteArea, Bytes, SectionWriter};

/// Mutable builder for [`CompactVector`].
///
/// This structure collects integers using [`set_int`] or [`set_ints`]
/// and finally [`freeze`]s into an immutable [`CompactVector`].
///
/// # Examples
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use jerky::int_vectors::CompactVectorBuilder;
/// use anybytes::ByteArea;
/// let mut area = ByteArea::new()?;
/// let mut sections = area.sections();
/// let mut builder = CompactVectorBuilder::with_capacity(3, 3, &mut sections)?;
/// builder.set_ints(0..3, [1, 2, 5])?;
/// let cv = builder.freeze();
/// assert_eq!(cv.get_int(1), Some(2));
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct CompactVectorBuilder<'a> {
    chunks: BitVectorBuilder<'a>,
    len: usize,
    width: usize,
    capacity: usize,
}

impl<'a> CompactVectorBuilder<'a> {
    /// Creates a new builder reserving space for `capa` integers.
    ///
    /// Pushing more than `capa` integers will return an error.
    pub fn with_capacity(
        capa: usize,
        width: usize,
        writer: &mut SectionWriter<'a>,
    ) -> Result<Self> {
        if !(1..=64).contains(&width) {
            return Err(Error::invalid_argument(format!(
                "width must be in 1..=64, but got {width}."
            )));
        }
        let bits = capa
            .checked_mul(width)
            .ok_or_else(|| Error::invalid_argument("capa * width overflowed"))?;
        Ok(Self {
            chunks: BitVectorBuilder::with_capacity(bits, writer)?,
            len: 0,
            width,
            capacity: capa,
        })
    }

    /// Sets the `pos`-th integer to `val`.
    ///
    /// # Errors
    ///
    /// Returns an error if `pos` is out of bounds or if `val` does not fit in
    /// `self.width()` bits.
    pub fn set_int(&mut self, pos: usize, val: usize) -> Result<()> {
        if self.capacity <= pos {
            return Err(Error::invalid_argument(format!(
                "pos must be no greater than self.capacity()={}, but got {pos}.",
                self.capacity
            )));
        }
        if self.width != 64 && val >> self.width != 0 {
            return Err(Error::invalid_argument(format!(
                "val must fit in self.width()={} bits, but got {val}.",
                self.width
            )));
        }
        for i in 0..self.width {
            let bit = ((val >> i) & 1) == 1;
            self.chunks.set_bit(pos * self.width + i, bit)?;
        }
        if self.len <= pos {
            self.len = pos + 1;
        }
        Ok(())
    }

    /// Sets integers in `range` from the provided values.
    ///
    /// The number of integers in `vals` must match `range.len()`.
    pub fn set_ints<I>(&mut self, range: std::ops::Range<usize>, vals: I) -> Result<()>
    where
        I: IntoIterator<Item = usize>,
    {
        if range.end > self.capacity {
            return Err(Error::invalid_argument(format!(
                "range end must be no greater than self.capacity()={}, but got {}.",
                self.capacity, range.end
            )));
        }
        let mut pos = range.start;
        for x in vals.into_iter() {
            if pos >= range.end {
                return Err(Error::invalid_argument(
                    "too many values for the specified range",
                ));
            }
            self.set_int(pos, x)?;
            pos += 1;
        }
        if pos != range.end {
            return Err(Error::invalid_argument(
                "not enough values for the specified range",
            ));
        }
        Ok(())
    }

    /// Finalizes the builder into an immutable [`CompactVector`].
    ///
    /// The builder can no longer be used after freezing.
    ///
    /// # Examples
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::int_vectors::CompactVectorBuilder;
    /// use anybytes::ByteArea;
    /// let mut area = ByteArea::new()?;
    /// let mut sections = area.sections();
    /// let cv = CompactVectorBuilder::with_capacity(0, 2, &mut sections)?.freeze();
    /// assert!(cv.is_empty());
    /// # Ok(())
    /// # }
    /// ```
    pub fn freeze(self) -> CompactVector {
        let chunks: BitVector<NoIndex> = self.chunks.freeze::<NoIndex>();
        CompactVector {
            chunks,
            len: self.len,
            width: self.width,
        }
    }
}

/// Updatable compact vector in which each integer is represented in a fixed number of bits.
///
/// # Memory usage
///
/// $`n \lceil \lg u \rceil`$ bits for $`n`$ integers in which a value is in $`[0,u)`$.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use jerky::int_vectors::{CompactVector, CompactVectorBuilder};
/// use anybytes::ByteArea;
///
/// // Can store integers within 3 bits each.
/// let mut area = ByteArea::new()?;
/// let mut sections = area.sections();
/// let mut builder = CompactVectorBuilder::with_capacity(3, 3, &mut sections)?;
/// builder.set_ints(0..2, [7, 2])?;
/// builder.set_int(0, 5)?;
/// let cv = builder.freeze();
///
/// assert_eq!(cv.len(), 2);
/// assert_eq!(cv.get_int(0), Some(5));
/// # Ok(())
/// # }
/// ```
#[derive(Clone)]
pub struct CompactVector {
    chunks: BitVector<NoIndex>,
    len: usize,
    width: usize,
}

impl PartialEq for CompactVector {
    fn eq(&self, other: &Self) -> bool {
        self.chunks == other.chunks && self.len == other.len && self.width == other.width
    }
}

impl Eq for CompactVector {}

impl Default for CompactVector {
    fn default() -> Self {
        let mut area = ByteArea::new().expect("byte area");
        let mut sections = area.sections();
        let builder = BitVectorBuilder::with_capacity(0, &mut sections).unwrap();
        let chunks = builder.freeze::<NoIndex>();
        Self {
            chunks,
            len: 0,
            width: 0,
        }
    }
}

/// Metadata describing a [`CompactVector`] stored in a [`ByteArea`].
#[derive(Debug, Clone, Copy, zerocopy::FromBytes, zerocopy::KnownLayout, zerocopy::Immutable)]
#[repr(C)]
pub struct CompactVectorMeta {
    /// Number of integers stored.
    pub len: usize,
    /// Bit width for each integer.
    pub width: usize,
    /// Handle to the raw `u64` words backing the vector.
    pub handle: SectionHandle<u64>,
}

impl CompactVector {
    /// Creates a new builder storing integers in `width` bits and
    /// reserving space for at least `capa` integers.
    ///
    /// # Arguments
    ///
    ///  - `capa`: Number of elements reserved at least.
    ///  - `width`: Number of bits used to store an integer.
    ///
    /// # Errors
    ///
    /// An error is returned if `width` is not in `1..=64`.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::int_vectors::CompactVector;
    ///
    /// use anybytes::ByteArea;
    /// let mut area = ByteArea::new()?;
    /// let mut sections = area.sections();
    /// let cv = CompactVector::with_capacity(10, 3, &mut sections)?.freeze();
    ///
    /// assert_eq!(cv.len(), 0);
    /// assert_eq!(cv.width(), 3);
    /// assert_eq!(cv.capacity(), 0);
    /// # Ok(())
    /// # }
    /// ```
    pub fn with_capacity<'a>(
        capa: usize,
        width: usize,
        writer: &mut SectionWriter<'a>,
    ) -> Result<CompactVectorBuilder<'a>> {
        CompactVectorBuilder::with_capacity(capa, width, writer)
    }

    /// Creates a new vector storing an integer in `width` bits,
    /// which stores `len` values initialized by `val`.
    ///
    /// # Arguments
    ///
    ///  - `val`: Integer value.
    ///  - `len`: Number of elements.
    ///  - `width`: Number of bits used to store an integer.
    ///
    /// # Errors
    ///
    /// An error is returned if
    ///
    ///  - `width` is not in `1..=64`, or
    ///  - `val` cannot be represent in `width` bits.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::int_vectors::CompactVector;
    ///
    /// let mut cv = CompactVector::from_int(7, 2, 3)?;
    /// assert_eq!(cv.len(), 2);
    /// assert_eq!(cv.width(), 3);
    /// assert_eq!(cv.get_int(0), Some(7));
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_int(val: usize, len: usize, width: usize) -> Result<Self> {
        if !(1..=64).contains(&width) {
            return Err(Error::invalid_argument(format!(
                "width must be in 1..=64, but got {width}."
            )));
        }
        if width < 64 && val >> width != 0 {
            return Err(Error::invalid_argument(format!(
                "val must fit in width={width} bits, but got {val}."
            )));
        }
        let mut area = ByteArea::new().expect("byte area");
        let mut sections = area.sections();
        let mut builder = CompactVectorBuilder::with_capacity(len, width, &mut sections)?;
        for i in 0..len {
            builder.set_int(i, val)?;
        }
        Ok(builder.freeze())
    }

    /// Creates a new vector from a slice of integers `vals`.
    ///
    /// The width of each element automatically fits to the maximum value in `vals`.
    ///
    /// # Arguments
    ///
    ///  - `vals`: Slice of integers to be stored.
    ///
    /// # Errors
    ///
    /// An error is returned if `vals` contains an integer that cannot be cast to [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::int_vectors::CompactVector;
    ///
    /// let mut cv = CompactVector::from_slice(&[7, 2])?;
    /// assert_eq!(cv.len(), 2);
    /// assert_eq!(cv.width(), 3);
    /// assert_eq!(cv.get_int(0), Some(7));
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_slice<T>(vals: &[T]) -> Result<Self>
    where
        T: ToPrimitive,
    {
        if vals.is_empty() {
            return Ok(Self::default());
        }
        let mut max_int = 0;
        for x in vals {
            max_int = max_int.max(x.to_usize().ok_or_else(|| {
                Error::invalid_argument("vals must consist only of values castable into usize.")
            })?);
        }
        let mut area = ByteArea::new().expect("byte area");
        let mut sections = area.sections();
        let mut builder = CompactVectorBuilder::with_capacity(
            vals.len(),
            utils::needed_bits(max_int),
            &mut sections,
        )?;
        for (i, x) in vals.iter().enumerate() {
            builder.set_int(i, x.to_usize().unwrap())?;
        }
        Ok(builder.freeze())
    }

    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    ///
    /// # Arguments
    ///
    ///  - `pos`: Position.
    ///
    /// # Complexity
    ///
    /// Constant
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::int_vectors::CompactVector;
    ///
    /// let cv = CompactVector::from_slice(&[5, 256, 0])?;
    /// assert_eq!(cv.get_int(0), Some(5));
    /// assert_eq!(cv.get_int(1), Some(256));
    /// assert_eq!(cv.get_int(2), Some(0));
    /// assert_eq!(cv.get_int(3), None);
    /// # Ok(())
    /// # }
    pub fn get_int(&self, pos: usize) -> Option<usize> {
        self.chunks.get_bits(pos * self.width, self.width)
    }

    /// Sets the `pos`-th integer to `val`.

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::int_vectors::CompactVector;
    ///
    /// let cv = CompactVector::from_slice(&[5, 256, 0])?;
    /// let mut it = cv.iter();
    ///
    /// assert_eq!(it.next(), Some(5));
    /// assert_eq!(it.next(), Some(256));
    /// assert_eq!(it.next(), Some(0));
    /// assert_eq!(it.next(), None);
    /// # Ok(())
    /// # }
    /// ```
    pub const fn iter(&'_ self) -> Iter<'_> {
        Iter::new(self)
    }

    /// Collects all integers into a `Vec<usize>` for inspection.
    pub fn to_vec(&self) -> Vec<usize> {
        self.iter().collect()
    }

    /// Gets the number of integers.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the total number of integers it can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.len()
    }

    /// Gets the number of bits to represent an integer.
    #[inline(always)]
    pub const fn width(&self) -> usize {
        self.width
    }

    /// Serializes the vector into a [`Bytes`] buffer and accompanying metadata.
    /// Returns metadata describing this vector.
    pub fn metadata(&self) -> CompactVectorMeta {
        <Self as Serializable>::metadata(self)
    }

    /// Reconstructs the vector from zero-copy [`Bytes`] and its metadata.
    pub fn from_bytes(meta: CompactVectorMeta, bytes: Bytes) -> Result<Self> {
        <Self as Serializable>::from_bytes(meta, bytes)
    }
}

impl Serializable for CompactVector {
    type Meta = CompactVectorMeta;
    type Error = Error;

    fn metadata(&self) -> Self::Meta {
        CompactVectorMeta {
            len: self.len,
            width: self.width,
            handle: self.chunks.handle().expect("missing handle"),
        }
    }

    fn from_bytes(meta: Self::Meta, bytes: Bytes) -> Result<Self> {
        let data_len = meta
            .len
            .checked_mul(meta.width)
            .ok_or_else(|| Error::invalid_metadata("len * width overflowed"))?;
        let data = BitVectorData::from_bytes(
            BitVectorDataMeta {
                len: data_len,
                handle: meta.handle,
            },
            bytes,
        )?;
        let chunks = BitVector::new(data, NoIndex);
        Ok(Self {
            chunks,
            len: meta.len,
            width: meta.width,
        })
    }
}

impl Build for CompactVector {
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

impl NumVals for CompactVector {
    /// Returns the number of integers stored (just wrapping [`Self::len()`]).
    fn num_vals(&self) -> usize {
        self.len()
    }
}

impl Access for CompactVector {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds
    /// (just wrapping [`Self::get_int()`]).
    ///
    /// # Arguments
    ///
    ///  - `pos`: Position.
    ///
    /// # Complexity
    ///
    /// Constant
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use jerky::int_vectors::{CompactVector, Access};
    ///
    /// let cv = CompactVector::from_slice(&[5, 256, 0])?;
    /// assert_eq!(cv.access(0), Some(5));
    /// assert_eq!(cv.access(1), Some(256));
    /// assert_eq!(cv.access(2), Some(0));
    /// assert_eq!(cv.access(3), None);
    /// # Ok(())
    /// # }
    fn access(&self, pos: usize) -> Option<usize> {
        self.get_int(pos)
    }
}

/// Iterator for enumerating integers, created by [`CompactVector::iter()`].
pub struct Iter<'a> {
    cv: &'a CompactVector,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(cv: &'a CompactVector) -> Self {
        Self { cv, pos: 0 }
    }
}

impl Iterator for Iter<'_> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.cv.len() {
            let x = self.cv.access(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.cv.len(), Some(self.cv.len()))
    }
}

impl ExactSizeIterator for Iter<'_> {}

impl std::fmt::Debug for CompactVector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ints = vec![0; self.len()];
        for (i, b) in ints.iter_mut().enumerate() {
            *b = self.access(i).unwrap();
        }
        f.debug_struct("CompactVector")
            .field("ints", &ints)
            .field("len", &self.len)
            .field("width", &self.width)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_with_capacity_oob_0() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let e = CompactVector::with_capacity(0, 0, &mut sections);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("width must be in 1..=64, but got 0.".to_string())
        );
    }

    #[test]
    fn test_with_capacity_oob_65() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let e = CompactVector::with_capacity(0, 65, &mut sections);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("width must be in 1..=64, but got 65.".to_string())
        );
    }

    #[test]
    fn test_from_int_oob_0() {
        let e = CompactVector::from_int(0, 0, 0);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("width must be in 1..=64, but got 0.".to_string())
        );
    }

    #[test]
    fn test_from_int_oob_65() {
        let e = CompactVector::from_int(0, 0, 65);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("width must be in 1..=64, but got 65.".to_string())
        );
    }

    #[test]
    fn test_from_int_unfit() {
        let e = CompactVector::from_int(4, 0, 2);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("val must fit in width=2 bits, but got 4.".to_string())
        );
    }

    #[test]
    fn test_from_slice_uncastable() {
        let e = CompactVector::from_slice(&[u128::MAX]);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("vals must consist only of values castable into usize.".to_string())
        );
    }

    #[test]
    fn test_set_int_oob() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder = CompactVectorBuilder::with_capacity(1, 2, &mut sections).unwrap();
        let e = builder.set_int(1, 1);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("pos must be no greater than self.capacity()=1, but got 1.".to_string())
        );
    }

    #[test]
    fn test_set_int_unfit() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder = CompactVectorBuilder::with_capacity(1, 2, &mut sections).unwrap();
        let e = builder.set_int(0, 4);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("val must fit in self.width()=2 bits, but got 4.".to_string())
        );
    }

    #[test]
    fn test_set_ints_mismatch() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder = CompactVectorBuilder::with_capacity(2, 2, &mut sections).unwrap();
        let e = builder.set_ints(0..2, [1]);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("not enough values for the specified range".to_string())
        );
    }

    #[test]
    fn test_64b() {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut builder = CompactVectorBuilder::with_capacity(1, 64, &mut sections).unwrap();
        builder.set_int(0, 42).unwrap();
        builder.set_int(0, 334).unwrap();
        let cv = builder.freeze();
        assert_eq!(cv.get_int(0), Some(334));
    }

    #[test]
    fn test_64b_from_int() {
        let cv = CompactVector::from_int(42, 1, 64).unwrap();
        assert_eq!(cv.get_int(0), Some(42));
    }

    #[test]
    fn iter_collects() {
        let cv = CompactVector::from_slice(&[1, 2, 3]).unwrap();
        let collected: Vec<usize> = cv.iter().collect();
        assert_eq!(collected, vec![1, 2, 3]);
    }

    #[test]
    fn to_vec_collects() {
        let cv = CompactVector::from_slice(&[1, 2, 3]).unwrap();
        assert_eq!(cv.to_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn from_bytes_roundtrip() {
        let cv = CompactVector::from_slice(&[4, 5, 6]).unwrap();
        let meta = cv.metadata();
        let bytes = cv.chunks.data.words.clone().bytes();
        let other = CompactVector::from_bytes(meta, bytes).unwrap();
        assert_eq!(cv, other);
    }

    #[test]
    fn from_bytes_rejects_overflowing_metadata() {
        let cv = CompactVector::from_slice(&[1]).unwrap();
        let mut meta = cv.metadata();
        meta.len = usize::MAX;
        meta.width = 2;
        let bytes = cv.chunks.data.words.clone().bytes();

        let err = CompactVector::from_bytes(meta, bytes).unwrap_err();
        assert!(matches!(err, Error::InvalidMetadata(_)));
    }
}
