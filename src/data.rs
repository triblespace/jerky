//! Raw storage types for bit and integer sequences.

/// Immutable bit vector data without auxiliary indexes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitVectorData {
    /// Underlying machine words storing bit data.
    pub words: Vec<usize>,
    /// Number of valid bits in `words`.
    pub len: usize,
}

impl BitVectorData {
    /// Creates bit vector data from a bit iterator.
    pub fn from_bits<I: IntoIterator<Item = bool>>(bits: I) -> Self {
        let mut words = Vec::new();
        let mut len = 0usize;
        let mut cur = 0usize;
        let mut shift = 0usize;
        for b in bits {
            if shift == usize::BITS as usize {
                words.push(cur);
                cur = 0;
                shift = 0;
            }
            if b {
                cur |= 1usize << shift;
            }
            shift += 1;
            len += 1;
        }
        if shift != 0 {
            words.push(cur);
        }
        Self { words, len }
    }

    /// Returns the number of bits stored.
    pub const fn len(&self) -> usize {
        self.len
    }
}

/// Immutable integer vector data without auxiliary indexes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntVectorData {
    /// Stored integers in raw form.
    pub ints: Vec<usize>,
}

impl IntVectorData {
    /// Creates integer vector data from a slice of values.
    pub fn from_slice<T: num_traits::ToPrimitive>(vals: &[T]) -> anyhow::Result<Self> {
        let mut ints = Vec::with_capacity(vals.len());
        for v in vals {
            ints.push(
                v.to_usize()
                    .ok_or_else(|| anyhow::anyhow!("vals must be castable"))?,
            );
        }
        Ok(Self { ints })
    }

    /// Returns the number of integers stored.
    pub const fn len(&self) -> usize {
        self.ints.len()
    }
}
