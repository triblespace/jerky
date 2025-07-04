//! Raw storage types for integer sequences.

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
