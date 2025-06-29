use anyhow::Result;

use super::inner::DArrayIndexBuilder;
use super::DArray;
use crate::bit_vectors::rank9sel::inner::Rank9SelIndex;
use crate::bit_vectors::BitVector;
use crate::builder::Builder;

/// Streaming builder for [`DArray`](super::DArray).
#[derive(Debug, Default, Clone)]
pub struct DArrayBuilder<const RANK: bool = false, const SELECT0: bool = false> {
    bv: BitVector,
}

impl DArrayBuilder {
    /// Creates a new builder without optional indexes.
    pub fn new() -> Self {
        Self::new_stream()
    }
}

impl<const RANK: bool, const SELECT0: bool> DArrayBuilder<RANK, SELECT0> {
    /// Creates an empty streaming builder.
    pub fn new_stream() -> Self {
        Self {
            bv: BitVector::new(),
        }
    }

    /// Creates a builder from an existing [`BitVector`].
    pub fn from_bitvec(bv: BitVector) -> Self {
        Self { bv }
    }

    /// Creates a builder from a bit iterator.
    pub fn from_bits<I>(bits: I) -> Self
    where
        I: IntoIterator<Item = bool>,
    {
        let mut b = Self::new_stream();
        b.extend(bits);
        b
    }

    /// Pushes a bit for streaming construction.
    pub fn push_bit(&mut self, bit: bool) {
        self.bv.push_bit(bit);
    }

    /// Extends bits from an iterator.
    pub fn extend<I>(&mut self, bits: I)
    where
        I: IntoIterator<Item = bool>,
    {
        for bit in bits {
            self.push_bit(bit);
        }
    }

    /// Finalizes the builder and returns the constructed [`DArray`].
    pub fn build(self) -> DArray {
        let s1 = DArrayIndexBuilder::new(&self.bv, true).build();
        let s0 = if SELECT0 {
            Some(DArrayIndexBuilder::new(&self.bv, false).build())
        } else {
            None
        };
        let r9 = if RANK {
            Some(Rank9SelIndex::new(&self.bv))
        } else {
            None
        };
        DArray {
            bv: self.bv,
            s1,
            s0,
            r9,
        }
    }
}

impl<const RANK: bool, const SELECT0: bool> Builder for DArrayBuilder<RANK, SELECT0> {
    type Item = bool;
    type Build = DArray;

    fn push(&mut self, item: Self::Item) -> Result<()> {
        self.push_bit(item);
        Ok(())
    }

    fn extend<I>(&mut self, iter: I) -> Result<()>
    where
        I: IntoIterator<Item = Self::Item>,
    {
        DArrayBuilder::extend(self, iter);
        Ok(())
    }

    fn build(self) -> Self::Build {
        self.build()
    }
}
