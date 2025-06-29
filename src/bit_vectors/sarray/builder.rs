use anyhow::Result;

use super::SArray;
use crate::bit_vectors::BitVector;
use crate::broadword;
use crate::builder::Builder;
use crate::mii_sequences::EliasFanoBuilder;

/// Streaming builder for [`SArray`](super::SArray).
#[derive(Debug, Default, Clone)]
pub struct SArrayBuilder<const RANK: bool = false> {
    bv: BitVector,
}

impl SArrayBuilder {
    /// Creates a new builder without rank support.
    pub fn new() -> Self {
        Self::new_stream()
    }
}

impl<const RANK: bool> SArrayBuilder<RANK> {
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

    /// Finalizes the builder and returns the constructed [`SArray`].
    pub fn build(self) -> SArray {
        let num_bits = self.bv.len();
        let num_ones = (0..self.bv.num_words())
            .fold(0, |acc, i| acc + broadword::popcount(self.bv.words()[i]));
        let ef = if num_ones != 0 {
            let mut b = EliasFanoBuilder::new(num_bits, num_ones).unwrap();
            for i in self.bv.unary_iter(0) {
                b.push(i).unwrap();
            }
            Some(b.build())
        } else {
            None
        };
        let mut sa = SArray {
            ef,
            num_bits,
            num_ones,
            has_rank: false,
        };
        if RANK {
            sa = sa.enable_rank();
        }
        sa
    }
}

impl<const RANK: bool> Builder for SArrayBuilder<RANK> {
    type Item = bool;
    type Build = SArray;

    fn push(&mut self, item: Self::Item) -> Result<()> {
        self.push_bit(item);
        Ok(())
    }

    fn extend<I>(&mut self, iter: I) -> Result<()>
    where
        I: IntoIterator<Item = Self::Item>,
    {
        SArrayBuilder::extend(self, iter);
        Ok(())
    }

    fn build(self) -> Self::Build {
        self.build()
    }
}
