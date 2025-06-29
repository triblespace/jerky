//! Builder for [`Rank9Sel`](super::Rank9Sel).
//! This structure enables streaming construction of a `Rank9Sel`
//! while bits are pushed incrementally.

use super::inner::Rank9SelIndexBuilder;
use super::Rank9Sel;
use crate::bit_vectors::BitVector;
use crate::builder::Builder;

/// Builder type for [`Rank9Sel`].
#[derive(Debug, Clone, Default)]
pub struct Rank9SelBuilder<const SELECT1: bool = false, const SELECT0: bool = false> {
    bv: BitVector,
    idx: Rank9SelIndexBuilder<SELECT1, SELECT0>,
}

impl<const SELECT1: bool, const SELECT0: bool> Builder for Rank9SelBuilder<SELECT1, SELECT0> {
    type Item = bool;
    type Build = Rank9Sel;

    fn push(&mut self, item: Self::Item) -> anyhow::Result<()> {
        self.push_bit(item);
        Ok(())
    }

    fn extend<I>(&mut self, iter: I) -> anyhow::Result<()>
    where
        I: IntoIterator<Item = Self::Item>,
    {
        Rank9SelBuilder::extend(self, iter);
        Ok(())
    }

    fn build(self) -> Self::Build {
        self.build()
    }
}

impl Rank9SelBuilder {
    /// Creates a new streaming builder without select hints.
    pub fn new() -> Self {
        Self::new_stream()
    }
}

impl<const SELECT1: bool, const SELECT0: bool> Rank9SelBuilder<SELECT1, SELECT0> {
    /// Creates a new empty streaming builder.
    pub fn new_stream() -> Self {
        Self {
            bv: BitVector::new(),
            idx: Rank9SelIndexBuilder::<SELECT1, SELECT0>::new_stream(),
        }
    }

    /// Creates a builder initialized from an existing [`BitVector`].
    pub fn from_bitvec(bv: BitVector) -> Self {
        let idx = Rank9SelIndexBuilder::<SELECT1, SELECT0>::new_generic(&bv);
        Self { bv, idx }
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
        self.idx.push_bit(bit);
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

    /// Finalizes the builder and returns the constructed [`Rank9Sel`].
    pub fn build(self) -> Rank9Sel {
        let rs = self.idx.build();
        Rank9Sel { bv: self.bv, rs }
    }
}
