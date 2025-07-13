//! Rank9/Select index implementation.
pub mod inner;

use crate::bit_vectors::data::{BitVectorData, IndexBuilder};
use inner::{Rank9SelIndex, Rank9SelIndexBuilder};

impl IndexBuilder for Rank9SelIndex {
    type Built = Rank9SelIndex;

    fn build(data: &BitVectorData) -> Self::Built {
        Rank9SelIndexBuilder::from_data(data)
            .select1_hints()
            .select0_hints()
            .build()
    }
}
