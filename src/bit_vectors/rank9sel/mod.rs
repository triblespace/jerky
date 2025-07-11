//! Rank9/Select index implementation.
pub mod inner;

use anyhow::Result;

use crate::bit_vectors::data::{BitVector, BitVectorBuilder};
use crate::bit_vectors::{Build, NoIndex};
use inner::{Rank9SelIndex, Rank9SelIndexBuilder};

impl Build for BitVector<Rank9SelIndex> {
    fn build_from_bits<I>(
        bits: I,
        _with_rank: bool,
        with_select1: bool,
        with_select0: bool,
    ) -> Result<Self>
    where
        I: IntoIterator<Item = bool>,
        Self: Sized,
    {
        let mut bvb = BitVectorBuilder::new();
        bvb.extend_bits(bits);
        let BitVector { data, .. }: BitVector<NoIndex> = bvb.freeze::<NoIndex>();
        let mut builder = Rank9SelIndexBuilder::from_data(&data);
        if with_select1 {
            builder = builder.select1_hints();
        }
        if with_select0 {
            builder = builder.select0_hints();
        }
        let rs = builder.build();
        Ok(BitVector::new(data, rs))
    }
}
