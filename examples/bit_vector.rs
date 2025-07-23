use jerky::bit_vector::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut builder = BitVectorBuilder::new();
    builder.extend_bits([true, false, true, false, true]);
    let bv = builder.freeze::<Rank9SelIndex>();

    assert_eq!(bv.num_bits(), 5);
    assert_eq!(bv.rank1(4), Some(2));
    assert_eq!(bv.select1(1), Some(2));
    Ok(())
}
