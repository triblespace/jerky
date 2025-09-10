use anybytes::ByteArea;
use jerky::bit_vector::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut area = ByteArea::new()?;
    let mut sections = area.sections();
    let mut builder = BitVectorBuilder::with_capacity(5, &mut sections)?;
    builder.set_bit(0, true)?;
    builder.set_bit(2, true)?;
    builder.set_bit(4, true)?;
    let bv = builder.freeze::<Rank9SelIndex>();

    assert_eq!(bv.num_bits(), 5);
    assert_eq!(bv.rank1(4), Some(2));
    assert_eq!(bv.select1(1), Some(2));
    Ok(())
}
