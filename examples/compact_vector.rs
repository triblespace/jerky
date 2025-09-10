use anybytes::ByteArea;
use jerky::int_vectors::{CompactVector, CompactVectorBuilder};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Build a vector storing integers within 3 bits each.
    let mut area = ByteArea::new()?;
    let mut sections = area.sections();
    let mut builder = CompactVectorBuilder::with_capacity(3, 3, &mut sections)?;
    builder.set_ints(0..3, [7, 2, 5])?;
    let cv = builder.freeze();
    let meta = cv.metadata();
    let bytes = area.freeze()?;
    let view = CompactVector::from_bytes(meta, bytes.clone())?;

    assert_eq!(view.len(), 3);
    assert_eq!(view.get_int(0), Some(7));
    assert_eq!(view.get_int(2), Some(5));
    Ok(())
}
