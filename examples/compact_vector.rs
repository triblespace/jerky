use jerky::int_vectors::CompactVectorBuilder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Build a vector storing integers within 3 bits each.
    let mut builder = CompactVectorBuilder::new(3)?;
    builder.extend([7, 2, 5])?;
    let cv = builder.freeze();

    assert_eq!(cv.len(), 3);
    assert_eq!(cv.get_int(0), Some(7));
    assert_eq!(cv.get_int(2), Some(5));
    Ok(())
}
