use anybytes::ByteArea;
use jerky::bit_vector::Rank9SelIndex;
use jerky::int_vectors::{Access, DacsByte};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut area = ByteArea::new()?;
    let mut writer = area.sections();
    let seq = DacsByte::<Rank9SelIndex>::from_slice(&[5, 0, 100000, 334], &mut writer)?;
    let meta = seq.metadata();
    let bytes = area.freeze()?;
    let view = DacsByte::<Rank9SelIndex>::from_bytes(meta, bytes.clone())?;

    assert_eq!(view.access(2), Some(100000));
    assert_eq!(seq, view);
    Ok(())
}
