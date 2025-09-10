use anybytes::ByteArea;
use jerky::bit_vector::Rank9SelIndex;
use jerky::char_sequences::{WaveletMatrix, WaveletMatrixBuilder};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let text = "banana";
    let alph_size = ('n' as usize) + 1;
    let mut area = ByteArea::new()?;
    let mut sections = area.sections();
    let ints: Vec<usize> = text.chars().map(|c| c as usize).collect();
    let mut builder = WaveletMatrixBuilder::with_capacity(alph_size, ints.len(), &mut sections)?;
    for (i, &x) in ints.iter().enumerate() {
        builder.set_int(i, x)?;
    }
    let wm: WaveletMatrix<Rank9SelIndex> = builder.freeze()?;
    let meta = wm.metadata();
    let bytes = area.freeze()?;
    let view = WaveletMatrix::<Rank9SelIndex>::from_bytes(meta, bytes.clone())?;

    assert_eq!(view.len(), text.len());
    assert_eq!(view.access(2), Some('n' as usize));
    assert_eq!(view.rank(4, 'a' as usize), Some(2));
    assert_eq!(view.select(1, 'n' as usize), Some(4));
    Ok(())
}
