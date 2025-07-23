use jerky::bit_vector::Rank9SelIndex;
use jerky::char_sequences::WaveletMatrix;
use jerky::int_vectors::CompactVectorBuilder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let text = "banana";
    let mut builder = CompactVectorBuilder::new(8)?;
    builder.extend(text.chars().map(|c| c as usize))?;
    let wm = WaveletMatrix::<Rank9SelIndex>::new(builder.freeze())?;

    assert_eq!(wm.len(), text.len());
    assert_eq!(wm.access(2), Some('n' as usize));
    assert_eq!(wm.rank(4, 'a' as usize), Some(2));
    assert_eq!(wm.select(1, 'n' as usize), Some(4));
    Ok(())
}
