use jerky::bit_vectors::data::BitVectorBuilder;
use jerky::bit_vectors::Rank;
use jerky::int_vectors::CompactVector;

const DBLP_PSEF_STR: &str = include_str!("../data/texts/dblp.1MiB.txt");
const DNA_PSEF_STR: &str = include_str!("../data/texts/dna.1MiB.txt");
const PROTEINS_PSEF_STR: &str = include_str!("../data/texts/proteins.1MiB.txt");

fn main() {
    show_memories("dblp", &load_text(DBLP_PSEF_STR));
    show_memories("dna", &load_text(DNA_PSEF_STR));
    show_memories("proteins", &load_text(PROTEINS_PSEF_STR));
}

// In effective alphabet
fn load_text(s: &str) -> CompactVector {
    let mut text = s.as_bytes().to_vec();
    let mut builder = BitVectorBuilder::new();
    builder.extend_bits(core::iter::repeat(false).take(256));
    for &c in &text {
        builder.set_bit(c as usize, true).unwrap();
    }
    let alphabet: jerky::bit_vectors::BitVector<jerky::bit_vectors::NoIndex> =
        builder.freeze::<jerky::bit_vectors::NoIndex>();
    for i in 0..text.len() {
        text[i] = alphabet.rank1(text[i] as usize).unwrap() as u8;
    }
    CompactVector::from_slice(&text).unwrap()
}

fn show_memories(title: &str, text: &CompactVector) {
    println!("[{title}]");
    show_data_stats(text);

    let bytes = {
        let idx =
            jerky::char_sequences::WaveletMatrix::<jerky::bit_vectors::Rank9Sel>::new(text.clone())
                .unwrap();
        idx.size_in_bytes()
    };
    print_memory("WaveletMatrix<Rank9Sel>", bytes, text.len());

    let bytes = {
        let idx =
            jerky::char_sequences::WaveletMatrix::<jerky::bit_vectors::DArray>::new(text.clone())
                .unwrap();
        idx.size_in_bytes()
    };
    print_memory("WaveletMatrix<DArray>", bytes, text.len());
}

fn show_data_stats(text: &CompactVector) {
    let nvals = text.len();
    let alph_size = text.iter().max().unwrap() + 1;
    println!("Basic: n_vals={nvals}, alph_size={alph_size}");
}

fn print_memory(name: &str, bytes: usize, nvals: usize) {
    println!(
        "{}: {:.3} bits per value",
        name,
        (bytes * 8) as f64 / nvals as f64
    );
}
