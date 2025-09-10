use anybytes::ByteArea;
use jerky::bit_vector::{BitVector, BitVectorBuilder, Rank9SelIndex};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

const SEED_BITS: u64 = 113;
const NUM_BITS: usize = 1 << 20;

fn main() {
    show_memories(0.5);
    show_memories(0.1);
    show_memories(0.01);
}

fn gen_random_bits(len: usize, p: f64, seed: u64) -> Vec<bool> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    (0..len).map(|_| rng.gen_bool(p)).collect()
}

fn show_memories(p: f64) {
    let bits = gen_random_bits(NUM_BITS, p, SEED_BITS);
    println!("[p = {p}]");

    let bytes = {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut b = BitVectorBuilder::with_capacity(bits.len(), &mut sections).unwrap();
        for (i, &bv) in bits.iter().enumerate() {
            b.set_bit(i, bv).unwrap();
        }
        let idx: BitVector<Rank9SelIndex> = b.freeze::<Rank9SelIndex>();
        let len = idx.data.len;
        let data_bytes = idx.data.words.bytes();
        data_bytes.as_ref().len() + std::mem::size_of_val(&len)
    };
    print_memory("BitVector<Rank9SelIndex>", bytes);

    let bytes = {
        let mut area = ByteArea::new().unwrap();
        let mut sections = area.sections();
        let mut b = BitVectorBuilder::with_capacity(bits.len(), &mut sections).unwrap();
        for (i, &bv) in bits.iter().enumerate() {
            b.set_bit(i, bv).unwrap();
        }
        let idx: BitVector<Rank9SelIndex> = b.freeze::<Rank9SelIndex>();
        let len = idx.data.len;
        let data_bytes = idx.data.words.bytes();
        data_bytes.as_ref().len() + std::mem::size_of_val(&len)
    };
    print_memory("BitVector<Rank9SelIndex> (with select hints)", bytes);
}

fn print_memory(name: &str, bytes: usize) {
    println!(
        "{}: {:.3} bits per bit",
        name,
        (bytes * 8) as f64 / NUM_BITS as f64
    );
}
