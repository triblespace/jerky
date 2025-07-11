use jerky::bit_vectors::data::BitVectorBuilder;
use jerky::bit_vectors::Build;
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
        let mut b = BitVectorBuilder::new();
        b.extend_bits(bits.iter().cloned());
        let idx: jerky::bit_vectors::BitVector<jerky::bit_vectors::rank9sel::inner::Rank9SelIndex> =
            b.freeze::<jerky::bit_vectors::rank9sel::inner::Rank9SelIndexBuilder>();
        idx.data.size_in_bytes() + idx.index.size_in_bytes()
    };
    print_memory("BitVector<Rank9SelIndex>", bytes);

    let bytes = {
        let idx = jerky::bit_vectors::BitVector::<
            jerky::bit_vectors::rank9sel::inner::Rank9SelIndex,
        >::build_from_bits(bits.iter().cloned(), false, true, true)
        .unwrap();
        idx.data.size_in_bytes() + idx.index.size_in_bytes()
    };
    print_memory("BitVector<Rank9SelIndex> (with select hints)", bytes);

    let bytes = {
        let mut b = BitVectorBuilder::new();
        b.extend_bits(bits.iter().cloned());
        let idx: jerky::bit_vectors::BitVector<jerky::bit_vectors::darray::inner::DArrayFullIndex> =
            b.freeze::<jerky::bit_vectors::darray::inner::DArrayFullIndexBuilder>();
        idx.data.size_in_bytes() + idx.index.size_in_bytes()
    };
    print_memory("BitVector<DArrayFullIndex>", bytes);

    let bytes = {
        let mut b = BitVectorBuilder::new();
        b.extend_bits(bits.iter().cloned());
        let idx: jerky::bit_vectors::BitVector<jerky::bit_vectors::darray::inner::DArrayFullIndex> =
            b.freeze::<jerky::bit_vectors::darray::inner::DArrayFullIndexBuilder>();
        let r9 = jerky::bit_vectors::rank9sel::inner::Rank9SelIndex::new(&idx.data);
        idx.data.size_in_bytes() + idx.index.size_in_bytes() + r9.size_in_bytes()
    };
    print_memory("BitVector<DArrayFullIndex> (with rank index)", bytes);
}

fn print_memory(name: &str, bytes: usize) {
    println!(
        "{}: {:.3} bits per bit",
        name,
        (bytes * 8) as f64 / NUM_BITS as f64
    );
}
