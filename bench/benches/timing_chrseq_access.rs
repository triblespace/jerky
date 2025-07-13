use std::time::Duration;

use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

use jerky::bit_vectors::darray::inner::DArrayFullIndex;
use jerky::bit_vectors::data::BitVectorBuilder;
use jerky::bit_vectors::prelude::*;
use jerky::bit_vectors::rank9sel::inner::Rank9SelIndex;
use jerky::bit_vectors::{BitVector, NoIndex};
use jerky::char_sequences::WaveletMatrix;
use jerky::int_vectors::CompactVector;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion, SamplingMode,
};

const SAMPLE_SIZE: usize = 30;
const WARM_UP_TIME: Duration = Duration::from_secs(5);
const MEASURE_TIME: Duration = Duration::from_secs(10);

const SEED_QUERIES: u64 = 114514;
const NUM_QUERIES: usize = 1000;

const DBLP_PSEF_STR: &str = include_str!("../data/texts/dblp.1MiB.txt");
const DNA_PSEF_STR: &str = include_str!("../data/texts/dna.1MiB.txt");
const PROTEINS_PSEF_STR: &str = include_str!("../data/texts/proteins.1MiB.txt");

// In effective alphabet
fn load_text(s: &str) -> CompactVector {
    let mut text = s.as_bytes().to_vec();
    let mut builder = BitVectorBuilder::new();
    builder.extend_bits(core::iter::repeat(false).take(256));
    for &c in &text {
        builder.set_bit(c as usize, true).unwrap();
    }
    let alphabet: BitVector<NoIndex> = builder.freeze();
    for i in 0..text.len() {
        text[i] = alphabet.rank1(text[i] as usize).unwrap() as u8;
    }
    CompactVector::from_slice(&text).unwrap()
}

fn gen_random_ints(len: usize, min: usize, max: usize, seed: u64) -> Vec<usize> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    (0..len).map(|_| rng.gen_range(min..max)).collect()
}

fn criterion_chrseq_access_dblp(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_chrseq_access_dblp_1MiB");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let text = load_text(DBLP_PSEF_STR);
    perform_chrseq_access(&mut group, &text);
}

fn criterion_chrseq_access_dna(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_chrseq_access_dna_1MiB");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let text = load_text(DNA_PSEF_STR);
    perform_chrseq_access(&mut group, &text);
}

fn criterion_chrseq_access_proteins(c: &mut Criterion) {
    let mut group = c.benchmark_group("timing_chrseq_access_proteins_1MiB");
    group.sample_size(SAMPLE_SIZE);
    group.warm_up_time(WARM_UP_TIME);
    group.measurement_time(MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);

    let text = load_text(PROTEINS_PSEF_STR);
    perform_chrseq_access(&mut group, &text);
}

fn run_queries<I>(idx: &WaveletMatrix<I>, queries: &[usize])
where
    I: BitVectorIndex + IndexBuilder<Built = I>,
{
    let mut sum = 0;
    for &q in queries {
        sum += idx.access(q).unwrap();
    }
    if sum == 0 {
        panic!("Should not come.");
    }
}

fn perform_chrseq_access(group: &mut BenchmarkGroup<WallTime>, text: &CompactVector) {
    let queries = gen_random_ints(NUM_QUERIES, 0, text.len(), SEED_QUERIES);

    group.bench_function("jerky/WaveletMatrix<Rank9SelIndex>", |b| {
        let idx = WaveletMatrix::<Rank9SelIndex>::new(text.clone()).unwrap();
        b.iter(|| run_queries(&idx, &queries));
    });

    group.bench_function("jerky/WaveletMatrix<DArrayFullIndex>", |b| {
        let idx = WaveletMatrix::<DArrayFullIndex>::new(text.clone()).unwrap();
        b.iter(|| run_queries(&idx, &queries));
    });
}

criterion_group!(
    benches,
    criterion_chrseq_access_dblp,
    criterion_chrseq_access_dna,
    criterion_chrseq_access_proteins
);

criterion_main!(benches);
