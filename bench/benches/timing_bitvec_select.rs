use std::time::Duration;

use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion, SamplingMode,
};
use jerky::bit_vector::{BitVector, BitVectorBuilder, NoIndex, Rank9SelIndex, Select};

const SAMPLE_SIZE: usize = 30;
const WARM_UP_TIME: Duration = Duration::from_secs(5);
const MEASURE_TIME: Duration = Duration::from_secs(10);

const SEED_BITS: u64 = 334;
const SEED_QUERIES: u64 = 114514;
const NUM_QUERIES: usize = 1000;

fn gen_random_bits(len: usize, p: f64, seed: u64) -> Vec<bool> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    (0..len).map(|_| rng.gen_bool(p)).collect()
}

fn gen_random_ints(len: usize, min: usize, max: usize, seed: u64) -> Vec<usize> {
    let mut rng = ChaChaRng::seed_from_u64(seed);
    (0..len).map(|_| rng.gen_range(min..=max)).collect()
}

fn count_ones(bits: &[bool]) -> usize {
    bits.iter().filter(|&&b| b).count()
}

fn run_queries<S: Select>(idx: &S, queries: &[usize]) {
    let mut sum = 0;
    for &q in queries {
        sum += idx.select1(q).unwrap();
    }
    if sum == 0 {
        panic!("Should not come.");
    }
}

fn perform_bitvec_select(group: &mut BenchmarkGroup<WallTime>, bits: &[bool], queries: &[usize]) {
    group.bench_function("jerky/BitVector", |b| {
        let mut builder = BitVectorBuilder::new();
        builder.extend_bits(bits.iter().cloned());
        let idx: BitVector<NoIndex> = builder.freeze();
        b.iter(|| run_queries(&idx, &queries));
    });

    group.bench_function("jerky/BitVector<Rank9SelIndex>", |b| {
        let mut builder = BitVectorBuilder::new();
        builder.extend_bits(bits.iter().cloned());
        let idx = builder.freeze::<Rank9SelIndex>();
        b.iter(|| run_queries(&idx, &queries));
    });
}

macro_rules! criterion_common {
    ($name:ident, $dens:expr, $size:expr) => {
        fn $name(c: &mut Criterion) {
            let mut group =
                c.benchmark_group(format!("timing_bitvec_select/p{}/n{}", $dens, $size));
            group.sample_size(SAMPLE_SIZE);
            group.warm_up_time(WARM_UP_TIME);
            group.measurement_time(MEASURE_TIME);
            group.sampling_mode(SamplingMode::Flat);

            let bits = gen_random_bits($size, $dens as f64 / 100.0, SEED_BITS);
            let queries = gen_random_ints(NUM_QUERIES, 0, count_ones(&bits) - 1, SEED_QUERIES);

            perform_bitvec_select(&mut group, &bits, &queries);
        }
    };
}

criterion_common!(criterion_select_p50_n1000, 50, 1000);
criterion_common!(criterion_select_p10_n1000, 10, 1000);
criterion_common!(criterion_select_p1_n1000, 1, 1000);
criterion_common!(criterion_select_p50_n1000000, 50, 1000000);
criterion_common!(criterion_select_p10_n1000000, 10, 1000000);
criterion_common!(criterion_select_p1_n1000000, 1, 1000000);

criterion_group!(
    benches,
    criterion_select_p50_n1000,
    criterion_select_p10_n1000,
    criterion_select_p1_n1000,
    criterion_select_p50_n1000000,
    criterion_select_p10_n1000000,
    criterion_select_p1_n1000000,
);

criterion_main!(benches);
