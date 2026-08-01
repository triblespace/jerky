//! Deterministic latency profile for `WaveletMatrix::rank_range_batch_into`.
//!
//! The timed region contains only a sequence of batch calls over precomputed
//! ranges and values. Run control and candidate binaries in an interleaved
//! order; each output line is one raw sample in nanoseconds per probe.
//!
//! Run:
//! `cargo run --release --example rank_range_batch_profile -- [n] [alphabet_bits] [probes] [batch] [span] [samples]`

use std::time::Instant;

use anybytes::ByteArea;
use jerky::bit_vector::Rank9SelIndex;
use jerky::char_sequences::WaveletMatrix;

struct Rng(u64);

impl Rng {
    #[inline(always)]
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
}

fn arg(args: &mut impl Iterator<Item = String>, name: &str, default: usize) -> usize {
    args.next()
        .map(|value| value.parse().unwrap_or_else(|_| panic!("invalid {}", name)))
        .unwrap_or(default)
}

fn run(
    wm: &WaveletMatrix<Rank9SelIndex>,
    ranges: &[(usize, usize)],
    values: &[usize],
    out: &mut [Option<usize>],
    batch: usize,
) {
    for (batch_index, chunk) in values.chunks(batch).enumerate() {
        let lo = batch_index * batch;
        let hi = lo + chunk.len();
        let (start, end) = ranges[batch_index];
        wm.rank_range_batch_into(start..end, chunk, &mut out[lo..hi])
            .unwrap();
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let n = arg(&mut args, "n", 8_000_000);
    let alphabet_bits = arg(&mut args, "alphabet_bits", 24);
    let probes = arg(&mut args, "probes", 262_144);
    let batch = arg(&mut args, "batch", 64);
    let span = arg(&mut args, "span", 4_096);
    let samples = arg(&mut args, "samples", 9);

    assert!(n > 0, "n must be nonzero");
    assert!(alphabet_bits < usize::BITS as usize);
    assert!(batch > 0, "batch must be nonzero");
    assert!(span > 0 && span <= n, "span must be in 1..=n");

    let alphabet_size = 1usize << alphabet_bits;
    let mut area = ByteArea::new()?;
    let mut sections = area.sections();
    let mut build_rng = Rng(0x1234_5678_9abc_def0);
    let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
        alphabet_size,
        (0..n).map(|_| (build_rng.next() as usize) & (alphabet_size - 1)),
        &mut sections,
    )?;

    let num_batches = probes.div_ceil(batch);
    let mut query_rng = Rng(0x0bad_c0de_0bad_c0de);
    let values: Vec<usize> = (0..probes)
        .map(|_| (query_rng.next() as usize) & (alphabet_size - 1))
        .collect();
    let ranges: Vec<(usize, usize)> = (0..num_batches)
        .map(|_| {
            let start = (query_rng.next() as usize) % (n - span + 1);
            (start, start + span)
        })
        .collect();
    let mut out = vec![None; probes];

    println!(
        "# n={n} alphabet_bits={alphabet_bits} probes={probes} batch={batch} span={span} samples={samples} layers={}",
        wm.alph_width()
    );

    // Warm page tables, code, and the output allocation outside measurement.
    run(&wm, &ranges, &values, &mut out, batch);
    std::hint::black_box(&out);

    for sample in 0..samples {
        let started = Instant::now();
        run(&wm, &ranges, &values, &mut out, batch);
        let elapsed = started.elapsed();
        std::hint::black_box(&out);
        let checksum = out
            .iter()
            .fold(0usize, |sum, answer| sum.wrapping_add(answer.unwrap_or(0)));
        println!(
            "sample={sample} elapsed_ns={} ns_per_probe={:.6} checksum={checksum}",
            elapsed.as_nanos(),
            elapsed.as_nanos() as f64 / probes as f64
        );
    }

    // Scalar parity is deliberately after all timing samples.
    for (batch_index, chunk) in values.chunks(batch).enumerate() {
        let lo = batch_index * batch;
        let (start, end) = ranges[batch_index];
        for (offset, &value) in chunk.iter().enumerate() {
            assert_eq!(
                out[lo + offset],
                wm.rank_range(start..end, value),
                "batch/scalar mismatch at probe {}",
                lo + offset
            );
        }
    }
    println!("parity=ok");

    Ok(())
}
