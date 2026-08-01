//! Phase 1 profile: is `WaveletMatrix::rank` ALU-bound or memory-bound?
//!
//! The experiment is a **working-set sweep at fixed alphabet width**.
//! `rank(pos, val)` walks `alph_width()` layers and does exactly two
//! `rank1` ops per layer regardless of `n`, so holding `alph_bits`
//! constant while varying `n` holds the *instruction count per probe*
//! constant and varies only the *footprint*. Any change in ns/probe is
//! therefore attributable to the memory hierarchy alone — no counter
//! access required, and no way for an ALU effect to masquerade as a
//! cache effect.
//!
//! Run: `cargo run --release --example rank_profile -- [alph_bits] [probes]`

use std::time::Instant;

use anybytes::ByteArea;
use jerky::bit_vector::Rank9SelIndex;
use jerky::char_sequences::WaveletMatrix;

/// xorshift64* — a deterministic, inlinable generator so probe
/// generation never shows up as the thing being measured.
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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let alph_bits: usize = args
        .next()
        .map(|a| a.parse().expect("alph_bits"))
        .unwrap_or(24);
    let probes: usize = args
        .next()
        .map(|a| a.parse().expect("probes"))
        .unwrap_or(200_000);

    let alph_size = 1usize << alph_bits;

    println!("# rank_profile: alph_bits={alph_bits} probes={probes}");
    println!("# layers (alph_width) is constant across every row below,");
    println!("# so instructions/probe is constant and only footprint varies.");
    println!();
    println!(
        "{:>12}  {:>10}  {:>12}  {:>12}  {:>8}  {:>6}",
        "n", "MiB", "scalar ns", "batch ns", "speedup", "layers"
    );

    // Sizes chosen to straddle the M4 Max hierarchy: 64 KiB L1d,
    // 4 MiB L2, 16 MiB cluster L2, then DRAM.
    let sizes: Vec<usize> = vec![
        16_000,     // ~60 KiB  — L1-resident
        128_000,    // ~480 KiB — L2-resident
        1_000_000,  // ~3.7 MiB — L2-resident
        8_000_000,  // ~30 MiB  — beyond cluster L2
        40_000_000, // ~150 MiB — DRAM
    ];

    for n in sizes {
        let mut area = ByteArea::new()?;
        let mut sections = area.sections();
        let mut build_rng = Rng(0x1234_5678_9abc_def0);
        let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
            alph_size,
            (0..n).map(|_| (build_rng.next() as usize) & (alph_size - 1)),
            &mut sections,
        )?;

        // Footprint: every layer's bits plus its rank/select index.
        let layers = wm.alph_width();
        // n bits of payload + rank9 index (2 usize per 512 bits) per layer,
        // which is what the sweep is actually walking.
        let bytes = layers * (n / 8 + (n / 512) * 16);

        // Probe streams are precomputed so the timed region contains
        // only the rank descent.
        let mut rng = Rng(0xdead_beef_cafe_babe);
        let pos: Vec<usize> = (0..probes).map(|_| (rng.next() as usize) % n).collect();
        let val: Vec<usize> = (0..probes)
            .map(|_| (rng.next() as usize) & (alph_size - 1))
            .collect();

        // Warm the structure so the first row is not measuring page faults.
        let mut sink = 0usize;
        for i in 0..probes.min(20_000) {
            sink = sink.wrapping_add(wm.rank(pos[i], val[i]).unwrap_or(0));
        }

        let t = Instant::now();
        for i in 0..probes {
            sink = sink.wrapping_add(wm.rank(pos[i], val[i]).unwrap_or(0));
        }
        let scalar = t.elapsed();
        std::hint::black_box(sink);

        // Mechanism (b) in isolation: identical arithmetic, identical
        // number of rank ops, only the traversal order differs.
        let mut out = vec![None; probes];
        let w = probes.min(20_000);
        wm.rank_batch_into(&pos[..w], &val[..w], &mut out[..w])
            .unwrap();
        let t = Instant::now();
        wm.rank_batch_into(&pos, &val, &mut out).unwrap();
        let batch = t.elapsed();
        std::hint::black_box(&out);

        // The two arms must agree, or the speedup is meaningless.
        for i in 0..probes {
            assert_eq!(
                out[i],
                wm.rank(pos[i], val[i]),
                "batch/scalar mismatch at {i}"
            );
        }

        let scalar_ns = scalar.as_nanos() as f64 / probes as f64;
        let batch_ns = batch.as_nanos() as f64 / probes as f64;
        println!(
            "{:>12}  {:>10.1}  {:>12.1}  {:>12.1}  {:>7.2}x  {:>6}",
            n,
            bytes as f64 / (1024.0 * 1024.0),
            scalar_ns,
            batch_ns,
            scalar_ns / batch_ns,
            layers
        );
    }

    // ---------------------------------------------------------------
    // Where is the crossover? A confirm region's median size is ONE
    // candidate, so a batch tier that only pays above some size must know
    // that size. Same DRAM-resident structure, same total probe count,
    // varying only how many probes are handed over per call.
    // ---------------------------------------------------------------
    println!();
    println!("# batch-size sweep (n=8000000, DRAM-resident, {probes} probes total)");
    println!(
        "{:>12}  {:>12}  {:>12}  {:>8}",
        "batch", "scalar ns", "batch ns", "speedup"
    );

    let n = 8_000_000usize;
    let mut area = ByteArea::new()?;
    let mut sections = area.sections();
    let mut build_rng = Rng(0x1234_5678_9abc_def0);
    let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
        alph_size,
        (0..n).map(|_| (build_rng.next() as usize) & (alph_size - 1)),
        &mut sections,
    )?;

    let mut rng = Rng(0x0bad_c0de_0bad_c0de);
    let pos: Vec<usize> = (0..probes).map(|_| (rng.next() as usize) % n).collect();
    let val: Vec<usize> = (0..probes)
        .map(|_| (rng.next() as usize) & (alph_size - 1))
        .collect();
    let mut out = vec![None; probes];

    let mut sink = 0usize;
    for i in 0..probes.min(20_000) {
        sink = sink.wrapping_add(wm.rank(pos[i], val[i]).unwrap_or(0));
    }
    std::hint::black_box(sink);

    for batch in [1usize, 2, 4, 8, 16, 32, 64, 128, 512, 4096] {
        let t = Instant::now();
        for (ci, c) in pos.chunks(batch).enumerate() {
            let lo = ci * batch;
            for (k, &p) in c.iter().enumerate() {
                sink = sink.wrapping_add(wm.rank(p, val[lo + k]).unwrap_or(0));
            }
        }
        let scalar = t.elapsed();
        std::hint::black_box(sink);

        let t = Instant::now();
        for (ci, c) in pos.chunks(batch).enumerate() {
            let lo = ci * batch;
            let hi = lo + c.len();
            wm.rank_batch_into(&pos[lo..hi], &val[lo..hi], &mut out[lo..hi])
                .unwrap();
        }
        let b = t.elapsed();
        std::hint::black_box(&out);

        let s_ns = scalar.as_nanos() as f64 / probes as f64;
        let b_ns = b.as_nanos() as f64 / probes as f64;
        println!(
            "{:>12}  {:>12.1}  {:>12.1}  {:>7.2}x",
            batch,
            s_ns,
            b_ns,
            s_ns / b_ns
        );
    }

    Ok(())
}
