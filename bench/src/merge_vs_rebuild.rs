//! Measures the linear structural merge (`WaveletMatrix::merge_sorted`)
//! against the decode–concatenate–sort–rebuild baseline it replaces, at
//! LSMT-compaction scales.
//!
//! Both paths start from already-built segments (the compaction setting)
//! and end with a complete queryable matrix (bit-planes + Rank9Sel):
//!
//! - REBUILD: `to_vec` each input, concatenate, `sort`, `from_iter`
//!   (bit-plane fill + freeze permutation + index builds).
//! - MERGE: `merge_sorted` = `to_vec` each input, linear multi-way merge
//!   of the runs, structural bit-plane interleave + index builds. No
//!   sort, no freeze permutation.
//!
//! Run with: `cargo run --release --bin merge_vs_rebuild`

use std::time::Instant;

use anybytes::ByteArea;
use jerky::bit_vector::Rank9SelIndex;
use jerky::char_sequences::WaveletMatrix;

/// splitmix64: deterministic input generation, matching the
/// gpu-succinct-probe methodology.
fn sm(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn gen_sorted_run(seed: u64, len: usize, alph_size: usize) -> Vec<usize> {
    let mut st = seed;
    let mut run: Vec<usize> = (0..len).map(|_| sm(&mut st) as usize % alph_size).collect();
    run.sort_unstable();
    run
}

fn build(alph_size: usize, ints: &[usize]) -> (ByteArea, WaveletMatrix<Rank9SelIndex>) {
    let mut area = ByteArea::new().unwrap();
    let mut sections = area.sections();
    let wm =
        WaveletMatrix::<Rank9SelIndex>::from_iter(alph_size, ints.iter().copied(), &mut sections)
            .unwrap();
    (area, wm)
}

fn main() {
    println!(
        "WaveletMatrix segment compaction: linear structural merge vs \
         decode+sort+rebuild\n"
    );

    for &(na, nb) in &[
        (200_000usize, 100_000usize),
        (1_000_000, 1_000_000),
        (4_000_000, 1_000_000),
    ] {
        let n = na + nb;
        let alph_size = n; // ~n distinct values, width = needed_bits(n)
        let run_a = gen_sorted_run(0xA ^ na as u64, na, alph_size);
        let run_b = gen_sorted_run(0xB ^ nb as u64, nb, alph_size);

        // Segment construction is common setup for both paths (untimed).
        let (_area_a, wm_a) = build(alph_size, &run_a);
        let (_area_b, wm_b) = build(alph_size, &run_b);

        // ---- REBUILD baseline: decode + concatenate + sort + from_iter ----
        let t = Instant::now();
        let mut union: Vec<usize> = wm_a.to_vec();
        union.extend(wm_b.to_vec());
        union.sort_unstable(); // THE SORT the merge avoids
        let decode_sort_ms = t.elapsed().as_secs_f64() * 1e3;
        let t = Instant::now();
        let (_rebuild_area, rebuilt) = build(alph_size, &union);
        let from_iter_ms = t.elapsed().as_secs_f64() * 1e3;
        let rebuild_ms = decode_sort_ms + from_iter_ms;

        // ---- MERGE: linear multi-way structural merge ----
        let t = Instant::now();
        let mut merge_area = ByteArea::new().unwrap();
        let mut sections = merge_area.sections();
        let merged =
            WaveletMatrix::<Rank9SelIndex>::merge_sorted(&[&wm_a, &wm_b], &mut sections).unwrap();
        let merge_ms = t.elapsed().as_secs_f64() * 1e3;

        // ---- Correctness gate ----
        assert_eq!(merged.len(), rebuilt.len());
        assert_eq!(merged.to_vec(), union, "merged sequence != sorted union");
        let mut st = 0xC0FFEEu64;
        for _ in 0..10_000 {
            let pos = sm(&mut st) as usize % (n + 1);
            let val = union[sm(&mut st) as usize % n];
            assert_eq!(merged.rank(pos, val), rebuilt.rank(pos, val));
            let k = sm(&mut st) as usize % n;
            assert_eq!(merged.select(k, val), rebuilt.select(k, val));
        }

        let per = |ms: f64| ms * 1e6 / n as f64; // ns per merged element
        println!(
            "==== {}k + {}k = {} values | alphabet {} | width {} bits ====",
            na / 1000,
            nb / 1000,
            n,
            alph_size,
            merged.alph_width()
        );
        println!(
            "  REBUILD  {rebuild_ms:9.2} ms ({:6.1} ns/el)  \
             [decode+sort {decode_sort_ms:.2} ms | from_iter {from_iter_ms:.2} ms]",
            per(rebuild_ms)
        );
        println!("  MERGE    {merge_ms:9.2} ms ({:6.1} ns/el)", per(merge_ms));
        println!(
            "  SPEEDUP  {:.2}x  [correctness: sequence + rank/select vs rebuild OK]\n",
            rebuild_ms / merge_ms
        );
    }
}
