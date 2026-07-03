//! Parity gate for the GPU batch query kernels (feature `gpu`): every batch
//! result must be identical to the CPU per-query result, over random matrices
//! spanning sizes and alphabets, including out-of-range queries.
//!
//! Needs a working GPU (wgpu device). The large 4M+ case is `#[ignore]`d so
//! plain `cargo test --features gpu` stays fast; run it with
//! `cargo test --release --features gpu -- --ignored`.
#![cfg(all(feature = "gpu", target_pointer_width = "64"))]
// One-element `&[Range]` arguments below are deliberate batch-of-one calls.
#![allow(clippy::single_range_in_vec_init)]

use anybytes::area::ByteArea;
use jerky::bit_vector::Rank9SelIndex;
use jerky::char_sequences::WaveletMatrix;
use jerky::gpu::GpuWaveletMatrix;

/// splitmix64: deterministic PRNG without deps.
fn sm(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn build(
    seed: u64,
    len: usize,
    alph_size: usize,
) -> (ByteArea, WaveletMatrix<Rank9SelIndex>, Vec<usize>) {
    let mut st = seed;
    let ints: Vec<usize> = (0..len).map(|_| sm(&mut st) as usize % alph_size).collect();
    let mut area = ByteArea::new().unwrap();
    let mut sections = area.sections();
    let wm =
        WaveletMatrix::<Rank9SelIndex>::from_iter(alph_size, ints.iter().copied(), &mut sections)
            .unwrap();
    (area, wm, ints)
}

/// Checks GPU batch results against CPU per-query results for all four ops.
fn check_parity(wm: &WaveletMatrix<Rank9SelIndex>, ints: &[usize], queries: usize, seed: u64) {
    let gpu = GpuWaveletMatrix::on_wgpu(wm).unwrap();
    assert_eq!(gpu.len(), wm.len());
    assert_eq!(gpu.alph_size(), wm.alph_size());
    assert_eq!(gpu.alph_width(), wm.alph_width());

    let n = wm.len();
    let sigma = wm.alph_size();
    let mut st = seed;
    let ctx = |q: usize| format!("n={n} sigma={sigma} query#{q}");

    // access: in-range, boundary, and out-of-range positions.
    let positions: Vec<usize> = (0..queries)
        .map(|i| match i % 8 {
            0 => n,                                  // one-past-the-end
            1 => n + 1 + (sm(&mut st) as usize % 7), // clearly out of range
            _ => sm(&mut st) as usize % (n + 2),
        })
        .collect();
    let gpu_res = gpu.access_batch(&positions).unwrap();
    for (i, (&p, g)) in positions.iter().zip(&gpu_res).enumerate() {
        assert_eq!(wm.access(p), *g, "access({p}) [{}]", ctx(i));
    }

    // rank: positions 0..=n and beyond, values in and out of the alphabet.
    let ranks: Vec<(usize, usize)> = (0..queries)
        .map(|i| {
            let pos = match i % 8 {
                0 => n,
                1 => n + 1 + (sm(&mut st) as usize % 7),
                _ => sm(&mut st) as usize % (n + 2),
            };
            // Mix stored values, arbitrary in-alphabet values, and values
            // beyond the alphabet (CPU aliases them through the width mask).
            let val = match i % 4 {
                0 if n > 0 => ints[sm(&mut st) as usize % n],
                1 => sigma + (sm(&mut st) as usize % (sigma + 1)),
                _ => sm(&mut st) as usize % sigma,
            };
            (pos, val)
        })
        .collect();
    let (ps, vs): (Vec<_>, Vec<_>) = ranks.iter().copied().unzip();
    let gpu_res = gpu.rank_batch(&ps, &vs).unwrap();
    for (i, (&(p, v), g)) in ranks.iter().zip(&gpu_res).enumerate() {
        assert_eq!(wm.rank(p, v), *g, "rank({p}, {v}) [{}]", ctx(i));
    }

    // select: in-range ks against stored values (full descend+ascend path),
    // plus out-of-range ks, where the GPU must report None. The CPU walk is
    // compared only for in-range ks (its out-of-range behavior relies on
    // per-layer select bounds and is exercised by its own test suite).
    let selects: Vec<(usize, usize, bool)> = (0..queries)
        .map(|_| {
            if n > 0 && sm(&mut st) % 4 != 0 {
                let val = ints[sm(&mut st) as usize % n];
                let occ = wm.rank(n, val).unwrap();
                (sm(&mut st) as usize % occ, val, true)
            } else {
                // Absent or exhausted: k >= occurrences by construction.
                let val = sm(&mut st) as usize % sigma;
                let occ = wm.rank(n, val).unwrap_or(0);
                (occ + (sm(&mut st) as usize % 3), val, false)
            }
        })
        .collect();
    let ks: Vec<_> = selects.iter().map(|&(k, _, _)| k).collect();
    let vs: Vec<_> = selects.iter().map(|&(_, v, _)| v).collect();
    let gpu_res = gpu.select_batch(&ks, &vs).unwrap();
    for (i, (&(k, v, in_range), g)) in selects.iter().zip(&gpu_res).enumerate() {
        if in_range {
            assert_eq!(wm.select(k, v), *g, "select({k}, {v}) [{}]", ctx(i));
        } else {
            assert_eq!(*g, None, "select({k}, {v}) beyond occurrences [{}]", ctx(i));
        }
    }

    // quantile: random ranges (valid, empty, inverted, out of bounds) with
    // ks in and out of range.
    let quantiles: Vec<(std::ops::Range<usize>, usize)> = (0..queries)
        .map(|i| {
            let a = sm(&mut st) as usize % (n + 2);
            let b = sm(&mut st) as usize % (n + 2);
            let range = match i % 4 {
                0 => a..a, // empty
                1 => a..b, // possibly inverted / out of bounds
                _ => a.min(b)..a.max(b) + 1,
            };
            let k = sm(&mut st) as usize % (range.len() + 2);
            (range, k)
        })
        .collect();
    let ranges: Vec<_> = quantiles.iter().map(|(r, _)| r.clone()).collect();
    let ks: Vec<_> = quantiles.iter().map(|&(_, k)| k).collect();
    let gpu_res = gpu.quantile_batch(&ranges, &ks).unwrap();
    for (i, ((r, k), g)) in quantiles.iter().zip(&gpu_res).enumerate() {
        assert_eq!(
            wm.quantile(r.clone(), *k),
            *g,
            "quantile({r:?}, {k}) [{}]",
            ctx(i)
        );
    }
}

#[test]
fn parity_small_and_medium_matrices() {
    let mut seed = 0x6B0A_0001u64;
    for &(len, alph_size) in &[
        (1usize, 1usize),
        (1, 300),
        (7, 2),
        (63, 5),
        (64, 5),
        (65, 1000),
        (511, 2),    // block boundary - 1
        (512, 2),    // exactly one rank block
        (513, 2),    // block boundary + 1
        (1000, 941), // non-power-of-two alphabet
        (4096, 65_536),
        (100_000, 3),
        (200_000, 65_536),
    ] {
        seed += 1;
        let (_area, wm, ints) = build(seed, len, alph_size);
        check_parity(&wm, &ints, 2000, seed ^ 0xFACE);
    }
}

#[test]
fn parity_empty_matrix() {
    let (_area, wm, ints) = build(1, 0, 1);
    let gpu = GpuWaveletMatrix::on_wgpu(&wm).unwrap();
    assert!(gpu.is_empty());
    assert_eq!(gpu.access_batch(&[0, 1]).unwrap(), vec![None, None]);
    // rank(0, v) on an empty matrix is Some(0) (empty range), like the CPU.
    assert_eq!(wm.rank(0, 0), Some(0));
    assert_eq!(
        gpu.rank_batch(&[0, 1], &[0, 0]).unwrap(),
        vec![Some(0), None]
    );
    assert_eq!(gpu.select_batch(&[0], &[0]).unwrap(), vec![None]);
    assert_eq!(gpu.quantile_batch(&[0..0], &[0]).unwrap(), vec![None]);
    let _ = ints;
}

#[test]
fn parity_empty_batches() {
    let (_area, wm, _ints) = build(7, 100, 16);
    let gpu = GpuWaveletMatrix::on_wgpu(&wm).unwrap();
    assert_eq!(gpu.access_batch(&[]).unwrap(), Vec::new());
    assert_eq!(gpu.rank_batch(&[], &[]).unwrap(), Vec::new());
    assert_eq!(gpu.select_batch(&[], &[]).unwrap(), Vec::new());
    assert_eq!(gpu.quantile_batch(&[], &[]).unwrap(), Vec::new());
}

#[test]
fn mismatched_lengths_are_rejected() {
    let (_area, wm, _ints) = build(9, 100, 16);
    let gpu = GpuWaveletMatrix::on_wgpu(&wm).unwrap();
    assert!(gpu.rank_batch(&[0, 1], &[0]).is_err());
    assert!(gpu.select_batch(&[0], &[0, 1]).is_err());
    assert!(gpu.quantile_batch(&[0..1], &[0, 0]).is_err());
}

#[test]
fn oversize_positions_map_to_none() {
    let (_area, wm, _ints) = build(11, 100, 16);
    let gpu = GpuWaveletMatrix::on_wgpu(&wm).unwrap();
    assert_eq!(
        gpu.access_batch(&[usize::MAX, 5]).unwrap()[0],
        None,
        "positions beyond u32 are out of range by construction"
    );
    assert_eq!(gpu.rank_batch(&[usize::MAX], &[0]).unwrap(), vec![None]);
    assert_eq!(gpu.select_batch(&[usize::MAX], &[0]).unwrap(), vec![None]);
    assert_eq!(
        gpu.quantile_batch(&[0..usize::MAX], &[0]).unwrap(),
        vec![None]
    );
}

/// The 4M+/64k case from the deliverable spec. Slow to build in debug mode;
/// run with `cargo test --release --features gpu -- --ignored`.
#[test]
#[ignore = "large matrix; run in release mode"]
fn parity_large_4m_matrix() {
    let (_area, wm, ints) = build(0xB16, (4 << 20) + 7, 65_536);
    check_parity(&wm, &ints, 100_000, 0xB16_FACE);
}
