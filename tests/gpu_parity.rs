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
// The feature-gated CubeCL dependency already requires a much newer compiler
// than the base crate's declared MSRV.
#![allow(clippy::incompatible_msrv)]

use anybytes::area::ByteArea;
use cubecl::prelude::*;
use jerky::bit_vector::Rank9SelIndex;
use jerky::char_sequences::WaveletMatrix;
use jerky::gpu::{GpuContext, GpuWaveletMatrix};

/// A deliberately separate downstream stage: if resident rank results can be
/// consumed here before the one final host read, the public buffer API is
/// sufficient to compose a multi-kernel query pipeline.
#[cube(launch_unchecked)]
fn consume_rank_kernel(ranks: &Array<u32>, consumed: &mut Array<u32>, mask: u32) {
    let t = ABSOLUTE_POS;
    if t < ranks.len() {
        consumed[t] = ranks[t] ^ mask;
    }
}

/// Mimics a scan/compaction stage that produces control entirely on device.
/// Dispatch is written as storage here, then used only as indirect control by
/// the rank consumer in the following launch.
#[cube(launch_unchecked)]
fn produce_batch_control(
    meta: &mut Array<u32>,
    dispatch: &mut Array<u32>,
    logical_len: u32,
    threads: u32,
) {
    if ABSOLUTE_POS == 0 {
        meta[0] = logical_len;
        dispatch[0] = logical_len.div_ceil(threads);
        dispatch[1] = 1u32;
        dispatch[2] = 1u32;
    }
}

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
fn resident_rank_chains_into_device_consumer_before_one_final_read() {
    let (_area, wm, ints) = build(0x00D3_A1CE, 4096, 257);
    let gpu = GpuWaveletMatrix::on_wgpu(&wm).unwrap();
    let batch = 8193usize;
    let positions_host: Vec<u32> = (0..batch)
        .map(|i| match i % 11 {
            0 => wm.len() as u32 + 1,
            1 => wm.len() as u32,
            _ => ((i * 37) % (wm.len() + 1)) as u32,
        })
        .collect();
    let values_host: Vec<u32> = (0..batch)
        .map(|i| {
            if i % 7 == 0 {
                (wm.alph_size() + i % 19) as u32
            } else {
                ints[(i * 53) % ints.len()] as u32
            }
        })
        .collect();

    // The upload is the producer boundary. Rank and the consumer below only
    // enqueue device work; neither performs a host read.
    let positions = gpu.upload_u32(&positions_host).unwrap();
    let values = gpu.upload_u32(&values_host).unwrap();
    let ranks = gpu.rank_batch_resident(&positions, &values).unwrap();
    let mut consumed = gpu.empty_u32(batch).unwrap();
    let mask = 0xA5A5_5A5Au32;
    let groups = (batch as u32).div_ceil(256);
    unsafe {
        consume_rank_kernel::launch_unchecked::<cubecl::wgpu::WgpuRuntime>(
            ranks.client(),
            CubeCount::new_1d(groups),
            CubeDim::new_1d(256),
            ranks.input_arg(),
            consumed.output_arg(),
            mask,
        );
    }

    // The only host read in the resident chain synchronizes both queued
    // kernels. Compare the consumed values rather than reading ranks midway.
    let actual = consumed.read();
    let expected: Vec<u32> = positions_host
        .iter()
        .zip(&values_host)
        .map(|(&position, &value)| {
            wm.rank(position as usize, value as usize)
                .map(|rank| rank as u32)
                .unwrap_or(u32::MAX)
                ^ mask
        })
        .collect();
    assert_eq!(actual, expected);
}

#[test]
fn dynamic_resident_rank_uses_device_length_and_indirect_dispatch() {
    let (_area, wm, ints) = build(0xD1CE_BA7C, 4096, 257);
    let context = GpuContext::on_wgpu();
    let gpu = GpuWaveletMatrix::with_context(context.clone(), &wm).unwrap();
    let capacity = 8193usize;
    let logical_len = 5003usize;
    let positions_host: Vec<u32> = (0..capacity)
        .map(|i| ((i * 43) % (wm.len() + 2)) as u32)
        .collect();
    let values_host: Vec<u32> = (0..capacity)
        .map(|i| ints[(i * 59) % ints.len()] as u32)
        .collect();
    let poison = 0xC0DE_CAFEu32;
    let mask = 0x5A5A_A5A5u32;

    let positions = context.upload_u32(&positions_host).unwrap();
    let values = context.upload_u32(&values_host).unwrap();
    let mut ranks = context.upload_u32(&vec![poison; capacity]).unwrap();
    let mut meta = context.batch_meta(0, capacity).unwrap();
    let cube_dim = CubeDim::new_1d(64);
    let mut dispatch = context.batch_dispatch(0, capacity, cube_dim).unwrap();

    unsafe {
        produce_batch_control::launch_unchecked::<cubecl::wgpu::WgpuRuntime>(
            context.client(),
            CubeCount::new_single(),
            CubeDim::new_single(),
            meta.output_arg(),
            dispatch.output_arg(),
            logical_len as u32,
            cube_dim.num_elems(),
        );
    }
    gpu.rank_batch_into_dynamic(&positions, &values, &mut ranks, &meta, &dispatch)
        .unwrap();

    // A separate full-capacity consumer makes the untouched tail observable
    // without reading rank or metadata between device stages.
    let mut consumed = context.empty_u32(capacity).unwrap();
    unsafe {
        consume_rank_kernel::launch_unchecked::<cubecl::wgpu::WgpuRuntime>(
            context.client(),
            CubeCount::new_1d((capacity as u32).div_ceil(256)),
            CubeDim::new_1d(256),
            ranks.input_arg(),
            consumed.output_arg(),
            mask,
        );
    }
    let actual = consumed.read();
    let expected: Vec<u32> = positions_host
        .iter()
        .zip(&values_host)
        .enumerate()
        .map(|(index, (&position, &value))| {
            let rank = if index < logical_len {
                wm.rank(position as usize, value as usize)
                    .map(|rank| rank as u32)
                    .unwrap_or(u32::MAX)
            } else {
                poison
            };
            rank ^ mask
        })
        .collect();
    assert_eq!(actual, expected);
}

#[test]
fn resident_rank_rejects_foreign_and_mismatched_buffers() {
    let (_area, wm, _ints) = build(0x000A_11CE, 128, 17);
    let shared = GpuContext::on_wgpu();
    let first = GpuWaveletMatrix::with_context(shared.clone(), &wm).unwrap();
    let second = GpuWaveletMatrix::with_context(shared.clone(), &wm).unwrap();
    let foreign = GpuWaveletMatrix::on_wgpu(&wm).unwrap();

    let positions = first.upload_u32(&[0, 64, 128]).unwrap();
    let values = first.upload_u32(&[0, 1, 2]).unwrap();
    let short_values = first.upload_u32(&[0, 1]).unwrap();
    let mut output = first.empty_u32(3).unwrap();
    let mut short_output = first.empty_u32(2).unwrap();
    let mut shared_output = second.empty_u32(3).unwrap();
    let mut foreign_output = foreign.empty_u32(3).unwrap();

    assert!(first
        .rank_batch_into(&positions, &short_values, &mut output)
        .is_err());
    assert!(first
        .rank_batch_into(&positions, &values, &mut short_output)
        .is_err());
    first
        .rank_batch_into(&positions, &values, &mut shared_output)
        .unwrap();
    assert_eq!(
        shared_output.read(),
        vec![
            wm.rank(0, 0).unwrap() as u32,
            wm.rank(64, 1).unwrap() as u32,
            wm.rank(128, 2).unwrap() as u32,
        ]
    );
    assert!(first
        .rank_batch_into(&positions, &values, &mut foreign_output)
        .is_err());
    assert!(shared.batch_meta(4, 3).is_err());
    assert!(shared.batch_dispatch(0, 3, CubeDim::new_1d(0)).is_err());
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
