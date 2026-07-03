//! GPU-resident batch query kernels for [`WaveletMatrix`] (feature `gpu`).
//!
//! # What this is
//!
//! [`GpuWaveletMatrix`] uploads a frozen [`WaveletMatrix`] to the GPU **once**
//! (bit-planes plus a flat rank-block directory) and then answers *batches* of
//! queries — [`access_batch`](GpuWaveletMatrix::access_batch),
//! [`rank_batch`](GpuWaveletMatrix::rank_batch),
//! [`select_batch`](GpuWaveletMatrix::select_batch),
//! [`quantile_batch`](GpuWaveletMatrix::quantile_batch) — with **one kernel
//! dispatch and one host↔device synchronization per batch**, never per query.
//! Each GPU thread runs one full query (a data-dependent chain of ~`lg σ`
//! stacked rank/select steps); thousands of such chains in flight hide the
//! memory latency that stalls a CPU core on the same walk.
//!
//! # When to use it (and when not to)
//!
//! Wavelet queries are *latency-bound*, not bandwidth-bound: each layer step
//! is a dependent scattered load. That is exactly the regime where GPU thread
//! oversubscription wins — measured ~14× over a fully loaded 16-thread CPU
//! for million-query access batches on Apple silicon — but only when the
//! batch is large enough to amortize the fixed launch + sync cost (a sync
//! round-trip alone is 1.6–3.9 ms on wgpu/Metal):
//!
//! - **Use the GPU form** for large analytic batches: thousands to millions
//!   of independent queries issued at once, e.g. evaluating a query
//!   constraint against every candidate in a column (the
//!   SuccinctArchive/wd_bench shape).
//! - **Use the CPU form** ([`WaveletMatrix`]) for point lookups and small
//!   batches. Below the break-even batch size (order of 10k queries; run
//!   `cargo run --release --features gpu --example gpu_bench` on your
//!   hardware) the fixed dispatch/sync cost dominates and the CPU wins.
//!
//! # Downstream adapter shape
//!
//! A consumer like triblespace's `SuccinctArchive` evaluates per-clause
//! constraints by probing the same wavelet matrix for every proposed element.
//! The adapter shape is: collect the per-clause probe set host-side, call one
//! `*_batch` method per clause (one sync each), and only then branch on the
//! results. Do **not** wrap single-probe call sites — that reintroduces a
//! sync per query and is orders of magnitude slower than the CPU path.
//!
//! # Limits
//!
//! - `len() < u32::MAX` and `alph_size() <= u32::MAX` (positions, ranks, and
//!   values travel as `u32`; `u32::MAX` is the in-kernel "no result"
//!   sentinel).
//! - The device buffers are plain storage buffers; a matrix must fit in the
//!   adapter's max buffer size (bit-planes are `len·alph_width` bits plus
//!   ~6% rank directory).
//! - Queries return exactly what the CPU API returns, including `None` for
//!   out-of-range arguments.
//!
//! # Example
//!
//! ```no_run
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use jerky::bit_vector::Rank9SelIndex;
//! use jerky::char_sequences::WaveletMatrix;
//! use jerky::gpu::GpuWaveletMatrix;
//! use anybytes::ByteArea;
//!
//! let text = "banana";
//! let mut area = ByteArea::new()?;
//! let mut sections = area.sections();
//! let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(
//!     ('n' as usize) + 1,
//!     text.bytes().map(|b| b as usize),
//!     &mut sections,
//! )?;
//!
//! let gpu = GpuWaveletMatrix::on_wgpu(&wm)?; // upload once
//! let values = gpu.access_batch(&[0, 2, 5, 99])?; // one dispatch, one sync
//! assert_eq!(
//!     values,
//!     vec![Some('b' as usize), Some('n' as usize), Some('a' as usize), None],
//! );
//! # Ok(())
//! # }
//! ```
#![cfg(target_pointer_width = "64")]
// The `gpu` feature requires a recent stable toolchain regardless (cubecl's
// MSRV is far above the base crate's 1.61), so post-1.61 std items are fine
// inside this feature-gated module.
#![allow(clippy::incompatible_msrv)]

use std::ops::Range;

use cubecl::client::ComputeClient;
use cubecl::prelude::*;
use cubecl::server::Handle;

use crate::bit_vector::{BitVectorIndex, NumBits};
use crate::char_sequences::WaveletMatrix;
use crate::error::{Error, Result};

/// Threads per workgroup for all query kernels.
const THREADS: u32 = 256;
/// `u32` words per rank block (16 × 32 = 512-bit blocks).
const WORDS_PER_BLOCK: u32 = 16;
/// In-kernel "no result" sentinel, decoded to `None` host-side.
const NONE_SENTINEL: u32 = u32::MAX;
/// wgpu's per-dimension dispatch limit.
const MAX_GROUPS_PER_DIM: u32 = 65_535;

// ---------------------------------------------------------------------------
// device-side primitives
// ---------------------------------------------------------------------------

/// rank1 within one layer: number of set bits in `0..pos` of the layer whose
/// words start at `wo` and whose block directory starts at `bo`.
///
/// Layers are padded with at least one all-zero word (and the directory with
/// the matching flat block entries), so `pos == len` is safe even on word and
/// block boundaries.
#[cube]
fn layer_rank1(words: &Array<u32>, counts: &Array<u32>, wo: u32, bo: u32, pos: u32) -> u32 {
    let word_idx = pos / 32u32;
    let bit_idx = pos % 32u32;
    let block_idx = word_idx / WORDS_PER_BLOCK;
    let mut r = counts[(bo + block_idx) as usize];
    let mut w = block_idx * WORDS_PER_BLOCK;
    while w < word_idx {
        r += words[(wo + w) as usize].count_ones();
        w += 1u32;
    }
    r + (words[(wo + word_idx) as usize] & ((1u32 << bit_idx) - 1u32)).count_ones()
}

/// Position of the `r`-th (0-indexed) set bit within a 32-bit word.
#[cube]
fn select_in_word(word: u32, r: u32) -> u32 {
    let mut cur = word;
    let mut rem = r;
    let mut pos = u32::new(0);
    let mut step = u32::new(16);
    while step > 0u32 {
        let cnt = (cur & ((1u32 << step) - 1u32)).count_ones();
        if rem >= cnt {
            rem -= cnt;
            pos += step;
            cur >>= step;
        }
        step /= 2u32;
    }
    pos
}

/// select1 within one layer: position of the `k`-th set bit. `k` must be in
/// range (`k < num_ones` of the layer); guaranteed by the callers' occurrence
/// checks.
#[cube]
fn layer_select1(
    words: &Array<u32>,
    counts: &Array<u32>,
    wo: u32,
    bo: u32,
    k: u32,
    bpl: u32,
) -> u32 {
    // Largest block whose prefix count is <= k (counts[bo] == 0 <= k).
    let mut lo = u32::new(0);
    let mut hi = bpl;
    while hi - lo > 1u32 {
        let mid = (lo + hi) / 2u32;
        if counts[(bo + mid) as usize] <= k {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let mut rem = k - counts[(bo + lo) as usize];
    let mut w = lo * WORDS_PER_BLOCK;
    let mut cnt = words[(wo + w) as usize].count_ones();
    while cnt <= rem {
        rem -= cnt;
        w += 1u32;
        cnt = words[(wo + w) as usize].count_ones();
    }
    w * 32u32 + select_in_word(words[(wo + w) as usize], rem)
}

/// select0 within one layer: position of the `k`-th unset bit. `k` must be in
/// range (`k < num_zeros` of the layer); padding zeros past `len` are never
/// reached for in-range `k` because they sort after every valid position.
#[cube]
fn layer_select0(
    words: &Array<u32>,
    counts: &Array<u32>,
    wo: u32,
    bo: u32,
    k: u32,
    bpl: u32,
) -> u32 {
    // Zero-prefix of block b is b*512 - counts[b]; largest block with it <= k.
    let mut lo = u32::new(0);
    let mut hi = bpl;
    while hi - lo > 1u32 {
        let mid = (lo + hi) / 2u32;
        if mid * WORDS_PER_BLOCK * 32u32 - counts[(bo + mid) as usize] <= k {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let mut rem = k - (lo * WORDS_PER_BLOCK * 32u32 - counts[(bo + lo) as usize]);
    let mut w = lo * WORDS_PER_BLOCK;
    let mut cnt = (words[(wo + w) as usize] ^ 0xFFFF_FFFFu32).count_ones();
    while cnt <= rem {
        rem -= cnt;
        w += 1u32;
        cnt = (words[(wo + w) as usize] ^ 0xFFFF_FFFFu32).count_ones();
    }
    w * 32u32 + select_in_word(words[(wo + w) as usize] ^ 0xFFFF_FFFFu32, rem)
}

// ---------------------------------------------------------------------------
// query kernels: one thread = one query, one dispatch = one batch
// ---------------------------------------------------------------------------

#[cube(launch_unchecked)]
fn wm_access_kernel(
    words: &Array<u32>,
    counts: &Array<u32>,
    zeros: &Array<u32>,
    pos_q: &Array<u32>,
    out: &mut Array<u32>,
    n: u32,
    wpl: u32,
    bpl: u32,
    num_layers: u32,
) {
    let t = ABSOLUTE_POS;
    if t < pos_q.len() {
        let mut pos = pos_q[t];
        if pos >= n {
            out[t] = 0xFFFF_FFFFu32;
        } else {
            let mut val = u32::new(0);
            let mut l = u32::new(0);
            while l < num_layers {
                let wo = l * wpl;
                let bo = l * bpl;
                let bit = (words[(wo + pos / 32u32) as usize] >> (pos % 32u32)) & 1u32;
                val = (val << 1u32) | bit;
                let r = layer_rank1(words, counts, wo, bo, pos);
                if bit == 1u32 {
                    pos = r + zeros[l as usize];
                } else {
                    pos -= r;
                }
                l += 1u32;
            }
            out[t] = val;
        }
    }
}

#[cube(launch_unchecked)]
#[allow(clippy::too_many_arguments)]
fn wm_rank_kernel(
    words: &Array<u32>,
    counts: &Array<u32>,
    zeros: &Array<u32>,
    pos_q: &Array<u32>,
    val_q: &Array<u32>,
    out: &mut Array<u32>,
    n: u32,
    wpl: u32,
    bpl: u32,
    num_layers: u32,
) {
    let t = ABSOLUTE_POS;
    if t < pos_q.len() {
        let pos = pos_q[t];
        if pos > n {
            out[t] = 0xFFFF_FFFFu32;
        } else {
            let val = val_q[t];
            let mut s = u32::new(0);
            let mut e = pos;
            let mut l = u32::new(0);
            while l < num_layers {
                let wo = l * wpl;
                let bo = l * bpl;
                let bit = (val >> (num_layers - 1u32 - l)) & 1u32;
                let rs = layer_rank1(words, counts, wo, bo, s);
                let re = layer_rank1(words, counts, wo, bo, e);
                if bit == 1u32 {
                    s = rs + zeros[l as usize];
                    e = re + zeros[l as usize];
                } else {
                    s -= rs;
                    e -= re;
                }
                l += 1u32;
            }
            out[t] = e - s;
        }
    }
}

#[cube(launch_unchecked)]
#[allow(clippy::too_many_arguments)]
fn wm_select_kernel(
    words: &Array<u32>,
    counts: &Array<u32>,
    zeros: &Array<u32>,
    k_q: &Array<u32>,
    val_q: &Array<u32>,
    out: &mut Array<u32>,
    n: u32,
    wpl: u32,
    bpl: u32,
    num_layers: u32,
) {
    let t = ABSOLUTE_POS;
    if t < k_q.len() {
        let k = k_q[t];
        let val = val_q[t];
        // Descend, tracking val's bucket [s, e) per layer.
        let mut s = u32::new(0);
        let mut e = n;
        let mut l = u32::new(0);
        while l < num_layers {
            let wo = l * wpl;
            let bo = l * bpl;
            let bit = (val >> (num_layers - 1u32 - l)) & 1u32;
            let rs = layer_rank1(words, counts, wo, bo, s);
            let re = layer_rank1(words, counts, wo, bo, e);
            if bit == 1u32 {
                s = rs + zeros[l as usize];
                e = re + zeros[l as usize];
            } else {
                s -= rs;
                e -= re;
            }
            l += 1u32;
        }
        if k >= e - s {
            out[t] = 0xFFFF_FFFFu32;
        } else {
            // Ascend from the k-th element of the bottom bucket.
            let mut p = s + k;
            let mut d = num_layers;
            while d > 0u32 {
                d -= 1u32;
                let wo = d * wpl;
                let bo = d * bpl;
                let bit = (val >> (num_layers - 1u32 - d)) & 1u32;
                if bit == 1u32 {
                    p = layer_select1(words, counts, wo, bo, p - zeros[d as usize], bpl);
                } else {
                    p = layer_select0(words, counts, wo, bo, p, bpl);
                }
            }
            out[t] = p;
        }
    }
}

#[cube(launch_unchecked)]
#[allow(clippy::too_many_arguments)]
fn wm_quantile_kernel(
    words: &Array<u32>,
    counts: &Array<u32>,
    zeros: &Array<u32>,
    start_q: &Array<u32>,
    end_q: &Array<u32>,
    k_q: &Array<u32>,
    out: &mut Array<u32>,
    n: u32,
    wpl: u32,
    bpl: u32,
    num_layers: u32,
) {
    let t = ABSOLUTE_POS;
    if t < k_q.len() {
        let mut s = start_q[t];
        let mut e = end_q[t];
        let mut k = k_q[t];
        if e > n || s >= e || k >= e - s {
            out[t] = 0xFFFF_FFFFu32;
        } else {
            let mut val = u32::new(0);
            let mut l = u32::new(0);
            while l < num_layers {
                let wo = l * wpl;
                let bo = l * bpl;
                let s0 = s - layer_rank1(words, counts, wo, bo, s);
                let e0 = e - layer_rank1(words, counts, wo, bo, e);
                let z = e0 - s0;
                if k < z {
                    val <<= 1u32;
                    s = s0;
                    e = e0;
                } else {
                    k -= z;
                    val = (val << 1u32) | 1u32;
                    s = zeros[l as usize] + s - s0;
                    e = zeros[l as usize] + e - e0;
                }
                l += 1u32;
            }
            out[t] = val;
        }
    }
}

// ---------------------------------------------------------------------------
// host side
// ---------------------------------------------------------------------------

/// A [`WaveletMatrix`] uploaded to the GPU, answering batches of queries with
/// one dispatch and one synchronization per batch. See the [module docs](self)
/// for when this beats the CPU form and when it does not.
pub struct GpuWaveletMatrix<R: Runtime> {
    client: ComputeClient<R>,
    /// Bit-planes as `u32` words, one padded stripe of `wpl` words per layer.
    words: Handle,
    words_len: usize,
    /// Per-block rank1 prefix counts, `bpl` entries per layer.
    counts: Handle,
    counts_len: usize,
    /// Per-layer zero-bit counts.
    zeros: Handle,
    len: u32,
    alph_size: usize,
    alph_width: u32,
    /// Padded `u32` words per layer stripe (multiple of [`WORDS_PER_BLOCK`],
    /// always at least one all-zero word beyond the last data word).
    wpl: u32,
    /// Rank blocks per layer stripe (`wpl / WORDS_PER_BLOCK`).
    bpl: u32,
}

impl<R: Runtime> GpuWaveletMatrix<R> {
    /// Uploads `wm` to the device served by `client`.
    ///
    /// This is the only data transfer of the matrix itself; all subsequent
    /// batch queries move only query and result buffers.
    ///
    /// # Errors
    ///
    /// An error is returned if `wm.len() >= u32::MAX` or
    /// `wm.alph_size() > u32::MAX` (device positions and values are `u32`,
    /// with `u32::MAX` reserved as the miss sentinel).
    pub fn new<I: BitVectorIndex>(client: ComputeClient<R>, wm: &WaveletMatrix<I>) -> Result<Self> {
        if wm.len() >= u32::MAX as usize {
            return Err(Error::invalid_argument(format!(
                "GPU form requires len() < u32::MAX, but got {}",
                wm.len()
            )));
        }
        if wm.alph_size() > u32::MAX as usize {
            return Err(Error::invalid_argument(format!(
                "GPU form requires alph_size() <= u32::MAX, but got {}",
                wm.alph_size()
            )));
        }
        let n = wm.len();
        let width = wm.alph_width();
        debug_assert!(width <= 32, "alph_size <= u32::MAX implies width <= 32");

        // Words per layer, padded to a block boundary with at least one extra
        // zero word so rank at pos == n never reads past a stripe.
        let data_words = n.div_ceil(32);
        let wpl = (data_words + 1).div_ceil(WORDS_PER_BLOCK as usize) * WORDS_PER_BLOCK as usize;
        let bpl = wpl / WORDS_PER_BLOCK as usize;

        let mut words_host: Vec<u32> = Vec::with_capacity(wpl * width);
        let mut counts_host: Vec<u32> = Vec::with_capacity(bpl * width);
        let mut zeros_host: Vec<u32> = Vec::with_capacity(width);

        for layer in wm.layers() {
            zeros_host.push(layer.num_zeros() as u32);
            let stripe_start = words_host.len();
            for &w64 in layer.data.words() {
                words_host.push(w64 as u32);
                words_host.push((w64 >> 32) as u32);
            }
            words_host.truncate(stripe_start + data_words); // odd u64 tail
            words_host.resize(stripe_start + wpl, 0);
            let mut acc = 0u32;
            for (i, &w) in words_host[stripe_start..].iter().enumerate() {
                if i % WORDS_PER_BLOCK as usize == 0 {
                    counts_host.push(acc);
                }
                acc += w.count_ones();
            }
        }

        let words_len = words_host.len().max(1);
        let counts_len = counts_host.len().max(1);
        // Keep buffers non-empty so kernels can always bind them.
        words_host.resize(words_len, 0);
        counts_host.resize(counts_len, 0);
        let zeros_len = zeros_host.len().max(1);
        zeros_host.resize(zeros_len, 0);

        let words = client.create_from_slice(u32::as_bytes(&words_host));
        let counts = client.create_from_slice(u32::as_bytes(&counts_host));
        let zeros = client.create_from_slice(u32::as_bytes(&zeros_host));

        Ok(Self {
            client,
            words,
            words_len,
            counts,
            counts_len,
            zeros,
            len: n as u32,
            alph_size: wm.alph_size(),
            alph_width: width as u32,
            wpl: wpl as u32,
            bpl: bpl as u32,
        })
    }

    /// Returns the number of values stored.
    pub fn len(&self) -> usize {
        self.len as usize
    }

    /// Checks if the sequence is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the maximum value + 1 in the sequence, i.e., $`\sigma`$.
    pub fn alph_size(&self) -> usize {
        self.alph_size
    }

    /// Returns the number of bit-plane layers, i.e., $`\lceil \lg \sigma \rceil`$.
    pub fn alph_width(&self) -> usize {
        self.alph_width as usize
    }

    /// Batched [`WaveletMatrix::access`]: returns the integer at each
    /// position, or `None` where the position is out of bounds.
    ///
    /// One dispatch, one sync, regardless of `positions.len()`.
    pub fn access_batch(&self, positions: &[usize]) -> Result<Vec<Option<usize>>> {
        if positions.is_empty() {
            return Ok(Vec::new());
        }
        if self.len == 0 {
            return Ok(vec![None; positions.len()]);
        }
        let pos_q: Vec<u32> = positions.iter().map(|&p| clamp_u32(p)).collect();
        let batch = pos_q.len();
        let pos_h = self.client.create_from_slice(u32::as_bytes(&pos_q));
        let out_h = self.client.empty(batch * 4);
        let (count, dim) = self.dispatch(batch);
        unsafe {
            wm_access_kernel::launch_unchecked::<R>(
                &self.client,
                count,
                dim,
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                ArrayArg::from_raw_parts(self.zeros.clone(), self.alph_width as usize),
                ArrayArg::from_raw_parts(pos_h, batch),
                ArrayArg::from_raw_parts(out_h.clone(), batch),
                self.len,
                self.wpl,
                self.bpl,
                self.alph_width,
            );
        }
        Ok(self.read_results(out_h))
    }

    /// Batched [`WaveletMatrix::rank`]: for each `(positions[i], values[i])`
    /// pair, returns the number of occurrences of the value in `0..pos`, or
    /// `None` where `pos > len()`.
    ///
    /// For a single symbol over many positions, pass `values` filled with
    /// that symbol. One dispatch, one sync, regardless of batch size.
    ///
    /// # Errors
    ///
    /// An error is returned if the slices differ in length.
    pub fn rank_batch(&self, positions: &[usize], values: &[usize]) -> Result<Vec<Option<usize>>> {
        if positions.len() != values.len() {
            return Err(Error::invalid_argument(format!(
                "positions and values must have equal lengths, got {} and {}",
                positions.len(),
                values.len()
            )));
        }
        if positions.is_empty() {
            return Ok(Vec::new());
        }
        if self.len == 0 {
            return Ok(positions
                .iter()
                .map(|&p| if p == 0 { Some(0) } else { None })
                .collect());
        }
        let pos_q: Vec<u32> = positions.iter().map(|&p| clamp_u32(p)).collect();
        let val_q: Vec<u32> = values.iter().map(|&v| v as u32).collect();
        let batch = pos_q.len();
        let pos_h = self.client.create_from_slice(u32::as_bytes(&pos_q));
        let val_h = self.client.create_from_slice(u32::as_bytes(&val_q));
        let out_h = self.client.empty(batch * 4);
        let (count, dim) = self.dispatch(batch);
        unsafe {
            wm_rank_kernel::launch_unchecked::<R>(
                &self.client,
                count,
                dim,
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                ArrayArg::from_raw_parts(self.zeros.clone(), self.alph_width as usize),
                ArrayArg::from_raw_parts(pos_h, batch),
                ArrayArg::from_raw_parts(val_h, batch),
                ArrayArg::from_raw_parts(out_h.clone(), batch),
                self.len,
                self.wpl,
                self.bpl,
                self.alph_width,
            );
        }
        Ok(self.read_results(out_h))
    }

    /// Batched [`WaveletMatrix::select`]: for each `(ks[i], values[i])` pair,
    /// returns the position of the `k`-th occurrence of the value, or `None`
    /// where the value occurs at most `k` times.
    ///
    /// One dispatch, one sync, regardless of batch size.
    ///
    /// # Errors
    ///
    /// An error is returned if the slices differ in length.
    pub fn select_batch(&self, ks: &[usize], values: &[usize]) -> Result<Vec<Option<usize>>> {
        if ks.len() != values.len() {
            return Err(Error::invalid_argument(format!(
                "ks and values must have equal lengths, got {} and {}",
                ks.len(),
                values.len()
            )));
        }
        if ks.is_empty() {
            return Ok(Vec::new());
        }
        if self.len == 0 {
            return Ok(vec![None; ks.len()]);
        }
        let k_q: Vec<u32> = ks.iter().map(|&k| clamp_u32(k)).collect();
        let val_q: Vec<u32> = values.iter().map(|&v| v as u32).collect();
        let batch = k_q.len();
        let k_h = self.client.create_from_slice(u32::as_bytes(&k_q));
        let val_h = self.client.create_from_slice(u32::as_bytes(&val_q));
        let out_h = self.client.empty(batch * 4);
        let (count, dim) = self.dispatch(batch);
        unsafe {
            wm_select_kernel::launch_unchecked::<R>(
                &self.client,
                count,
                dim,
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                ArrayArg::from_raw_parts(self.zeros.clone(), self.alph_width as usize),
                ArrayArg::from_raw_parts(k_h, batch),
                ArrayArg::from_raw_parts(val_h, batch),
                ArrayArg::from_raw_parts(out_h.clone(), batch),
                self.len,
                self.wpl,
                self.bpl,
                self.alph_width,
            );
        }
        Ok(self.read_results(out_h))
    }

    /// Batched [`WaveletMatrix::quantile`]: for each `(ranges[i], ks[i])`
    /// pair, returns the `k`-th smallest value in the range, or `None` where
    /// the range is out of bounds or shorter than `k + 1`.
    ///
    /// One dispatch, one sync, regardless of batch size.
    ///
    /// # Errors
    ///
    /// An error is returned if the slices differ in length.
    pub fn quantile_batch(
        &self,
        ranges: &[Range<usize>],
        ks: &[usize],
    ) -> Result<Vec<Option<usize>>> {
        if ranges.len() != ks.len() {
            return Err(Error::invalid_argument(format!(
                "ranges and ks must have equal lengths, got {} and {}",
                ranges.len(),
                ks.len()
            )));
        }
        if ranges.is_empty() {
            return Ok(Vec::new());
        }
        if self.len == 0 {
            return Ok(vec![None; ranges.len()]);
        }
        let start_q: Vec<u32> = ranges.iter().map(|r| clamp_u32(r.start)).collect();
        let end_q: Vec<u32> = ranges.iter().map(|r| clamp_u32(r.end)).collect();
        let k_q: Vec<u32> = ks.iter().map(|&k| clamp_u32(k)).collect();
        let batch = k_q.len();
        let start_h = self.client.create_from_slice(u32::as_bytes(&start_q));
        let end_h = self.client.create_from_slice(u32::as_bytes(&end_q));
        let k_h = self.client.create_from_slice(u32::as_bytes(&k_q));
        let out_h = self.client.empty(batch * 4);
        let (count, dim) = self.dispatch(batch);
        unsafe {
            wm_quantile_kernel::launch_unchecked::<R>(
                &self.client,
                count,
                dim,
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                ArrayArg::from_raw_parts(self.zeros.clone(), self.alph_width as usize),
                ArrayArg::from_raw_parts(start_h, batch),
                ArrayArg::from_raw_parts(end_h, batch),
                ArrayArg::from_raw_parts(k_h, batch),
                ArrayArg::from_raw_parts(out_h.clone(), batch),
                self.len,
                self.wpl,
                self.bpl,
                self.alph_width,
            );
        }
        Ok(self.read_results(out_h))
    }

    /// One-thread-per-query launch shape; folds oversized batches into the
    /// Y dimension to stay under wgpu's 65 535 groups-per-dimension limit.
    fn dispatch(&self, batch: usize) -> (CubeCount, CubeDim) {
        let groups = (batch as u32).div_ceil(THREADS);
        let gx = groups.min(MAX_GROUPS_PER_DIM);
        let gy = groups.div_ceil(MAX_GROUPS_PER_DIM);
        (CubeCount::new_2d(gx, gy), CubeDim::new_1d(THREADS))
    }

    /// The batch's one synchronization: blocking readback + sentinel decode.
    fn read_results(&self, out: Handle) -> Vec<Option<usize>> {
        let bytes = self.client.read_one(out).expect("GPU readback");
        u32::from_bytes(&bytes)
            .iter()
            .map(|&v| {
                if v == NONE_SENTINEL {
                    None
                } else {
                    Some(v as usize)
                }
            })
            .collect()
    }
}

/// Clamps a host position/rank argument into `u32` range; anything above is
/// necessarily out of range on device (`len < u32::MAX`) and maps to `None`.
fn clamp_u32(x: usize) -> u32 {
    x.min(u32::MAX as usize) as u32
}

impl GpuWaveletMatrix<cubecl::wgpu::WgpuRuntime> {
    /// Uploads `wm` to the default wgpu device (Metal on macOS).
    ///
    /// # Errors
    ///
    /// See [`Self::new`].
    pub fn on_wgpu<I: BitVectorIndex>(wm: &WaveletMatrix<I>) -> Result<Self> {
        let device = Default::default();
        let client = cubecl::wgpu::WgpuRuntime::client(&device);
        Self::new(client, wm)
    }
}
