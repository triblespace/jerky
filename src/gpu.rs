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
//! # Device-resident pipelines
//!
//! [`DeviceU32Buffer`], [`GpuWaveletMatrix::access_batch_into`], and
//! [`GpuWaveletMatrix::rank_batch_into`] let a consumer keep query inputs and
//! results on the same device across several CubeCL kernels. [`GpuBitVector`]
//! provides the same resident seam for rank1/select1 over raw bit-vector data.
//! The slice-based batch methods remain the convenient
//! upload-dispatch-readback form; a multi-kernel query pipeline should upload
//! or produce its inputs once, chain resident launches, and call
//! [`DeviceU32Buffer::read`] only for the final result. Do **not** wrap
//! single-probe call sites — that reintroduces a sync per query and is orders of
//! magnitude slower than the CPU path. Construct all participating structures
//! from clones of one [`GpuContext`].
//! Device-compacted frontiers use separate [`DeviceBatchMeta`] and
//! [`DeviceDispatch`] records with the `*_into_dynamic` launch variants, so
//! capacity-sized buffers never turn spare slots into queries.
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
//! - The public types are runtime-generic, but this experimental module's
//!   execution parity is tested on WGPU. CubeCL 0.10 resolves CPU indirect
//!   dispatch by flushing its stream and reading the dispatch record, so the
//!   CPU backend cannot preserve WGPU's fully asynchronous scheduling even
//!   when downstream crates enable that backend.
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

use std::{ops::Range, sync::Arc};

use cubecl::client::ComputeClient;
use cubecl::prelude::*;
use cubecl::server::Handle;

use crate::bit_vector::{BitVectorData, BitVectorIndex, NumBits};
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
/// `[logical_len, capacity]` control record consumed as ordinary storage.
const BATCH_META_WORDS: usize = 2;
/// `[workgroups_x, workgroups_y, workgroups_z]` indirect dispatch record.
const DISPATCH_WORDS: usize = 3;

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

#[cube]
#[allow(clippy::too_many_arguments)]
fn wm_access_one(
    words: &Array<u32>,
    counts: &Array<u32>,
    zeros: &Array<u32>,
    mut pos: u32,
    n: u32,
    wpl: u32,
    bpl: u32,
    num_layers: u32,
) -> u32 {
    let mut result = 0xFFFF_FFFFu32;
    if pos < n {
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
        result = val;
    }
    result
}

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
        out[t] = wm_access_one(words, counts, zeros, pos_q[t], n, wpl, bpl, num_layers);
    }
}

#[cube(launch_unchecked)]
#[allow(clippy::too_many_arguments)]
fn wm_access_dynamic_kernel(
    words: &Array<u32>,
    counts: &Array<u32>,
    zeros: &Array<u32>,
    pos_q: &Array<u32>,
    out: &mut Array<u32>,
    batch_meta: &Array<u32>,
    n: u32,
    wpl: u32,
    bpl: u32,
    num_layers: u32,
) {
    let t = ABSOLUTE_POS;
    let logical_len = batch_meta[0] as usize;
    let declared_capacity = batch_meta[1] as usize;
    if t < logical_len && t < declared_capacity && t < pos_q.len() && t < out.len() {
        out[t] = wm_access_one(words, counts, zeros, pos_q[t], n, wpl, bpl, num_layers);
    }
}

#[cube]
#[allow(clippy::too_many_arguments)]
fn wm_rank_one(
    words: &Array<u32>,
    counts: &Array<u32>,
    zeros: &Array<u32>,
    pos: u32,
    val: u32,
    n: u32,
    wpl: u32,
    bpl: u32,
    num_layers: u32,
) -> u32 {
    let mut result = 0xFFFF_FFFFu32;
    if pos <= n {
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
        result = e - s;
    }
    result
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
        out[t] = wm_rank_one(
            words, counts, zeros, pos_q[t], val_q[t], n, wpl, bpl, num_layers,
        );
    }
}

#[cube(launch_unchecked)]
#[allow(clippy::too_many_arguments)]
fn wm_rank_dynamic_kernel(
    words: &Array<u32>,
    counts: &Array<u32>,
    zeros: &Array<u32>,
    pos_q: &Array<u32>,
    val_q: &Array<u32>,
    out: &mut Array<u32>,
    batch_meta: &Array<u32>,
    n: u32,
    wpl: u32,
    bpl: u32,
    num_layers: u32,
) {
    let t = ABSOLUTE_POS;
    let logical_len = batch_meta[0] as usize;
    let declared_capacity = batch_meta[1] as usize;
    // Both device-produced logical length and declared capacity are untrusted
    // inputs. Clamp them against the actual typed buffer bounds so a malformed
    // producer can under-process but can never make rank touch spare slots.
    if t < logical_len
        && t < declared_capacity
        && t < pos_q.len()
        && t < val_q.len()
        && t < out.len()
    {
        out[t] = wm_rank_one(
            words, counts, zeros, pos_q[t], val_q[t], n, wpl, bpl, num_layers,
        );
    }
}

#[cube]
fn bv_rank1_one(words: &Array<u32>, counts: &Array<u32>, pos: u32, n: u32) -> u32 {
    if pos <= n {
        layer_rank1(words, counts, 0u32, 0u32, pos)
    } else {
        u32::new(4_294_967_295i64)
    }
}

#[cube(launch_unchecked)]
fn bv_rank1_kernel(
    words: &Array<u32>,
    counts: &Array<u32>,
    pos_q: &Array<u32>,
    out: &mut Array<u32>,
    n: u32,
) {
    let t = ABSOLUTE_POS;
    if t < pos_q.len() {
        out[t] = bv_rank1_one(words, counts, pos_q[t], n);
    }
}

#[cube(launch_unchecked)]
fn bv_rank1_dynamic_kernel(
    words: &Array<u32>,
    counts: &Array<u32>,
    pos_q: &Array<u32>,
    out: &mut Array<u32>,
    batch_meta: &Array<u32>,
    n: u32,
) {
    let t = ABSOLUTE_POS;
    let logical_len = batch_meta[0] as usize;
    let declared_capacity = batch_meta[1] as usize;
    if t < logical_len && t < declared_capacity && t < pos_q.len() && t < out.len() {
        out[t] = bv_rank1_one(words, counts, pos_q[t], n);
    }
}

#[cube]
fn bv_select1_one(words: &Array<u32>, counts: &Array<u32>, k: u32, num_ones: u32, bpl: u32) -> u32 {
    if k < num_ones {
        layer_select1(words, counts, 0u32, 0u32, k, bpl)
    } else {
        u32::new(4_294_967_295i64)
    }
}

#[cube(launch_unchecked)]
fn bv_select1_kernel(
    words: &Array<u32>,
    counts: &Array<u32>,
    k_q: &Array<u32>,
    out: &mut Array<u32>,
    num_ones: u32,
    bpl: u32,
) {
    let t = ABSOLUTE_POS;
    if t < k_q.len() {
        out[t] = bv_select1_one(words, counts, k_q[t], num_ones, bpl);
    }
}

#[cube(launch_unchecked)]
fn bv_select1_dynamic_kernel(
    words: &Array<u32>,
    counts: &Array<u32>,
    k_q: &Array<u32>,
    out: &mut Array<u32>,
    batch_meta: &Array<u32>,
    num_ones: u32,
    bpl: u32,
) {
    let t = ABSOLUTE_POS;
    let logical_len = batch_meta[0] as usize;
    let declared_capacity = batch_meta[1] as usize;
    if t < logical_len && t < declared_capacity && t < k_q.len() && t < out.len() {
        out[t] = bv_select1_one(words, counts, k_q[t], num_ones, bpl);
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

/// A shared CubeCL client capability for matrices and typed resident buffers
/// that may safely participate in one device pipeline.
///
/// Clones preserve a private identity token as well as the client. Resident
/// launches accept buffers only when their context identity matches the
/// matrix's, so separately-created contexts fail closed while several matrices
/// constructed from clones of one context can share inputs and outputs.
pub struct GpuContext<R: Runtime> {
    client: ComputeClient<R>,
    identity: Arc<()>,
}

impl<R: Runtime> Clone for GpuContext<R> {
    fn clone(&self) -> Self {
        Self {
            client: self.client.clone(),
            identity: self.identity.clone(),
        }
    }
}

impl<R: Runtime> GpuContext<R> {
    /// Wraps a CubeCL client in a new, private compatibility domain.
    ///
    /// Clone this context when several [`GpuWaveletMatrix`] instances and
    /// buffers must compose in one resident pipeline. Constructing another
    /// context, even from a clone of the same raw client, intentionally creates
    /// a distinct domain.
    pub fn new(client: ComputeClient<R>) -> Self {
        Self {
            client,
            identity: Arc::new(()),
        }
    }

    /// Returns the CubeCL client for launching downstream kernels.
    pub fn client(&self) -> &ComputeClient<R> {
        &self.client
    }

    /// Uploads `values` into a typed device-resident buffer.
    ///
    /// Upload is enqueued without a host readback or synchronization. Empty
    /// logical buffers retain a one-word backing allocation so they remain
    /// bindable on runtimes that reject zero-byte storage buffers.
    ///
    /// # Errors
    ///
    /// An error is returned if the element count does not fit in the `u32`
    /// index space used by CubeCL query kernels.
    pub fn upload_u32(&self, values: &[u32]) -> Result<DeviceU32Buffer<R>> {
        validate_batch_len(values.len())?;
        let handle = if values.is_empty() {
            self.client.create_from_slice(u32::as_bytes(&[0]))
        } else {
            self.client.create_from_slice(u32::as_bytes(values))
        };
        Ok(DeviceU32Buffer {
            context: self.clone(),
            handle,
            len: values.len(),
        })
    }

    /// Allocates an uninitialized typed device-resident buffer.
    ///
    /// Kernels must initialize every element before it is read. Empty logical
    /// buffers retain a one-word backing allocation so they remain bindable on
    /// runtimes that reject zero-byte storage buffers.
    ///
    /// # Errors
    ///
    /// An error is returned if the element count does not fit in the `u32`
    /// index space used by CubeCL query kernels or its byte size overflows.
    pub fn empty_u32(&self, len: usize) -> Result<DeviceU32Buffer<R>> {
        validate_batch_len(len)?;
        let size = len
            .max(1)
            .checked_mul(std::mem::size_of::<u32>())
            .ok_or_else(|| Error::invalid_argument("device buffer byte length overflow"))?;
        Ok(DeviceU32Buffer {
            context: self.clone(),
            handle: self.client.empty(size),
            len,
        })
    }

    /// Creates an ordinary storage record `[logical_len, capacity]` for a
    /// device-produced batch.
    ///
    /// Downstream producer kernels may update the logical length through
    /// [`DeviceBatchMeta::output_arg`]. The capacity remains host-known and is
    /// checked against every data buffer before a dynamic launch.
    ///
    /// # Errors
    ///
    /// An error is returned if either value does not fit in `u32` or if
    /// `logical_len > capacity`.
    pub fn batch_meta(&self, logical_len: usize, capacity: usize) -> Result<DeviceBatchMeta<R>> {
        validate_logical_capacity(logical_len, capacity)?;
        let words = [logical_len as u32, capacity as u32];
        Ok(DeviceBatchMeta {
            context: self.clone(),
            handle: self.client.create_from_slice(u32::as_bytes(&words)),
            capacity,
        })
    }

    /// Creates an exclusive persistent indirect-dispatch record for a
    /// device-produced batch.
    ///
    /// The record starts as a constant-time tight `[x, y, 1]` cover for
    /// `ceil(logical_len / cube_dim.num_elems())` workgroups inside a
    /// host-validated capacity envelope.
    /// A producer kernel may update it through [`DeviceDispatch::output_arg`]
    /// before a consumer launches with [`DeviceDispatch::cube_count`]. Its
    /// allocation is deliberately persistent/exclusive: CubeCL's pooled small
    /// handles may share one WGPU buffer, while WGPU applies `INDIRECT` versus
    /// storage-usage conflicts at whole-buffer granularity.
    ///
    /// # Errors
    ///
    /// An error is returned for invalid lengths, an unsupported cube shape, or
    /// a capacity whose two-dimensional dispatch exceeds the device limit.
    ///
    /// # Panics
    ///
    /// Panics if the CubeCL runtime cannot create a persistent allocation.
    pub fn batch_dispatch(
        &self,
        logical_len: usize,
        capacity: usize,
        cube_dim: CubeDim,
    ) -> Result<DeviceDispatch<R>> {
        validate_logical_capacity(logical_len, capacity)?;
        let units = validate_cube_dim(&self.client, cube_dim)?;
        let max_groups = (capacity as u32).div_ceil(units);
        let max_cube_count = self.client.properties().hardware.max_cube_count;
        let (max_x, max_y) =
            dispatch_rectangle(max_groups, max_cube_count.0, max_cube_count.1).ok_or_else(|| {
                Error::invalid_argument(format!(
                    "batch capacity {capacity} needs {max_groups} workgroups, device 2-D limit is {}x{}",
                    max_cube_count.0, max_cube_count.1
                ))
            })?;
        if max_x as u64 * max_y as u64 * units as u64 > u32::MAX as u64 + 1 {
            return Err(Error::invalid_argument(
                "batch dispatch would wrap CubeCL's flattened u32 position",
            ));
        }
        let groups = (logical_len as u32).div_ceil(units);
        let (x, y) = tight_dispatch_rectangle(groups, max_x, max_y)
            .expect("logical dispatch fits because capacity dispatch fits");
        let words = [x, y, 1];
        let handle = self
            .client
            .memory_persistent_allocation((), |()| {
                self.client.create_from_slice(u32::as_bytes(&words))
            })
            .expect("persistent indirect-dispatch allocation");
        Ok(DeviceDispatch {
            context: self.clone(),
            handle,
            capacity,
            cube_dim,
            // Publish the capacity rectangle, rather than the raw hardware
            // limits, as the producer's planning envelope. Any rectangle
            // inside it is both device-legal and unable to exceed the
            // host-validated flattened-index budget.
            max_groups_x: max_x,
            max_groups_y: max_y,
        })
    }

    fn owns(&self, buffer: &DeviceU32Buffer<R>) -> bool {
        Arc::ptr_eq(&self.identity, &buffer.context.identity)
    }

    fn owns_meta(&self, meta: &DeviceBatchMeta<R>) -> bool {
        Arc::ptr_eq(&self.identity, &meta.context.identity)
    }

    fn owns_dispatch(&self, dispatch: &DeviceDispatch<R>) -> bool {
        Arc::ptr_eq(&self.identity, &dispatch.context.identity)
    }

    fn validate_owner(&self, name: &str, buffer: &DeviceU32Buffer<R>) -> Result<()> {
        if self.owns(buffer) {
            Ok(())
        } else {
            Err(Error::invalid_argument(format!(
                "{name} was allocated by a different GpuContext"
            )))
        }
    }

    fn validate_dynamic_batch(
        &self,
        buffers: &[(&str, &DeviceU32Buffer<R>)],
        meta: &DeviceBatchMeta<R>,
        dispatch: &DeviceDispatch<R>,
    ) -> Result<usize> {
        for &(name, buffer) in buffers {
            self.validate_owner(name, buffer)?;
        }
        if !self.owns_meta(meta) {
            return Err(Error::invalid_argument(
                "batch metadata was allocated by a different GpuContext",
            ));
        }
        if !self.owns_dispatch(dispatch) {
            return Err(Error::invalid_argument(
                "dispatch record was allocated by a different GpuContext",
            ));
        }
        let capacity = buffers
            .first()
            .map_or(meta.capacity(), |(_, buffer)| buffer.len());
        if buffers.iter().any(|(_, buffer)| buffer.len() != capacity)
            || meta.capacity() != capacity
            || dispatch.capacity() != capacity
        {
            let lengths = buffers
                .iter()
                .map(|(name, buffer)| format!("{name}={}", buffer.len()))
                .collect::<Vec<_>>()
                .join(", ");
            return Err(Error::invalid_argument(format!(
                "dynamic batch capacities must match: {lengths}, metadata={}, dispatch={}",
                meta.capacity(),
                dispatch.capacity()
            )));
        }
        Ok(capacity)
    }
}

/// Device-resident `[logical_len, capacity]` metadata for a dynamic batch.
///
/// This ordinary storage buffer is intentionally distinct from
/// [`DeviceDispatch`]: WGPU forbids binding an indirect-dispatch buffer as
/// storage in the consuming kernel. A dynamic query kernel defensively clamps
/// both metadata words against the typed data-buffer capacity.
pub struct DeviceBatchMeta<R: Runtime> {
    context: GpuContext<R>,
    handle: Handle,
    capacity: usize,
}

impl<R: Runtime> DeviceBatchMeta<R> {
    /// Returns the host-known maximum number of live batch elements.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Creates a typed CubeCL input argument for a consuming kernel.
    pub fn input_arg(&self) -> ArrayArg<R> {
        // SAFETY: the context allocates exactly two initialized `u32` words.
        unsafe { ArrayArg::from_raw_parts(self.handle.clone(), BATCH_META_WORDS) }
    }

    /// Creates a typed CubeCL output argument for a producer kernel.
    ///
    /// Producers must preserve `[logical_len, capacity]`, with
    /// `logical_len <= capacity`. Consumers still clamp both words against the
    /// actual data-buffer capacity, so malformed device metadata cannot cause
    /// an out-of-bounds query probe.
    pub fn output_arg(&mut self) -> ArrayArg<R> {
        // SAFETY: see `input_arg`; the mutable borrow represents producer
        // access to the complete two-word record.
        unsafe { ArrayArg::from_raw_parts(self.handle.clone(), BATCH_META_WORDS) }
    }
}

/// An exclusive persistent `[x, y, z]` indirect-dispatch record.
///
/// The record carries the [`CubeDim`] used to interpret its workgroup count
/// and the host-known capacity it may cover. Bind it as storage only in a
/// producer kernel, then as indirect dispatch through [`cube_count`](Self::cube_count)
/// in a later consumer launch; never bind it as storage in that same consumer.
pub struct DeviceDispatch<R: Runtime> {
    context: GpuContext<R>,
    handle: Handle,
    capacity: usize,
    cube_dim: CubeDim,
    max_groups_x: u32,
    max_groups_y: u32,
}

impl<R: Runtime> DeviceDispatch<R> {
    /// Returns the maximum number of batch elements represented by the record.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Returns the workgroup shape paired with this indirect record.
    pub fn cube_dim(&self) -> CubeDim {
        self.cube_dim
    }

    /// Maximum capacity-safe X workgroup count for a device-written rectangle.
    pub fn max_groups_x(&self) -> u32 {
        self.max_groups_x
    }

    /// Maximum capacity-safe Y workgroup count for a device-written rectangle.
    pub fn max_groups_y(&self) -> u32 {
        self.max_groups_y
    }

    /// Creates a typed CubeCL output argument for a producer kernel.
    ///
    /// The producer must write `[x, y, 1]` covering
    /// `ceil(logical_len / cube_dim.num_elems())` workgroups, without exceeding
    /// [`max_groups_x`](Self::max_groups_x),
    /// [`max_groups_y`](Self::max_groups_y), the host-known capacity, or the
    /// flattened `u32` index space. For a nonempty batch, a constant-time
    /// tight cover is `y = ceil(groups / max_groups_x)`, then
    /// `x = ceil(groups / y)`; it launches fewer than `y` spare workgroups and
    /// stays inside the capacity-safe envelope. Use `[0, 1, 1]` for an empty
    /// batch.
    pub fn output_arg(&mut self) -> ArrayArg<R> {
        // SAFETY: the persistent allocation contains exactly three `u32`
        // words and is exclusively owned by this typed wrapper.
        unsafe { ArrayArg::from_raw_parts(self.handle.clone(), DISPATCH_WORDS) }
    }

    /// Returns this record as CubeCL's indirect dispatch count.
    pub fn cube_count(&self) -> CubeCount {
        CubeCount::Dynamic(self.handle.clone().binding())
    }
}

/// An owned, device-resident array of `u32` values allocated by a
/// [`GpuContext`].
///
/// Its handle and length stay private; [`input_arg`](Self::input_arg) and
/// [`output_arg`](Self::output_arg) expose a length-checked CubeCL array
/// argument for downstream kernels without exposing raw byte handles.
///
/// Device work is enqueued asynchronously. Calling [`read`](Self::read) is the
/// synchronization point. A pipeline should enqueue its kernels and final read
/// on one CubeCL stream (as the single-threaded launch sequence does here);
/// stream coordination across host threads remains CubeCL's responsibility.
pub struct DeviceU32Buffer<R: Runtime> {
    context: GpuContext<R>,
    handle: Handle,
    len: usize,
}

impl<R: Runtime> DeviceU32Buffer<R> {
    /// Returns the number of `u32` elements in the buffer.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns whether the buffer contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the CubeCL client that owns this buffer.
    ///
    /// Use this client when launching a downstream CubeCL kernel with
    /// [`input_arg`](Self::input_arg) or [`output_arg`](Self::output_arg).
    pub fn client(&self) -> &ComputeClient<R> {
        self.context.client()
    }

    /// Creates a typed CubeCL input argument over the complete buffer.
    pub fn input_arg(&self) -> ArrayArg<R> {
        // SAFETY: `handle` was allocated by `context.client` for at least
        // `len * size_of::<u32>()` bytes and the element count is immutable.
        unsafe { ArrayArg::from_raw_parts(self.handle.clone(), self.len) }
    }

    /// Creates a typed CubeCL output argument over the complete buffer.
    ///
    /// The mutable borrow makes write intent explicit at Jerky's wrapper
    /// boundary. CubeCL arguments own cloned handles, so launch-level aliasing
    /// remains the downstream kernel author's responsibility.
    pub fn output_arg(&mut self) -> ArrayArg<R> {
        // SAFETY: See `input_arg`; this method additionally requires exclusive
        // access to the typed wrapper while creating the output argument.
        unsafe { ArrayArg::from_raw_parts(self.handle.clone(), self.len) }
    }

    /// Reads all values back to the host, synchronizing queued device work.
    ///
    /// A resident pipeline should call this only for its final output.
    ///
    /// # Panics
    ///
    /// Panics if the CubeCL runtime cannot read the device buffer.
    pub fn read(&self) -> Vec<u32> {
        let bytes = self
            .context
            .client
            .read_one(self.handle.clone())
            .expect("GPU readback");
        u32::from_bytes(&bytes)[..self.len].to_vec()
    }
}

fn layer_layout(len: usize) -> (usize, usize, usize) {
    let data_words = len.div_ceil(32);
    let words_per_layer =
        (data_words + 1).div_ceil(WORDS_PER_BLOCK as usize) * WORDS_PER_BLOCK as usize;
    let blocks_per_layer = words_per_layer / WORDS_PER_BLOCK as usize;
    (data_words, words_per_layer, blocks_per_layer)
}

fn append_packed_layer(
    source: &[u64],
    data_words: usize,
    words_per_layer: usize,
    words: &mut Vec<u32>,
    counts: &mut Vec<u32>,
) -> u32 {
    let stripe_start = words.len();
    for &word in source {
        words.push(word as u32);
        words.push((word >> 32) as u32);
    }
    words.truncate(stripe_start + data_words);
    words.resize(stripe_start + words_per_layer, 0);

    let mut rank = 0u32;
    for (index, &word) in words[stripe_start..].iter().enumerate() {
        if index % WORDS_PER_BLOCK as usize == 0 {
            counts.push(rank);
        }
        rank += word.count_ones();
    }
    rank
}

/// Raw [`BitVectorData`] uploaded once for resident rank1/select1 batches.
///
/// The GPU form builds its own compact block-rank directory from the canonical
/// raw words; it does not depend on, expose, or duplicate a host-side
/// `BitVectorIndex`. All query buffers must belong to the same [`GpuContext`].
pub struct GpuBitVector<R: Runtime> {
    context: GpuContext<R>,
    words: Handle,
    words_len: usize,
    counts: Handle,
    counts_len: usize,
    len: u32,
    num_ones: u32,
    bpl: u32,
}

impl<R: Runtime> GpuBitVector<R> {
    /// Uploads raw bit-vector data to the device served by `client`.
    pub fn new(client: ComputeClient<R>, data: &BitVectorData) -> Result<Self> {
        Self::with_context(GpuContext::new(client), data)
    }

    /// Uploads raw bit-vector data into an existing compatibility domain.
    ///
    /// An error is returned when `data.len() >= u32::MAX`, because
    /// `u32::MAX` is reserved as the device miss sentinel.
    pub fn with_context(context: GpuContext<R>, data: &BitVectorData) -> Result<Self> {
        if data.len() >= u32::MAX as usize {
            return Err(Error::invalid_argument(format!(
                "GPU form requires len() < u32::MAX, but got {}",
                data.len()
            )));
        }
        let (data_words, wpl, bpl) = layer_layout(data.len());
        let mut words_host = Vec::with_capacity(wpl);
        let mut counts_host = Vec::with_capacity(bpl);
        let num_ones = append_packed_layer(
            data.words(),
            data_words,
            wpl,
            &mut words_host,
            &mut counts_host,
        );
        let words_len = words_host.len();
        let counts_len = counts_host.len();
        let words = context.client.create_from_slice(u32::as_bytes(&words_host));
        let counts = context
            .client
            .create_from_slice(u32::as_bytes(&counts_host));
        Ok(Self {
            context,
            words,
            words_len,
            counts,
            counts_len,
            len: data.len() as u32,
            num_ones,
            bpl: bpl as u32,
        })
    }

    /// Number of valid bits.
    pub fn len(&self) -> usize {
        self.len as usize
    }

    /// Whether the vector has no valid bits.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Number of set bits.
    pub fn num_ones(&self) -> usize {
        self.num_ones as usize
    }

    /// Shared context owning this vector's device allocations.
    pub fn context(&self) -> &GpuContext<R> {
        &self.context
    }

    /// Host convenience wrapper for batched rank1 queries.
    pub fn rank1_batch(&self, positions: &[usize]) -> Result<Vec<Option<usize>>> {
        let positions: Vec<_> = positions
            .iter()
            .map(|&position| clamp_u32(position))
            .collect();
        let positions = self.context.upload_u32(&positions)?;
        let output = self.rank1_batch_resident(&positions)?;
        Ok(decode_results(output.read()))
    }

    /// Enqueues rank1 for resident positions and returns a resident result.
    pub fn rank1_batch_resident(
        &self,
        positions: &DeviceU32Buffer<R>,
    ) -> Result<DeviceU32Buffer<R>> {
        self.context.validate_owner("positions", positions)?;
        let mut output = self.context.empty_u32(positions.len())?;
        self.rank1_batch_into(positions, &mut output)?;
        Ok(output)
    }

    /// Enqueues rank1 into a caller-owned resident result buffer.
    pub fn rank1_batch_into(
        &self,
        positions: &DeviceU32Buffer<R>,
        output: &mut DeviceU32Buffer<R>,
    ) -> Result<()> {
        self.validate_pair("positions", positions, output)?;
        if positions.is_empty() {
            return Ok(());
        }
        let (count, dim) = dispatch(positions.len());
        unsafe {
            bv_rank1_kernel::launch_unchecked::<R>(
                &self.context.client,
                count,
                dim,
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                positions.input_arg(),
                output.output_arg(),
                self.len,
            );
        }
        Ok(())
    }

    /// Enqueues rank1 for a device-produced logical prefix using indirect
    /// dispatch, leaving spare capacity slots untouched.
    pub fn rank1_batch_into_dynamic(
        &self,
        positions: &DeviceU32Buffer<R>,
        output: &mut DeviceU32Buffer<R>,
        meta: &DeviceBatchMeta<R>,
        dispatch: &DeviceDispatch<R>,
    ) -> Result<()> {
        let capacity = self.context.validate_dynamic_batch(
            &[("positions", positions), ("output", output)],
            meta,
            dispatch,
        )?;
        if capacity == 0 {
            return Ok(());
        }
        unsafe {
            bv_rank1_dynamic_kernel::launch_unchecked::<R>(
                &self.context.client,
                dispatch.cube_count(),
                dispatch.cube_dim(),
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                positions.input_arg(),
                output.output_arg(),
                meta.input_arg(),
                self.len,
            );
        }
        Ok(())
    }

    /// Host convenience wrapper for batched select1 queries.
    pub fn select1_batch(&self, ranks: &[usize]) -> Result<Vec<Option<usize>>> {
        let ranks: Vec<_> = ranks.iter().map(|&rank| clamp_u32(rank)).collect();
        let ranks = self.context.upload_u32(&ranks)?;
        let output = self.select1_batch_resident(&ranks)?;
        Ok(decode_results(output.read()))
    }

    /// Enqueues select1 for resident ranks and returns a resident result.
    pub fn select1_batch_resident(&self, ranks: &DeviceU32Buffer<R>) -> Result<DeviceU32Buffer<R>> {
        self.context.validate_owner("ranks", ranks)?;
        let mut output = self.context.empty_u32(ranks.len())?;
        self.select1_batch_into(ranks, &mut output)?;
        Ok(output)
    }

    /// Enqueues select1 into a caller-owned resident result buffer.
    pub fn select1_batch_into(
        &self,
        ranks: &DeviceU32Buffer<R>,
        output: &mut DeviceU32Buffer<R>,
    ) -> Result<()> {
        self.validate_pair("ranks", ranks, output)?;
        if ranks.is_empty() {
            return Ok(());
        }
        let (count, dim) = dispatch(ranks.len());
        unsafe {
            bv_select1_kernel::launch_unchecked::<R>(
                &self.context.client,
                count,
                dim,
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                ranks.input_arg(),
                output.output_arg(),
                self.num_ones,
                self.bpl,
            );
        }
        Ok(())
    }

    /// Enqueues select1 for a device-produced logical prefix using indirect
    /// dispatch, leaving spare capacity slots untouched.
    pub fn select1_batch_into_dynamic(
        &self,
        ranks: &DeviceU32Buffer<R>,
        output: &mut DeviceU32Buffer<R>,
        meta: &DeviceBatchMeta<R>,
        dispatch: &DeviceDispatch<R>,
    ) -> Result<()> {
        let capacity = self.context.validate_dynamic_batch(
            &[("ranks", ranks), ("output", output)],
            meta,
            dispatch,
        )?;
        if capacity == 0 {
            return Ok(());
        }
        unsafe {
            bv_select1_dynamic_kernel::launch_unchecked::<R>(
                &self.context.client,
                dispatch.cube_count(),
                dispatch.cube_dim(),
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                ranks.input_arg(),
                output.output_arg(),
                meta.input_arg(),
                self.num_ones,
                self.bpl,
            );
        }
        Ok(())
    }

    fn validate_pair(
        &self,
        input_name: &str,
        input: &DeviceU32Buffer<R>,
        output: &DeviceU32Buffer<R>,
    ) -> Result<()> {
        self.context.validate_owner(input_name, input)?;
        self.context.validate_owner("output", output)?;
        if input.len() == output.len() {
            Ok(())
        } else {
            Err(Error::invalid_argument(format!(
                "{input_name} and output must have equal lengths, got {} and {}",
                input.len(),
                output.len()
            )))
        }
    }
}

/// A [`WaveletMatrix`] uploaded to the GPU, answering batches of queries with
/// one dispatch and one synchronization per batch. See the [module docs](self)
/// for when this beats the CPU form and when it does not.
pub struct GpuWaveletMatrix<R: Runtime> {
    context: GpuContext<R>,
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
        Self::with_context(GpuContext::new(client), wm)
    }

    /// Uploads `wm` into an existing context's compatibility domain.
    ///
    /// Construct several matrices from clones of the same context when their
    /// resident rank launches must share typed input or output buffers.
    ///
    /// # Errors
    ///
    /// An error is returned if `wm.len() >= u32::MAX` or
    /// `wm.alph_size() > u32::MAX`.
    pub fn with_context<I: BitVectorIndex>(
        context: GpuContext<R>,
        wm: &WaveletMatrix<I>,
    ) -> Result<Self> {
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
        let (data_words, wpl, bpl) = layer_layout(n);

        let mut words_host: Vec<u32> = Vec::with_capacity(wpl * width);
        let mut counts_host: Vec<u32> = Vec::with_capacity(bpl * width);
        let mut zeros_host: Vec<u32> = Vec::with_capacity(width);

        for layer in wm.layers() {
            zeros_host.push(layer.num_zeros() as u32);
            append_packed_layer(
                layer.data.words(),
                data_words,
                wpl,
                &mut words_host,
                &mut counts_host,
            );
        }

        let words_len = words_host.len().max(1);
        let counts_len = counts_host.len().max(1);
        // Keep buffers non-empty so kernels can always bind them.
        words_host.resize(words_len, 0);
        counts_host.resize(counts_len, 0);
        let zeros_len = zeros_host.len().max(1);
        zeros_host.resize(zeros_len, 0);

        let words = context.client.create_from_slice(u32::as_bytes(&words_host));
        let counts = context
            .client
            .create_from_slice(u32::as_bytes(&counts_host));
        let zeros = context.client.create_from_slice(u32::as_bytes(&zeros_host));

        Ok(Self {
            context,
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

    /// Returns the shared context that owns this matrix's device allocations.
    pub fn context(&self) -> &GpuContext<R> {
        &self.context
    }

    /// Uploads `values` into a typed device-resident buffer owned by this
    /// matrix's shared context.
    ///
    /// Upload is enqueued without a host readback or synchronization. Empty
    /// logical buffers retain a one-word backing allocation so they remain
    /// bindable on runtimes that reject zero-byte storage buffers.
    ///
    /// # Errors
    ///
    /// An error is returned if the element count does not fit in the `u32`
    /// index space used by CubeCL query kernels.
    pub fn upload_u32(&self, values: &[u32]) -> Result<DeviceU32Buffer<R>> {
        self.context.upload_u32(values)
    }

    /// Allocates an uninitialized typed device-resident buffer owned by this
    /// matrix's shared context.
    ///
    /// Kernels must initialize every element before it is read. Empty logical
    /// buffers retain a one-word backing allocation so they remain bindable on
    /// runtimes that reject zero-byte storage buffers.
    ///
    /// # Errors
    ///
    /// An error is returned if the element count does not fit in the `u32`
    /// index space used by CubeCL query kernels or its byte size overflows.
    pub fn empty_u32(&self, len: usize) -> Result<DeviceU32Buffer<R>> {
        self.context.empty_u32(len)
    }

    /// Batched [`WaveletMatrix::access`]: returns the integer at each
    /// position, or `None` where the position is out of bounds.
    ///
    /// One dispatch, one sync, regardless of `positions.len()`.
    pub fn access_batch(&self, positions: &[usize]) -> Result<Vec<Option<usize>>> {
        let pos_q: Vec<u32> = positions.iter().map(|&p| clamp_u32(p)).collect();
        let positions = self.upload_u32(&pos_q)?;
        let output = self.access_batch_resident(&positions)?;
        Ok(decode_results(output.read()))
    }

    /// Enqueues access queries from a device-resident position buffer.
    ///
    /// No host transfer or synchronization occurs. The returned raw `u32`
    /// values use `u32::MAX` for out-of-range positions. Use
    /// [`access_batch_into`](Self::access_batch_into) to reuse an allocation.
    pub fn access_batch_resident(
        &self,
        positions: &DeviceU32Buffer<R>,
    ) -> Result<DeviceU32Buffer<R>> {
        self.context.validate_owner("positions", positions)?;
        let mut output = self.empty_u32(positions.len())?;
        self.access_batch_into(positions, &mut output)?;
        Ok(output)
    }

    /// Enqueues access queries into a caller-owned device buffer.
    ///
    /// Both buffers must have equal lengths and belong to this matrix's
    /// [`GpuContext`]. This method performs no host read or synchronization.
    pub fn access_batch_into(
        &self,
        positions: &DeviceU32Buffer<R>,
        output: &mut DeviceU32Buffer<R>,
    ) -> Result<()> {
        self.context.validate_owner("positions", positions)?;
        self.context.validate_owner("output", output)?;
        if positions.len() != output.len() {
            return Err(Error::invalid_argument(format!(
                "positions and output must have equal lengths, got {} and {}",
                positions.len(),
                output.len()
            )));
        }
        if positions.is_empty() {
            return Ok(());
        }

        let (count, dim) = dispatch(positions.len());
        unsafe {
            wm_access_kernel::launch_unchecked::<R>(
                &self.context.client,
                count,
                dim,
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                ArrayArg::from_raw_parts(self.zeros.clone(), self.alph_width as usize),
                positions.input_arg(),
                output.output_arg(),
                self.len,
                self.wpl,
                self.bpl,
                self.alph_width,
            );
        }
        Ok(())
    }

    /// Enqueues access for a device-produced logical prefix using indirect
    /// dispatch, leaving spare capacity slots untouched.
    ///
    /// Positions, output, metadata, and dispatch must share this matrix's
    /// context and capacity. The device-written logical length is checked by
    /// every thread; no host read or synchronization occurs.
    pub fn access_batch_into_dynamic(
        &self,
        positions: &DeviceU32Buffer<R>,
        output: &mut DeviceU32Buffer<R>,
        meta: &DeviceBatchMeta<R>,
        dispatch: &DeviceDispatch<R>,
    ) -> Result<()> {
        let capacity = self.context.validate_dynamic_batch(
            &[("positions", positions), ("output", output)],
            meta,
            dispatch,
        )?;
        if capacity == 0 {
            return Ok(());
        }

        unsafe {
            wm_access_dynamic_kernel::launch_unchecked::<R>(
                &self.context.client,
                dispatch.cube_count(),
                dispatch.cube_dim(),
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                ArrayArg::from_raw_parts(self.zeros.clone(), self.alph_width as usize),
                positions.input_arg(),
                output.output_arg(),
                meta.input_arg(),
                self.len,
                self.wpl,
                self.bpl,
                self.alph_width,
            );
        }
        Ok(())
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
        let pos_q: Vec<u32> = positions.iter().map(|&p| clamp_u32(p)).collect();
        let val_q: Vec<u32> = values.iter().map(|&v| v as u32).collect();
        let positions = self.upload_u32(&pos_q)?;
        let values = self.upload_u32(&val_q)?;
        let output = self.rank_batch_resident(&positions, &values)?;
        Ok(decode_results(output.read()))
    }

    /// Enqueues batched rank queries using device-resident inputs and returns
    /// a device-resident output buffer.
    ///
    /// No host transfer or synchronization occurs. The returned `u32` values
    /// use `u32::MAX` for out-of-range positions, matching the `None` entries
    /// decoded by [`rank_batch`](Self::rank_batch). Use
    /// [`rank_batch_into`](Self::rank_batch_into) to reuse an existing output
    /// allocation.
    ///
    /// # Errors
    ///
    /// An error is returned if the input lengths differ or either input belongs
    /// to another [`GpuContext`].
    pub fn rank_batch_resident(
        &self,
        positions: &DeviceU32Buffer<R>,
        values: &DeviceU32Buffer<R>,
    ) -> Result<DeviceU32Buffer<R>> {
        if positions.len() != values.len() {
            return Err(Error::invalid_argument(format!(
                "positions and values must have equal lengths, got {} and {}",
                positions.len(),
                values.len()
            )));
        }
        self.context.validate_owner("positions", positions)?;
        self.context.validate_owner("values", values)?;
        let mut output = self.empty_u32(positions.len())?;
        self.rank_batch_into(positions, values, &mut output)?;
        Ok(output)
    }

    /// Enqueues batched rank queries from device-resident `positions` and
    /// `values` into an existing device-resident `output` buffer.
    ///
    /// This method only launches work; it performs no host transfer or
    /// synchronization. All three buffers must have equal lengths and belong
    /// to this matrix's [`GpuContext`]. Each output is the raw `u32` rank, with
    /// `u32::MAX` denoting an out-of-range position.
    ///
    /// # Errors
    ///
    /// An error is returned for mismatched lengths or buffer ownership.
    pub fn rank_batch_into(
        &self,
        positions: &DeviceU32Buffer<R>,
        values: &DeviceU32Buffer<R>,
        output: &mut DeviceU32Buffer<R>,
    ) -> Result<()> {
        self.context.validate_owner("positions", positions)?;
        self.context.validate_owner("values", values)?;
        self.context.validate_owner("output", output)?;
        if positions.len() != values.len() || positions.len() != output.len() {
            return Err(Error::invalid_argument(format!(
                "positions, values, and output must have equal lengths, got {}, {}, and {}",
                positions.len(),
                values.len(),
                output.len()
            )));
        }
        if positions.is_empty() {
            return Ok(());
        }

        let (count, dim) = dispatch(positions.len());
        unsafe {
            wm_rank_kernel::launch_unchecked::<R>(
                &self.context.client,
                count,
                dim,
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                ArrayArg::from_raw_parts(self.zeros.clone(), self.alph_width as usize),
                positions.input_arg(),
                values.input_arg(),
                output.output_arg(),
                self.len,
                self.wpl,
                self.bpl,
                self.alph_width,
            );
        }
        Ok(())
    }

    /// Enqueues rank for a device-produced logical prefix of capacity-sized
    /// resident buffers using indirect dispatch.
    ///
    /// `meta` is ordinary `[logical_len, capacity]` storage read by the rank
    /// kernel. `dispatch` is a separate exclusive `[x, y, z]` record used only
    /// as [`CubeCount::Dynamic`]; it is deliberately not bound as storage in
    /// the consuming kernel. Each thread checks the device logical length,
    /// declared capacity, and actual buffer bounds before probing, so spare or
    /// uninitialized capacity slots are never queried.
    ///
    /// All data buffers must have the same capacity. Their shared
    /// [`GpuContext`], `meta`, and `dispatch` must also match. This method
    /// enqueues work without a host read or synchronization.
    ///
    /// # Errors
    ///
    /// An error is returned for mismatched capacities or compatibility
    /// domains.
    pub fn rank_batch_into_dynamic(
        &self,
        positions: &DeviceU32Buffer<R>,
        values: &DeviceU32Buffer<R>,
        output: &mut DeviceU32Buffer<R>,
        meta: &DeviceBatchMeta<R>,
        dispatch: &DeviceDispatch<R>,
    ) -> Result<()> {
        let capacity = self.context.validate_dynamic_batch(
            &[
                ("positions", positions),
                ("values", values),
                ("output", output),
            ],
            meta,
            dispatch,
        )?;
        if capacity == 0 {
            return Ok(());
        }

        unsafe {
            wm_rank_dynamic_kernel::launch_unchecked::<R>(
                &self.context.client,
                dispatch.cube_count(),
                dispatch.cube_dim(),
                ArrayArg::from_raw_parts(self.words.clone(), self.words_len),
                ArrayArg::from_raw_parts(self.counts.clone(), self.counts_len),
                ArrayArg::from_raw_parts(self.zeros.clone(), self.alph_width as usize),
                positions.input_arg(),
                values.input_arg(),
                output.output_arg(),
                meta.input_arg(),
                self.len,
                self.wpl,
                self.bpl,
                self.alph_width,
            );
        }
        Ok(())
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
        let k_h = self.context.client.create_from_slice(u32::as_bytes(&k_q));
        let val_h = self.context.client.create_from_slice(u32::as_bytes(&val_q));
        let out_h = self.context.client.empty(batch * 4);
        let (count, dim) = dispatch(batch);
        unsafe {
            wm_select_kernel::launch_unchecked::<R>(
                &self.context.client,
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
        let start_h = self
            .context
            .client
            .create_from_slice(u32::as_bytes(&start_q));
        let end_h = self.context.client.create_from_slice(u32::as_bytes(&end_q));
        let k_h = self.context.client.create_from_slice(u32::as_bytes(&k_q));
        let out_h = self.context.client.empty(batch * 4);
        let (count, dim) = dispatch(batch);
        unsafe {
            wm_quantile_kernel::launch_unchecked::<R>(
                &self.context.client,
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

    /// The batch's one synchronization: blocking readback + sentinel decode.
    fn read_results(&self, out: Handle) -> Vec<Option<usize>> {
        let bytes = self.context.client.read_one(out).expect("GPU readback");
        decode_results(u32::from_bytes(&bytes).to_vec())
    }
}

/// Returns the least-area legal 2-D workgroup rectangle covering `groups`.
/// Ties prefer the wider rectangle. At least one side of an optimal rectangle
/// is no larger than `ceil(sqrt(groups))`, so the two bounded scans cover every
/// candidate without walking either complete device dimension.
fn dispatch_rectangle(groups: u32, max_x: u32, max_y: u32) -> Option<(u32, u32)> {
    if groups == 0 {
        return Some((0, 1));
    }
    if max_x == 0 || max_y == 0 || groups as u64 > max_x as u64 * max_y as u64 {
        return None;
    }
    if groups <= max_x {
        return Some((groups, 1));
    }

    let mut root = (groups as f64).sqrt() as u32;
    if (root as u64) * (root as u64) < groups as u64 {
        root += 1;
    }
    let mut best: Option<(u64, u32, u32)> = None;
    let mut consider = |x: u32, y: u32| {
        if x == 0 || y == 0 || x > max_x || y > max_y {
            return;
        }
        let area = x as u64 * y as u64;
        if area < groups as u64 {
            return;
        }
        if best.is_none_or(|(best_area, best_x, _)| {
            area < best_area || (area == best_area && x > best_x)
        }) {
            best = Some((area, x, y));
        }
    };

    let min_y = groups.div_ceil(max_x).max(1);
    for y in min_y..=root.min(max_y) {
        consider(groups.div_ceil(y), y);
    }
    let min_x = groups.div_ceil(max_y).max(1);
    for x in min_x..=root.min(max_x) {
        consider(x, groups.div_ceil(x));
    }
    best.map(|(_, x, y)| (x, y))
}

/// Returns a constant-time bounded-overdispatch rectangle inside a previously
/// validated planning envelope. The result covers `groups` with fewer than
/// `y` spare workgroups.
fn tight_dispatch_rectangle(groups: u32, max_x: u32, max_y: u32) -> Option<(u32, u32)> {
    if groups == 0 {
        return Some((0, 1));
    }
    if max_x == 0 || max_y == 0 || groups as u64 > max_x as u64 * max_y as u64 {
        return None;
    }
    let y = groups.div_ceil(max_x);
    let x = groups.div_ceil(y);
    debug_assert!(x <= max_x && y <= max_y);
    Some((x, y))
}

/// One-thread-per-query launch shape with the least possible number of spare
/// workgroups under wgpu's 65,535-per-dimension limit.
fn dispatch(batch: usize) -> (CubeCount, CubeDim) {
    debug_assert!(batch > 0 && batch <= u32::MAX as usize);
    let groups = (batch as u32).div_ceil(THREADS);
    let (x, y) = dispatch_rectangle(groups, MAX_GROUPS_PER_DIM, MAX_GROUPS_PER_DIM)
        .expect("a u32-sized batch fits the WGPU 2-D dispatch limit");
    let lanes = x as u64 * y as u64 * THREADS as u64;
    assert!(
        lanes <= u32::MAX as u64 + 1,
        "dispatch would wrap CubeCL's flattened u32 position"
    );
    (CubeCount::new_2d(x, y), CubeDim::new_1d(THREADS))
}

fn decode_results(values: Vec<u32>) -> Vec<Option<usize>> {
    values
        .into_iter()
        .map(|v| {
            if v == NONE_SENTINEL {
                None
            } else {
                Some(v as usize)
            }
        })
        .collect()
}

/// Clamps a host position/rank argument into `u32` range; anything above is
/// necessarily out of range on device (`len < u32::MAX`) and maps to `None`.
fn clamp_u32(x: usize) -> u32 {
    x.min(u32::MAX as usize) as u32
}

fn validate_batch_len(len: usize) -> Result<()> {
    if len <= u32::MAX as usize {
        Ok(())
    } else {
        Err(Error::invalid_argument(format!(
            "GPU batch length must fit in u32, but got {len}"
        )))
    }
}

fn validate_logical_capacity(logical_len: usize, capacity: usize) -> Result<()> {
    validate_batch_len(logical_len)?;
    validate_batch_len(capacity)?;
    if logical_len <= capacity {
        Ok(())
    } else {
        Err(Error::invalid_argument(format!(
            "logical batch length {logical_len} exceeds capacity {capacity}"
        )))
    }
}

fn validate_cube_dim<R: Runtime>(client: &ComputeClient<R>, cube_dim: CubeDim) -> Result<u32> {
    let units = cube_dim
        .x
        .checked_mul(cube_dim.y)
        .and_then(|xy| xy.checked_mul(cube_dim.z))
        .filter(|&units| units != 0)
        .ok_or_else(|| {
            Error::invalid_argument("cube dimensions must be nonzero and not overflow")
        })?;
    let hardware = &client.properties().hardware;
    let max_dim = hardware.max_cube_dim;
    if cube_dim.x > max_dim.0 || cube_dim.y > max_dim.1 || cube_dim.z > max_dim.2 {
        return Err(Error::invalid_argument(format!(
            "cube dimensions ({}, {}, {}) exceed device limit ({}, {}, {})",
            cube_dim.x, cube_dim.y, cube_dim.z, max_dim.0, max_dim.1, max_dim.2
        )));
    }
    if units > hardware.max_units_per_cube {
        return Err(Error::invalid_argument(format!(
            "cube has {units} units, device limit is {}",
            hardware.max_units_per_cube
        )));
    }
    Ok(units)
}

impl GpuContext<cubecl::wgpu::WgpuRuntime> {
    /// Creates a compatibility domain on the default wgpu device (Metal on
    /// macOS).
    pub fn on_wgpu() -> Self {
        let device = Default::default();
        let client = cubecl::wgpu::WgpuRuntime::client(&device);
        Self::new(client)
    }
}

impl GpuBitVector<cubecl::wgpu::WgpuRuntime> {
    /// Uploads raw bit-vector data to the default wgpu device.
    pub fn on_wgpu(data: &BitVectorData) -> Result<Self> {
        Self::with_context(GpuContext::on_wgpu(), data)
    }
}

impl GpuWaveletMatrix<cubecl::wgpu::WgpuRuntime> {
    /// Uploads `wm` to the default wgpu device (Metal on macOS).
    ///
    /// # Errors
    ///
    /// See [`Self::new`].
    pub fn on_wgpu<I: BitVectorIndex>(wm: &WaveletMatrix<I>) -> Result<Self> {
        Self::with_context(GpuContext::on_wgpu(), wm)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dispatch_rectangle_is_globally_minimal_on_small_domains() {
        for max_x in 1u32..20 {
            for max_y in 1u32..20 {
                for groups in 0u32..=max_x * max_y {
                    let actual = dispatch_rectangle(groups, max_x, max_y).unwrap();
                    let actual_area = actual.0 as u64 * actual.1 as u64;
                    let expected_area = if groups == 0 {
                        0
                    } else {
                        (1..=max_x)
                            .flat_map(|x| (1..=max_y).map(move |y| x as u64 * y as u64))
                            .filter(|&area| area >= groups as u64)
                            .min()
                            .unwrap()
                    };
                    assert_eq!(actual_area, expected_area, "{groups} in {max_x}x{max_y}");
                }
            }
        }
    }

    #[test]
    fn dispatch_rectangle_does_not_double_the_first_2d_batch() {
        assert_eq!(
            dispatch_rectangle(65_536, MAX_GROUPS_PER_DIM, MAX_GROUPS_PER_DIM),
            Some((32_768, 2))
        );
    }

    #[test]
    fn tight_dispatch_rectangle_is_legal_and_bounded() {
        for max_x in 1u32..20 {
            for max_y in 1u32..20 {
                for groups in 1u32..=max_x * max_y {
                    let (x, y) = tight_dispatch_rectangle(groups, max_x, max_y).unwrap();
                    let area = x as u64 * y as u64;
                    assert!(x <= max_x && y <= max_y);
                    assert!(area >= groups as u64);
                    assert!(area - (groups as u64) < y as u64);
                }
            }
        }
        assert_eq!(
            tight_dispatch_rectangle(65_536, MAX_GROUPS_PER_DIM, MAX_GROUPS_PER_DIM),
            Some((32_768, 2))
        );
    }

    #[test]
    fn largest_fixed_batch_cannot_wrap_absolute_position() {
        let groups = u32::MAX.div_ceil(THREADS);
        let (x, y) = dispatch_rectangle(groups, MAX_GROUPS_PER_DIM, MAX_GROUPS_PER_DIM).unwrap();
        assert!(x as u64 * y as u64 * THREADS as u64 <= u32::MAX as u64 + 1);
    }
}
