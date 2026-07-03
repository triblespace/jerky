//! GPU vs CPU batch query benchmark for `WaveletMatrix` (feature `gpu`).
//!
//! Builds a large random matrix, uploads it once, then times batched
//! access/rank/select/quantile on the GPU against per-query CPU loops
//! (single-threaded and one thread per core). GPU timings include the
//! per-batch query upload, the dispatch, and the one blocking readback —
//! i.e. the honest end-to-end batch cost — but not the one-time matrix
//! upload.
//!
//! Run with:
//!
//! ```sh
//! cargo run --release --features gpu --example gpu_bench
//! ```

use std::time::Instant;

use anybytes::area::ByteArea;
use jerky::bit_vector::Rank9SelIndex;
use jerky::char_sequences::WaveletMatrix;
use jerky::gpu::GpuWaveletMatrix;

const N: usize = 4 << 20; // 4 Mi values
const ALPH: usize = 1 << 16; // 64 Ki alphabet -> 16 layers
const SWEEP: &[usize] = &[
    256, 1_000, 4_000, 16_000, 65_536, 100_000, 262_144, 1_000_000,
];
const MAIN: &[usize] = &[1_000, 4_000, 16_000, 65_536, 100_000, 1_000_000];

/// splitmix64
fn sm(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn median_secs(mut xs: Vec<f64>) -> f64 {
    xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    xs[xs.len() / 2]
}

/// Times `f` (median of `rounds`), checksumming to keep it honest.
fn time<F: FnMut() -> u64>(rounds: usize, mut f: F) -> (f64, u64) {
    let mut times = Vec::with_capacity(rounds);
    let mut sum = 0;
    for _ in 0..rounds {
        let t = Instant::now();
        sum = f();
        times.push(t.elapsed().as_secs_f64());
    }
    (median_secs(times), sum)
}

fn cpu_threads<Q: Sync, F: Fn(&Q) -> u64 + Sync>(queries: &[Q], nthreads: usize, f: F) -> u64 {
    let chunk = queries.len().div_ceil(nthreads);
    std::thread::scope(|s| {
        let hs: Vec<_> = queries
            .chunks(chunk)
            .map(|qs| {
                let f = &f;
                s.spawn(move || qs.iter().map(f).fold(0u64, u64::wrapping_add))
            })
            .collect();
        hs.into_iter()
            .map(|h| h.join().unwrap())
            .fold(0, u64::wrapping_add)
    })
}

fn opt_sum(res: &[Option<usize>]) -> u64 {
    res.iter()
        .map(|r| r.map_or(u64::MAX, |v| v as u64))
        .fold(0, u64::wrapping_add)
}

struct Row {
    batch: usize,
    cpu1: f64,
    cpun: f64,
    gpu: f64,
}

fn report(op: &str, nthreads: usize, rows: &[Row]) {
    println!("\n== {op} ==");
    println!(
        "{:>9} | {:>12} | {:>12} | {:>12} | {:>9} | {:>9}",
        "batch",
        "CPU-1t",
        format!("CPU-{nthreads}t"),
        "GPU",
        "GPU/1t",
        format!("GPU/{nthreads}t"),
    );
    for r in rows {
        println!(
            "{:>9} | {:>9.3}ms | {:>9.3}ms | {:>9.3}ms | {:>8.2}x | {:>8.2}x",
            r.batch,
            r.cpu1 * 1e3,
            r.cpun * 1e3,
            r.gpu * 1e3,
            r.cpu1 / r.gpu,
            r.cpun / r.gpu,
        );
    }
    let be1 = rows.iter().find(|r| r.gpu < r.cpu1).map(|r| r.batch);
    let ben = rows.iter().find(|r| r.gpu < r.cpun).map(|r| r.batch);
    let fmt = |b: Option<usize>| b.map_or("never (in sweep)".into(), |b| format!("~{b}"));
    println!(
        "break-even vs CPU-1t: {} | vs CPU-{nthreads}t: {}",
        fmt(be1),
        fmt(ben)
    );
}

fn main() {
    let mut st = 0xC0FFEEu64;
    println!("building WaveletMatrix: n={N}, alphabet={ALPH} ...");
    let ints: Vec<usize> = (0..N).map(|_| sm(&mut st) as usize % ALPH).collect();
    let t = Instant::now();
    let mut area = ByteArea::new().unwrap();
    let mut sections = area.sections();
    let wm = WaveletMatrix::<Rank9SelIndex>::from_iter(ALPH, ints.iter().copied(), &mut sections)
        .unwrap();
    println!(
        "built in {:.1}s ({} layers)",
        t.elapsed().as_secs_f64(),
        wm.alph_width()
    );

    let t = Instant::now();
    let gpu = GpuWaveletMatrix::on_wgpu(&wm).unwrap();
    println!(
        "uploaded to GPU in {:.1}ms",
        t.elapsed().as_secs_f64() * 1e3
    );

    let nthreads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8);
    let rounds = 5;

    // -- access sweep (the SuccinctArchive-dominant op) --------------------
    let mut rows = Vec::new();
    for &batch in SWEEP {
        let pos: Vec<usize> = (0..batch).map(|_| sm(&mut st) as usize % N).collect();
        let (cpu1, s1) = time(rounds, || {
            pos.iter()
                .map(|&p| wm.access(p).unwrap() as u64)
                .fold(0, u64::wrapping_add)
        });
        let (cpun, sn) = time(rounds, || {
            cpu_threads(&pos, nthreads, |&p| wm.access(p).unwrap() as u64)
        });
        let (gput, sg) = time(rounds, || opt_sum(&gpu.access_batch(&pos).unwrap()));
        assert_eq!(s1, sg, "access parity failure at batch {batch}");
        assert_eq!(sn, sg);
        rows.push(Row {
            batch,
            cpu1,
            cpun,
            gpu: gput,
        });
    }
    report("access (positions -> values)", nthreads, &rows);

    // -- rank ---------------------------------------------------------------
    let mut rows = Vec::new();
    for &batch in MAIN {
        let q: Vec<(usize, usize)> = (0..batch)
            .map(|_| (sm(&mut st) as usize % (N + 1), sm(&mut st) as usize % ALPH))
            .collect();
        let (ps, vs): (Vec<_>, Vec<_>) = q.iter().copied().unzip();
        let (cpu1, s1) = time(rounds, || {
            q.iter()
                .map(|&(p, v)| wm.rank(p, v).unwrap() as u64)
                .fold(0, u64::wrapping_add)
        });
        let (cpun, sn) = time(rounds, || {
            cpu_threads(&q, nthreads, |&(p, v)| wm.rank(p, v).unwrap() as u64)
        });
        let (gput, sg) = time(rounds, || opt_sum(&gpu.rank_batch(&ps, &vs).unwrap()));
        assert_eq!(s1, sg, "rank parity failure at batch {batch}");
        assert_eq!(sn, sg);
        rows.push(Row {
            batch,
            cpu1,
            cpun,
            gpu: gput,
        });
    }
    report("rank (pos, value) -> count", nthreads, &rows);

    // -- select ---------------------------------------------------------------
    // In-range (k, value) pairs: pick a random occurrence of a random stored
    // value so CPU and GPU both take the full descend+ascend path.
    let mut rows = Vec::new();
    for &batch in MAIN {
        let q: Vec<(usize, usize)> = (0..batch)
            .map(|_| {
                let v = ints[sm(&mut st) as usize % N];
                let occ = wm.rank(N, v).unwrap();
                (sm(&mut st) as usize % occ, v)
            })
            .collect();
        let (ks, vs): (Vec<_>, Vec<_>) = q.iter().copied().unzip();
        let (cpu1, s1) = time(rounds, || {
            q.iter()
                .map(|&(k, v)| wm.select(k, v).unwrap() as u64)
                .fold(0, u64::wrapping_add)
        });
        let (cpun, sn) = time(rounds, || {
            cpu_threads(&q, nthreads, |&(k, v)| wm.select(k, v).unwrap() as u64)
        });
        let (gput, sg) = time(rounds, || opt_sum(&gpu.select_batch(&ks, &vs).unwrap()));
        assert_eq!(s1, sg, "select parity failure at batch {batch}");
        assert_eq!(sn, sg);
        rows.push(Row {
            batch,
            cpu1,
            cpun,
            gpu: gput,
        });
    }
    report("select (k, value) -> position", nthreads, &rows);

    // -- quantile -------------------------------------------------------------
    let mut rows = Vec::new();
    for &batch in MAIN {
        let q: Vec<(std::ops::Range<usize>, usize)> = (0..batch)
            .map(|_| {
                let a = sm(&mut st) as usize % N;
                let b = sm(&mut st) as usize % N;
                let (lo, hi) = if a <= b { (a, b + 1) } else { (b, a + 1) };
                (lo..hi, sm(&mut st) as usize % (hi - lo))
            })
            .collect();
        let ranges: Vec<_> = q.iter().map(|(r, _)| r.clone()).collect();
        let ks: Vec<_> = q.iter().map(|&(_, k)| k).collect();
        let (cpu1, s1) = time(rounds, || {
            q.iter()
                .map(|(r, k)| wm.quantile(r.clone(), *k).unwrap() as u64)
                .fold(0, u64::wrapping_add)
        });
        let (cpun, sn) = time(rounds, || {
            cpu_threads(&q, nthreads, |(r, k)| {
                wm.quantile(r.clone(), *k).unwrap() as u64
            })
        });
        let (gput, sg) = time(rounds, || {
            opt_sum(&gpu.quantile_batch(&ranges, &ks).unwrap())
        });
        assert_eq!(s1, sg, "quantile parity failure at batch {batch}");
        assert_eq!(sn, sg);
        rows.push(Row {
            batch,
            cpu1,
            cpun,
            gpu: gput,
        });
    }
    report("quantile (range, k) -> value", nthreads, &rows);
}
