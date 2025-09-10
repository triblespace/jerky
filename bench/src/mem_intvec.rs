const DBLP_PSEF_STR: &str = include_str!("../data/lcps/dblp.1MiB.txt");
const DNA_PSEF_STR: &str = include_str!("../data/lcps/dna.1MiB.txt");
const PROTEINS_PSEF_STR: &str = include_str!("../data/lcps/proteins.1MiB.txt");

use anybytes::ByteArea;

fn parse_ints_from_str(s: &str) -> Vec<u32> {
    let mut ints = vec![];
    for l in s.split('\n') {
        if !l.is_empty() {
            ints.push(l.parse().unwrap());
        }
    }
    ints
}

fn main() {
    show_memories("dblp", &parse_ints_from_str(DBLP_PSEF_STR));
    show_memories("dna", &parse_ints_from_str(DNA_PSEF_STR));
    show_memories("proteins", &parse_ints_from_str(PROTEINS_PSEF_STR));
}

fn show_data_stats(vals: &[u32]) {
    let nvals = vals.len();
    let max = vals.iter().cloned().max().unwrap();
    let mean = vals.iter().cloned().sum::<u32>() as f64 / nvals as f64;

    let mut sorted = vals.to_vec();
    sorted.sort_unstable();
    let median = sorted[nvals / 2];

    println!("Basic: n_vals={nvals}, max_val={max}, mean_val={mean:.3}, median_val={median}");
}

fn show_memories(title: &str, vals: &[u32]) {
    println!("[{title}]");
    show_data_stats(vals);

    let bytes = {
        let idx = jerky::int_vectors::CompactVector::from_slice(vals).unwrap();
        let data_bytes = idx.chunks.data.words.bytes();
        data_bytes.as_ref().len() + std::mem::size_of_val(&idx)
    };
    print_memory("CompactVector", bytes, vals.len());

    let bytes = {
        let mut area = ByteArea::new().unwrap();
        let mut writer = area.sections();
        let idx = jerky::int_vectors::DacsByte::from_slice(vals, &mut writer).unwrap();
        area.freeze().unwrap();
        let data_bytes: usize = idx.data.iter().map(|lvl| lvl.as_ref().len()).sum();
        let flags_bytes: usize = idx
            .flags
            .iter()
            .map(|bv| {
                let data = bv.data.words.bytes();
                data.as_ref().len() + std::mem::size_of_val(&bv.index)
            })
            .sum();
        data_bytes + flags_bytes + std::mem::size_of_val(&idx)
    };
    print_memory("DacsByte", bytes, vals.len());
}

fn print_memory(name: &str, bytes: usize, nvals: usize) {
    println!(
        "{}: {:.3} bits per value",
        name,
        (bytes * 8) as f64 / nvals as f64
    );
}
