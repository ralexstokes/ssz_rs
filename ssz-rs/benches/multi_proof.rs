use criterion::{criterion_group, criterion_main, Criterion};
use ssz_rs::{multiproofs::verify_merkle_multiproof, HashTreeRoot, List, PathElement, Prove};

use std::{convert::TryFrom, env, fs::File, hint::black_box, io::BufReader, path::Path};

// https://github.com/ethereum/consensus-specs/blob/85b4d003668731cbad63d6b6ba53fcc7d042cba1/specs/bellatrix/beacon-chain.md?plain=1#L69-L76
const MAX_BYTES_PER_TRANSACTION: usize = 1_073_741_824; // 1 GiB
const MAX_TRANSACTIONS_PER_PAYLOAD: usize = 1_048_576; // 2^20

// Test blocks just above and below 256, a power of 2.
// 21315748.json contains 247 transactions.
// 21327802.json contains 261 transactions.
const TRANSACTIONS_JSON_PATHS: &[&str] = &["benches/21315748.json", "benches/21327802.json"];

/// Represents the structure of the JSON file.
/// Each transaction is a hex-encoded string prefixed with "0x".
type TransactionsJson = Vec<String>;

/// Reads transaction data from a local JSON file.
fn load_transactions<P: AsRef<Path>>(
    file_path: P,
) -> List<List<u8, MAX_BYTES_PER_TRANSACTION>, MAX_TRANSACTIONS_PER_PAYLOAD> {
    // Open the JSON file
    let current_dir = env::current_dir().expect("Failed to get current working directory");
    let file = File::open(&file_path).unwrap_or_else(|e| {
        panic!(
            "Failed to open JSON file at {:?}. Current working directory: {:?}. Error: {}",
            file_path.as_ref(),
            current_dir,
            e
        )
    });
    let reader = BufReader::new(file);

    // Deserialize the JSON into a Vec<String>
    let transactions_json: TransactionsJson =
        serde_json::from_reader(reader).expect("Failed to parse JSON");

    // Convert each hex string to Vec<u8> and then to List<u8, MAX_BYTES_PER_TRANSACTION>
    let mut inner: Vec<List<u8, MAX_BYTES_PER_TRANSACTION>> =
        Vec::with_capacity(transactions_json.len());

    for (i, tx_hex) in transactions_json.into_iter().enumerate() {
        // Remove "0x" prefix
        let tx_hex_trimmed = tx_hex.strip_prefix("0x").unwrap_or(&tx_hex);

        // Decode hex string to Vec<u8>
        let tx_bytes = hex::decode(tx_hex_trimmed)
            .unwrap_or_else(|_| panic!("Failed to decode hex string at index {}", i));

        // Convert Vec<u8> to List<u8, MAX_BYTES_PER_TRANSACTION>
        let tx_list = List::<u8, MAX_BYTES_PER_TRANSACTION>::try_from(tx_bytes).expect(&format!(
            "Failed to convert Vec<u8> to List<u8, {}> at index {}",
            MAX_BYTES_PER_TRANSACTION, i
        ));

        inner.push(tx_list);
    }

    let outer =
        List::<List<u8, MAX_BYTES_PER_TRANSACTION>, MAX_TRANSACTIONS_PER_PAYLOAD>::try_from(inner)
            .expect("Failed to convert Vec<List<u8, MAX_BYTES_PER_TRANSACTION>> to outer List");

    outer
}

fn bench_multi_prove(c: &mut Criterion) {
    for &file_path_str in TRANSACTIONS_JSON_PATHS {
        let file_path = Path::new(file_path_str);
        let outer = load_transactions(file_path);
        let size = outer.len();

        // Create paths for single proof
        let single_index = [PathElement::from(size / 2)];
        let single_path = [&single_index[..]];

        // Create paths for 10 proofs
        let indices: Vec<[PathElement; 1]> =
            (0..10).map(|i| [PathElement::from(i * (size / 10))]).collect();
        let ten_paths: Vec<&[PathElement]> = indices.iter().map(|p| &p[..]).collect();

        let mut group = c.benchmark_group(format!(
            "MultiProve Benchmark - File: {} - size {}",
            file_path_str, size
        ));
        group.sample_size(10);

        // Benchmark single proof generation and verification
        group.bench_function("Generate Single Proof", |b| {
            b.iter(|| {
                let proof =
                    outer.multi_prove(black_box(&single_path)).expect("Failed to generate proof");
                black_box(proof)
            })
        });

        let single_proof = outer.multi_prove(&single_path).unwrap();
        let root = outer.hash_tree_root().unwrap();

        group.bench_function("Verify Single Proof", |b| {
            b.iter(|| {
                let result = verify_merkle_multiproof(
                    black_box(&single_proof.0.leaves),
                    black_box(&single_proof.0.branch),
                    black_box(&single_proof.0.indices),
                    black_box(root),
                );
                black_box(result)
            })
        });

        // Benchmark 10 proofs generation and verification
        group.bench_function("Generate Ten Proofs", |b| {
            b.iter(|| {
                let proof =
                    outer.multi_prove(black_box(&ten_paths)).expect("Failed to generate proof");
                black_box(proof)
            })
        });

        let ten_proof = outer.multi_prove(&ten_paths).unwrap();

        group.bench_function("Verify Ten Proofs", |b| {
            b.iter(|| {
                let result = verify_merkle_multiproof(
                    black_box(&ten_proof.0.leaves),
                    black_box(&ten_proof.0.branch),
                    black_box(&ten_proof.0.indices),
                    black_box(root),
                );
                black_box(result)
            })
        });

        group.finish();
    }
}

criterion_group!(benches, bench_multi_prove);
criterion_main!(benches);
