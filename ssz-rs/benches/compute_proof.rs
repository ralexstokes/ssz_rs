use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;

use ssz_rs::{List, PathElement, Prove};
use std::convert::TryFrom;

/// Generate fake transactions to benchmark with.
fn generate_dummy_transactions(size: usize) -> List<[u8; 32], 1000> {
    let txs = (0..size).map(|i| [i as u8; 32]).collect::<Vec<_>>();
    List::try_from(txs).expect("Failed to create transaction list")
}

/// Function to determine transaction indices based on the current size
/// Returns first, half, and second last indexes.
fn get_transaction_indices(size: usize) -> Vec<usize> {
    if size == 0 {
        vec![]
    } else {
        vec![0, size / 2, size - 1]
    }
}

fn bench_prove(c: &mut Criterion) {
    let sizes = [100, 300, 1000];

    for &size in &sizes {
        let dummy_transactions = generate_dummy_transactions(size);
        let indices = get_transaction_indices(size);
        let mut group = c.benchmark_group(format!("Prove Benchmark - size {}", size));
        // Reduce sample size as benchmark for 1000 is unable to complete
        // 100 samples in 5.0s on an M2 laptop.
        group.sample_size(50);

        for &index in &indices {
            // Ensure the index is within the current size
            if index >= size {
                continue;
            }
            let path = vec![PathElement::from(index)];

            group.bench_with_input(BenchmarkId::from_parameter(index), &path, |b, path| {
                b.iter(|| {
                    let proof = dummy_transactions
                        .prove(black_box(path))
                        .expect("Failed to generate proof");
                    black_box(proof)
                })
            });
        }

        group.finish();
    }
}

criterion_group!(benches, bench_prove);
criterion_main!(benches);
