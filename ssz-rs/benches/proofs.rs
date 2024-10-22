use criterion::{criterion_group, criterion_main, Criterion};
use ssz_rs::{List, PathElement, Prove};

fn bench_proof_generation(c: &mut Criterion) {
    let inner: Vec<List<u8, 1073741824>> = vec![
        vec![0u8, 1u8, 2u8].try_into().unwrap(),
        vec![3u8, 4u8, 5u8].try_into().unwrap(),
        vec![6u8, 7u8, 8u8].try_into().unwrap(),
        vec![9u8, 10u8, 11u8].try_into().unwrap(),
    ];

    // Emulate a transactions tree
    let index = PathElement::from(1);
    let outer: List<List<u8, 1073741824>, 1048576> = List::try_from(inner).unwrap();

    c.bench_function("proof generation", |b| b.iter(|| outer.prove(&[index.clone()]).unwrap()));
}

fn bench_proof_verification(c: &mut Criterion) {
    let inner: Vec<List<u8, 1073741824>> = vec![
        vec![0u8, 1u8, 2u8].try_into().unwrap(),
        vec![3u8, 4u8, 5u8].try_into().unwrap(),
        vec![6u8, 7u8, 8u8].try_into().unwrap(),
        vec![9u8, 10u8, 11u8].try_into().unwrap(),
    ];

    // Emulate a transactions tree
    let outer: List<List<u8, 1073741824>, 1048576> = List::try_from(inner).unwrap();
    let index = PathElement::from(1);
    let (proof, witness) = outer.prove(&[index]).unwrap();

    c.bench_function("proof verification", |b| b.iter(|| proof.verify(witness)));
}

criterion_group!(benches, bench_proof_generation, bench_proof_verification);
criterion_main!(benches);
