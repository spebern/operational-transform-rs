use operational_transform::OperationSeq;

#[path = "../src/utilities.rs"]
mod utilities;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use utilities::Rng;

pub fn compose(c: &mut Criterion) {
    let mut rng = Rng::from_seed(Default::default());
    let input = (0..1000)
        .map(|_| {
            let s = rng.gen_string(20);
            let a = rng.gen_operation_seq(&s);
            let after_a = a.apply(&s).unwrap();
            let b = rng.gen_operation_seq(&after_a);
            (a, b)
        })
        .collect::<Vec<_>>();
    c.bench_function("compose", |b| {
        b.iter(|| {
            for (a, b) in input.iter() {
                let _ = a.compose(black_box(b));
            }
        })
    });
}

pub fn transform(c: &mut Criterion) {
    let mut rng = Rng::from_seed(Default::default());
    let input = (0..1000)
        .map(|_| {
            let s = rng.gen_string(20);
            let a = rng.gen_operation_seq(&s);
            let b = rng.gen_operation_seq(&s);
            (a, b)
        })
        .collect::<Vec<_>>();
    c.bench_function("transform", |b| {
        b.iter(|| {
            for (a, b) in input.iter() {
                let _ = a.transform(black_box(b));
            }
        })
    });
}

pub fn invert(c: &mut Criterion) {
    let mut rng = Rng::from_seed(Default::default());
    let input = (0..1000)
        .map(|_| {
            let s = rng.gen_string(50);
            let o = rng.gen_operation_seq(&s);
            (o, s)
        })
        .collect::<Vec<_>>();
    c.bench_function("invert", |b| {
        b.iter(|| {
            for (o, s) in input.iter() {
                let _ = o.invert(black_box(&s));
            }
        })
    });
}

pub fn apply(c: &mut Criterion) {
    let mut rng = Rng::from_seed(Default::default());
    let input = (0..1000)
        .map(|_| {
            let s = rng.gen_string(50);
            let o = rng.gen_operation_seq(&s);
            (o, s)
        })
        .collect::<Vec<_>>();
    c.bench_function("apply", |b| {
        b.iter(|| {
            for (o, s) in input.iter() {
                let _ = o.apply(black_box(&s));
            }
        })
    });
}

criterion_group!(benches, compose, transform, invert, apply);
criterion_main!(benches);
