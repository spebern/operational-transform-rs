use operational_transform::OperationSeq;

#[path = "../src/utilities.rs"]
mod utilities;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use utilities::{random_operation_seq, random_string};

pub fn compose(c: &mut Criterion) {
    let mut input = Vec::with_capacity(1000);
    for i in 0..1000_u32 {
        let mut seed = [0; 32];
        for (i, seed) in i.to_be_bytes().iter().zip(&mut seed) {
            *seed = *i;
        }
        let s = random_string(20, Some(seed));
        seed[seed.len() - 1] = 1;
        let a = random_operation_seq(&s, Some(seed));
        seed[seed.len() - 1] = 2;
        let after_a = a.apply(&s).unwrap();
        seed[seed.len() - 1] = 3;
        let b = random_operation_seq(&after_a, Some(seed));
        input.push((a, b));
    }

    c.bench_function("compose", |b| {
        b.iter(|| {
            for (a, b) in input.iter() {
                let _ = a.compose(black_box(b));
            }
        })
    });
}

pub fn transform(c: &mut Criterion) {
    let mut input = Vec::with_capacity(1000);
    for i in 0..1000_u32 {
        let mut seed = [0; 32];
        for (i, seed) in i.to_be_bytes().iter().zip(&mut seed) {
            *seed = *i;
        }
        let s = random_string(20, Some(seed));
        seed[seed.len() - 1] = 1;
        let a = random_operation_seq(&s, Some(seed));
        seed[seed.len() - 1] = 2;
        let b = random_operation_seq(&s, Some(seed));
        input.push((a, b));
    }

    c.bench_function("transform", |b| {
        b.iter(|| {
            for (a, b) in input.iter() {
                let _ = a.transform(black_box(b));
            }
        })
    });
}

pub fn invert(c: &mut Criterion) {
    let mut input = Vec::with_capacity(1000);
    for i in 0..1000_u32 {
        let mut seed = [0; 32];
        for (i, seed) in i.to_be_bytes().iter().zip(&mut seed) {
            *seed = *i;
        }
        let s = random_string(50, Some(seed));
        seed[seed.len() - 1] = 1;
        let o = random_operation_seq(&s, Some(seed));
        input.push((o, s));
    }

    c.bench_function("invert", |b| {
        b.iter(|| {
            for (o, s) in input.iter() {
                let _ = o.invert(black_box(&s));
            }
        })
    });
}

pub fn apply(c: &mut Criterion) {
    let mut input = Vec::with_capacity(1000);
    for i in 0..1000_u32 {
        let mut seed = [0; 32];
        for (i, seed) in i.to_be_bytes().iter().zip(&mut seed) {
            *seed = *i;
        }
        let s = random_string(50, Some(seed));
        seed[seed.len() - 1] = 1;
        let o = random_operation_seq(&s, Some(seed));
        input.push((o, s));
    }

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