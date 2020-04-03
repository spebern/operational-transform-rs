use crate::OperationSeq;
use rand::prelude::*;

pub fn random_string(len: usize, seed: Option<[u8; 32]>) -> String {
    let mut rng: StdRng = if let Some(seed) = seed {
        SeedableRng::from_seed(seed)
    } else {
        SeedableRng::from_seed(rand::random())
    };
    (0..len).map(|_| rng.gen::<char>()).collect()
}

pub fn random_operation_seq(s: &str, seed: Option<[u8; 32]>) -> OperationSeq {
    let mut op = OperationSeq::default();
    let mut rng: StdRng = if let Some(seed) = seed {
        SeedableRng::from_seed(seed)
    } else {
        SeedableRng::from_seed(rand::random())
    };
    loop {
        let left = s.chars().count() - op.base_len();
        if left == 0 {
            break;
        }
        let i = if left == 1 {
            1
        } else {
            1 + rng.gen_range(0, std::cmp::min(left - 1, 20))
        };
        match rng.gen_range(0.0, 1.0) {
            f if f < 0.2 => {
                op.insert(random_string(i, seed));
            }
            f if f < 0.4 => {
                op.delete(i as u32);
            }
            _ => {
                op.retain(i as u32);
            }
        }
    }
    if rng.gen_range(0.0, 1.0) < 0.3 {
        op.insert("1".to_owned() + &random_string(10, seed));
    }
    op
}
