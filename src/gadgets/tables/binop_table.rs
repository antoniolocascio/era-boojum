use super::*;
use crate::cs::traits::gate::LookupTableRepr;

pub const TABLE_NAME: &str = "Binop table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinopTable;

impl LookupTableRepr for BinopTable {
    fn id() -> String {
        TABLE_NAME.into()
    }

    fn n_keys() -> usize {
        2
    }

    fn n_values() -> usize {
        1
    }

    fn ranges() -> Vec<usize> {
        vec![8, 8, 32]
    }
}

pub fn create_binop_table<F: SmallField>() -> LookupTable<F, 3> {
    let mut all_keys = Vec::with_capacity(1 << 16);
    for a in 0..=u8::MAX {
        for b in 0..=u8::MAX {
            let key = smallvec::smallvec![
                F::from_u64_unchecked(a as u64),
                F::from_u64_unchecked(b as u64)
            ];
            all_keys.push(key);
        }
    }
    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        TABLE_NAME.to_string(),
        2,
        |keys| {
            let a = keys[0].as_u64_reduced() as u8;
            let b = keys[1].as_u64_reduced() as u8;

            let xor_result = a ^ b;
            let or_result = a | b;
            let and_result = a & b;
            let value = (xor_result as u64) << 32 | (or_result as u64) << 16 | (and_result as u64);

            smallvec::smallvec![F::from_u64_unchecked(value)]
        },
    )
}
