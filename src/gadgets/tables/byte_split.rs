use super::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteSplitTable<const SPLIT_AT: usize>;

impl<const SPLIT_AT: usize> crate::cs::traits::gate::LookupTableRepr for ByteSplitTable<SPLIT_AT> {
    fn id() -> String {
        TABLE_NAME.into()
    }

    fn n_keys() -> usize {
        1
    }

    fn n_values() -> usize {
        2
    }

    fn ranges() -> Vec<usize> {
        vec![8, SPLIT_AT, 8 - SPLIT_AT]
    }

    fn other_params() -> Vec<u8> {
        SPLIT_AT.to_le_bytes().to_vec()
    }

    fn inversible_inputs() -> Option<Vec<usize>> {
        Some(vec![1, 2])
    }
}

pub fn create_byte_split_table<F: SmallField, const SPLIT_AT: usize>() -> LookupTable<F, 3> {
    assert!(SPLIT_AT > 0);
    assert!(SPLIT_AT < 8);
    let mut all_keys = Vec::with_capacity(1 << 8);
    for a in 0..=u8::MAX {
        let key = smallvec::smallvec![F::from_u64_unchecked(a as u64),];
        all_keys.push(key);
    }

    let mask = (1u8 << SPLIT_AT) - 1;

    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        format!("Byte split at {}", SPLIT_AT),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced() as u8;

            let low = a & mask;
            let high = a >> SPLIT_AT;

            smallvec::smallvec![
                F::from_u64_unchecked(low as u64),
                F::from_u64_unchecked(high as u64)
            ]
        },
    )
}
