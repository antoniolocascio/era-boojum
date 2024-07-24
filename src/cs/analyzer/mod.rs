use std::collections::HashSet;

use crypto_bigint::rand_core::le;
use itertools::Itertools;

use super::{gates::ConstantsAllocatorGate, log, traits::gate::GateRepr, Variable};
use crate::field::SmallField;
use std::collections::HashMap;

type CS<F> = Vec<Box<dyn GateRepr<F>>>;

fn collect_all_out<F: SmallField>(cs: &CS<F>) -> Vec<Variable> {
    cs.iter().flat_map(|g| g.output_vars()).collect_vec()
}

fn collect_all_in<F: SmallField>(cs: &CS<F>) -> HashSet<Variable> {
    cs.iter().flat_map(|g| g.input_vars()).collect()
}

// Find wires that are never inputs to a gate or outputs to the circuit
fn find_unused_wires(all_in: &HashSet<Variable>, outputs: &[Variable], witness_size: usize) {
    for i in 0..witness_size {
        if !(all_in.contains(&Variable(i as u64)) || outputs.contains(&Variable(i as u64))) {
            panic!("Unused wire: {:?}", i)
        }
    }
}

type GateCompId = (String, Vec<Variable>, Vec<u8>);
type GateCompMap = HashMap<GateCompId, Vec<Variable>>;

fn find_duplicated_computation<F: SmallField>(cs: &CS<F>) {
    let mut compmap = GateCompMap::new();
    cs.iter().for_each(|boxed| {
        let id = boxed.id();
        let inputs = boxed.input_vars();
        let other = boxed.other_params();
        let previous_outputs = compmap.insert((id, inputs, other), boxed.output_vars());
        if previous_outputs.is_some() {
            panic!(
                "Duplicated gate:\n{:?}\n was already bound to outputs {:?}",
                boxed,
                previous_outputs.unwrap()
            );
        }
    });
}

fn uniqueness_propagation_pass<F: SmallField>(cs: &CS<F>, unique: &mut HashSet<Variable>) -> bool {
    cs.iter().fold(false, |acc, g| {
        let before_size = unique.len();
        // Basic input-output uniqueness propagation
        if g.input_vars().iter().all(|v| unique.contains(v)) {
            unique.extend(g.output_vars());
        }
        // Constants are unique
        if let Some(c) = g.downcast_ref::<ConstantsAllocatorGate<F>>() {
            unique.insert(c.variable_with_constant_value);
        }
        acc || unique.len() > before_size
    })
}

fn uniqueness_propagation<F: SmallField>(cs: &CS<F>, unique: &mut HashSet<Variable>) {
    while uniqueness_propagation_pass(cs, unique) {
        log!("Uniqueness propagation pass")
    }
}

pub fn run_analysis<F: SmallField>(
    cs: &CS<F>,
    inputs: &[Variable],
    outputs: &[Variable],
    witness_size: usize,
) {
    // let all_out = collect_all_out(cs);
    let all_in = collect_all_in(cs);
    find_unused_wires(&all_in, outputs, witness_size);
    find_duplicated_computation(cs);
    let mut unique: HashSet<Variable> = inputs.iter().cloned().collect();
    uniqueness_propagation(cs, &mut unique);
    assert!(
        outputs.iter().all(|o| unique.contains(o)),
        "Not all outputs are unique!"
    )
}
