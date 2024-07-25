use std::{collections::HashSet, ops::Not};

use itertools::Itertools;

use super::{
    gates::{
        ConstantsAllocatorGate, FmaGateInBaseFieldWithoutConstant,
        FmaGateInBaseWithoutConstantParams,
    },
    log,
    traits::gate::GateRepr,
    Variable,
};
use crate::cs::traits::gate::Assertion;
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
// Returns if it finds any unused wire
fn find_unused_wires(
    all_in: &HashSet<Variable>,
    outputs: &[Variable],
    witness_size: usize,
) -> bool {
    (0..witness_size).fold(false, |acc, i| {
        if !(all_in.contains(&Variable(i as u64)) || outputs.contains(&Variable(i as u64))) {
            log!("Unused wire: {:?}", i);
            true
        } else {
            acc
        }
    })
}

type GateCompId = (String, Vec<Variable>, Vec<u8>);
type GateCompMap = HashMap<GateCompId, Vec<Variable>>;

fn find_duplicated_computation<F: SmallField>(cs: &CS<F>) -> bool {
    let mut compmap = GateCompMap::new();
    cs.iter().fold(false, |acc, boxed| {
        let id = boxed.id();
        let inputs = boxed.input_vars();
        let other = boxed.other_params();
        let previous_outputs = compmap.insert((id, inputs, other), boxed.output_vars());
        if previous_outputs.is_some() {
            log!(
                "Duplicated gate:\n{:?}\n was already bound to outputs {:?}",
                boxed,
                previous_outputs.unwrap()
            );
            true
        } else {
            acc
        }
    })
}

// This can be generalized somewhat
fn var_not_zero<F: SmallField>(const_map: &HashMap<Variable, F>, var: &Variable) -> bool {
    const_map
        .get(var)
        .and_then(|v| v.is_zero().not().then_some(()))
        .is_some()
}

// Given the constraint: q * a * b = d
// where: q /= 0, d /= 0
// Then:
//   unique(a) /\ unique(d) => unique(b)
//   unique(b) /\ unique(d) => unique(a)
fn inverse_uniqueness_rule<F: SmallField>(
    g: &dyn GateRepr<F>,
    unique: &mut HashSet<Variable>,
    const_map: &HashMap<Variable, F>,
) -> Option<Variable> {
    g.downcast_ref::<Assertion<FmaGateInBaseFieldWithoutConstant<F>>>()
        .and_then(
            |Assertion(FmaGateInBaseFieldWithoutConstant {
                 params:
                     FmaGateInBaseWithoutConstantParams {
                         coeff_for_quadtaric_part: c0,
                         linear_term_coeff: c1,
                     },
                 quadratic_part: (a, b),
                 linear_part: _,
                 rhs_part: d,
             })| {
                if c1.is_zero() && !c0.is_zero() {
                    if unique.contains(a) && unique.contains(d) && var_not_zero(const_map, d) {
                        Some(*b)
                    } else if unique.contains(b) && unique.contains(d) && var_not_zero(const_map, d)
                    {
                        Some(*a)
                    } else {
                        None
                    }
                } else {
                    None
                }
            },
        )
}

fn uniqueness_propagation_pass<F: SmallField>(
    cs: &CS<F>,
    unique: &mut HashSet<Variable>,
    const_map: &HashMap<Variable, F>,
) -> bool {
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
        // Multiplicative inverse is unique
        if let Some(to_add) = inverse_uniqueness_rule(g.as_ref(), unique, const_map) {
            unique.insert(to_add);
        }
        acc || unique.len() > before_size
    })
}

fn uniqueness_propagation<F: SmallField>(cs: &CS<F>, unique: &mut HashSet<Variable>) {
    let mut const_map: HashMap<Variable, F> = HashMap::new();
    cs.iter().for_each(|g| {
        if let Some(c) = g.downcast_ref::<ConstantsAllocatorGate<F>>() {
            const_map.insert(c.variable_with_constant_value, c.constant_to_add);
        }
    });

    while uniqueness_propagation_pass(cs, unique, &const_map) {
        log!("Uniqueness propagation pass")
    }
}

pub fn run_analysis<F: SmallField>(
    cs: &CS<F>,
    inputs: &[Variable],
    outputs: &[Variable],
    witness_size: usize,
) -> bool {
    // let all_out = collect_all_out(cs);
    let all_in = collect_all_in(cs);
    let unused_wire = find_unused_wires(&all_in, outputs, witness_size);
    let duplicated_comp = find_duplicated_computation(cs);
    let mut unique: HashSet<Variable> = inputs.iter().cloned().collect();
    uniqueness_propagation(cs, &mut unique);
    let unsound = !outputs.iter().all(|o| unique.contains(o));
    if unsound {
        log!("Not all outputs are unique!")
    }
    unused_wire || duplicated_comp || unsound
}

#[cfg(test)]
mod test {

    use super::*;

    use crate::cs::gates::*;
    use crate::cs::traits::cs::ConstraintSystem;
    use crate::cs::traits::gate::GatePlacementStrategy;
    use crate::cs::CSGeometry;
    use crate::dag::CircuitResolverOpts;
    use crate::field::Field;
    type F = crate::field::goldilocks::GoldilocksField;

    #[test]
    fn test_analyzer_unused_wire() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 5,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        use crate::config::SetupCSConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, SetupCSConfig>::new(geometry, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

        let cs = &mut owned_cs;

        let input = cs.alloc_variable_without_value();

        // Start of circuit
        // Circuit(input) :=
        //  _ <- input + 1
        //  output <- input * 2
        //  output

        let one_variable = cs.allocate_constant(F::ONE);

        // input + 1
        FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            F::ONE,
            (one_variable, input),
            F::ONE,
            one_variable,
        );

        // output <- input * 2
        let output = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            F::TWO,
            (one_variable, input),
            F::ZERO,
            one_variable,
        );

        drop(cs);
        owned_cs.pad_and_shrink();

        let gates = owned_cs.get_gate_reprs();
        let witness_size = owned_cs.get_witness_size();
        let errors = run_analysis(gates, &[input], &[output], witness_size);
        assert!(errors)
    }

    #[test]
    fn test_analyzer_duplicated_computation() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 5,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        use crate::config::SetupCSConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, SetupCSConfig>::new(geometry, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

        let cs = &mut owned_cs;

        let input = cs.alloc_variable_without_value();

        // Start of circuit
        // Circuit(input) :=
        //  x <- input + 1
        //  y <- input + 1
        //  output <- x * y
        //  output

        let one_variable = cs.allocate_constant(F::ONE);

        // x <- input + 1
        let x = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            F::ONE,
            (one_variable, input),
            F::ONE,
            one_variable,
        );

        // y <- input + 1
        let y = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            F::ONE,
            (one_variable, input),
            F::ONE,
            one_variable,
        );

        // output <- x * y
        let output = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            F::ONE,
            (x, y),
            F::ZERO,
            one_variable,
        );

        drop(cs);
        owned_cs.pad_and_shrink();

        let gates = owned_cs.get_gate_reprs();
        let witness_size = owned_cs.get_witness_size();
        let errors = run_analysis(gates, &[input], &[output], witness_size);
        assert!(errors)
    }

    #[test]
    fn test_analyzer_unsound_inv() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 5,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        use crate::config::SetupCSConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, SetupCSConfig>::new(geometry, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

        let cs = &mut owned_cs;

        let input = cs.alloc_variable_without_value();

        // Start of circuit
        // Circuit(input) :=
        //  output <- fresh()
        //  add_witness_resolver(output = 1/input)
        //  output

        // Note that output is not constrained

        let output = cs.alloc_variable_without_value();

        let value_fn = move |input: [F; 1]| {
            let i = input[0].to_reduced_u64();
            [F::from_nonreduced_u64(1 / i)]
        };
        cs.set_values_with_dependencies(&[input.into()], &[output.into()], value_fn);

        drop(cs);
        owned_cs.pad_and_shrink();

        let gates = owned_cs.get_gate_reprs();
        let witness_size = owned_cs.get_witness_size();
        let errors = run_analysis(gates, &[input], &[output], witness_size);
        assert!(errors)
    }

    #[test]
    fn test_analyzer_sound_inv() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 5,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        use crate::config::SetupCSConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, SetupCSConfig>::new(geometry, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

        let cs = &mut owned_cs;

        let input = cs.alloc_variable_without_value();

        // Start of circuit
        // Circuit(input) :=
        //  output <- fresh()
        //  add_witness_resolver(output = 1/input)
        //  constrain(input * output == 1)
        //  output

        let one_variable = cs.allocate_constant(F::ONE);

        let output = cs.alloc_variable_without_value();

        let g = FmaGateInBaseFieldWithoutConstant {
            params: FmaGateInBaseWithoutConstantParams {
                coeff_for_quadtaric_part: F::ONE,
                linear_term_coeff: F::ZERO,
            },
            quadratic_part: (input, output),
            linear_part: one_variable,
            rhs_part: one_variable,
        };
        g.add_to_cs(cs);

        let value_fn = move |input: [F; 1]| {
            let i = input[0].to_reduced_u64();
            [F::from_nonreduced_u64(1 / i)]
        };
        cs.set_values_with_dependencies(&[input.into()], &[output.into()], value_fn);

        drop(cs);
        owned_cs.pad_and_shrink();

        let gates = owned_cs.get_gate_reprs();
        let witness_size = owned_cs.get_witness_size();
        let errors = run_analysis(gates, &[input], &[output], witness_size);
        assert!(!errors)
    }
}
