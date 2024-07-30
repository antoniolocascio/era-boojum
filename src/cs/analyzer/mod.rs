use std::{collections::HashSet, ops::Not};

use itertools::Itertools;

use super::{
    gates::{
        ConstantsAllocatorGate, FmaGateInBaseFieldWithoutConstant,
        FmaGateInBaseWithoutConstantParams, ReductionGate, ReductionGateParams,
    },
    log,
    traits::gate::GateRepr,
    Variable,
};
use crate::cs::traits::gate::Assertion;
use crate::field::SmallField;
use std::collections::HashMap;

type CS<F> = Vec<(Box<dyn GateRepr<F>>, Vec<String>)>;

fn collect_all_out<F: SmallField>(cs: &CS<F>) -> Vec<Variable> {
    cs.iter().flat_map(|(g, _)| g.output_vars()).collect_vec()
}

fn collect_all_in<F: SmallField>(cs: &CS<F>) -> HashSet<Variable> {
    cs.iter().flat_map(|(g, _)| g.input_vars()).collect()
}

// Finds wires that are never inputs to a gate or outputs to the circuit
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

// A gate is fully determined by it's id, inputs and constants.
// This is captured by the type [GateCompId]
// This function collects all such ids, and checks if two gates
// have the same id (even if they have different outputs).
fn find_duplicated_computation<F: SmallField>(cs: &CS<F>) -> bool {
    let mut compmap = GateCompMap::new();
    cs.iter().fold(false, |acc, (boxed, _)| {
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

#[derive(Debug, Clone, PartialEq, Eq)]
enum RangeInfo<F: SmallField> {
    Sized(usize),
    Const(F),
}

type RangeMap<F> = HashMap<Variable, RangeInfo<F>>;

impl<F: SmallField> RangeInfo<F> {
    fn is_zero(&self) -> bool {
        match self {
            RangeInfo::Const(v) => v.is_zero(),
            _ => false,
        }
    }
}

// Compute initial ranges, using constants and gate determined ranges
fn gen_initial_range_map<F: SmallField>(cs: &CS<F>) -> RangeMap<F> {
    let mut range_map: RangeMap<F> = RangeMap::new();
    cs.iter().for_each(|(g, _)| {
        if let Some(c) = g.downcast_ref::<ConstantsAllocatorGate<F>>() {
            range_map.insert(
                c.variable_with_constant_value,
                RangeInfo::Const(c.constant_to_add),
            );
        }
        g.checked_ranges().iter().for_each(|(v, size)| {
            range_map.insert(*v, RangeInfo::Sized(*size));
        })
    });
    range_map
}

// Check that a variable is not zero
fn var_not_zero<F: SmallField>(range_map: &RangeMap<F>, var: &Variable) -> bool {
    range_map
        .get(var)
        .and_then(|v| v.is_zero().not().then_some(()))
        .is_some()
}

// Check if a variable is known to be equal to a constant
fn var_eq_c<F: SmallField>(range_map: &RangeMap<F>, var: &Variable, c: F) -> bool {
    range_map
        .get(var)
        .and_then(|r| match r {
            RangeInfo::Const(v) => (*v == c).then_some(()),
            _ => None,
        })
        .is_some()
}

// Unwrap the assertion
fn ignore_fma_assertion<F: SmallField>(
    g: &dyn GateRepr<F>,
) -> Option<FmaGateInBaseFieldWithoutConstant<F>> {
    if let Some(fma) = g.downcast_ref::<FmaGateInBaseFieldWithoutConstant<F>>() {
        Some(fma.clone())
    } else if let Some(Assertion(fma)) =
        g.downcast_ref::<Assertion<FmaGateInBaseFieldWithoutConstant<F>>>()
    {
        Some(fma.clone())
    } else {
        None
    }
}

// Unwrap the assertion
fn ignore_reduction_assertion<F: SmallField>(g: &dyn GateRepr<F>) -> Option<ReductionGate<F, 4>> {
    if let Some(r) = g.downcast_ref::<ReductionGate<F, 4>>() {
        Some(r.clone())
    } else if let Some(Assertion(r)) = g.downcast_ref::<Assertion<ReductionGate<F, 4>>>() {
        Some(r.clone())
    } else {
        None
    }
}

// Σ 2^k_i v_i = o
// Assuming v_i are bounded correctly (see [check_recomposition_bounds]),
// then o will be bounded by the size k_n + size(v_n)
fn range_propagation_reduction_recomposition<F: SmallField>(
    g: &dyn GateRepr<F>,
    range_map: &RangeMap<F>,
) -> Option<(Variable, usize)> {
    let rg = ignore_reduction_assertion(g)?;
    let ReductionGate {
        params: ReductionGateParams {
            reduction_constants,
        },
        terms,
        reduction_result,
    } = rg;
    // Drop padding
    let (terms, reduction_constants) = if reduction_constants.last().unwrap().is_zero() {
        (terms[..3].to_vec(), reduction_constants[..3].to_vec())
    } else {
        (terms.to_vec(), reduction_constants.to_vec())
    };
    let coeffs_and_terms = reduction_constants
        .into_iter()
        .zip(terms.clone())
        .collect_vec();

    if check_recomposition_bounds(&coeffs_and_terms, range_map) {
        // Compute shifts
        let shifts = get_shifts_from_recomposition(&coeffs_and_terms)?;
        let last_shift = *shifts.last().unwrap();
        let last_width = get_var_size(*terms.last().unwrap(), range_map)?;
        Some((reduction_result, last_shift + last_width))
    } else {
        None
    }
}

fn num_bits(n: u64) -> usize {
    if n == 0 {
        return 1;
    }
    (n as f64).log2().floor() as usize + 1
}

fn get_var_size<F: SmallField>(var: Variable, range_map: &RangeMap<F>) -> Option<usize> {
    let r = range_map.get(&var)?;
    match r {
        RangeInfo::Const(c) => Some(num_bits(c.as_raw_u64())),
        RangeInfo::Sized(s) => Some(*s),
    }
}

// q * b + c = d, where q == 2^size(c)
// -----
// d is of size(c) + size(b)
fn range_propagation_fma_recomposition<F: SmallField>(
    g: &dyn GateRepr<F>,
    range_map: &RangeMap<F>,
) -> Option<(Variable, usize)> {
    let fma = ignore_fma_assertion(g)?;
    if fma.params.linear_term_coeff == F::ONE && var_eq_c(range_map, &fma.quadratic_part.0, F::ONE)
    {
        let c_size = get_var_size(fma.linear_part, range_map)?;
        if fma.params.coeff_for_quadtaric_part == F::from_u64_unchecked(1u64 << c_size) {
            let b_size = get_var_size(fma.quadratic_part.1, range_map)?;
            Some((fma.rhs_part, b_size + c_size))
        } else {
            None
        }
    } else {
        None
    }
}

fn insert_range<F: SmallField>(var: Variable, size: usize, range_map: &mut RangeMap<F>) -> bool {
    match range_map.get(&var) {
        Some(RangeInfo::Sized(old)) if size < *old => {
            range_map.insert(var, RangeInfo::Sized(size));
            true
        }
        None => {
            range_map.insert(var, RangeInfo::Sized(size));
            true
        }
        _ => false,
    }
}

fn range_propagation_pass<F: SmallField>(cs: &CS<F>, range_map: &mut RangeMap<F>) -> bool {
    cs.iter().fold(false, |acc, (g, _)| {
        if let Some((v, size)) = range_propagation_reduction_recomposition(g.as_ref(), range_map) {
            insert_range(v, size, range_map)
        } else if let Some((v, size)) = range_propagation_fma_recomposition(g.as_ref(), range_map) {
            insert_range(v, size, range_map)
        } else {
            acc
        }
    })
}

fn range_propagation<F: SmallField>(cs: &CS<F>, range_map: &mut RangeMap<F>) {
    while range_propagation_pass(cs, range_map) {
        // log!("Range propagation pass")
    }
}

// Given the constraint: q * a * b = d
// where: q /= 0, d /= 0
// Then:
//   unique(a) /\ unique(d) => unique(b)
//   unique(b) /\ unique(d) => unique(a)
fn inverse_uniqueness_rule<F: SmallField>(
    g: &dyn GateRepr<F>,
    unique: &HashSet<Variable>,
    range_map: &RangeMap<F>,
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
                    if unique.contains(a) && unique.contains(d) && var_not_zero(range_map, d) {
                        Some(*b)
                    } else if unique.contains(b) && unique.contains(d) && var_not_zero(range_map, d)
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

// Outputs a pair (terms, o) if the gate g represents the computation:
// o = Σ terms_i.0 * terms_i.1
#[allow(clippy::manual_map)]
fn get_lc_generic<F: SmallField>(
    g: &dyn GateRepr<F>,
    range_map: &RangeMap<F>,
) -> Option<(Vec<(F, Variable)>, Variable)> {
    if let Some(fma) = ignore_fma_assertion(g) {
        if var_eq_c(range_map, &fma.quadratic_part.0, F::ONE) {
            Some((
                vec![
                    (fma.params.linear_term_coeff, fma.linear_part),
                    (fma.params.coeff_for_quadtaric_part, fma.quadratic_part.1),
                ],
                fma.rhs_part,
            ))
        } else {
            None
        }
    } else if let Some(r) = ignore_reduction_assertion(g) {
        if r.params.reduction_constants.last().unwrap().is_zero() {
            // Remove padding
            let coeffs = r.params.reduction_constants[..3].to_vec();
            let terms = r.terms[..3].to_vec();
            Some((coeffs.into_iter().zip(terms).collect(), r.reduction_result))
        } else {
            Some((
                r.params
                    .reduction_constants
                    .into_iter()
                    .zip(r.terms)
                    .collect(),
                r.reduction_result,
            ))
        }
    } else {
        None
    }
}

// Returns i only for v = 2^i
fn log2_pow2(v: u64) -> Option<usize> {
    if v.count_ones() == 1 {
        Some(v.trailing_zeros() as usize)
    } else {
        None
    }
}

// For a recomposition Σ 2^ki vi returns the vector [ki]
fn get_shifts_from_recomposition<F: SmallField>(terms: &[(F, Variable)]) -> Option<Vec<usize>> {
    let mut shifts = vec![];
    terms.iter().fold(Some(()), |acc, (coeff, _)| {
        let total_shift = log2_pow2(coeff.as_raw_u64())?;
        shifts.push(total_shift);
        acc
    })?;
    Some(shifts)
}

fn var_bound_by_size<F: SmallField>(range_map: &RangeMap<F>, var: Variable, size: usize) -> bool {
    get_var_size(var, range_map).map_or(false, |actual_size| actual_size <= size)
}

// In a decomposition of the shape
// Σ 2^k_i v_i, where k_i are the shifts and vi are the variable,
// this function checks:
//  vi <= 2^(k_i+1  - k_i) -1 for i = 0..(n-1)
//  v_n <= 2^(64 - k_n) - 2^(32 - k_n) - 1
fn check_recomposition_bounds<F: SmallField>(
    terms: &[(F, Variable)],
    range_map: &RangeMap<F>,
) -> bool {
    match get_shifts_from_recomposition(terms) {
        Some(shifts) => {
            let n = terms.len();
            let intermediate_vars_bound =
                terms[0..n - 1].iter().enumerate().all(|(i, (_, var))| {
                    let shift_next = shifts.get(i + 1).unwrap();
                    let shift = shifts.get(i).unwrap();
                    let size = shift_next - shift;
                    var_bound_by_size(range_map, *var, size)
                });
            let final_shift = shifts.last().unwrap();
            let final_var = terms.last().unwrap().1;
            let real_bound = (1u128 << (64 - final_shift)) - (1u128 << (32 - final_shift)) - 1;
            let conservative_size = (real_bound as f64).log2().floor() as usize;
            let final_var_bound = var_bound_by_size(range_map, final_var, conservative_size);
            intermediate_vars_bound && final_var_bound
        }
        _ => false,
    }
}

// o = Σ 2^k_i v_i    unique(o)   check_recomposition_bounds(k, v)
// ---------------------------------------------------------------
//                        unique(v_i)
fn uniqueness_propagation_recomposition_rule<F: SmallField>(
    g: &dyn GateRepr<F>,
    unique: &HashSet<Variable>,
    range_map: &RangeMap<F>,
) -> Option<Vec<Variable>> {
    if let Some((terms, o)) = get_lc_generic(g, range_map) {
        let o_unique = unique.contains(&o);
        if o_unique && check_recomposition_bounds(&terms, range_map) {
            Some(terms.into_iter().map(|(_, v)| v).collect_vec())
        } else {
            None
        }
    } else {
        None
    }
}

fn uniqueness_propagation_pass<F: SmallField>(
    cs: &CS<F>,
    unique: &mut HashSet<Variable>,
    range_map: &RangeMap<F>,
) -> bool {
    cs.iter().fold(false, |acc, (g, _)| {
        let before_size = unique.len();
        // Basic input-output uniqueness propagation
        if g.input_vars().iter().all(|v| unique.contains(v)) {
            unique.extend(g.output_vars());
        }
        // Some gates are inversible (some of their outputs determine
        // the inputs)
        if g.inversible_inputs()
            .is_some_and(|inputs| inputs.iter().all(|v| unique.contains(v)))
        {
            // Original inputs are outputs here
            unique.extend(g.input_vars());
        }
        // Constants are unique
        if let Some(c) = g.downcast_ref::<ConstantsAllocatorGate<F>>() {
            unique.insert(c.variable_with_constant_value);
        }
        // Multiplicative inverse is unique
        if let Some(to_add) = inverse_uniqueness_rule(g.as_ref(), unique, range_map) {
            unique.insert(to_add);
        }
        // The decomposition of a number is unique given a base
        if let Some(to_add) =
            uniqueness_propagation_recomposition_rule(g.as_ref(), unique, range_map)
        {
            unique.extend(to_add);
        }
        acc || unique.len() > before_size
    })
}

fn uniqueness_propagation<F: SmallField>(
    cs: &CS<F>,
    unique: &mut HashSet<Variable>,
    range_map: &RangeMap<F>,
) {
    while uniqueness_propagation_pass(cs, unique, range_map) {
        // log!("Uniqueness propagation pass")
    }
}

fn report_first_unsound<F: SmallField>(
    cs: &CS<F>,
    witness_size: usize,
    unique: &HashSet<Variable>,
) {
    let first_unsound = (0..witness_size)
        .fold(None, |acc, i| {
            acc.or_else(|| {
                if unique.contains(&Variable(i as u64)) {
                    acc
                } else {
                    Some(Variable(i as u64))
                }
            })
        })
        .unwrap();
    println!("First unsound is {:?}", first_unsound);
    println!("Used in:");
    cs.iter().for_each(|(g, context)| {
        if g.output_vars().contains(&first_unsound) || g.input_vars().contains(&first_unsound) {
            println!("Gate: {:?}\nContext: {}", g, context.join("::"));
        }
    });
    println!("====================")
}

pub fn run_analysis<F: SmallField>(
    cs: &CS<F>,
    inputs: &[Variable],
    outputs: &[Variable],
    witness_size: usize,
) -> bool {
    // let all_out = collect_all_out(cs);
    // println!("outputs: {:?}", outputs);
    // log!("Gates:");
    // cs.iter().for_each(|(g,_)| log!("{:?}", g));
    let all_in = collect_all_in(cs);
    let unused_wire = find_unused_wires(&all_in, outputs, witness_size);
    let duplicated_comp = find_duplicated_computation(cs);
    let mut unique: HashSet<Variable> = inputs.iter().cloned().collect();
    let mut range_map = gen_initial_range_map(cs);
    range_propagation(cs, &mut range_map);
    // println!("ranges: {:?}", range_map);
    uniqueness_propagation(cs, &mut unique, &range_map);
    // println!("unique: {:?}", unique);
    let unsound = !outputs.iter().all(|o| unique.contains(o));
    if unsound {
        log!("\n========== Not all outputs are unique! ==========");
        report_first_unsound(cs, witness_size, &unique)
    } else {
        log!("\n========== SOUND CIRCUIT! ==========")
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
            num_columns_under_copy_permutation: 20,
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

    #[test]
    fn test_analyzer_unsound_split36() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
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

        let builder = builder.allow_lookup(crate::cs::LookupParameters::TableIdAsConstant {
            width: 4,
            share_table_id: true,
        });

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<F, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

        use crate::gadgets::sha256::round_function::{
            range_check_uint32_using_sha256_tables, split_36_bits_unchecked,
        };
        use crate::gadgets::tables::trixor4::*;

        let table = create_tri_xor_table();
        owned_cs.add_lookup_table::<TriXor4Table, 4>(table);

        let cs = &mut owned_cs;

        let input = cs.alloc_variable_without_value();

        // Start of circuit
        // Circuit(input) :=
        //   (low, _high) <- split_36_bits_unchecked(input)
        //   range_check_32(low)
        //   low

        let (low, _high) = split_36_bits_unchecked(cs, input);
        range_check_uint32_using_sha256_tables(cs, low);
        // let _ = cs.perform_lookup_::<TriXor4Table, 3, 1>(&[high, high, high]);

        drop(cs);
        owned_cs.pad_and_shrink();

        let gates = owned_cs.get_gate_reprs();
        gates.iter().for_each(|(g, _)| println!("{:?}", g));
        let witness_size = owned_cs.get_witness_size();
        let errors = run_analysis(gates, &[input], &[low], witness_size);
        assert!(errors)
    }

    #[test]
    fn test_analyzer_sound_split36() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
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

        let builder = builder.allow_lookup(crate::cs::LookupParameters::TableIdAsConstant {
            width: 4,
            share_table_id: true,
        });

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<F, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

        use crate::gadgets::sha256::round_function::range_check_36_bits_using_sha256_tables;
        use crate::gadgets::tables::trixor4::*;

        let table = create_tri_xor_table();
        owned_cs.add_lookup_table::<TriXor4Table, 4>(table);

        let cs = &mut owned_cs;

        let input = cs.alloc_variable_without_value();

        // Start of circuit
        // Circuit(input) :=
        //   (low, _) <- range_check_36(input)
        //   low

        let (low, _) = range_check_36_bits_using_sha256_tables(cs, input);

        drop(cs);
        owned_cs.pad_and_shrink();

        let gates = owned_cs.get_gate_reprs();
        gates.iter().for_each(|(g, _)| println!("{:?}", g));
        let witness_size = owned_cs.get_witness_size();
        let errors = run_analysis(gates, &[input], &[low], witness_size);
        assert!(errors)
    }

    #[test]
    fn test_analyzer_sound_split_and_rotate() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
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

        let builder = builder.allow_lookup(crate::cs::LookupParameters::TableIdAsConstant {
            width: 4,
            share_table_id: true,
        });

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<F, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

        use crate::gadgets::sha256::round_function::{split_and_rotate, tri_xor_many};
        use crate::gadgets::tables::chunk4bits::*;
        use crate::gadgets::tables::trixor4::*;

        let table = create_tri_xor_table();
        owned_cs.add_lookup_table::<TriXor4Table, 4>(table);
        let table = create_4bit_chunk_split_table::<F, 1>();
        owned_cs.add_lookup_table::<Split4BitChunkTable<1>, 4>(table);
        let table = create_4bit_chunk_split_table::<F, 2>();
        owned_cs.add_lookup_table::<Split4BitChunkTable<2>, 4>(table);

        let cs = &mut owned_cs;

        let input = cs.alloc_variable_without_value();

        // Start of circuit

        let (e_rot_6, _, _) = split_and_rotate(cs, input, 6);
        let s1 = tri_xor_many(cs, &e_rot_6, &e_rot_6, &e_rot_6);

        drop(cs);
        owned_cs.pad_and_shrink();

        let gates = owned_cs.get_gate_reprs();
        gates.iter().for_each(|(g, _)| println!("{:?}", g));
        let witness_size = owned_cs.get_witness_size();
        let errors = run_analysis(gates, &[input], &s1, witness_size);
        assert!(errors)
    }
}
