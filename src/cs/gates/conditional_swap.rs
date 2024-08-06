use crate::{
    config::CSSetupConfig,
    cs::cs_builder::{CsBuilder, CsBuilderImpl},
    field::PrimeField,
    gadgets::traits::castable::WitnessCastable,
};
use traits::gate::GateRepr;

use super::*;

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConditionalSwapGate<const N: usize> {
    pub a: [Variable; N],
    pub b: [Variable; N],
    pub should_swap: Variable,
    pub result_a: [Variable; N],
    pub result_b: [Variable; N],
}

impl<F: SmallField, const N: usize> GateRepr<F> for ConditionalSwapGate<N> {
    fn id(&self) -> String {
        "BooleanConstraintGate".into()
    }

    fn input_vars(&self) -> Vec<Variable> {
        let mut inputs: Vec<Variable> = vec![];
        inputs.extend(self.a);
        inputs.extend(self.b);
        inputs.push(self.should_swap);
        inputs
    }

    fn output_vars(&self) -> Vec<Variable> {
        let mut outs: Vec<Variable> = vec![];
        outs.extend(self.result_a);
        outs.extend(self.result_b);
        outs
    }

    fn rage_checks_required(&self) -> Vec<(Variable, usize)> {
        vec![(self.should_swap, 1)]
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ConditionalSwapGateConstraintEvaluator<const N: usize>;

impl<const N: usize> ConditionalSwapGateConstraintEvaluator<N> {
    pub const fn principal_width() -> usize {
        4 * N + 1
    }
}

impl<F: PrimeField, const N: usize> GateConstraintEvaluator<F>
    for ConditionalSwapGateConstraintEvaluator<N>
{
    type UniqueParameterizationParams = ();

    #[inline(always)]
    fn new_from_parameters(_params: Self::UniqueParameterizationParams) -> Self {
        Self
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {}

    #[inline]
    fn type_name() -> std::borrow::Cow<'static, str> {
        Cow::Borrowed(std::any::type_name::<Self>())
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        GatePrincipalInstanceWidth {
            num_variables: Self::principal_width(),
            num_witnesses: 0,
            num_constants: 0,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 2,
            num_quotient_terms: N * 2,
        }
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::MultipleOnRow {
            per_chunk_offset: PerChunkOffset {
                variables_offset: Self::principal_width(),
                witnesses_offset: 0,
                constants_offset: 0,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        geometry.num_columns_under_copy_permutation / Self::principal_width()
    }
    #[inline]
    fn num_required_constants_in_geometry(&self, _geometry: &CSGeometry) -> usize {
        0
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        _ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
    }

    type RowSharedConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn load_row_shared_constants<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
    >(
        &self,
        _trace_source: &S,
        _ctx: &mut P::Context,
    ) -> Self::RowSharedConstants<P> {
    }

    #[inline(always)]
    fn evaluate_once<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
        D: EvaluationDestination<F, P>,
    >(
        &self,
        trace_source: &S,
        destination: &mut D,
        _shared_constants: &Self::RowSharedConstants<P>,
        _global_constants: &Self::GlobalConstants<P>,
        ctx: &mut P::Context,
    ) {
        let selector = trace_source.get_variable_value(0);

        for i in 0..N {
            let a = trace_source.get_variable_value(4 * i + 1);
            let b = trace_source.get_variable_value(4 * i + 2);
            let result_a = trace_source.get_variable_value(4 * i + 3);
            let result_b = trace_source.get_variable_value(4 * i + 4);

            // if we swap - take B
            let mut contribution = b;
            contribution.mul_assign(&selector, ctx);

            // otherwise A
            let mut tmp = P::one(ctx);
            tmp.sub_assign(&selector, ctx);
            P::mul_and_accumulate_into(&mut contribution, &tmp, &a, ctx);

            contribution.sub_assign(&result_a, ctx);
            destination.push_evaluation_result(contribution, ctx);

            // if we swap - take A
            let mut contribution = a;
            contribution.mul_assign(&selector, ctx);

            // otherwise B
            let mut tmp = P::one(ctx);
            tmp.sub_assign(&selector, ctx);
            P::mul_and_accumulate_into(&mut contribution, &tmp, &b, ctx);

            contribution.sub_assign(&result_b, ctx);
            destination.push_evaluation_result(contribution, ctx);
        }
    }
}

impl<F: SmallField, const N: usize> Gate<F> for ConditionalSwapGate<N> {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 2
            && geometry.num_columns_under_copy_permutation
                >= <Self as Gate<F>>::Evaluator::principal_width()
    }

    type Evaluator = ConditionalSwapGateConstraintEvaluator<N>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        ConditionalSwapGateConstraintEvaluator
    }
}

impl<const N: usize> ConditionalSwapGate<N> {
    pub const fn empty() -> Self {
        Self {
            a: [Variable::placeholder(); N],
            b: [Variable::placeholder(); N],
            should_swap: Variable::placeholder(),
            result_a: [Variable::placeholder(); N],
            result_b: [Variable::placeholder(); N],
        }
    }

    pub fn configure_builder<
        F: SmallField,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, NextGateCounterWithoutParams>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, Self, NextGateCounterWithoutParams>, GC), TB> {
        builder.allow_gate(placement_strategy, (), None)
    }

    pub fn conditionally_swap<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: &[Variable; N],
        b: &[Variable; N],
        should_swap: Variable,
    ) -> ([Variable; N], [Variable; N]) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variables_a = cs.alloc_multiple_variables_without_values::<N>();
        let output_variables_b = cs.alloc_multiple_variables_without_values::<N>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: &[F], outputs: &mut DstBuffer<'_, '_, F>| {
                let should_swap = inputs[0];
                let should_swap = <bool as WitnessCastable<F, F>>::cast_from_source(should_swap);

                for (a, b) in inputs[1..(N + 1)].iter().zip(inputs[(N + 1)..].iter()) {
                    let result = if should_swap == false { *a } else { *b };

                    outputs.push(result);
                }

                // and symmetrical
                for (a, b) in inputs[1..(N + 1)].iter().zip(inputs[(N + 1)..].iter()) {
                    let result = if should_swap == true { *a } else { *b };

                    outputs.push(result);
                }
            };

            let mut dependencies = Vec::with_capacity(2 * N + 1);
            dependencies.push(should_swap.into());
            dependencies.extend(Place::from_variables(*a));
            dependencies.extend(Place::from_variables(*b));

            let mut outputs = Vec::with_capacity(N * 2);
            outputs.extend(Place::from_variables(output_variables_a));
            outputs.extend(Place::from_variables(output_variables_b));

            cs.set_values_with_dependencies_vararg(&dependencies, &outputs, value_fn);
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                a: *a,
                b: *b,
                should_swap,
                result_a: output_variables_a,
                result_b: output_variables_b,
            };
            gate.add_to_cs(cs);
        }

        (output_variables_a, output_variables_b)
    }

    pub fn add_to_cs<F: SmallField, CS: ConstraintSystem<F>>(self, cs: &mut CS) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        cs.push_gate_repr(Box::new(self.clone()));

        match cs.get_gate_placement_strategy::<Self>() {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                let offered_row_idx = cs.next_available_row();
                let capacity_per_row = self.capacity_per_row(&*cs);
                let tooling: &mut NextGateCounterWithoutParams = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (row, num_instances_already_placed) =
                    find_next_gate_without_params(tooling, capacity_per_row, offered_row_idx);
                drop(tooling);

                // now we can use methods of CS to inform it of low level operations
                let mut offset =
                    num_instances_already_placed * <Self as Gate<F>>::Evaluator::principal_width();
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                cs.place_variable(self.should_swap, row, offset);
                offset += 1;
                for (((a, b), result_a), result_b) in self
                    .a
                    .into_iter()
                    .zip(self.b.into_iter())
                    .zip(self.result_a.into_iter())
                    .zip(self.result_b.into_iter())
                {
                    cs.place_multiple_variables_into_row(&[a, b, result_a, result_b], row, offset);
                    offset += 4;
                }
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions,
                share_constants: _,
            } => {
                // gate knows how to place itself
                let capacity_per_row = num_repetitions;
                let tooling: &mut NextGateCounterWithoutParams = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (row, num_instances_already_placed) =
                    find_next_specialized_gate_without_params(tooling, capacity_per_row);
                cs.place_gate_specialized(&self, num_instances_already_placed, row);
                let mut offset = 0;
                cs.place_variable_specialized::<Self>(
                    self.should_swap,
                    num_instances_already_placed,
                    row,
                    offset,
                );
                offset += 1;
                for (((a, b), result_a), result_b) in self
                    .a
                    .into_iter()
                    .zip(self.b.into_iter())
                    .zip(self.result_a.into_iter())
                    .zip(self.result_b.into_iter())
                {
                    cs.place_multiple_variables_into_row_specialized::<Self, 4>(
                        &[a, b, result_a, result_b],
                        num_instances_already_placed,
                        row,
                        offset,
                    );
                    offset += 4;
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cs::gates::testing_tools::test_evaluator;
    use crate::field::goldilocks::GoldilocksField;
    type F = GoldilocksField;

    #[test]
    fn test_properties() {
        // particular geometry is not important
        let _geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 80,
            num_constant_columns: 10,
            max_allowed_constraint_degree: 8,
        };

        let evaluator = <ConditionalSwapGateConstraintEvaluator<4> as GateConstraintEvaluator<F>>::new_from_parameters(
            ()
        );

        test_evaluator::<F, _>(evaluator);
    }
}
