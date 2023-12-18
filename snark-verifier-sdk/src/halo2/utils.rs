use halo2_base::halo2_proofs::{
    halo2curves::bn256::{Fr, G1Affine},
    plonk::{Circuit, VerifyingKey},
    poly::kzg::commitment::ParamsKZG,
};
use rand::{rngs::StdRng, SeedableRng};

use crate::{Snark, SHPLONK};

use super::{aggregation::AggregationCircuit, gen_dummy_snark_from_vk};

#[derive(Clone, Copy, Debug)]
pub struct AggregationDependencyIntent<'a> {
    pub vk: &'a VerifyingKey<G1Affine>,
    pub num_instance: &'a [usize],
    pub accumulator_indices: Option<&'a [(usize, usize)]>,
}

#[derive(Clone, Debug)]
pub struct AggregationDependencyIntentOwned {
    pub vk: VerifyingKey<G1Affine>,
    pub num_instance: Vec<usize>,
    pub accumulator_indices: Option<Vec<(usize, usize)>>,
}

/// This trait should be implemented on the minimal circuit configuration data necessary to
/// completely determine an aggregation circuit
/// (independent of circuit inputs or specific snarks to be aggregated).
/// This is used to generate a _dummy_ instantiation of a concrete `Circuit` type for the purposes of key generation.
/// This dummy instantiation just needs to have the correct arithmetization format, but the witnesses do not need to
/// satisfy constraints.
///
/// This trait is specialized for aggregation circuits, which need to aggregate **dependency** snarks.
/// The aggregation circuit should only depend on the verifying key of each dependency snark.
pub trait KeygenAggregationCircuitIntent {
    /// Concrete circuit type. Defaults to [`AggregationCircuit`].
    type AggregationCircuit: Circuit<Fr> = AggregationCircuit;

    /// The **ordered** list of [`VerifyingKey`]s of the circuits to be aggregated.
    fn intent_of_dependencies(&self) -> Vec<AggregationDependencyIntent>;

    /// Builds a _dummy_ instantiation of `Self::AggregationCircuit` for the purposes of key generation.
    /// Assumes that `snarks` is an ordered list of [`Snark`]s, where the `i`th snark corresponds to the `i`th [`VerifyingKey`] in `vk_of_dependencies`.
    /// The `snarks` only need to have the correct witness sizes (e.g., proof length) but the
    /// snarks do _not_ need to verify.
    ///
    /// May specify additional custom logic for building the aggregation circuit from the snarks.
    fn build_keygen_circuit_from_snarks(self, snarks: Vec<Snark>) -> Self::AggregationCircuit;

    /// Builds a _dummy_ instantiation of `Self::AggregationCircuit` for the purposes of key generation.
    ///
    /// Generates dummy snarks from the verifying keys in `vk_of_dependencies`, **assuming** that SHPLONK is
    /// used for the multi-open scheme.
    fn build_keygen_circuit_shplonk(self) -> Self::AggregationCircuit
    where
        Self: Sized,
    {
        let mut rng = StdRng::seed_from_u64(0u64);
        let snarks = self
            .intent_of_dependencies()
            .into_iter()
            .map(|AggregationDependencyIntent { vk, num_instance, accumulator_indices }| {
                let k = vk.get_domain().k();
                // In KZG `gen_dummy_snark_from_vk` calls `compile`, which only uses `params` for `params.k()` so we can just use a random untrusted setup.
                // Moreover since this is a dummy snark, the trusted setup shouldn't matter.
                let params = ParamsKZG::setup(k, &mut rng);
                gen_dummy_snark_from_vk::<SHPLONK>(
                    &params,
                    vk,
                    num_instance.to_vec(),
                    accumulator_indices.map(|v| v.to_vec()),
                )
            })
            .collect();
        self.build_keygen_circuit_from_snarks(snarks)
    }
}

impl<'a> From<&'a AggregationDependencyIntentOwned> for AggregationDependencyIntent<'a> {
    fn from(intent: &'a AggregationDependencyIntentOwned) -> Self {
        Self {
            vk: &intent.vk,
            num_instance: &intent.num_instance,
            accumulator_indices: intent.accumulator_indices.as_deref(),
        }
    }
}
