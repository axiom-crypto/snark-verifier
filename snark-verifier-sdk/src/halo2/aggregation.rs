use super::PlonkSuccinctVerifier;
use crate::{BITS, LIMBS};
use halo2_base::{
    gates::{
        builder::{
            BaseConfigParams, CircuitBuilderStage, GateThreadBuilder, MultiPhaseThreadBreakPoints,
            PublicBaseConfig, RangeWithInstanceCircuitBuilder,
        },
        flex_gate::GateStrategy,
        RangeChip,
    },
    halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        halo2curves::bn256::{Bn256, Fr, G1Affine},
        plonk::{self, Circuit, ConstraintSystem, Selector},
        poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
    },
    utils::ScalarField,
    AssignedValue,
};
use itertools::Itertools;
use rand::{rngs::StdRng, SeedableRng};
use serde::{Deserialize, Serialize};
#[cfg(debug_assertions)]
use snark_verifier::util::arithmetic::fe_to_limbs;
use snark_verifier::{
    loader::{
        self,
        halo2::halo2_ecc::{self, bn254::FpChip},
        native::NativeLoader,
    },
    pcs::{
        kzg::{KzgAccumulator, KzgAsProvingKey, KzgAsVerifyingKey, KzgSuccinctVerifyingKey},
        AccumulationScheme, AccumulationSchemeProver, PolynomialCommitmentScheme,
    },
    verifier::SnarkVerifier,
};
use std::{fs::File, path::Path, rc::Rc};

use super::{CircuitExt, PoseidonTranscript, Snark, POSEIDON_SPEC};

pub type Svk = KzgSuccinctVerifyingKey<G1Affine>;
pub type BaseFieldEccChip<'chip> = halo2_ecc::ecc::BaseFieldEccChip<'chip, G1Affine>;
pub type Halo2Loader<'chip> = loader::halo2::Halo2Loader<G1Affine, BaseFieldEccChip<'chip>>;

#[allow(clippy::type_complexity)]
/// Core function used in `synthesize` to aggregate multiple `snarks`.
///  
/// Returns the assigned instances of previous snarks and the new final pair that needs to be verified in a pairing check.
/// For each previous snark, we concatenate all instances into a single vector. We return a vector of vectors,
/// one vector per snark, for convenience.
///
/// # Assumptions
/// * `snarks` is not empty
pub fn aggregate<'a, AS>(
    svk: &Svk,
    loader: &Rc<Halo2Loader<'a>>,
    snarks: &[Snark],
    as_proof: &[u8],
) -> (Vec<Vec<AssignedValue<Fr>>>, KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>>)
where
    AS: PolynomialCommitmentScheme<
            G1Affine,
            Rc<Halo2Loader<'a>>,
            VerifyingKey = Svk,
            Output = KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>>,
        > + AccumulationScheme<
            G1Affine,
            Rc<Halo2Loader<'a>>,
            Accumulator = KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>>,
            VerifyingKey = KzgAsVerifyingKey,
        >,
{
    assert!(!snarks.is_empty(), "trying to aggregate 0 snarks");
    let assign_instances = |instances: &[Vec<Fr>]| {
        instances
            .iter()
            .map(|instances| {
                instances.iter().map(|instance| loader.assign_scalar(*instance)).collect_vec()
            })
            .collect_vec()
    };

    let mut previous_instances = Vec::with_capacity(snarks.len());
    // to avoid re-loading the spec each time, we create one transcript and clear the stream
    let mut transcript = PoseidonTranscript::<Rc<Halo2Loader<'a>>, &[u8]>::from_spec(
        loader,
        &[],
        POSEIDON_SPEC.clone(),
    );

    let mut accumulators = snarks
        .iter()
        .flat_map(|snark| {
            let protocol = snark.protocol.loaded(loader);
            let instances = assign_instances(&snark.instances);

            // read the transcript and perform Fiat-Shamir
            // run through verification computation and produce the final pair `succinct`
            transcript.new_stream(snark.proof());
            let proof = PlonkSuccinctVerifier::<AS>::read_proof(
                svk,
                &protocol,
                &instances,
                &mut transcript,
            )
            .unwrap();
            let accumulator =
                PlonkSuccinctVerifier::<AS>::verify(svk, &protocol, &instances, &proof).unwrap();

            previous_instances.push(
                instances.into_iter().flatten().map(|scalar| scalar.into_assigned()).collect(),
            );

            accumulator
        })
        .collect_vec();

    let accumulator = if accumulators.len() > 1 {
        transcript.new_stream(as_proof);
        let proof = <AS as AccumulationScheme<_, _>>::read_proof(
            &Default::default(),
            &accumulators,
            &mut transcript,
        )
        .unwrap();
        <AS as AccumulationScheme<_, _>>::verify(&Default::default(), &accumulators, &proof)
            .unwrap()
    } else {
        accumulators.pop().unwrap()
    };

    (previous_instances, accumulator)
}

/// Same as `FlexGateConfigParams` except we assume a single Phase and default 'Vertical' strategy.
/// Also adds `lookup_bits` field.
#[derive(Clone, Copy, Default, Debug, Serialize, Deserialize)]
pub struct AggregationConfigParams {
    pub degree: u32,
    pub num_advice: usize,
    pub num_lookup_advice: usize,
    pub num_fixed: usize,
    pub lookup_bits: usize,
}

impl AggregationConfigParams {
    pub fn from_path(path: impl AsRef<Path>) -> Self {
        serde_json::from_reader(File::open(path).expect("Aggregation config path does not exist"))
            .unwrap()
    }
}

impl From<AggregationConfigParams> for BaseConfigParams {
    fn from(params: AggregationConfigParams) -> Self {
        BaseConfigParams {
            strategy: GateStrategy::Vertical,
            k: params.degree as usize,
            num_advice_per_phase: vec![params.num_advice],
            num_lookup_advice_per_phase: vec![params.num_lookup_advice],
            num_fixed: params.num_fixed,
            lookup_bits: Some(params.lookup_bits),
        }
    }
}

impl TryFrom<&BaseConfigParams> for AggregationConfigParams {
    type Error = &'static str;

    fn try_from(params: &BaseConfigParams) -> Result<Self, Self::Error> {
        if params.num_advice_per_phase.iter().skip(1).any(|&n| n != 0) {
            return Err("AggregationConfigParams only supports 1 phase");
        }
        if params.num_lookup_advice_per_phase.iter().skip(1).any(|&n| n != 0) {
            return Err("AggregationConfigParams only supports 1 phase");
        }
        if params.lookup_bits.is_none() {
            return Err("AggregationConfigParams requires lookup_bits");
        }
        Ok(Self {
            degree: params.k as u32,
            num_advice: params.num_advice_per_phase[0],
            num_lookup_advice: params.num_lookup_advice_per_phase[0],
            num_fixed: params.num_fixed,
            lookup_bits: params.lookup_bits.unwrap(),
        })
    }
}

/// Holds virtual contexts for the cells used to verify a collection of snarks
#[derive(Clone, Debug)]
pub struct AggregationCtxBuilder {
    /// Virtual region with virtual contexts (columns)
    pub builder: GateThreadBuilder<Fr>,
    /// The limbs of the pair of elliptic curve points that need to be verified in a final pairing check.
    pub accumulator: Vec<AssignedValue<Fr>>,
    // the public instances from previous snarks that were aggregated
    pub previous_instances: Vec<Vec<AssignedValue<Fr>>>,
}

#[derive(Clone, Debug)]
pub struct AggregationCircuit {
    pub inner: RangeWithInstanceCircuitBuilder<Fr>,
    // the public instances from previous snarks that were aggregated, now collected as PRIVATE assigned values
    // the user can optionally append these to `inner.assigned_instances` to expose them
    pub previous_instances: Vec<Vec<AssignedValue<Fr>>>,
    // accumulation scheme proof, private input
    // pub as_proof: Vec<u8>,
}

// trait just so we can have a generic that is either SHPLONK or GWC
pub trait Halo2KzgAccumulationScheme<'a> = PolynomialCommitmentScheme<
        G1Affine,
        Rc<Halo2Loader<'a>>,
        VerifyingKey = Svk,
        Output = KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>>,
    > + AccumulationScheme<
        G1Affine,
        Rc<Halo2Loader<'a>>,
        Accumulator = KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>>,
        VerifyingKey = KzgAsVerifyingKey,
    > + PolynomialCommitmentScheme<
        G1Affine,
        NativeLoader,
        VerifyingKey = Svk,
        Output = KzgAccumulator<G1Affine, NativeLoader>,
    > + AccumulationScheme<
        G1Affine,
        NativeLoader,
        Accumulator = KzgAccumulator<G1Affine, NativeLoader>,
        VerifyingKey = KzgAsVerifyingKey,
    > + AccumulationSchemeProver<G1Affine, ProvingKey = KzgAsProvingKey<G1Affine>>;

impl AggregationCtxBuilder {
    /// Given snarks, this runs the `GateThreadBuilder` to verify all the snarks.
    ///
    /// Also returns the limbs of the pair of elliptic curve points, referred to as the `accumulator`, that need to be verified in a final pairing check.
    ///
    /// Warning: will fail silently if `snarks` were created using a different multi-open scheme than `AS`
    /// where `AS` can be either [`crate::SHPLONK`] or [`crate::GWC`] (for original PLONK multi-open scheme)
    pub fn new<AS>(
        witness_gen_only: bool,
        lookup_bits: usize,
        params: &ParamsKZG<Bn256>,
        snarks: impl IntoIterator<Item = Snark>,
    ) -> Self
    where
        AS: for<'a> Halo2KzgAccumulationScheme<'a>,
    {
        let svk: Svk = params.get_g()[0].into();
        let snarks = snarks.into_iter().collect_vec();

        let mut transcript_read =
            PoseidonTranscript::<NativeLoader, &[u8]>::from_spec(&[], POSEIDON_SPEC.clone());
        // TODO: the snarks can probably store these accumulators
        let accumulators = snarks
            .iter()
            .flat_map(|snark| {
                transcript_read.new_stream(snark.proof());
                let proof = PlonkSuccinctVerifier::<AS>::read_proof(
                    &svk,
                    &snark.protocol,
                    &snark.instances,
                    &mut transcript_read,
                )
                .unwrap();
                PlonkSuccinctVerifier::<AS>::verify(&svk, &snark.protocol, &snark.instances, &proof)
                    .unwrap()
            })
            .collect_vec();

        let (_accumulator, as_proof) = {
            let mut transcript_write = PoseidonTranscript::<NativeLoader, Vec<u8>>::from_spec(
                vec![],
                POSEIDON_SPEC.clone(),
            );
            let rng = StdRng::from_entropy();
            let accumulator =
                AS::create_proof(&Default::default(), &accumulators, &mut transcript_write, rng)
                    .unwrap();
            (accumulator, transcript_write.finalize())
        };

        // create thread builder and run aggregation witness gen
        let builder = GateThreadBuilder::new(witness_gen_only);
        // create halo2loader
        let range = RangeChip::<Fr>::default(lookup_bits);
        let fp_chip = FpChip::<Fr>::new(&range, BITS, LIMBS);
        let ecc_chip = BaseFieldEccChip::new(&fp_chip);
        let loader = Halo2Loader::new(ecc_chip, builder);

        let (previous_instances, accumulator) =
            aggregate::<AS>(&svk, &loader, &snarks, as_proof.as_slice());
        let lhs = accumulator.lhs.assigned();
        let rhs = accumulator.rhs.assigned();
        let accumulator = lhs
            .x()
            .limbs()
            .iter()
            .chain(lhs.y().limbs().iter())
            .chain(rhs.x().limbs().iter())
            .chain(rhs.y().limbs().iter())
            .copied()
            .collect_vec();

        #[cfg(debug_assertions)]
        {
            let KzgAccumulator { lhs, rhs } = _accumulator;
            let instances =
                [lhs.x, lhs.y, rhs.x, rhs.y].map(fe_to_limbs::<_, Fr, LIMBS, BITS>).concat();
            for (lhs, rhs) in instances.iter().zip(accumulator.iter()) {
                assert_eq!(lhs, rhs.value());
            }
        }

        let builder = loader.take_ctx();
        Self { builder, accumulator, previous_instances }
    }
}

impl AggregationCircuit {
    /// Given snarks, this creates a circuit and runs the `GateThreadBuilder` to verify all the snarks.
    /// By default, the returned circuit has public instances equal to the limbs of the pair of elliptic curve points, referred to as the `accumulator`, that need to be verified in a final pairing check.
    ///
    /// The user can optionally modify the circuit after calling this function to add more instances to `assigned_instances` to expose.
    ///
    /// Warning: will fail silently if `snarks` were created using a different multi-open scheme than `AS`
    /// where `AS` can be either [`crate::SHPLONK`] or [`crate::GWC`] (for original PLONK multi-open scheme)
    pub fn new<AS>(
        stage: CircuitBuilderStage,
        agg_config: AggregationConfigParams,
        break_points: Option<MultiPhaseThreadBreakPoints>,
        params: &ParamsKZG<Bn256>,
        snarks: impl IntoIterator<Item = Snark>,
    ) -> Self
    where
        AS: for<'a> Halo2KzgAccumulationScheme<'a>,
    {
        let AggregationCtxBuilder { builder, accumulator, previous_instances } =
            AggregationCtxBuilder::new::<AS>(
                stage == CircuitBuilderStage::Prover,
                agg_config.lookup_bits,
                params,
                snarks,
            );
        let inner = RangeWithInstanceCircuitBuilder::from_stage(
            stage,
            builder,
            agg_config.into(),
            break_points,
            accumulator,
        );
        Self { inner, previous_instances }
    }

    pub fn public<AS>(
        stage: CircuitBuilderStage,
        agg_config: AggregationConfigParams,
        break_points: Option<MultiPhaseThreadBreakPoints>,
        params: &ParamsKZG<Bn256>,
        snarks: impl IntoIterator<Item = Snark>,
        has_prev_accumulator: bool,
    ) -> Self
    where
        AS: for<'a> Halo2KzgAccumulationScheme<'a>,
    {
        let mut private = Self::new::<AS>(stage, agg_config, break_points, params, snarks);
        private.expose_previous_instances(has_prev_accumulator);
        private
    }

    /// Re-expose the previous public instances of aggregated snarks again.
    /// If `hash_prev_accumulator` is true, then we assume all aggregated snarks were themselves
    /// aggregation snarks, and we exclude the old accumulators from the public input.
    pub fn expose_previous_instances(&mut self, has_prev_accumulator: bool) {
        let start = (has_prev_accumulator as usize) * 4 * LIMBS;
        for prev in self.previous_instances.iter() {
            self.inner.assigned_instances.extend_from_slice(&prev[start..]);
        }
    }

    /// Auto-configure the circuit and change the circuit's internal configuration parameters.
    pub fn config(&mut self, k: u32, minimum_rows: Option<usize>) -> BaseConfigParams {
        let mut new_config = self.inner.circuit.0.builder.borrow().config(k as usize, minimum_rows);
        new_config.lookup_bits = self.inner.circuit.0.config_params.lookup_bits;
        self.inner.circuit.0.config_params = new_config.clone();
        new_config
    }

    pub fn break_points(&self) -> MultiPhaseThreadBreakPoints {
        self.inner.break_points()
    }

    pub fn instance_count(&self) -> usize {
        self.inner.instance_count()
    }

    pub fn instance(&self) -> Vec<Fr> {
        self.inner.instance()
    }
}

impl<F: ScalarField> CircuitExt<F> for RangeWithInstanceCircuitBuilder<F> {
    fn num_instance(&self) -> Vec<usize> {
        vec![self.instance_count()]
    }

    fn instances(&self) -> Vec<Vec<F>> {
        vec![self.instance()]
    }

    fn selectors(config: &Self::Config) -> Vec<Selector> {
        config.base.gate().basic_gates[0].iter().map(|gate| gate.q_enable).collect()
    }
}

impl Circuit<Fr> for AggregationCircuit {
    type Config = PublicBaseConfig<Fr>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = AggregationConfigParams;

    fn params(&self) -> Self::Params {
        (&self.inner.circuit.0.config_params).try_into().unwrap()
    }

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure_with_params(
        meta: &mut ConstraintSystem<Fr>,
        params: Self::Params,
    ) -> Self::Config {
        RangeWithInstanceCircuitBuilder::configure_with_params(meta, params.into())
    }

    fn configure(_: &mut ConstraintSystem<Fr>) -> Self::Config {
        unreachable!()
    }

    fn synthesize(
        &self,
        config: Self::Config,
        layouter: impl Layouter<Fr>,
    ) -> Result<(), plonk::Error> {
        self.inner.synthesize(config, layouter)
    }
}

impl CircuitExt<Fr> for AggregationCircuit {
    fn num_instance(&self) -> Vec<usize> {
        self.inner.num_instance()
    }

    fn instances(&self) -> Vec<Vec<Fr>> {
        self.inner.instances()
    }

    fn accumulator_indices() -> Option<Vec<(usize, usize)>> {
        Some((0..4 * LIMBS).map(|idx| (0, idx)).collect())
    }

    fn selectors(config: &Self::Config) -> Vec<Selector> {
        RangeWithInstanceCircuitBuilder::selectors(config)
    }
}

pub fn load_verify_circuit_degree() -> u32 {
    let path = std::env::var("VERIFY_CONFIG")
        .unwrap_or_else(|_| "./configs/verify_circuit.config".to_string());
    let params: AggregationConfigParams = serde_json::from_reader(
        File::open(path.as_str()).unwrap_or_else(|_| panic!("{path} does not exist")),
    )
    .unwrap();
    params.degree
}
