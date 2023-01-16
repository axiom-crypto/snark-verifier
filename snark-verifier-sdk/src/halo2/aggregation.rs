#![allow(clippy::clone_on_copy)]
use crate::{Plonk, BITS, LIMBS};
#[cfg(feature = "display")]
use ark_std::{end_timer, start_timer};
use halo2_base::{
    halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        halo2curves::bn256::{Bn256, Fq, Fr, G1Affine},
        plonk::{self, Circuit, Column, ConstraintSystem, Instance, Selector},
        poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
    },
    utils::value_to_option,
};
use halo2_base::{Context, ContextParams};
use itertools::Itertools;
use rand::Rng;
use snark_verifier::{
    loader::{
        self,
        halo2::{
            halo2_ecc::{self, ecc::EccChip},
            EccInstructions,
        },
        native::NativeLoader,
    },
    pcs::{
        kzg::{Bdfg21, Kzg, KzgAccumulator, KzgAs, KzgSuccinctVerifyingKey},
        AccumulationScheme, AccumulationSchemeProver, MultiOpenScheme, PolynomialCommitmentScheme,
    },
    util::arithmetic::fe_to_limbs,
    verifier::PlonkVerifier,
};
use std::{fs::File, rc::Rc};

use super::{CircuitExt, PoseidonTranscript, Snark, SnarkWitness, POSEIDON_SPEC};

pub type Svk = KzgSuccinctVerifyingKey<G1Affine>;
pub type BaseFieldEccChip = halo2_ecc::ecc::BaseFieldEccChip<G1Affine>;
pub type Halo2Loader<'a> = loader::halo2::Halo2Loader<'a, G1Affine, BaseFieldEccChip>;
pub type Shplonk = Plonk<Kzg<Bn256, Bdfg21>>;

pub fn load_verify_circuit_degree() -> u32 {
    let path = std::env::var("VERIFY_CONFIG")
        .unwrap_or_else(|_| "./configs/verify_circuit.config".to_string());
    let params: AggregationConfigParams = serde_json::from_reader(
        File::open(path.as_str()).unwrap_or_else(|_| panic!("{path} does not exist")),
    )
    .unwrap();
    params.degree
}

#[allow(clippy::type_complexity)]
/// Core function used in `synthesize` to aggregate multiple `snarks`.
///  
/// Returns the assigned instances of previous snarks (all concatenated together) and the new final pair that needs to be verified in a pairing check
pub fn aggregate<'a, PCS>(
    svk: &PCS::SuccinctVerifyingKey,
    loader: &Rc<Halo2Loader<'a>>,
    snarks: &[SnarkWitness],
    as_proof: Value<&'_ [u8]>,
) -> (
    Vec<<BaseFieldEccChip as EccInstructions<'a, G1Affine>>::AssignedScalar>,
    KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>>,
)
where
    PCS: PolynomialCommitmentScheme<
            G1Affine,
            Rc<Halo2Loader<'a>>,
            Accumulator = KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>>,
        > + MultiOpenScheme<G1Affine, Rc<Halo2Loader<'a>>>,
{
    let assign_instances = |instances: &[Vec<Value<Fr>>]| {
        instances
            .iter()
            .map(|instances| {
                instances.iter().map(|instance| loader.assign_scalar(*instance)).collect_vec()
            })
            .collect_vec()
    };

    // TODO pre-allocate capacity better
    let mut previous_instances = Vec::new();
    let mut transcript = PoseidonTranscript::<Rc<Halo2Loader<'a>>, _>::from_spec(
        loader,
        Value::unknown(),
        POSEIDON_SPEC.clone(),
    );

    let mut accumulators = snarks
        .iter()
        .flat_map(|snark| {
            let protocol = snark.protocol.loaded(loader);
            // TODO use 1d vector
            let instances = assign_instances(&snark.instances);

            // read the transcript and perform Fiat-Shamir
            // run through verification computation and produce the final pair `succinct`
            transcript.new_stream(snark.proof());
            let proof = Plonk::<PCS>::read_proof(svk, &protocol, &instances, &mut transcript);
            let accumulator = Plonk::<PCS>::succinct_verify(svk, &protocol, &instances, &proof);

            previous_instances
                .extend(instances.into_iter().flatten().map(|scalar| scalar.into_assigned()));

            accumulator
        })
        .collect_vec();

    let accumulator = if accumulators.len() > 1 {
        transcript.new_stream(as_proof);
        let proof =
            KzgAs::<PCS>::read_proof(&Default::default(), &accumulators, &mut transcript).unwrap();
        KzgAs::<PCS>::verify(&Default::default(), &accumulators, &proof).unwrap()
    } else {
        accumulators.pop().unwrap()
    };

    (previous_instances, accumulator)
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct AggregationConfigParams {
    pub strategy: halo2_ecc::fields::fp::FpStrategy,
    pub degree: u32,
    pub num_advice: Vec<usize>,
    pub num_lookup_advice: Vec<usize>,
    pub num_fixed: usize,
    pub lookup_bits: usize,
    pub limb_bits: usize,
    pub num_limbs: usize,
}

#[derive(Clone, Debug)]
pub struct AggregationConfig {
    pub base_field_config: halo2_ecc::fields::fp::FpConfig<Fr, Fq>,
    pub instance: Column<Instance>,
}

impl AggregationConfig {
    pub fn configure(meta: &mut ConstraintSystem<Fr>, params: AggregationConfigParams) -> Self {
        assert!(
            params.limb_bits == BITS && params.num_limbs == LIMBS,
            "For now we fix limb_bits = {}, otherwise change code",
            BITS
        );
        let base_field_config = halo2_ecc::fields::fp::FpConfig::configure(
            meta,
            params.strategy,
            &params.num_advice,
            &params.num_lookup_advice,
            params.num_fixed,
            params.lookup_bits,
            BITS,
            LIMBS,
            halo2_base::utils::modulus::<Fq>(),
            0,
            params.degree as usize,
        );

        let instance = meta.instance_column();
        meta.enable_equality(instance);

        Self { base_field_config, instance }
    }

    pub fn range(&self) -> &halo2_base::gates::range::RangeConfig<Fr> {
        &self.base_field_config.range
    }

    pub fn gate(&self) -> &halo2_base::gates::flex_gate::FlexGateConfig<Fr> {
        &self.base_field_config.range.gate
    }

    pub fn ecc_chip(&self) -> halo2_ecc::ecc::BaseFieldEccChip<G1Affine> {
        EccChip::construct(self.base_field_config.clone())
    }
}

/// Aggregation circuit that does not re-expose any public inputs from aggregated snarks
///
/// This is mostly a reference implementation. In practice one will probably need to re-implement the circuit for one's particular use case with specific instance logic.
#[derive(Clone)]
pub struct AggregationCircuit {
    svk: Svk,
    snarks: Vec<SnarkWitness>,
    instances: Vec<Fr>,
    as_proof: Value<Vec<u8>>,
}

impl AggregationCircuit {
    pub fn new(
        params: &ParamsKZG<Bn256>,
        snarks: impl IntoIterator<Item = Snark>,
        transcript_write: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
        rng: impl Rng + Send,
    ) -> Self {
        let svk = params.get_g()[0].into();
        let snarks = snarks.into_iter().collect_vec();

        // TODO: this is all redundant calculation to get the public output
        // Halo2 should just be able to expose public output to instance column directly
        let mut transcript_read =
            PoseidonTranscript::<NativeLoader, &[u8]>::from_spec(&[], POSEIDON_SPEC.clone());
        let accumulators = snarks
            .iter()
            .flat_map(|snark| {
                transcript_read.new_stream(snark.proof.as_slice());
                let proof = Shplonk::read_proof(
                    &svk,
                    &snark.protocol,
                    &snark.instances,
                    &mut transcript_read,
                );
                Shplonk::succinct_verify(&svk, &snark.protocol, &snark.instances, &proof)
            })
            .collect_vec();

        let (accumulator, as_proof) = {
            transcript_write.clear();
            // We always use SHPLONK for accumulation scheme when aggregating proofs
            let accumulator = KzgAs::<Kzg<Bn256, Bdfg21>>::create_proof(
                &Default::default(),
                &accumulators,
                transcript_write,
                rng,
            )
            .unwrap();
            (accumulator, transcript_write.stream_mut().split_off(0))
        };

        let KzgAccumulator { lhs, rhs } = accumulator;
        let instances = [lhs.x, lhs.y, rhs.x, rhs.y].map(fe_to_limbs::<_, _, LIMBS, BITS>).concat();

        Self {
            svk,
            snarks: snarks.into_iter().map_into().collect(),
            instances,
            as_proof: Value::known(as_proof),
        }
    }

    pub fn instance(&self) -> Vec<Fr> {
        self.instances.clone()
    }

    pub fn succinct_verifying_key(&self) -> &Svk {
        &self.svk
    }

    pub fn snarks(&self) -> &[SnarkWitness] {
        &self.snarks
    }

    pub fn as_proof(&self) -> Value<&[u8]> {
        self.as_proof.as_ref().map(Vec::as_slice)
    }
}

impl CircuitExt<Fr> for AggregationCircuit {
    fn num_instance(&self) -> Vec<usize> {
        // [..lhs, ..rhs]
        vec![4 * LIMBS]
    }

    fn instances(&self) -> Vec<Vec<Fr>> {
        vec![self.instance()]
    }

    fn accumulator_indices() -> Option<Vec<(usize, usize)>> {
        Some((0..4 * LIMBS).map(|idx| (0, idx)).collect())
    }

    fn selectors(config: &Self::Config) -> Vec<Selector> {
        config.gate().basic_gates[0].iter().map(|gate| gate.q_enable).collect()
    }
}

impl Circuit<Fr> for AggregationCircuit {
    type Config = AggregationConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            svk: self.svk,
            snarks: self.snarks.iter().map(SnarkWitness::without_witnesses).collect(),
            instances: Vec::new(),
            as_proof: Value::unknown(),
        }
    }

    fn configure(meta: &mut plonk::ConstraintSystem<Fr>) -> Self::Config {
        let path = std::env::var("VERIFY_CONFIG")
            .unwrap_or_else(|_| "configs/verify_circuit.config".to_owned());
        let params: AggregationConfigParams = serde_json::from_reader(
            File::open(path.as_str()).unwrap_or_else(|_| panic!("{path:?} does not exist")),
        )
        .unwrap();

        AggregationConfig::configure(meta, params)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), plonk::Error> {
        #[cfg(feature = "display")]
        let witness_time = start_timer!(|| "synthesize | Aggregation Circuit");
        config.range().load_lookup_table(&mut layouter).expect("load range lookup table");
        let mut first_pass = halo2_base::SKIP_FIRST_PASS;
        let mut instances = vec![];
        layouter
            .assign_region(
                || "",
                |region| {
                    if first_pass {
                        first_pass = false;
                        return Ok(());
                    }
                    let ctx = Context::new(
                        region,
                        ContextParams {
                            max_rows: config.gate().max_rows,
                            num_context_ids: 1,
                            fixed_columns: config.gate().constants.clone(),
                        },
                    );

                    let ecc_chip = config.ecc_chip();
                    let loader = Halo2Loader::new(ecc_chip, ctx);
                    let (_, KzgAccumulator { lhs, rhs }) = aggregate::<Kzg<Bn256, Bdfg21>>(
                        &self.svk,
                        &loader,
                        &self.snarks,
                        self.as_proof(),
                    );

                    let lhs = lhs.assigned();
                    let rhs = rhs.assigned();

                    instances.extend(
                        lhs.x
                            .truncation
                            .limbs
                            .iter()
                            .chain(lhs.y.truncation.limbs.iter())
                            .chain(rhs.x.truncation.limbs.iter())
                            .chain(rhs.y.truncation.limbs.iter())
                            .map(|assigned| assigned.cell().clone()),
                    );
                    config.range().finalize(&mut loader.ctx_mut());
                    #[cfg(feature = "display")]
                    loader.ctx_mut().print_stats(&["Range"]);
                    Ok(())
                },
            )
            .unwrap();

        // Expose instances
        for (i, cell) in instances.into_iter().enumerate() {
            layouter.constrain_instance(cell, config.instance, i);
        }
        #[cfg(feature = "display")]
        end_timer!(witness_time);
        Ok(())
    }
}

/// This circuit takes multiple SNARKs and passes through all of their instances except the old accumulators.
///
/// * If `has_prev_accumulator = true`, we assume all SNARKs are of aggregation circuits with old accumulators
/// only in the first instance column.
/// * Otherwise if `has_prev_accumulator = false`, then all previous instances are passed through.
#[derive(Clone)]
pub struct PublicAggregationCircuit {
    pub aggregation: AggregationCircuit,
    pub has_prev_accumulator: bool,
}

impl PublicAggregationCircuit {
    pub fn new(
        params: &ParamsKZG<Bn256>,
        snarks: Vec<Snark>,
        has_prev_accumulator: bool,
        transcript_write: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
        rng: &mut (impl Rng + Send),
    ) -> Self {
        Self {
            aggregation: AggregationCircuit::new(params, snarks, transcript_write, rng),
            has_prev_accumulator,
        }
    }
}

impl CircuitExt<Fr> for PublicAggregationCircuit {
    fn num_instance(&self) -> Vec<usize> {
        let prev_num = self
            .aggregation
            .snarks
            .iter()
            .map(|snark| snark.instances.iter().map(|instance| instance.len()).sum::<usize>())
            .sum::<usize>()
            - self.aggregation.snarks.len() * 4 * LIMBS * usize::from(self.has_prev_accumulator);
        vec![4 * LIMBS + prev_num]
    }

    fn instances(&self) -> Vec<Vec<Fr>> {
        let start_idx = 4 * LIMBS * usize::from(self.has_prev_accumulator);
        let instance = self
            .aggregation
            .instances
            .iter()
            .cloned()
            .chain(self.aggregation.snarks.iter().flat_map(|snark| {
                snark.instances.iter().enumerate().flat_map(|(i, instance)| {
                    instance[usize::from(i == 0) * start_idx..]
                        .iter()
                        .map(|v| value_to_option(*v).unwrap())
                })
            }))
            .collect_vec();
        vec![instance]
    }

    fn accumulator_indices() -> Option<Vec<(usize, usize)>> {
        Some((0..4 * LIMBS).map(|idx| (0, idx)).collect())
    }

    fn selectors(config: &Self::Config) -> Vec<Selector> {
        config.gate().basic_gates[0].iter().map(|gate| gate.q_enable).collect()
    }
}

impl Circuit<Fr> for PublicAggregationCircuit {
    type Config = AggregationConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            aggregation: self.aggregation.without_witnesses(),
            has_prev_accumulator: self.has_prev_accumulator,
        }
    }

    fn configure(meta: &mut plonk::ConstraintSystem<Fr>) -> Self::Config {
        AggregationCircuit::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), plonk::Error> {
        #[cfg(feature = "display")]
        let witness_time = start_timer!(|| { "synthesize | EVM verifier" });
        config.range().load_lookup_table(&mut layouter).expect("load range lookup table");
        let mut first_pass = halo2_base::SKIP_FIRST_PASS;
        let mut instances = vec![];
        layouter
            .assign_region(
                || "",
                |region| {
                    if first_pass {
                        first_pass = false;
                        return Ok(());
                    }
                    let ctx = Context::new(
                        region,
                        ContextParams {
                            max_rows: config.gate().max_rows,
                            num_context_ids: 1,
                            fixed_columns: config.gate().constants.clone(),
                        },
                    );

                    let ecc_chip = config.ecc_chip();
                    let loader = Halo2Loader::new(ecc_chip, ctx);
                    let (prev_instances, KzgAccumulator { lhs, rhs }) =
                        aggregate::<Kzg<Bn256, Bdfg21>>(
                            &self.aggregation.svk,
                            &loader,
                            &self.aggregation.snarks,
                            self.aggregation.as_proof(),
                        );
                    let lhs = lhs.assigned();
                    let rhs = rhs.assigned();

                    // accumulator
                    instances.extend(
                        lhs.x
                            .truncation
                            .limbs
                            .iter()
                            .chain(lhs.y.truncation.limbs.iter())
                            .chain(rhs.x.truncation.limbs.iter())
                            .chain(rhs.y.truncation.limbs.iter())
                            .map(|a| a.cell().clone()),
                    );
                    // prev instances except accumulators
                    let mut idx = 0;
                    let start_idx = 4 * LIMBS * usize::from(self.has_prev_accumulator);
                    for snark in self.aggregation.snarks.iter() {
                        for (i, instance) in snark.instances.iter().enumerate() {
                            let start_idx = usize::from(i == 0) * start_idx;
                            instances.extend(
                                prev_instances[idx + start_idx..idx + instance.len()]
                                    .iter()
                                    .map(|a| a.cell().clone()),
                            );
                            idx += instance.len();
                        }
                    }

                    config.range().finalize(&mut loader.ctx_mut());
                    #[cfg(feature = "display")]
                    loader.ctx_mut().print_stats(&["Range"]);
                    Ok(())
                },
            )
            .unwrap();
        // Expose instances
        for (i, cell) in instances.into_iter().enumerate() {
            layouter.constrain_instance(cell, config.instance, i);
        }
        #[cfg(feature = "display")]
        end_timer!(witness_time);
        Ok(())
    }
}
