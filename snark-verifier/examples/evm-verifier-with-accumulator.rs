use ethereum_types::Address;
use halo2_base::halo2_proofs;
use halo2_proofs::{
    dev::MockProver,
    halo2curves::bn256::{Bn256, Fq, Fr, G1Affine},
    plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey},
    poly::{
        commitment::{Params, ParamsProver},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::AccumulatorStrategy,
        },
        VerificationStrategy,
    },
    transcript::{EncodedChallenge, TranscriptReadBuffer, TranscriptWriterBuffer},
};
use itertools::Itertools;
use rand::rngs::OsRng;
use snark_verifier::{
    loader::{
        evm::{self, encode_calldata, EvmLoader, ExecutorBuilder},
        native::NativeLoader,
    },
    pcs::kzg::{Gwc19, Kzg, KzgAs, LimbsEncoding},
    system::halo2::{compile, transcript::evm::EvmTranscript, Config},
    verifier::{self, PlonkVerifier},
};
use std::{io::Cursor, rc::Rc};

const LIMBS: usize = 3;
const BITS: usize = 88;

type Pcs = Kzg<Bn256, Gwc19>;
type As = KzgAs<Pcs>;
type Plonk = verifier::Plonk<Pcs, LimbsEncoding<LIMBS, BITS>>;

mod application {
    use super::halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance},
        poly::Rotation,
    };
    use super::Fr;
    use halo2_base::halo2_proofs::plonk::Assigned;
    use rand::RngCore;

    #[derive(Clone, Copy)]
    pub struct StandardPlonkConfig {
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
        q_a: Column<Fixed>,
        q_b: Column<Fixed>,
        q_c: Column<Fixed>,
        q_ab: Column<Fixed>,
        constant: Column<Fixed>,
        #[allow(dead_code)]
        instance: Column<Instance>,
    }

    impl StandardPlonkConfig {
        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self {
            let [a, b, c] = [(); 3].map(|_| meta.advice_column());
            let [q_a, q_b, q_c, q_ab, constant] = [(); 5].map(|_| meta.fixed_column());
            let instance = meta.instance_column();

            [a, b, c].map(|column| meta.enable_equality(column));

            meta.create_gate(
                "q_a·a + q_b·b + q_c·c + q_ab·a·b + constant + instance = 0",
                |meta| {
                    let [a, b, c] =
                        [a, b, c].map(|column| meta.query_advice(column, Rotation::cur()));
                    let [q_a, q_b, q_c, q_ab, constant] = [q_a, q_b, q_c, q_ab, constant]
                        .map(|column| meta.query_fixed(column, Rotation::cur()));
                    let instance = meta.query_instance(instance, Rotation::cur());
                    Some(
                        q_a * a.clone()
                            + q_b * b.clone()
                            + q_c * c
                            + q_ab * a * b
                            + constant
                            + instance,
                    )
                },
            );

            StandardPlonkConfig { a, b, c, q_a, q_b, q_c, q_ab, constant, instance }
        }
    }

    #[derive(Clone, Default)]
    pub struct StandardPlonk(Fr);

    impl StandardPlonk {
        pub fn rand<R: RngCore>(mut rng: R) -> Self {
            Self(Fr::from(rng.next_u32() as u64))
        }

        pub fn num_instance() -> Vec<usize> {
            vec![1]
        }

        pub fn instances(&self) -> Vec<Vec<Fr>> {
            vec![vec![self.0]]
        }
    }

    impl Circuit<Fr> for StandardPlonk {
        type Config = StandardPlonkConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            meta.set_minimum_degree(4);
            StandardPlonkConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "",
                |mut region| {
                    #[cfg(feature = "halo2-pse")]
                    {
                        region.assign_advice(|| "", config.a, 0, || Value::known(self.0))?;
                        region.assign_fixed(|| "", config.q_a, 0, || Value::known(-Fr::one()))?;

                        region.assign_advice(
                            || "",
                            config.a,
                            1,
                            || Value::known(-Fr::from(5u64)),
                        )?;
                        for (idx, column) in (1..).zip([
                            config.q_a,
                            config.q_b,
                            config.q_c,
                            config.q_ab,
                            config.constant,
                        ]) {
                            region.assign_fixed(
                                || "",
                                column,
                                1,
                                || Value::known(Fr::from(idx as u64)),
                            )?;
                        }

                        let a =
                            region.assign_advice(|| "", config.a, 2, || Value::known(Fr::one()))?;
                        a.copy_advice(|| "", &mut region, config.b, 3)?;
                        a.copy_advice(|| "", &mut region, config.c, 4)?;
                    }
                    #[cfg(feature = "halo2-axiom")]
                    {
                        region.assign_advice(
                            config.a,
                            0,
                            Value::known(Assigned::Trivial(self.0)),
                        )?;
                        region.assign_fixed(config.q_a, 0, Assigned::Trivial(-Fr::one()));

                        region.assign_advice(
                            config.a,
                            1,
                            Value::known(Assigned::Trivial(-Fr::from(5u64))),
                        )?;
                        for (idx, column) in (1..).zip([
                            config.q_a,
                            config.q_b,
                            config.q_c,
                            config.q_ab,
                            config.constant,
                        ]) {
                            region.assign_fixed(column, 1, Assigned::Trivial(Fr::from(idx as u64)));
                        }

                        let a = region.assign_advice(
                            config.a,
                            2,
                            Value::known(Assigned::Trivial(Fr::one())),
                        )?;
                        a.copy_advice(&mut region, config.b, 3);
                        a.copy_advice(&mut region, config.c, 4);
                    }

                    Ok(())
                },
            )
        }
    }
}

mod aggregation {
    use super::halo2_proofs::{
        circuit::{Cell, Layouter, SimpleFloorPlanner, Value},
        plonk::{self, Circuit, Column, ConstraintSystem, Instance},
        poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
    };
    use super::{As, Plonk, BITS, LIMBS};
    use super::{Bn256, Fq, Fr, G1Affine};
    use ark_std::{end_timer, start_timer};
    use halo2_base::{Context, ContextParams};
    use halo2_ecc::ecc::EccChip;
    use itertools::Itertools;
    use rand::rngs::OsRng;
    use snark_verifier::{
        loader::{self, native::NativeLoader},
        pcs::{
            kzg::{KzgAccumulator, KzgSuccinctVerifyingKey},
            AccumulationScheme, AccumulationSchemeProver,
        },
        system,
        util::arithmetic::fe_to_limbs,
        verifier::PlonkVerifier,
        Protocol,
    };
    use std::{fs::File, rc::Rc};

    const T: usize = 5;
    const RATE: usize = 4;
    const R_F: usize = 8;
    const R_P: usize = 60;

    type Svk = KzgSuccinctVerifyingKey<G1Affine>;
    type BaseFieldEccChip = halo2_ecc::ecc::BaseFieldEccChip<G1Affine>;
    type Halo2Loader<'a> = loader::halo2::Halo2Loader<'a, G1Affine, BaseFieldEccChip>;
    pub type PoseidonTranscript<L, S> =
        system::halo2::transcript::halo2::PoseidonTranscript<G1Affine, L, S, T, RATE, R_F, R_P>;

    pub struct Snark {
        protocol: Protocol<G1Affine>,
        instances: Vec<Vec<Fr>>,
        proof: Vec<u8>,
    }

    impl Snark {
        pub fn new(protocol: Protocol<G1Affine>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) -> Self {
            Self { protocol, instances, proof }
        }
    }

    impl From<Snark> for SnarkWitness {
        fn from(snark: Snark) -> Self {
            Self {
                protocol: snark.protocol,
                instances: snark
                    .instances
                    .into_iter()
                    .map(|instances| instances.into_iter().map(Value::known).collect_vec())
                    .collect(),
                proof: Value::known(snark.proof),
            }
        }
    }

    #[derive(Clone)]
    pub struct SnarkWitness {
        protocol: Protocol<G1Affine>,
        instances: Vec<Vec<Value<Fr>>>,
        proof: Value<Vec<u8>>,
    }

    impl SnarkWitness {
        fn without_witnesses(&self) -> Self {
            SnarkWitness {
                protocol: self.protocol.clone(),
                instances: self
                    .instances
                    .iter()
                    .map(|instances| vec![Value::unknown(); instances.len()])
                    .collect(),
                proof: Value::unknown(),
            }
        }

        fn proof(&self) -> Value<&[u8]> {
            self.proof.as_ref().map(Vec::as_slice)
        }
    }

    pub fn aggregate<'a>(
        svk: &Svk,
        loader: &Rc<Halo2Loader<'a>>,
        snarks: &[SnarkWitness],
        as_proof: Value<&'_ [u8]>,
    ) -> KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>> {
        let assign_instances = |instances: &[Vec<Value<Fr>>]| {
            instances
                .iter()
                .map(|instances| {
                    instances.iter().map(|instance| loader.assign_scalar(*instance)).collect_vec()
                })
                .collect_vec()
        };

        let accumulators = snarks
            .iter()
            .flat_map(|snark| {
                let protocol = snark.protocol.loaded(loader);
                let instances = assign_instances(&snark.instances);
                let mut transcript =
                    PoseidonTranscript::<Rc<Halo2Loader>, _>::new(loader, snark.proof());
                let proof = Plonk::read_proof(svk, &protocol, &instances, &mut transcript);
                Plonk::succinct_verify(svk, &protocol, &instances, &proof)
            })
            .collect_vec();

        let acccumulator = {
            let mut transcript = PoseidonTranscript::<Rc<Halo2Loader>, _>::new(loader, as_proof);
            let proof =
                As::read_proof(&Default::default(), &accumulators, &mut transcript).unwrap();
            As::verify(&Default::default(), &accumulators, &proof).unwrap()
        };

        acccumulator
    }

    #[derive(serde::Serialize, serde::Deserialize)]
    pub struct AggregationConfigParams {
        pub strategy: halo2_ecc::fields::fp::FpStrategy,
        pub degree: u32,
        pub num_advice: usize,
        pub num_lookup_advice: usize,
        pub num_fixed: usize,
        pub lookup_bits: usize,
        pub limb_bits: usize,
        pub num_limbs: usize,
    }

    #[derive(Clone)]
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
                &[params.num_advice],
                &[params.num_lookup_advice],
                params.num_fixed,
                params.lookup_bits,
                params.limb_bits,
                params.num_limbs,
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

        pub fn ecc_chip(&self) -> halo2_ecc::ecc::BaseFieldEccChip<G1Affine> {
            EccChip::construct(self.base_field_config.clone())
        }
    }

    #[derive(Clone)]
    pub struct AggregationCircuit {
        svk: Svk,
        snarks: Vec<SnarkWitness>,
        instances: Vec<Fr>,
        as_proof: Value<Vec<u8>>,
    }

    impl AggregationCircuit {
        pub fn new(params: &ParamsKZG<Bn256>, snarks: impl IntoIterator<Item = Snark>) -> Self {
            let svk = params.get_g()[0].into();
            let snarks = snarks.into_iter().collect_vec();

            let accumulators = snarks
                .iter()
                .flat_map(|snark| {
                    let mut transcript =
                        PoseidonTranscript::<NativeLoader, _>::new(snark.proof.as_slice());
                    let proof =
                        Plonk::read_proof(&svk, &snark.protocol, &snark.instances, &mut transcript);
                    Plonk::succinct_verify(&svk, &snark.protocol, &snark.instances, &proof)
                })
                .collect_vec();

            let (accumulator, as_proof) = {
                let mut transcript = PoseidonTranscript::<NativeLoader, _>::new(Vec::new());
                let accumulator =
                    As::create_proof(&Default::default(), &accumulators, &mut transcript, OsRng)
                        .unwrap();
                (accumulator, transcript.finalize())
            };

            let KzgAccumulator { lhs, rhs } = accumulator;
            let instances =
                [lhs.x, lhs.y, rhs.x, rhs.y].map(fe_to_limbs::<_, _, LIMBS, BITS>).concat();

            Self {
                svk,
                snarks: snarks.into_iter().map_into().collect(),
                instances,
                as_proof: Value::known(as_proof),
            }
        }

        pub fn as_proof(&self) -> Value<&[u8]> {
            self.as_proof.as_ref().map(Vec::as_slice)
        }

        pub fn num_instance() -> Vec<usize> {
            // [..lhs, ..rhs]
            vec![4 * LIMBS]
        }

        pub fn instances(&self) -> Vec<Vec<Fr>> {
            vec![self.instances.clone()]
        }

        pub fn accumulator_indices() -> Vec<(usize, usize)> {
            (0..4 * LIMBS).map(|idx| (0, idx)).collect()
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
            let path = std::env::var("VERIFY_CONFIG").unwrap();
            let params: AggregationConfigParams = serde_json::from_reader(
                File::open(path.as_str())
                    .unwrap_or_else(|err| panic!("Path {path} does not exist: {err:?}")),
            )
            .unwrap();

            AggregationConfig::configure(meta, params)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), plonk::Error> {
            config.range().load_lookup_table(&mut layouter)?;
            let max_rows = config.range().gate.max_rows;

            let mut first_pass = halo2_base::SKIP_FIRST_PASS; // assume using simple floor planner
            let mut assigned_instances: Option<Vec<Cell>> = None;
            layouter.assign_region(
                || "",
                |region| {
                    if first_pass {
                        first_pass = false;
                        return Ok(());
                    }
                    let witness_time = start_timer!(|| "Witness Collection");
                    let ctx = Context::new(
                        region,
                        ContextParams {
                            max_rows,
                            num_context_ids: 1,
                            fixed_columns: config.base_field_config.range.gate.constants.clone(),
                        },
                    );

                    let ecc_chip = config.ecc_chip();
                    let loader = Halo2Loader::new(ecc_chip, ctx);
                    let KzgAccumulator { lhs, rhs } =
                        aggregate(&self.svk, &loader, &self.snarks, self.as_proof());

                    let lhs = lhs.assigned();
                    let rhs = rhs.assigned();

                    config.base_field_config.finalize(&mut loader.ctx_mut());
                    #[cfg(feature = "display")]
                    println!("Total advice cells: {}", loader.ctx().total_advice);
                    #[cfg(feature = "display")]
                    println!("Advice columns used: {}", loader.ctx().advice_alloc[0].0 + 1);

                    let instances: Vec<_> = lhs
                        .x
                        .truncation
                        .limbs
                        .iter()
                        .chain(lhs.y.truncation.limbs.iter())
                        .chain(rhs.x.truncation.limbs.iter())
                        .chain(rhs.y.truncation.limbs.iter())
                        .map(|assigned| assigned.cell().clone())
                        .collect();
                    assigned_instances = Some(instances);
                    end_timer!(witness_time);
                    Ok(())
                },
            )?;

            // Expose instances
            // TODO: use less instances by following Scroll's strategy of keeping only last bit of y coordinate
            let mut layouter = layouter.namespace(|| "expose");
            for (i, cell) in assigned_instances.unwrap().into_iter().enumerate() {
                layouter.constrain_instance(cell, config.instance, i);
            }
            Ok(())
        }
    }
}

fn gen_pk<C: Circuit<Fr>>(params: &ParamsKZG<Bn256>, circuit: &C) -> ProvingKey<G1Affine> {
    let vk = keygen_vk(params, circuit).unwrap();
    keygen_pk(params, vk, circuit).unwrap()
}

fn gen_proof<
    C: Circuit<Fr>,
    E: EncodedChallenge<G1Affine>,
    TR: TranscriptReadBuffer<Cursor<Vec<u8>>, G1Affine, E>,
    TW: TranscriptWriterBuffer<Vec<u8>, G1Affine, E>,
>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
) -> Vec<u8> {
    MockProver::run(params.k(), &circuit, instances.clone()).unwrap().assert_satisfied();

    let instances = instances.iter().map(|instances| instances.as_slice()).collect_vec();
    let proof = {
        let mut transcript = TW::init(Vec::new());
        create_proof::<KZGCommitmentScheme<Bn256>, ProverGWC<_>, _, _, TW, _>(
            params,
            pk,
            &[circuit],
            &[instances.as_slice()],
            OsRng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };

    let accept = {
        let mut transcript = TR::init(Cursor::new(proof.clone()));
        VerificationStrategy::<_, VerifierGWC<_>>::finalize(
            verify_proof::<_, VerifierGWC<_>, _, TR, _>(
                params.verifier_params(),
                pk.get_vk(),
                AccumulatorStrategy::new(params.verifier_params()),
                &[instances.as_slice()],
                &mut transcript,
            )
            .unwrap(),
        )
    };
    assert!(accept);

    proof
}

fn gen_application_snark(params: &ParamsKZG<Bn256>) -> aggregation::Snark {
    let circuit = application::StandardPlonk::rand(OsRng);

    let pk = gen_pk(params, &circuit);
    let protocol = compile(
        params,
        pk.get_vk(),
        Config::kzg().with_num_instance(application::StandardPlonk::num_instance()),
    );

    let proof = gen_proof::<
        _,
        _,
        aggregation::PoseidonTranscript<NativeLoader, _>,
        aggregation::PoseidonTranscript<NativeLoader, _>,
    >(params, &pk, circuit.clone(), circuit.instances());
    aggregation::Snark::new(protocol, circuit.instances(), proof)
}

fn gen_aggregation_evm_verifier(
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    num_instance: Vec<usize>,
    accumulator_indices: Vec<(usize, usize)>,
) -> Vec<u8> {
    let svk = params.get_g()[0].into();
    let dk = (params.g2(), params.s_g2()).into();
    let protocol = compile(
        params,
        vk,
        Config::kzg()
            .with_num_instance(num_instance.clone())
            .with_accumulator_indices(Some(accumulator_indices)),
    );

    let loader = EvmLoader::new::<Fq, Fr>();
    let protocol = protocol.loaded(&loader);
    let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(&loader);

    let instances = transcript.load_instances(num_instance);
    let proof = Plonk::read_proof(&svk, &protocol, &instances, &mut transcript);
    Plonk::verify(&svk, &dk, &protocol, &instances, &proof);

    evm::compile_yul(&loader.yul_code())
}

fn evm_verify(deployment_code: Vec<u8>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) {
    let calldata = encode_calldata(&instances, &proof);
    let success = {
        let mut evm = ExecutorBuilder::default().with_gas_limit(u64::MAX.into()).build();

        let caller = Address::from_low_u64_be(0xfe);
        let verifier = evm.deploy(caller, deployment_code.into(), 0.into()).address.unwrap();
        let result = evm.call_raw(caller, verifier, calldata.into(), 0.into());

        dbg!(result.gas_used);

        !result.reverted
    };
    assert!(success);
}

fn main() {
    std::env::set_var("VERIFY_CONFIG", "./configs/example_evm_accumulator.config");
    let params = halo2_base::utils::fs::gen_srs(21);
    let params_app = {
        let mut params = params.clone();
        params.downsize(8);
        params
    };

    let snarks = [(); 3].map(|_| gen_application_snark(&params_app));
    let agg_circuit = aggregation::AggregationCircuit::new(&params, snarks);
    let pk = gen_pk(&params, &agg_circuit);
    let deployment_code = gen_aggregation_evm_verifier(
        &params,
        pk.get_vk(),
        aggregation::AggregationCircuit::num_instance(),
        aggregation::AggregationCircuit::accumulator_indices(),
    );

    let proof = gen_proof::<_, _, EvmTranscript<G1Affine, _, _, _>, EvmTranscript<G1Affine, _, _, _>>(
        &params,
        &pk,
        agg_circuit.clone(),
        agg_circuit.instances(),
    );
    evm_verify(deployment_code, agg_circuit.instances(), proof);
}
