use application::StandardPlonk;
use ark_std::{end_timer, start_timer};
use ethereum_types::Address;
use foundry_evm::executor::{fork::MultiFork, Backend, ExecutorBuilder};
use halo2_curves::bn256::{Bn256, Fq, Fr, G1Affine};
use halo2_proofs::{
    dev::MockProver,
    plonk::{create_proof, verify_proof, Circuit, ProvingKey, VerifyingKey},
    poly::{
        commitment::{Params, ParamsProver},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::AccumulatorStrategy,
        },
        VerificationStrategy,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, EncodedChallenge, TranscriptReadBuffer,
        TranscriptWriterBuffer,
    },
};
use itertools::Itertools;
use plonk_verifier::{
    loader::{
        evm::{encode_calldata, EvmLoader},
        native::NativeLoader,
    },
    pcs::kzg::{Gwc19, Kzg, LimbsEncoding},
    system::halo2::{
        aggregation::{
            self, create_snark_shplonk, gen_pk, gen_srs, write_bytes, AggregationCircuit, Snark,
            TargetCircuit,
        },
        compile,
        transcript::evm::EvmTranscript,
        Config,
    },
    verifier::{self, PlonkVerifier},
};
use rand::rngs::OsRng;
use std::{fs, io::Cursor, rc::Rc};

const LIMBS: usize = 3;
const BITS: usize = 88;

type Pcs = Kzg<Bn256, Gwc19>;
// type As = KzgAs<Pcs>;
type Plonk = verifier::Plonk<Pcs, LimbsEncoding<LIMBS, BITS>>;

mod application {
    use halo2_curves::bn256::Fr;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance},
        poly::Rotation,
    };
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
    pub struct StandardPlonk(pub Fr);

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
                    region.assign_advice(|| "", config.a, 0, || Value::known(self.0))?;
                    region.assign_fixed(|| "", config.q_a, 0, || Value::known(-Fr::one()))?;

                    region.assign_advice(|| "", config.a, 1, || Value::known(-Fr::from(5)))?;
                    for (idx, column) in (1..).zip([
                        config.q_a,
                        config.q_b,
                        config.q_c,
                        config.q_ab,
                        config.constant,
                    ]) {
                        region.assign_fixed(|| "", column, 1, || Value::known(Fr::from(idx)))?;
                    }

                    let a = region.assign_advice(|| "", config.a, 2, || Value::known(Fr::one()))?;
                    a.copy_advice(|| "", &mut region, config.b, 3)?;
                    a.copy_advice(|| "", &mut region, config.c, 4)?;

                    Ok(())
                },
            )
        }
    }
}

fn gen_proof<
    C: Circuit<Fr> + Clone,
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
    // For testing purposes: Native verify
    // Uncomment to test if evm verifier fails silently
    /*{
        let proof = {
            let mut transcript = Blake2bWrite::init(Vec::new());
            create_proof::<
                KZGCommitmentScheme<Bn256>,
                ProverGWC<_>,
                Challenge255<G1Affine>,
                _,
                Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
                _,
            >(
                params,
                pk,
                &[circuit.clone()],
                &[&[instances[0].as_slice()]],
                OsRng,
                &mut transcript,
            )
            .unwrap();
            transcript.finalize()
        };
        let svk = params.get_g()[0].into();
        let dk = (params.g2(), params.s_g2()).into();
        let protocol = compile(
            params,
            pk.get_vk(),
            Config::kzg(aggregation::KZG_QUERY_INSTANCE)
                .with_num_instance(vec![instances[0].len()])
                .with_accumulator_indices(aggregation::AggregationCircuit::accumulator_indices()),
        );
        let mut transcript = Blake2bRead::<_, G1Affine, _>::init(proof.as_slice());
        let instances = &[instances[0].to_vec()];
        let proof = Plonk::read_proof(&svk, &protocol, instances, &mut transcript).unwrap();
        assert!(Plonk::verify(&svk, &dk, &protocol, instances, &proof).unwrap());
    }*/

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
        Config::kzg(aggregation::KZG_QUERY_INSTANCE)
            .with_num_instance(num_instance.clone())
            .with_accumulator_indices(accumulator_indices),
    );

    let loader = EvmLoader::new::<Fq, Fr>();
    let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(loader.clone());

    let instances = transcript.load_instances(num_instance);
    let proof = Plonk::read_proof(&svk, &protocol, &instances, &mut transcript).unwrap();
    Plonk::verify(&svk, &dk, &protocol, &instances, &proof).unwrap();

    loader.deployment_code()
}

fn evm_verify(deployment_code: Vec<u8>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) {
    let calldata = encode_calldata(&instances, &proof);
    fs::write("./data/verifier_calldata.dat", hex::encode(&calldata)).unwrap();
    let success = {
        let mut evm = ExecutorBuilder::default()
            .with_gas_limit(u64::MAX.into())
            .build(Backend::new(MultiFork::new().0, None));

        let caller = Address::from_low_u64_be(0xfe);
        let verifier = evm.deploy(caller, deployment_code.into(), 0.into(), None).unwrap();
        dbg!(verifier.gas);
        let verifier = verifier.address;
        let result = evm.call_raw(caller, verifier, calldata.into(), 0.into()).unwrap();

        dbg!(result.gas);

        !result.reverted
    };
    assert!(success);
}

pub fn load_verify_circuit_degree() -> u32 {
    let path = "./configs/verify_circuit.config";
    let params_str =
        std::fs::read_to_string(path).expect(format!("{} file should exist", path).as_str());
    let params: plonk_verifier::system::halo2::Halo2VerifierCircuitConfigParams =
        serde_json::from_str(params_str.as_str()).unwrap();
    params.degree
}

impl TargetCircuit for StandardPlonk {
    const N_PROOFS: usize = 1;
    const NAME: &'static str = "standard_plonk";

    type Circuit = Self;
}

fn main() {
    let k = load_verify_circuit_degree();
    let params = gen_srs(k);

    let params_app = {
        let mut params = params.clone();
        params.downsize(8);
        params
    };
    let app_circuit = StandardPlonk::rand(OsRng);
    let snark = create_snark_shplonk::<StandardPlonk>(
        &params_app,
        vec![app_circuit.clone()],
        vec![vec![vec![app_circuit.0]]],
        None,
    );
    let snarks = vec![snark];

    let agg_circuit = AggregationCircuit::new(&params, snarks, true);
    let pk = gen_pk(&params, &agg_circuit, "standard_plonk_agg_circuit");

    let deploy_time = start_timer!(|| "generate aggregation evm verifier code");
    let deployment_code = gen_aggregation_evm_verifier(
        &params,
        pk.get_vk(),
        agg_circuit.num_instance(),
        AggregationCircuit::accumulator_indices(),
    );
    end_timer!(deploy_time);
    fs::write("./data/verifier_bytecode.dat", hex::encode(&deployment_code)).unwrap();

    // use different input snarks to test instances etc
    let app_circuit = StandardPlonk::rand(OsRng);
    let snark = create_snark_shplonk::<StandardPlonk>(
        &params_app,
        vec![app_circuit.clone()],
        vec![vec![vec![app_circuit.0]]],
        None,
    );
    let snarks = vec![snark];
    let agg_circuit = AggregationCircuit::new(&params, snarks, true);
    let proof_time = start_timer!(|| "create agg_circuit proof");
    let proof = gen_proof::<_, _, EvmTranscript<G1Affine, _, _, _>, EvmTranscript<G1Affine, _, _, _>>(
        &params,
        &pk,
        agg_circuit.clone(),
        agg_circuit.instances(),
    );
    end_timer!(proof_time);

    let verify_time = start_timer!(|| "on-chain verification");
    evm_verify(deployment_code, agg_circuit.instances(), proof);
    end_timer!(verify_time);
}
