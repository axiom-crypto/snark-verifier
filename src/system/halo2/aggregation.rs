use super::{BITS, LIMBS};
use crate::{
    loader::{self, native::NativeLoader, Loader},
    pcs::{
        kzg::{
            Bdfg21, Kzg, KzgAccumulator, KzgAs, KzgAsProvingKey, KzgAsVerifyingKey,
            KzgSuccinctVerifyingKey, LimbsEncoding,
        },
        AccumulationScheme, AccumulationSchemeProver,
    },
    system::{
        self,
        halo2::{
            compile, read_or_create_srs, transcript::halo2::ChallengeScalar, Config,
            Halo2VerifierCircuitConfig, Halo2VerifierCircuitConfigParams,
        },
    },
    util::arithmetic::fe_to_limbs,
    verifier::{self, PlonkVerifier},
    Protocol,
};
use ark_std::{end_timer, start_timer};
use halo2_base::AssignedValue;
pub use halo2_base::{
    utils::{biguint_to_fe, fe_to_biguint},
    Context, ContextParams,
};
use halo2_curves::bn256::{Bn256, Fr, G1Affine};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        self, create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey,
    },
    poly::{
        commitment::{Params, ParamsProver},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverSHPLONK, VerifierSHPLONK},
            strategy::AccumulatorStrategy,
        },
        VerificationStrategy,
    },
    transcript::{TranscriptReadBuffer, TranscriptWriterBuffer},
};
use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::Num;
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};
use std::{
    fs::File,
    io::{BufReader, BufWriter, Cursor, Read, Write},
    path::Path,
    rc::Rc,
};

pub const T: usize = 3;
pub const RATE: usize = 2;
pub const R_F: usize = 8;
pub const R_P: usize = 57;

pub type Halo2Loader<'a, 'b> = loader::halo2::Halo2Loader<'a, 'b, G1Affine>;
pub type PoseidonTranscript<L, S, B> =
    system::halo2::transcript::halo2::PoseidonTranscript<G1Affine, L, S, B, T, RATE, R_F, R_P>;

pub type Pcs = Kzg<Bn256, Bdfg21>;
pub type Svk = KzgSuccinctVerifyingKey<G1Affine>;
pub type As = KzgAs<Pcs>;
pub type AsPk = KzgAsProvingKey<G1Affine>;
pub type AsVk = KzgAsVerifyingKey;
pub type Plonk = verifier::Plonk<Pcs, LimbsEncoding<LIMBS, BITS>>;

pub struct Snark {
    protocol: Protocol<G1Affine>,
    instances: Vec<Vec<Fr>>,
    proof: Vec<u8>,
}

impl Snark {
    pub fn new(protocol: Protocol<G1Affine>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) -> Self {
        Self { protocol, instances, proof }
    }
    pub fn protocol(&self) -> &Protocol<G1Affine> {
        &self.protocol
    }
    pub fn instances(&self) -> &[Vec<Fr>] {
        &self.instances
    }
    pub fn proof(&self) -> &[u8] {
        &self.proof
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
    pub fn without_witnesses(&self) -> Self {
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

    pub fn protocol(&self) -> &Protocol<G1Affine> {
        &self.protocol
    }

    pub fn instances(&self) -> &[Vec<Value<Fr>>] {
        &self.instances
    }

    pub fn proof(&self) -> Value<&[u8]> {
        self.proof.as_ref().map(Vec::as_slice)
    }
}

pub fn aggregate<'a, 'b>(
    svk: &Svk,
    loader: &Rc<Halo2Loader<'a, 'b>>,
    snarks: &[SnarkWitness],
    as_vk: &AsVk,
    as_proof: Value<&'_ [u8]>,
    expose_instances: bool,
) -> Vec<AssignedValue<Fr>> {
    let assign_instances = |instances: &[Vec<Value<Fr>>]| {
        instances
            .iter()
            .map(|instances| {
                instances.iter().map(|instance| loader.assign_scalar(*instance)).collect_vec()
            })
            .collect_vec()
    };

    let mut instances_to_expose = vec![];
    let mut accumulators = snarks
        .iter()
        .flat_map(|snark| {
            let instances = assign_instances(&snark.instances);
            if expose_instances {
                instances_to_expose.extend(
                    instances
                        .iter()
                        .flat_map(|instance| instance.iter().map(|scalar| scalar.assigned())),
                );
            }
            let mut transcript =
                PoseidonTranscript::<Rc<Halo2Loader>, _, _>::new(loader, snark.proof());
            let proof =
                Plonk::read_proof(svk, &snark.protocol, &instances, &mut transcript).unwrap();
            Plonk::succinct_verify(svk, &snark.protocol, &instances, &proof).unwrap()
        })
        .collect_vec();

    let KzgAccumulator { lhs, rhs } = if accumulators.len() > 1 {
        let mut transcript = PoseidonTranscript::<Rc<Halo2Loader>, _, _>::new(loader, as_proof);
        let proof = As::read_proof(as_vk, &accumulators, &mut transcript).unwrap();
        As::verify(as_vk, &accumulators, &proof).unwrap()
    } else {
        accumulators.pop().unwrap()
    };

    let lhs = lhs.assigned();
    let rhs = rhs.assigned();

    lhs.x
        .truncation
        .limbs
        .iter()
        .chain(lhs.y.truncation.limbs.iter())
        .chain(rhs.x.truncation.limbs.iter())
        .chain(rhs.y.truncation.limbs.iter())
        .chain(instances_to_expose.iter())
        .cloned()
        .collect_vec()
}

pub fn recursive_aggregate<'a, 'b>(
    svk: &Svk,
    loader: &Rc<Halo2Loader<'a, 'b>>,
    snarks: &[SnarkWitness],
    recursive_snark: &SnarkWitness,
    as_vk: &AsVk,
    as_proof: Value<&'_ [u8]>,
    use_dummy: AssignedValue<Fr>,
) -> (Vec<AssignedValue<Fr>>, Vec<Vec<AssignedValue<Fr>>>) {
    let assign_instances = |instances: &[Vec<Value<Fr>>]| {
        instances
            .iter()
            .map(|instances| {
                instances.iter().map(|instance| loader.assign_scalar(*instance)).collect_vec()
            })
            .collect_vec()
    };

    let mut assigned_instances = vec![];
    let mut accumulators = snarks
        .iter()
        .flat_map(|snark| {
            let instances = assign_instances(&snark.instances);
            assigned_instances.push(
                instances
                    .iter()
                    .flat_map(|instance| instance.iter().map(|scalar| scalar.assigned()))
                    .collect_vec(),
            );
            let mut transcript =
                PoseidonTranscript::<Rc<Halo2Loader>, _, _>::new(loader, snark.proof());
            let proof =
                Plonk::read_proof(svk, &snark.protocol, &instances, &mut transcript).unwrap();
            Plonk::succinct_verify(svk, &snark.protocol, &instances, &proof).unwrap()
        })
        .collect_vec();

    let use_dummy = loader.scalar_from_assigned(use_dummy);

    let prev_instances = assign_instances(&recursive_snark.instances);
    let mut accs = {
        let mut transcript =
            PoseidonTranscript::<Rc<Halo2Loader>, _, _>::new(loader, recursive_snark.proof());
        let proof =
            Plonk::read_proof(svk, &recursive_snark.protocol, &prev_instances, &mut transcript)
                .unwrap();
        let mut accs = Plonk::succinct_verify_or_dummy(
            svk,
            &recursive_snark.protocol,
            &prev_instances,
            &proof,
            &use_dummy,
        )
        .unwrap();
        for acc in accs.iter_mut() {
            (*acc).lhs =
                loader.ec_point_select(&accumulators[0].lhs, &acc.lhs, &use_dummy).unwrap();
            (*acc).rhs =
                loader.ec_point_select(&accumulators[0].rhs, &acc.rhs, &use_dummy).unwrap();
        }
        accs
    };
    accumulators.append(&mut accs);

    let KzgAccumulator { lhs, rhs } = {
        let mut transcript = PoseidonTranscript::<Rc<Halo2Loader>, _, _>::new(loader, as_proof);
        let proof = As::read_proof(as_vk, &accumulators, &mut transcript).unwrap();
        As::verify(as_vk, &accumulators, &proof).unwrap()
    };

    let lhs = lhs.assigned();
    let rhs = rhs.assigned();

    let mut new_instances = prev_instances
        .iter()
        .flat_map(|instance| instance.iter().map(|scalar| scalar.assigned()))
        .collect_vec();
    for (i, acc_limb) in lhs
        .x
        .truncation
        .limbs
        .iter()
        .chain(lhs.y.truncation.limbs.iter())
        .chain(rhs.x.truncation.limbs.iter())
        .chain(rhs.y.truncation.limbs.iter())
        .enumerate()
    {
        new_instances[i] = acc_limb.clone();
    }
    (new_instances, assigned_instances)
}

#[derive(Clone)]
pub struct AggregationCircuit {
    svk: Svk,
    snarks: Vec<SnarkWitness>,
    pub instances: Vec<Fr>,
    as_vk: AsVk,
    as_proof: Value<Vec<u8>>,
    expose_target_instances: bool,
}

impl AggregationCircuit {
    pub fn new(
        params: &ParamsKZG<Bn256>,
        snarks: impl IntoIterator<Item = Snark>,
        expose_target_instances: bool,
    ) -> Self {
        let svk = params.get_g()[0].into();
        let snarks = snarks.into_iter().collect_vec();

        let mut accumulators = snarks
            .iter()
            .flat_map(|snark| {
                let mut transcript =
                    PoseidonTranscript::<NativeLoader, _, _>::new(snark.proof.as_slice());
                let proof =
                    Plonk::read_proof(&svk, &snark.protocol, &snark.instances, &mut transcript)
                        .unwrap();
                Plonk::succinct_verify(&svk, &snark.protocol, &snark.instances, &proof).unwrap()
            })
            .collect_vec();

        let as_pk = AsPk::new(Some((params.get_g()[0], params.get_g()[1])));
        let (accumulator, as_proof) = if accumulators.len() > 1 {
            let mut transcript = PoseidonTranscript::<NativeLoader, _, _>::new(Vec::new());
            let accumulator = As::create_proof(
                &as_pk,
                &accumulators,
                &mut transcript,
                ChaCha20Rng::from_seed(Default::default()),
            )
            .unwrap();
            (accumulator, Value::known(transcript.finalize()))
        } else {
            (accumulators.pop().unwrap(), Value::unknown())
        };

        let KzgAccumulator { lhs, rhs } = accumulator;
        let mut instances =
            [lhs.x, lhs.y, rhs.x, rhs.y].map(fe_to_limbs::<_, _, LIMBS, BITS>).concat();
        if expose_target_instances {
            instances.extend(snarks.iter().flat_map(|snark| snark.instances.iter().flatten()));
        }

        Self {
            svk,
            snarks: snarks.into_iter().map_into().collect(),
            instances,
            as_vk: as_pk.vk(),
            as_proof,
            expose_target_instances,
        }
    }

    pub fn accumulator_indices() -> Vec<(usize, usize)> {
        (0..4 * LIMBS).map(|idx| (0, idx)).collect()
    }

    pub fn num_instance(&self) -> Vec<usize> {
        dbg!(self.instances.len());
        vec![self.instances.len()]
    }

    pub fn instances(&self) -> Vec<Vec<Fr>> {
        vec![self.instances.clone()]
    }

    pub fn as_proof(&self) -> Value<&[u8]> {
        self.as_proof.as_ref().map(Vec::as_slice)
    }

    pub fn synthesize_proof(
        &self,
        config: Halo2VerifierCircuitConfig,
        layouter: &mut impl Layouter<Fr>,
        instance_equalities: Vec<(usize, usize)>,
    ) -> Result<Vec<AssignedValue<Fr>>, plonk::Error> {
        config.base_field_config.load_lookup_table(layouter)?;

        // Need to trick layouter to skip first pass in get shape mode
        let using_simple_floor_planner = true;
        let mut first_pass = true;
        let mut assigned_instances = None;
        layouter.assign_region(
            || "",
            |region| {
                if using_simple_floor_planner && first_pass {
                    first_pass = false;
                    return Ok(());
                }
                let ctx = config.base_field_config.new_context(region);

                let loader = Halo2Loader::new(&config.base_field_config, ctx);
                let instances = aggregate(
                    &self.svk,
                    &loader,
                    &self.snarks,
                    &self.as_vk,
                    self.as_proof(),
                    self.expose_target_instances,
                );

                for &(i, j) in &instance_equalities {
                    loader
                        .ctx_mut()
                        .region
                        .constrain_equal(instances[i].cell(), instances[j].cell())?;
                }
                // REQUIRED STEP
                loader.finalize();
                assigned_instances = Some(instances);
                Ok(())
            },
        )?;
        Ok(assigned_instances.unwrap())
    }
}

impl Circuit<Fr> for AggregationCircuit {
    type Config = Halo2VerifierCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            svk: self.svk,
            snarks: self.snarks.iter().map(SnarkWitness::without_witnesses).collect(),
            instances: Vec::new(),
            as_vk: self.as_vk,
            as_proof: Value::unknown(),
            expose_target_instances: self.expose_target_instances,
        }
    }

    fn configure(meta: &mut plonk::ConstraintSystem<Fr>) -> Self::Config {
        let path = std::env::var("VERIFY_CONFIG").expect("export VERIFY_CONFIG with config path");
        let params: Halo2VerifierCircuitConfigParams = serde_json::from_reader(
            File::open(path.as_str()).expect(format!("{} file should exist", path).as_str()),
        )
        .unwrap();

        Halo2VerifierCircuitConfig::configure(meta, params)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), plonk::Error> {
        let config_instance = config.instance.clone();
        let assigned_instances = self.synthesize_proof(config, &mut layouter, vec![])?;
        Ok({
            // TODO: use less instances by following Scroll's strategy of keeping only last bit of y coordinate
            let mut layouter = layouter.namespace(|| "expose");
            for (i, assigned_instance) in assigned_instances.iter().enumerate() {
                layouter.constrain_instance(
                    assigned_instance.cell().clone(),
                    config_instance,
                    i,
                )?;
            }
        })
    }
}

pub fn gen_srs(k: u32) -> ParamsKZG<Bn256> {
    read_or_create_srs::<G1Affine, _>(k, |k| {
        ParamsKZG::<Bn256>::setup(k, ChaCha20Rng::from_seed(Default::default()))
    })
}

pub fn gen_vk<ConcreteCircuit: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    circuit: &ConcreteCircuit,
    name: &str,
) -> VerifyingKey<G1Affine> {
    let path = format!("./data/{}_{}.vkey", name, params.k());
    #[cfg(feature = "serialize")]
    match File::open(path.as_str()) {
        Ok(f) => {
            let read_time = start_timer!(|| format!("Reading vkey from {}", path));
            let mut bufreader = BufReader::new(f);
            let vk = VerifyingKey::read::<_, ConcreteCircuit>(&mut bufreader, params)
                .expect("Reading vkey should not fail");
            end_timer!(read_time);
            vk
        }
        Err(_) => {
            let vk_time = start_timer!(|| "vkey");
            let vk = keygen_vk(params, circuit).unwrap();
            end_timer!(vk_time);
            let mut f = BufWriter::new(File::create(path.as_str()).unwrap());
            println!("Writing vkey to {}", path);
            vk.write(&mut f).unwrap();
            vk
        }
    }
    #[cfg(not(feature = "serialize"))]
    {
        let vk_time = start_timer!(|| "vkey");
        let vk = keygen_vk(params, circuit).unwrap();
        end_timer!(vk_time);
        vk
    }
}

pub fn gen_pk<ConcreteCircuit: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    circuit: &ConcreteCircuit,
    name: &str,
) -> ProvingKey<G1Affine> {
    let path = format!("./data/{}_{}.pkey", name, params.k());
    #[cfg(feature = "serialize")]
    match File::open(path.as_str()) {
        Ok(f) => {
            let read_time = start_timer!(|| format!("Reading pkey from {}", path));
            let mut bufreader = BufReader::new(f);
            let pk = ProvingKey::read::<_, ConcreteCircuit>(&mut bufreader, params)
                .expect("Reading pkey should not fail");
            end_timer!(read_time);
            pk
        }
        Err(_) => {
            let vk = gen_vk::<ConcreteCircuit>(params, circuit, name);
            let pk_time = start_timer!(|| "pkey");
            let pk = keygen_pk(params, vk, circuit).unwrap();
            end_timer!(pk_time);
            let mut f = BufWriter::new(File::create(path.as_str()).unwrap());
            println!("Writing pkey to {}", path);
            pk.write(&mut f).unwrap();
            pk
        }
    }
    #[cfg(not(feature = "serialize"))]
    {
        let vk = gen_vk::<ConcreteCircuit>(params, circuit, name);
        let pk_time = start_timer!(|| "pkey");
        let pk = keygen_pk(params, vk, circuit).unwrap();
        end_timer!(pk_time);
        pk
    }
}

pub fn read_bytes(path: &str) -> Vec<u8> {
    let mut buf = vec![];
    let mut f = File::open(path).unwrap();
    f.read_to_end(&mut buf).unwrap();
    buf
}

pub fn write_bytes(path: &str, buf: &Vec<u8>) {
    let mut f = File::create(path).unwrap();
    f.write(buf).unwrap();
}

/// reads the instances for T::N_PROOFS circuits from file
pub fn read_instances<T: TargetCircuit>(path: &str) -> Option<Vec<Vec<Vec<Fr>>>> {
    let f = File::open(path);
    if let Err(_) = f {
        return None;
    }
    let f = f.unwrap();
    let reader = BufReader::new(f);
    let instances_str: Vec<Vec<Vec<String>>> = serde_json::from_reader(reader).unwrap();
    let ret = instances_str
        .into_iter()
        .map(|circuit_instances| {
            circuit_instances
                .into_iter()
                .map(|instance_column| {
                    instance_column
                        .iter()
                        .map(|str| {
                            biguint_to_fe::<Fr>(&BigUint::from_str_radix(str.as_str(), 16).unwrap())
                        })
                        .collect_vec()
                })
                .collect_vec()
        })
        .collect_vec();
    Some(ret)
}

pub fn write_instances(instances: &Vec<Vec<Vec<Fr>>>, path: &str) {
    let mut hex_strings = vec![];
    for circuit_instances in instances.iter() {
        hex_strings.push(
            circuit_instances
                .iter()
                .map(|instance_column| {
                    instance_column.iter().map(|x| fe_to_biguint(x).to_str_radix(16)).collect_vec()
                })
                .collect_vec(),
        );
    }
    let f = BufWriter::new(File::create(path).unwrap());
    serde_json::to_writer(f, &hex_strings).unwrap();
}

pub trait TargetCircuit {
    const N_PROOFS: usize;

    type Circuit: Circuit<Fr>;

    fn name() -> String;
}

// this is a toggle that should match the fork of halo2_proofs you are using
// the current default in PSE/main is `false`, before 2022_10_22 it was `true`:
// see https://github.com/privacy-scaling-explorations/halo2/pull/96/files
pub const KZG_QUERY_INSTANCE: bool = false;

pub fn create_snark_shplonk<T: TargetCircuit>(
    params: &ParamsKZG<Bn256>,
    circuits: Vec<T::Circuit>,
    instances: Vec<Vec<Vec<Fr>>>, // instances[i][j][..] is the i-th circuit's j-th instance column
    accumulator_indices: Option<Vec<(usize, usize)>>,
) -> Snark {
    println!("CREATING SNARK FOR: {}", T::name());
    let config = if let Some(accumulator_indices) = accumulator_indices {
        Config::kzg(KZG_QUERY_INSTANCE)
            .set_zk(true)
            .with_num_proof(T::N_PROOFS)
            .with_accumulator_indices(accumulator_indices)
    } else {
        Config::kzg(KZG_QUERY_INSTANCE).set_zk(true).with_num_proof(T::N_PROOFS)
    };

    let pk = gen_pk(params, &circuits[0], T::name().as_str());
    // num_instance[i] is length of the i-th instance columns in circuit 0 (all circuits should have same shape of instances)
    let num_instance = instances[0].iter().map(|instance_column| instance_column.len()).collect();
    let protocol = compile(params, pk.get_vk(), config.with_num_instance(num_instance));

    // usual shenanigans to turn nested Vec into nested slice
    let instances1: Vec<Vec<&[Fr]>> = instances
        .iter()
        .map(|instances| instances.iter().map(Vec::as_slice).collect_vec())
        .collect_vec();
    let instances2: Vec<&[&[Fr]]> = instances1.iter().map(Vec::as_slice).collect_vec();
    // TODO: need to cache the instances as well!

    let proof = {
        let path = format!("./data/proof_{}_{}.dat", T::name(), params.k());
        let instance_path = format!("./data/instances_{}_{}.dat", T::name(), params.k());
        let cached_instances = read_instances::<T>(instance_path.as_str());
        #[cfg(feature = "serialize")]
        if cached_instances.is_some()
            && Path::new(path.as_str()).exists()
            && cached_instances.unwrap() == instances
        {
            let proof_time = start_timer!(|| "read proof");
            let mut file = File::open(path.as_str()).unwrap();
            let mut buf = vec![];
            file.read_to_end(&mut buf).unwrap();
            end_timer!(proof_time);
            buf
        } else {
            let proof_time = start_timer!(|| "create proof");
            let mut transcript = PoseidonTranscript::<NativeLoader, Vec<u8>, _>::init(Vec::new());
            create_proof::<KZGCommitmentScheme<_>, ProverSHPLONK<_>, ChallengeScalar<_>, _, _, _>(
                params,
                &pk,
                &circuits,
                instances2.as_slice(),
                &mut ChaCha20Rng::from_seed(Default::default()),
                &mut transcript,
            )
            .unwrap();
            let proof = transcript.finalize();
            let mut file = File::create(path.as_str()).unwrap();
            file.write_all(&proof).unwrap();
            write_instances(&instances, instance_path.as_str());
            end_timer!(proof_time);
            proof
        }
        #[cfg(not(feature = "serialize"))]
        {
            let proof_time = start_timer!(|| "create proof");
            let mut transcript = PoseidonTranscript::<NativeLoader, Vec<u8>, _>::init(Vec::new());
            create_proof::<KZGCommitmentScheme<_>, ProverSHPLONK<_>, ChallengeScalar<_>, _, _, _>(
                params,
                &pk,
                &circuits,
                instances2.as_slice(),
                &mut ChaCha20Rng::from_seed(Default::default()),
                &mut transcript,
            )
            .unwrap();
            let proof = transcript.finalize();
            end_timer!(proof_time);
            proof
        }
    };

    let verify_time = start_timer!(|| "verify proof");
    {
        let verifier_params = params.verifier_params();
        let strategy = AccumulatorStrategy::new(verifier_params);
        let mut transcript =
            <PoseidonTranscript<NativeLoader, Cursor<Vec<u8>>, _> as TranscriptReadBuffer<
                _,
                _,
                _,
            >>::init(Cursor::new(proof.clone()));
        assert!(VerificationStrategy::<_, VerifierSHPLONK<_>>::finalize(
            verify_proof::<_, VerifierSHPLONK<_>, _, _, _>(
                verifier_params,
                pk.get_vk(),
                strategy,
                instances2.as_slice(),
                &mut transcript,
            )
            .unwrap()
        ))
    }
    end_timer!(verify_time);

    Snark::new(protocol.clone(), instances.into_iter().flatten().collect_vec(), proof)
}
