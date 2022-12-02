#![allow(clippy::type_complexity)]
use crate::cost::CostEstimation;
use crate::halo2_proofs;
use crate::pcs::MultiOpenScheme;
use crate::{
    loader::native::NativeLoader,
    pcs,
    poseidon::Spec,
    system::halo2::{self, compile, Config},
    util::{hash, transcript::TranscriptWrite},
    verifier::PlonkProof,
    Protocol,
};
#[cfg(feature = "display")]
use ark_std::{end_timer, start_timer};
use halo2_proofs::{
    circuit::{Layouter, Value},
    dev::MockProver,
    halo2curves::{
        bn256::{Bn256, Fr, G1Affine},
        group::ff::Field,
    },
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ConstraintSystem, Error,
        ProvingKey, Selector, VerifyingKey,
    },
    poly::{
        commitment::{Params, ParamsProver, Prover, Verifier},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            msm::DualMSM,
            multiopen::{ProverGWC, ProverSHPLONK, VerifierGWC, VerifierSHPLONK},
            strategy::{AccumulatorStrategy, GuardKZG},
        },
        VerificationStrategy,
    },
};
use itertools::Itertools;
use lazy_static::lazy_static;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::{
    fs::{self, File},
    io::{BufReader, BufWriter},
    iter,
    marker::PhantomData,
    path::Path,
};

pub mod aggregation;

// Poseidon parameters
const T: usize = 5;
const RATE: usize = 4;
const R_F: usize = 8;
const R_P: usize = 60;

pub type PoseidonTranscript<L, S> =
    halo2::transcript::halo2::PoseidonTranscript<G1Affine, L, S, T, RATE, R_F, R_P>;
lazy_static! {
    pub static ref POSEIDON_SPEC: Spec<Fr, T, RATE> = Spec::new(R_F, R_P);
}

pub struct Snark {
    pub protocol: Protocol<G1Affine>,
    pub instances: Vec<Vec<Fr>>,
    pub proof: Vec<u8>,
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
    pub protocol: Protocol<G1Affine>,
    pub instances: Vec<Vec<Value<Fr>>>,
    pub proof: Value<Vec<u8>>,
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

    pub fn proof(&self) -> Value<&[u8]> {
        self.proof.as_ref().map(Vec::as_slice)
    }
}

pub trait CircuitExt<F: Field>: Circuit<F> {
    fn num_instance() -> Vec<usize>;

    fn instances(&self) -> Vec<Vec<F>>;

    fn accumulator_indices() -> Option<Vec<(usize, usize)>> {
        None
    }

    /// Output the simple selector columns (before selector compression) of the circuit
    fn selectors(_: &Self::Config) -> Vec<Selector> {
        vec![]
    }
}

pub fn gen_pk<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    circuit: &C,
    path: Option<&Path>,
) -> ProvingKey<G1Affine> {
    if let Some(path) = path {
        match File::open(path) {
            Ok(f) => {
                #[cfg(feature = "display")]
                let read_time = start_timer!(|| format!("Reading pkey from {path:?}"));

                // TODO: bench if BufReader is indeed faster than Read
                let mut bufreader = BufReader::new(f);
                let pk = ProvingKey::read::<_, C>(&mut bufreader, params)
                    .expect("Reading pkey should not fail");

                #[cfg(feature = "display")]
                end_timer!(read_time);

                pk
            }
            Err(_) => {
                #[cfg(feature = "display")]
                let pk_time = start_timer!(|| "Generating vkey & pkey");

                let vk = keygen_vk(params, circuit).unwrap();
                let pk = keygen_pk(params, vk, circuit).unwrap();

                #[cfg(feature = "display")]
                end_timer!(pk_time);

                #[cfg(feature = "display")]
                let write_time = start_timer!(|| format!("Writing pkey to {path:?}"));

                path.parent().and_then(|dir| fs::create_dir_all(dir).ok()).unwrap();
                let mut f = BufWriter::new(File::create(path).unwrap());
                pk.write(&mut f).unwrap();

                #[cfg(feature = "display")]
                end_timer!(write_time);

                pk
            }
        }
    } else {
        #[cfg(feature = "display")]
        let pk_time = start_timer!(|| "Generating vkey & pkey");

        let vk = keygen_vk(params, circuit).unwrap();
        let pk = keygen_pk(params, vk, circuit).unwrap();

        #[cfg(feature = "display")]
        end_timer!(pk_time);

        pk
    }
}

/// Generates a native proof using either SHPLONK or GWC proving method. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path` is specified.
pub fn gen_proof<'params, C, P, V>(
    params: &'params ParamsKZG<Bn256>,
    pk: &'params ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    path: Option<(&Path, &Path)>,
) -> Vec<u8>
where
    C: Circuit<Fr>,
    P: Prover<'params, KZGCommitmentScheme<Bn256>>,
    V: Verifier<
        'params,
        KZGCommitmentScheme<Bn256>,
        Guard = GuardKZG<'params, Bn256>,
        MSMAccumulator = DualMSM<'params, Bn256>,
    >,
{
    #[cfg(debug_assertions)]
    {
        MockProver::run(params.k(), &circuit, instances.clone()).unwrap().assert_satisfied();
    }

    let mut proof: Option<Vec<u8>> = None;

    if let Some((instance_path, proof_path)) = path {
        let cached_instances = read_instances(instance_path);
        if matches!(cached_instances, Ok(tmp) if tmp == instances) && proof_path.exists() {
            #[cfg(feature = "display")]
            let read_time = start_timer!(|| format!("Reading proof from {proof_path:?}"));

            proof = Some(fs::read(proof_path).unwrap());

            #[cfg(feature = "display")]
            end_timer!(read_time);
        }
    }

    let instances = instances.iter().map(Vec::as_slice).collect_vec();

    let proof = proof.unwrap_or_else(|| {
        #[cfg(feature = "display")]
        let proof_time = start_timer!(|| "Create proof");

        transcript.clear();
        create_proof::<_, P, _, _, _, _>(
            params,
            pk,
            &[circuit],
            &[&instances],
            &mut ChaCha20Rng::from_entropy(),
            transcript,
        )
        .unwrap();
        let proof = transcript.stream_mut().split_off(0);

        #[cfg(feature = "display")]
        end_timer!(proof_time);

        if let Some((instance_path, proof_path)) = path {
            write_instances(&instances, instance_path);
            fs::write(proof_path, &proof).unwrap();
        }
        proof
    });

    debug_assert!({
        let mut transcript = PoseidonTranscript::<NativeLoader, &[u8]>::new(proof.as_slice());
        VerificationStrategy::<_, V>::finalize(
            verify_proof::<_, V, _, _, _>(
                params.verifier_params(),
                pk.get_vk(),
                AccumulatorStrategy::new(params.verifier_params()),
                &[instances.as_slice()],
                &mut transcript,
            )
            .unwrap(),
        )
    });

    proof
}

pub fn gen_proof_gwc<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    path: Option<(&Path, &Path)>,
) -> Vec<u8> {
    gen_proof::<C, ProverGWC<_>, VerifierGWC<_>>(params, pk, circuit, instances, transcript, path)
}

pub fn gen_proof_shplonk<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    path: Option<(&Path, &Path)>,
) -> Vec<u8> {
    gen_proof::<C, ProverSHPLONK<_>, VerifierSHPLONK<_>>(
        params, pk, circuit, instances, transcript, path,
    )
}

pub fn gen_snark<'params, ConcreteCircuit, P, V>(
    params: &'params ParamsKZG<Bn256>,
    pk: &'params ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    path: Option<(&Path, &Path)>,
) -> Snark
where
    ConcreteCircuit: CircuitExt<Fr>,
    P: Prover<'params, KZGCommitmentScheme<Bn256>>,
    V: Verifier<
        'params,
        KZGCommitmentScheme<Bn256>,
        Guard = GuardKZG<'params, Bn256>,
        MSMAccumulator = DualMSM<'params, Bn256>,
    >,
{
    let protocol = compile(
        params,
        pk.get_vk(),
        Config::kzg()
            .with_num_instance(ConcreteCircuit::num_instance())
            .with_accumulator_indices(ConcreteCircuit::accumulator_indices()),
    );

    let instances = circuit.instances();
    let proof = gen_proof::<ConcreteCircuit, P, V>(
        params,
        pk,
        circuit,
        instances.clone(),
        transcript,
        path,
    );

    Snark::new(protocol, instances, proof)
}

pub fn gen_snark_gwc<ConcreteCircuit: CircuitExt<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    path: Option<(&Path, &Path)>,
) -> Snark {
    gen_snark::<ConcreteCircuit, ProverGWC<_>, VerifierGWC<_>>(
        params, pk, circuit, transcript, path,
    )
}

pub fn gen_snark_shplonk<ConcreteCircuit: CircuitExt<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    path: Option<(&Path, &Path)>,
) -> Snark {
    gen_snark::<ConcreteCircuit, ProverSHPLONK<_>, VerifierSHPLONK<_>>(
        params, pk, circuit, transcript, path,
    )
}

pub fn read_instances(path: impl AsRef<Path>) -> Result<Vec<Vec<Fr>>, bincode::Error> {
    let f = File::open(path)?;
    let reader = BufReader::new(f);
    let instances: Vec<Vec<[u8; 32]>> = bincode::deserialize_from(reader)?;
    instances
        .into_iter()
        .map(|instance_column| {
            instance_column
                .iter()
                .map(|bytes| {
                    Option::from(Fr::from_bytes(bytes)).ok_or(Box::new(bincode::ErrorKind::Custom(
                        "Invalid finite field point".to_owned(),
                    )))
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect()
}

pub fn write_instances(instances: &[&[Fr]], path: impl AsRef<Path>) {
    let instances: Vec<Vec<[u8; 32]>> = instances
        .iter()
        .map(|instance_column| instance_column.iter().map(|x| x.to_bytes()).collect_vec())
        .collect_vec();
    let f = BufWriter::new(File::create(path).unwrap());
    bincode::serialize_into(f, &instances).unwrap();
}

pub fn gen_dummy_snark<ConcreteCircuit, MOS>(
    params: &ParamsKZG<Bn256>,
    vk: Option<&VerifyingKey<G1Affine>>,
) -> Snark
where
    ConcreteCircuit: CircuitExt<Fr>,
    MOS: MultiOpenScheme<G1Affine, NativeLoader>
        + CostEstimation<G1Affine, Input = Vec<pcs::Query<Fr>>>,
{
    struct CsProxy<F, C>(PhantomData<(F, C)>);

    impl<F: Field, C: CircuitExt<F>> Circuit<F> for CsProxy<F, C> {
        type Config = C::Config;
        type FloorPlanner = C::FloorPlanner;

        fn without_witnesses(&self) -> Self {
            CsProxy(PhantomData)
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            C::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // when `C` has simple selectors, we tell `CsProxy` not to over-optimize the selectors (e.g., compressing them  all into one) by turning all selectors on in the first row
            // currently this only works if all simple selector columns are used in the actual circuit and there are overlaps amongst all enabled selectors (i.e., the actual circuit will not optimize constraint system further)
            layouter.assign_region(
                || "",
                |mut region| {
                    for q in C::selectors(&config).iter() {
                        q.enable(&mut region, 0)?;
                    }
                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    let dummy_vk = vk
        .is_none()
        .then(|| keygen_vk(params, &CsProxy::<Fr, ConcreteCircuit>(PhantomData)).unwrap());
    let protocol = compile(
        params,
        vk.or(dummy_vk.as_ref()).unwrap(),
        Config::kzg()
            .with_num_instance(ConcreteCircuit::num_instance())
            .with_accumulator_indices(ConcreteCircuit::accumulator_indices()),
    );
    let instances = ConcreteCircuit::num_instance()
        .into_iter()
        .map(|n| iter::repeat(Fr::default()).take(n).collect())
        .collect();
    let proof = {
        let mut transcript = PoseidonTranscript::<NativeLoader, _>::new(Vec::new());
        for _ in 0..protocol
            .num_witness
            .iter()
            .chain(Some(&protocol.quotient.num_chunk()))
            .sum::<usize>()
        {
            transcript.write_ec_point(G1Affine::default()).unwrap();
        }
        for _ in 0..protocol.evaluations.len() {
            transcript.write_scalar(Fr::default()).unwrap();
        }
        let queries = PlonkProof::<G1Affine, NativeLoader, MOS>::empty_queries(&protocol);
        for _ in 0..MOS::estimate_cost(&queries).num_commitment {
            transcript.write_ec_point(G1Affine::default()).unwrap();
        }
        transcript.finalize()
    };

    Snark::new(protocol, instances, proof)
}
