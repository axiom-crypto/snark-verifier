use super::{read_instances, write_instances, CircuitExt, Snark, SnarkWitness};
#[cfg(feature = "display")]
use ark_std::{end_timer, start_timer};
use halo2_base::{halo2_proofs, poseidon::Spec};
use halo2_proofs::{
    circuit::Layouter,
    dev::MockProver,
    halo2curves::{
        bn256::{Bn256, Fr, G1Affine},
        group::ff::Field,
    },
    plonk::{
        create_proof, keygen_vk, verify_proof, Circuit, ConstraintSystem, Error, ProvingKey,
        VerifyingKey,
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
use rand::Rng;
use snark_verifier::{
    cost::CostEstimation,
    loader::native::NativeLoader,
    pcs::{self, MultiOpenScheme},
    system::halo2::{compile, Config},
    util::transcript::TranscriptWrite,
    verifier::PlonkProof,
};
use std::{
    fs::{self, File},
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
    snark_verifier::system::halo2::transcript::halo2::PoseidonTranscript<
        G1Affine,
        L,
        S,
        T,
        RATE,
        R_F,
        R_P,
    >;

lazy_static! {
    pub static ref POSEIDON_SPEC: Spec<Fr, T, RATE> = Spec::new(R_F, R_P);
}

/// Generates a native proof using either SHPLONK or GWC proving method. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path = Some(instance_path, proof_path)` is specified.
pub fn gen_proof<'params, C, P, V>(
    // TODO: pass Option<&'params ParamsKZG<Bn256>> but hard to get lifetimes to work with `Cow`
    params: &'params ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    rng: &mut (impl Rng + Send),
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

    if let Some((instance_path, proof_path)) = path {
        let cached_instances = read_instances(instance_path);
        if matches!(cached_instances, Ok(tmp) if tmp == instances) && proof_path.exists() {
            #[cfg(feature = "display")]
            let read_time = start_timer!(|| format!("Reading proof from {proof_path:?}"));

            let proof = fs::read(proof_path).unwrap();

            #[cfg(feature = "display")]
            end_timer!(read_time);
            return proof;
        }
    }

    let instances = instances.iter().map(Vec::as_slice).collect_vec();

    #[cfg(feature = "display")]
    let proof_time = start_timer!(|| "Create proof");

    transcript.clear();
    create_proof::<_, P, _, _, _, _>(params, pk, &[circuit], &[&instances], rng, transcript)
        .unwrap();
    let proof = transcript.stream_mut().to_vec();

    #[cfg(feature = "display")]
    end_timer!(proof_time);

    if let Some((instance_path, proof_path)) = path {
        write_instances(&instances, instance_path);
        fs::write(proof_path, &proof).unwrap();
    }

    debug_assert!({
        let mut transcript_read = PoseidonTranscript::<NativeLoader, &[u8]>::new(proof.as_slice());
        VerificationStrategy::<_, V>::finalize(
            verify_proof::<_, V, _, _, _>(
                params.verifier_params(),
                pk.get_vk(),
                AccumulatorStrategy::new(params.verifier_params()),
                &[instances.as_slice()],
                &mut transcript_read,
            )
            .unwrap(),
        )
    });

    proof
}

/// Generates a native proof using original Plonk (GWC '19) multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path = Some(instance_path, proof_path)` is specified.
pub fn gen_proof_gwc<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    rng: &mut (impl Rng + Send),
    path: Option<(&Path, &Path)>,
) -> Vec<u8> {
    gen_proof::<C, ProverGWC<_>, VerifierGWC<_>>(
        params, pk, circuit, instances, transcript, rng, path,
    )
}

/// Generates a native proof using SHPLONK multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path` is specified.
pub fn gen_proof_shplonk<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    rng: &mut (impl Rng + Send),
    path: Option<(&Path, &Path)>,
) -> Vec<u8> {
    gen_proof::<C, ProverSHPLONK<_>, VerifierSHPLONK<_>>(
        params, pk, circuit, instances, transcript, rng, path,
    )
}

/// Generates a SNARK using either SHPLONK or GWC multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark<'params, ConcreteCircuit, P, V>(
    params: &'params ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    rng: &mut (impl Rng + Send),
    path: Option<impl AsRef<Path>>,
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
    if let Some(path) = &path {
        if let Ok(snark) = read_snark(path) {
            return snark;
        }
    }
    let protocol = compile(
        params,
        pk.get_vk(),
        Config::kzg()
            .with_num_instance(ConcreteCircuit::num_instance(&circuit.extra_params()))
            .with_accumulator_indices(ConcreteCircuit::accumulator_indices()),
    );

    let instances = circuit.instances();
    let proof = gen_proof::<ConcreteCircuit, P, V>(
        params,
        pk,
        circuit,
        instances.clone(),
        transcript,
        rng,
        None,
    );

    let snark = Snark::new(protocol, instances, proof);
    if let Some(path) = &path {
        let f = File::create(path).unwrap();
        #[cfg(feature = "display")]
        let write_time = start_timer!(|| "Write SNARK");
        bincode::serialize_into(f, &snark).unwrap();
        #[cfg(feature = "display")]
        end_timer!(write_time);
    }
    snark
}

/// Generates a SNARK using GWC multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark_gwc<ConcreteCircuit: CircuitExt<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    rng: &mut (impl Rng + Send),
    path: Option<impl AsRef<Path>>,
) -> Snark {
    gen_snark::<ConcreteCircuit, ProverGWC<_>, VerifierGWC<_>>(
        params, pk, circuit, transcript, rng, path,
    )
}

/// Generates a SNARK using SHPLONK multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark_shplonk<ConcreteCircuit: CircuitExt<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    transcript: &mut PoseidonTranscript<NativeLoader, Vec<u8>>,
    rng: &mut (impl Rng + Send),
    path: Option<impl AsRef<Path>>,
) -> Snark {
    gen_snark::<ConcreteCircuit, ProverSHPLONK<_>, VerifierSHPLONK<_>>(
        params, pk, circuit, transcript, rng, path,
    )
}

/// Tries to deserialize a SNARK from the specified `path` using `bincode`.
///
/// WARNING: The user must keep track of whether the SNARK was generated using the GWC or SHPLONK multi-open scheme.
pub fn read_snark(path: impl AsRef<Path>) -> Result<Snark, bincode::Error> {
    let f = File::open(path).map_err(Box::<bincode::ErrorKind>::from)?;
    bincode::deserialize_from(f)
}

pub fn gen_dummy_snark<ConcreteCircuit, MOS>(
    params: &ParamsKZG<Bn256>,
    vk: Option<&VerifyingKey<G1Affine>>,
    extra_params: &ConcreteCircuit::ExtraCircuitParams,
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
            .with_num_instance(ConcreteCircuit::num_instance(extra_params))
            .with_accumulator_indices(ConcreteCircuit::accumulator_indices()),
    );
    let instances = ConcreteCircuit::num_instance(extra_params)
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
