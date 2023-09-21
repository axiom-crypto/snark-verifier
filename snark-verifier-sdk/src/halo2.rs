use super::{read_instances, write_instances, CircuitExt, PlonkSuccinctVerifier, Snark};
#[cfg(feature = "display")]
use ark_std::{end_timer, start_timer};
use halo2_base::halo2_proofs;
pub use halo2_base::poseidon::hasher::spec::OptimizedPoseidonSpec;
use halo2_proofs::{
    circuit::Layouter,
    halo2curves::{
        bn256::{Bn256, Fr, G1Affine},
        group::ff::Field,
    },
    plonk::{
        create_proof, keygen_vk, verify_proof, Circuit, ConstraintSystem, Error, ProvingKey,
        VerifyingKey,
    },
    poly::{
        commitment::{ParamsProver, Prover, Verifier},
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
use rand::{rngs::StdRng, SeedableRng};
use snark_verifier::{
    cost::CostEstimation,
    loader::native::NativeLoader,
    pcs::{
        kzg::{KzgAccumulator, KzgAsVerifyingKey, KzgSuccinctVerifyingKey},
        AccumulationScheme, PolynomialCommitmentScheme, Query,
    },
    system::halo2::{compile, Config},
    util::arithmetic::Rotation,
    util::transcript::TranscriptWrite,
    verifier::plonk::PlonkProof,
};
use std::{
    fs::{self, File},
    marker::PhantomData,
    path::Path,
};

pub mod aggregation;

// Poseidon parameters
// We use the same ones Scroll uses for security: https://github.com/scroll-tech/poseidon-circuit/blob/714f50c7572a4ff6f2b1fa51a9604a99cd7b6c71/src/poseidon/primitives/bn256/fp.rs
// Verify generated constants: https://github.com/scroll-tech/poseidon-circuit/blob/714f50c7572a4ff6f2b1fa51a9604a99cd7b6c71/src/poseidon/primitives/bn256/mod.rs#L65
const T: usize = 3;
const RATE: usize = 2;
const R_F: usize = 8; // https://github.com/scroll-tech/poseidon-circuit/blob/714f50c7572a4ff6f2b1fa51a9604a99cd7b6c71/src/poseidon/primitives/p128pow5t3.rs#L26
const R_P: usize = 57; // https://github.com/scroll-tech/poseidon-circuit/blob/714f50c7572a4ff6f2b1fa51a9604a99cd7b6c71/src/poseidon/primitives/bn256/mod.rs#L8
const SECURE_MDS: usize = 0;

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
    pub static ref POSEIDON_SPEC: OptimizedPoseidonSpec<Fr, T, RATE> =
        OptimizedPoseidonSpec::new::<R_F, R_P, SECURE_MDS>();
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

    let mut transcript =
        PoseidonTranscript::<NativeLoader, Vec<u8>>::from_spec(vec![], POSEIDON_SPEC.clone());
    let rng = StdRng::from_entropy();
    create_proof::<_, P, _, _, _, _>(params, pk, &[circuit], &[&instances], rng, &mut transcript)
        .unwrap();
    let proof = transcript.finalize();

    #[cfg(feature = "display")]
    end_timer!(proof_time);

    // validate proof before caching
    assert!(
        {
            let mut transcript_read = PoseidonTranscript::<NativeLoader, &[u8]>::from_spec(
                &proof[..],
                POSEIDON_SPEC.clone(),
            );
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
        },
        "SNARK proof failed to verify"
    );

    if let Some((instance_path, proof_path)) = path {
        write_instances(&instances, instance_path);
        fs::write(proof_path, &proof).unwrap();
    }

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
    path: Option<(&Path, &Path)>,
) -> Vec<u8> {
    gen_proof::<C, ProverGWC<_>, VerifierGWC<_>>(params, pk, circuit, instances, path)
}

/// Generates a native proof using SHPLONK multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path` is specified.
pub fn gen_proof_shplonk<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    path: Option<(&Path, &Path)>,
) -> Vec<u8> {
    gen_proof::<C, ProverSHPLONK<_>, VerifierSHPLONK<_>>(params, pk, circuit, instances, path)
}

/// Generates a SNARK using either SHPLONK or GWC multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark<'params, ConcreteCircuit, P, V>(
    params: &'params ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
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
    #[cfg(feature = "halo2-axiom")]
    if let Some(path) = &path {
        if let Ok(snark) = read_snark(path) {
            return snark;
        }
    }
    let protocol = compile(
        params,
        pk.get_vk(),
        Config::kzg()
            .with_num_instance(circuit.num_instance())
            .with_accumulator_indices(ConcreteCircuit::accumulator_indices()),
    );

    let instances = circuit.instances();
    #[cfg(feature = "halo2-axiom")]
    let proof = gen_proof::<ConcreteCircuit, P, V>(params, pk, circuit, instances.clone(), None);
    // If we can't serialize the entire snark, at least serialize the proof
    #[cfg(not(feature = "halo2-axiom"))]
    let proof = {
        let path = path.map(|path| {
            let path = path.as_ref().to_str().unwrap();
            (format!("{path}.instances"), format!("{path}.proof"))
        });
        let paths = path.as_ref().map(|path| (Path::new(&path.0), Path::new(&path.1)));
        gen_proof::<ConcreteCircuit, P, V>(params, pk, circuit, instances.clone(), paths)
    };

    let snark = Snark::new(protocol, instances, proof);
    #[cfg(feature = "halo2-axiom")]
    if let Some(path) = &path {
        let f = File::create(path).unwrap();
        #[cfg(feature = "display")]
        let write_time = start_timer!(|| "Write SNARK");
        bincode::serialize_into(f, &snark).unwrap();
        #[cfg(feature = "display")]
        end_timer!(write_time);
    }
    #[allow(clippy::let_and_return)]
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
    path: Option<impl AsRef<Path>>,
) -> Snark {
    gen_snark::<ConcreteCircuit, ProverGWC<_>, VerifierGWC<_>>(params, pk, circuit, path)
}

/// Generates a SNARK using SHPLONK multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark_shplonk<ConcreteCircuit: CircuitExt<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    path: Option<impl AsRef<Path>>,
) -> Snark {
    gen_snark::<ConcreteCircuit, ProverSHPLONK<_>, VerifierSHPLONK<_>>(params, pk, circuit, path)
}

/// Tries to deserialize a SNARK from the specified `path` using `bincode`.
///
/// WARNING: The user must keep track of whether the SNARK was generated using the GWC or SHPLONK multi-open scheme.
#[cfg(feature = "halo2-axiom")]
pub fn read_snark(path: impl AsRef<Path>) -> Result<Snark, bincode::Error> {
    let f = File::open(path).map_err(Box::<bincode::ErrorKind>::from)?;
    bincode::deserialize_from(f)
}

// copied from snark_verifier --example recursion
pub fn gen_dummy_snark<ConcreteCircuit, AS>(
    params: &ParamsKZG<Bn256>,
    vk: Option<&VerifyingKey<G1Affine>>,
    num_instance: Vec<usize>,
) -> Snark
where
    ConcreteCircuit: CircuitExt<Fr>,
    AS: PolynomialCommitmentScheme<
            G1Affine,
            NativeLoader,
            VerifyingKey = KzgSuccinctVerifyingKey<G1Affine>,
            Output = KzgAccumulator<G1Affine, NativeLoader>,
        > + AccumulationScheme<
            G1Affine,
            NativeLoader,
            Accumulator = KzgAccumulator<G1Affine, NativeLoader>,
            VerifyingKey = KzgAsVerifyingKey,
        > + CostEstimation<G1Affine, Input = Vec<Query<Rotation>>>,
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
            .with_num_instance(num_instance.clone())
            .with_accumulator_indices(ConcreteCircuit::accumulator_indices()),
    );
    let instances = num_instance.into_iter().map(|n| vec![Fr::default(); n]).collect();
    let proof = {
        let mut transcript = PoseidonTranscript::<NativeLoader, _>::new::<SECURE_MDS>(Vec::new());
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
        let queries = PlonkProof::<G1Affine, NativeLoader, AS>::empty_queries(&protocol);
        for _ in 0..AS::estimate_cost(&queries).num_commitment {
            transcript.write_ec_point(G1Affine::default()).unwrap();
        }
        transcript.finalize()
    };

    Snark::new(protocol, instances, proof)
}
