//! Generate and verify the Poseidon example using Midnight's zk-stdlib (native path).
//! Run with:
//!   cargo run --example midnight_poseidon --features midnight
use blake2b_simd::State as Blake2bState;
use ff::Field;
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
};
use midnight_curves::Bls12;
use midnight_proofs::poly::kzg::params::ParamsKZG;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use rand::{rngs::OsRng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use snark_verifier_sdk::midnight_adapter::MidnightProofBundle;

type F = midnight_curves::Fq;

#[derive(Clone, Default)]
pub struct PoseidonExample;

impl Relation for PoseidonExample {
    type Instance = F;

    type Witness = [F; 3];

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned_message = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.poseidon(layouter, &assigned_message)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch { poseidon: true, ..ZkStdLibArch::default() }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonExample)
    }
}

fn main() {
    const K: u32 = 6;
    // For demo purposes generate an in-memory SRS instead of downloading Filecoin params.
    let srs = ParamsKZG::<Bls12>::unsafe_setup(K, OsRng);

    let relation = PoseidonExample;
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let mut rng = ChaCha8Rng::from_entropy();
    let witness: [F; 3] = core::array::from_fn(|_| F::random(&mut rng));
    let instance = <PoseidonChip<F> as HashCPU<F, F>>::hash(&witness);

    let proof = midnight_zk_stdlib::prove::<PoseidonExample, Blake2bState>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");

    midnight_zk_stdlib::verify::<PoseidonExample, Blake2bState>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof,
    )
    .expect("Verification should succeed");

    let bundle = MidnightProofBundle::new(
        srs.verifier_params(),
        vk.vk().clone(),
        proof.clone(),
        vec![vec![instance]],
    )
    .expect("Bundle creation should parse and verify natively");

    bundle.verify_with_snark_decider().expect("snark-verifier decider check should succeed");
    bundle.verify_with_snark_verifier().expect("snark-verifier full path should succeed");

    println!("Poseidon proof generated and verified successfully.");
    println!("Verified through Midnight native path, snark-verifier decider bridge, and full snark-verifier adapter.");
}
