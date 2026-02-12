//! Generate and verify the Poseidon example with Midnight's EVM transcript.
//! Run with:
//!   cargo run --example midnight_poseidon_evm --features midnight,loader_evm,revm -p snark-verifier-sdk
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
use snark_verifier_sdk::{
    midnight_adapter::MidnightProofBundle, midnight_evm_transcript::MidnightEvmHash,
};
use std::path::PathBuf;

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
    let srs = ParamsKZG::<Bls12>::unsafe_setup(K, OsRng);

    let relation = PoseidonExample;
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let mut rng = ChaCha8Rng::from_entropy();
    let witness: [F; 3] = core::array::from_fn(|_| F::random(&mut rng));
    let instance = <PoseidonChip<F> as HashCPU<F, F>>::hash(&witness);

    let proof = midnight_zk_stdlib::prove::<PoseidonExample, MidnightEvmHash>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("EVM-transcript proof generation should not fail");

    midnight_zk_stdlib::verify::<PoseidonExample, MidnightEvmHash>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof,
    )
    .expect("EVM-transcript native verification should succeed");

    let bundle = MidnightProofBundle::new_unchecked(
        srs.verifier_params(),
        vk.vk().clone(),
        proof.clone(),
        vec![vec![instance]],
    )
    .expect("Bundle creation should succeed");

    if std::env::var("CHECK_NATIVE_EVM_TRANSCRIPT").ok().as_deref() == Some("1") {
        bundle
            .verify_with_snark_verifier_evm_transcript()
            .expect("snark-verifier EVM-transcript path should succeed");
    }

    let solidity = bundle
        .generate_evm_verifier_solidity()
        .expect("failed to generate Solidity verifier source");
    let bytecode =
        bundle.generate_evm_verifier_bytecode().expect("failed to compile Solidity verifier");
    let calldata = bundle.encode_evm_calldata().expect("failed to encode EVM calldata");

    let out_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples");
    let solidity_path = out_dir.join("MidnightPoseidonVerifier.sol");
    let bytecode_path = out_dir.join("midnight_poseidon.bytecode");
    let calldata_path = out_dir.join("midnight_poseidon.calldata");

    std::fs::write(&solidity_path, &solidity)
        .expect("failed to write Solidity verifier");
    std::fs::write(&bytecode_path, format!("0x{}", hex::encode(&bytecode)))
        .expect("failed to write verifier bytecode");
    std::fs::write(&calldata_path, hex::encode(&calldata))
        .expect("failed to write calldata");

    println!("proof bytes: {}", proof.len());
    println!("deployment code bytes: {}", bytecode.len());
    println!("calldata bytes: {}", calldata.len());
    println!("wrote {}", solidity_path.display());
    println!("wrote {}", bytecode_path.display());
    println!("wrote {}", calldata_path.display());

    #[cfg(feature = "revm")]
    {
        if std::env::var("RUN_REVM").ok().as_deref() == Some("1") {
            let gas = bundle
                .verify_with_generated_solidity_revm()
                .expect("revm verification should succeed");
            println!("revm gas: {gas}");
        } else {
            println!("revm verification skipped (set RUN_REVM=1 to run local revm simulation)");
        }
    }
}
