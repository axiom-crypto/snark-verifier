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
    midnight_adapter::MidnightProofBundle,
    midnight_evm_transcript::{MidnightEvmHash, MidnightEvmHashCompressed},
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

    // Compressed-proof variant (`[sign || x]` per G1 point).
    let proof_compressed = midnight_zk_stdlib::prove::<PoseidonExample, MidnightEvmHashCompressed>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("compressed EVM-transcript proof generation should not fail");

    midnight_zk_stdlib::verify::<PoseidonExample, MidnightEvmHashCompressed>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof_compressed,
    )
    .expect("compressed EVM-transcript native verification should succeed");

    let bundle_compressed = MidnightProofBundle::new_unchecked(
        srs.verifier_params(),
        vk.vk().clone(),
        proof_compressed.clone(),
        vec![vec![instance]],
    )
    .expect("compressed bundle creation should succeed");

    let solidity_compressed = bundle_compressed
        .generate_evm_verifier_solidity_compressed_proof()
        .expect("failed to generate compressed Solidity verifier source");
    let bytecode_compressed = bundle_compressed
        .generate_evm_verifier_bytecode_compressed_proof()
        .expect("failed to compile compressed Solidity verifier");
    let calldata_compressed = bundle_compressed
        .encode_evm_calldata()
        .expect("failed to encode compressed EVM calldata");

    let solidity_compressed_path = out_dir.join("MidnightPoseidonVerifierCompressed.sol");
    let bytecode_compressed_path = out_dir.join("midnight_poseidon_compressed.bytecode");
    let calldata_compressed_path = out_dir.join("midnight_poseidon_compressed.calldata");

    std::fs::write(&solidity_compressed_path, &solidity_compressed)
        .expect("failed to write compressed Solidity verifier");
    std::fs::write(
        &bytecode_compressed_path,
        format!("0x{}", hex::encode(&bytecode_compressed)),
    )
    .expect("failed to write compressed verifier bytecode");
    std::fs::write(&calldata_compressed_path, hex::encode(&calldata_compressed))
        .expect("failed to write compressed calldata");

    println!("compressed proof bytes: {}", proof_compressed.len());
    println!("compressed deployment code bytes: {}", bytecode_compressed.len());
    println!("compressed calldata bytes: {}", calldata_compressed.len());
    println!(
        "proof byte delta (compressed - uncompressed): {}",
        proof_compressed.len() as isize - proof.len() as isize
    );
    println!(
        "calldata byte delta (compressed - uncompressed): {}",
        calldata_compressed.len() as isize - calldata.len() as isize
    );
    println!("wrote {}", solidity_compressed_path.display());
    println!("wrote {}", bytecode_compressed_path.display());
    println!("wrote {}", calldata_compressed_path.display());

    #[cfg(feature = "revm")]
    {
        if std::env::var("RUN_REVM").ok().as_deref() == Some("1") {
            let gas = bundle
                .verify_with_generated_solidity_revm()
                .expect("revm verification (uncompressed) should succeed");
            println!("revm gas (uncompressed): {gas}");

            match bundle_compressed.verify_with_generated_solidity_revm_compressed_proof() {
                Ok(gas_compressed) => {
                    println!("revm gas (compressed): {gas_compressed}");
                    println!(
                        "revm gas delta (compressed - uncompressed): {}",
                        gas_compressed as i64 - gas as i64
                    );
                }
                Err(err) => {
                    println!("revm compressed verification failed: {err}");
                }
            }
        } else {
            println!("revm verification skipped (set RUN_REVM=1 to run local revm simulation)");
        }
    }
}
