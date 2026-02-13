//! Generate and verify an IVC proof (ported from `zk_stdlib/examples/ivc.rs`) with
//! Midnight's EVM transcript, then emit Solidity verifier + calldata artifacts.
//! Run with:
//!   cargo run --example midnight_ivc_evm --features midnight,loader_evm,revm -p snark-verifier-sdk
//! Note: this example is intentionally slow.

use ff::Field;
use halo2_base::halo2_proofs::halo2curves::{
    ff::PrimeField as HaloPrimeField, Coordinates as HaloCoordinates,
    CurveAffine as HaloCurveAffine,
};
use midnight_circuits::{
    ecc::{
        curves::CircuitCurve,
        foreign::{nb_foreign_ecc_chip_columns, ForeignEccChip, ForeignEccConfig},
    },
    field::{
        decomposition::{
            chip::{P2RDecompositionChip, P2RDecompositionConfig},
            pow2range::Pow2RangeChip,
        },
        foreign::FieldChip,
        native::NB_ARITH_COLS,
        NativeChip, NativeConfig, NativeGadget,
    },
    hash::poseidon::{
        PoseidonChip, PoseidonConfig, PoseidonState, NB_POSEIDON_ADVICE_COLS,
        NB_POSEIDON_FIXED_COLS,
    },
    instructions::*,
    types::{AssignedNative, ComposableChip, Instantiable},
    verifier::{
        self, Accumulator, AssignedAccumulator, AssignedVk, BlstrsEmulation, Msm, SelfEmulation,
        VerifierGadget,
    },
};
use midnight_curves::Bls12;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{create_proof, keygen_pk, keygen_vk_with_k, prepare, Circuit, ConstraintSystem, Error},
    poly::{
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        EvaluationDomain,
    },
    transcript::{CircuitTranscript, Transcript},
};
use rand::rngs::OsRng;
use snark_verifier_sdk::{
    midnight_adapter::MidnightProofBundle, midnight_evm_transcript::MidnightEvmHash,
};
use std::{collections::BTreeMap, path::PathBuf, time::Instant};

type S = BlstrsEmulation;
type F = <S as SelfEmulation>::F;
type C = <S as SelfEmulation>::C;
type E = <S as SelfEmulation>::Engine;
type CBase = <C as CircuitCurve>::Base;
type NG = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;
type CurveChip = ForeignEccChip<F, C, C, NG, NG>;
type AssignedPoint = <CurveChip as EccInstructions<F, C>>::Point;

const K: u32 = 20;

#[cfg(feature = "revm")]
fn extract_revm_gas(message: &str) -> Option<u64> {
    let marker = "gas_used ";
    let start = message.find(marker)? + marker.len();
    let digits: String = message[start..].chars().take_while(|ch| ch.is_ascii_digit()).collect();
    if digits.is_empty() {
        return None;
    }
    digits.parse().ok()
}

#[derive(Clone, Debug)]
struct IvcCircuit {
    self_vk: (EvaluationDomain<F>, ConstraintSystem<F>, Value<F>),
    prev_state: Value<F>,
    prev_proof: Value<Vec<u8>>,
    prev_acc: Value<Accumulator<S>>,
    fixed_bases: BTreeMap<String, C>,
}

fn fully_collapsed_accumulator_as_public_input(
    acc: &Accumulator<S>,
    fixed_bases: &BTreeMap<String, C>,
) -> Vec<F> {
    let (lhs, rhs) = acc.fully_collapse(fixed_bases);
    [AssignedPoint::as_public_input(&lhs), AssignedPoint::as_public_input(&rhs)].concat()
}

fn configure_ivc_circuit(
    meta: &mut ConstraintSystem<F>,
) -> (NativeConfig, P2RDecompositionConfig, ForeignEccConfig<C>, PoseidonConfig<F>) {
    let nb_advice_cols = nb_foreign_ecc_chip_columns::<F, C, C, NG>();
    let nb_fixed_cols = NB_ARITH_COLS + 4;

    let advice_columns: Vec<_> = (0..nb_advice_cols).map(|_| meta.advice_column()).collect();
    let fixed_columns: Vec<_> = (0..nb_fixed_cols).map(|_| meta.fixed_column()).collect();
    let committed_instance_column = meta.instance_column();
    let instance_column = meta.instance_column();

    let native_config = NativeChip::configure(
        meta,
        &(
            advice_columns[..NB_ARITH_COLS].try_into().unwrap(),
            fixed_columns[..NB_ARITH_COLS + 4].try_into().unwrap(),
            [committed_instance_column, instance_column],
        ),
    );

    let core_decomp_config = {
        let pow2_config = Pow2RangeChip::configure(meta, &advice_columns[1..NB_ARITH_COLS]);
        P2RDecompositionChip::configure(meta, &(native_config.clone(), pow2_config))
    };

    let base_config = FieldChip::<F, CBase, C, NG>::configure(meta, &advice_columns);
    let curve_config =
        ForeignEccChip::<F, C, C, NG, NG>::configure(meta, &base_config, &advice_columns);

    let poseidon_config = PoseidonChip::configure(
        meta,
        &(
            advice_columns[..NB_POSEIDON_ADVICE_COLS].try_into().unwrap(),
            fixed_columns[..NB_POSEIDON_FIXED_COLS].try_into().unwrap(),
        ),
    );

    (native_config, core_decomp_config, curve_config, poseidon_config)
}

impl Circuit<F> for IvcCircuit {
    type Config = (NativeConfig, P2RDecompositionConfig, ForeignEccConfig<C>, PoseidonConfig<F>);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unreachable!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        configure_ivc_circuit(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let native_chip = <NativeChip<F> as ComposableChip<F>>::new(&config.0, &());
        let core_decomp_chip = P2RDecompositionChip::new(&config.1, &(K as usize - 1));
        let scalar_chip = NativeGadget::new(core_decomp_chip.clone(), native_chip.clone());
        let curve_chip = ForeignEccChip::new(&config.2, &scalar_chip, &scalar_chip);
        let poseidon_chip = PoseidonChip::new(&config.3, &native_chip);

        let verifier_chip = VerifierGadget::new(&curve_chip, &scalar_chip, &poseidon_chip);

        let self_vk_name = "self_vk";
        let (self_domain, self_cs, self_vk_value) = &self.self_vk;
        let assigned_self_vk: AssignedVk<S> = verifier_chip.assign_vk_as_public_input(
            &mut layouter,
            self_vk_name,
            self_domain,
            self_cs,
            *self_vk_value,
        )?;

        let prev_state = scalar_chip.assign(&mut layouter, self.prev_state)?;
        let next_state = scalar_chip.add_constant(&mut layouter, &prev_state, F::ONE)?;
        scalar_chip.constrain_as_public_input(&mut layouter, &next_state)?;

        let prev_acc = {
            let mut fixed_base_names = vec![String::from("com_instance")];
            fixed_base_names.extend(verifier::fixed_base_names::<S>(
                self_vk_name,
                self_cs.num_fixed_columns() + self_cs.num_selectors(),
                self_cs.permutation().columns.len(),
            ));
            AssignedAccumulator::assign(
                &mut layouter,
                &curve_chip,
                &scalar_chip,
                1,
                1,
                &[],
                &fixed_base_names,
                self.prev_acc.clone(),
            )?
        };
        let mut fixed_base_names = vec![String::from("com_instance")];
        fixed_base_names.extend(verifier::fixed_base_names::<S>(
            self_vk_name,
            self_cs.num_fixed_columns() + self_cs.num_selectors(),
            self_cs.permutation().columns.len(),
        ));
        let assigned_fixed_bases: BTreeMap<String, AssignedPoint> = fixed_base_names
            .iter()
            .map(|name| {
                let base = self.fixed_bases.get(name).cloned().unwrap_or_default();
                let assigned = curve_chip.assign(&mut layouter, Value::known(base))?;
                Ok((name.clone(), assigned))
            })
            .collect::<Result<_, Error>>()?;
        let (prev_acc_lhs, prev_acc_rhs) = prev_acc.fully_collapse_with_assigned_fixed_bases(
            &mut layouter,
            &curve_chip,
            &assigned_fixed_bases,
        )?;
        let mut prev_acc_pi = curve_chip.as_public_input(&mut layouter, &prev_acc_lhs)?;
        prev_acc_pi.extend(curve_chip.as_public_input(&mut layouter, &prev_acc_rhs)?);

        let id_point = curve_chip.assign_fixed(&mut layouter, C::default())?;

        let assigned_pi = [
            verifier_chip.as_public_input(&mut layouter, &assigned_self_vk)?,
            vec![prev_state.clone()],
            prev_acc_pi,
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();

        let mut proof_acc = verifier_chip.prepare(
            &mut layouter,
            &assigned_self_vk,
            &[("com_instance", id_point)],
            &[&assigned_pi],
            self.prev_proof.clone(),
        )?;

        let is_genesis = scalar_chip.is_zero(&mut layouter, &prev_state)?;
        let is_not_genesis = scalar_chip.not(&mut layouter, &is_genesis)?;

        AssignedAccumulator::scale_by_bit(
            &mut layouter,
            &scalar_chip,
            &is_not_genesis,
            &mut proof_acc,
        )?;

        proof_acc.collapse(&mut layouter, &curve_chip, &scalar_chip)?;

        let mut next_acc = AssignedAccumulator::<S>::accumulate(
            &mut layouter,
            &verifier_chip,
            &scalar_chip,
            &poseidon_chip,
            &[proof_acc, prev_acc],
        )?;

        next_acc.collapse(&mut layouter, &curve_chip, &scalar_chip)?;
        let (next_acc_lhs, next_acc_rhs) = next_acc.fully_collapse_with_assigned_fixed_bases(
            &mut layouter,
            &curve_chip,
            &assigned_fixed_bases,
        )?;
        curve_chip.constrain_as_public_input(&mut layouter, &next_acc_lhs)?;
        curve_chip.constrain_as_public_input(&mut layouter, &next_acc_rhs)?;

        core_decomp_chip.load(&mut layouter)
    }
}

fn main() {
    let self_k = K;

    let mut self_cs = ConstraintSystem::default();
    configure_ivc_circuit(&mut self_cs);
    let self_domain = EvaluationDomain::new(self_cs.degree() as u32, self_k);

    let default_ivc_circuit = IvcCircuit {
        self_vk: (self_domain.clone(), self_cs.clone(), Value::unknown()),
        prev_state: Value::unknown(),
        prev_proof: Value::unknown(),
        prev_acc: Value::unknown(),
        fixed_bases: BTreeMap::new(),
    };

    let srs = ParamsKZG::<Bls12>::unsafe_setup(self_k, OsRng);

    let start = Instant::now();
    let vk = keygen_vk_with_k(&srs, &default_ivc_circuit, self_k).expect("vk generation failed");
    let pk = keygen_pk(vk.clone(), &default_ivc_circuit).expect("pk generation failed");
    println!("computed vk and pk in {:?}", start.elapsed());

    let mut fixed_bases = BTreeMap::new();
    fixed_bases.insert(String::from("com_instance"), C::default());
    fixed_bases.extend(midnight_circuits::verifier::fixed_bases::<S>("self_vk", &vk));
    let fixed_base_names = fixed_bases.keys().cloned().collect::<Vec<_>>();

    let trivial_acc = Accumulator::<S>::new(
        Msm::new(&[C::default()], &[F::ONE], &BTreeMap::new()),
        Msm::new(
            &[C::default()],
            &[F::ONE],
            &fixed_base_names.iter().map(|name| (name.clone(), F::ZERO)).collect(),
        ),
    );

    // Step 0: create a Poseidon-transcript proof (matching ivc.rs recursion expectations).
    let state0 = F::ONE;
    let acc0 = trivial_acc.clone();
    let circuit0 = IvcCircuit {
        self_vk: (self_domain.clone(), self_cs.clone(), Value::known(vk.transcript_repr())),
        prev_state: Value::known(F::ZERO),
        prev_proof: Value::known(vec![]),
        prev_acc: Value::known(trivial_acc.clone()),
        fixed_bases: fixed_bases.clone(),
    };
    let field_bytes = <F as ff::PrimeField>::Repr::default().as_ref().len();

    let mut public_inputs0 = AssignedVk::<S>::as_public_input(&vk);
    public_inputs0.extend(AssignedNative::<F>::as_public_input(&state0));
    let collapsed_acc0_pi = fully_collapsed_accumulator_as_public_input(&acc0, &fixed_bases);
    println!(
        "collapsed accumulator (step 0): {} field elements ({} bytes)",
        collapsed_acc0_pi.len(),
        collapsed_acc0_pi.len() * field_bytes
    );
    public_inputs0.extend(collapsed_acc0_pi);

    let start = Instant::now();
    let proof0 = {
        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init();
        create_proof::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>, IvcCircuit>(
            &srs,
            &pk,
            &[circuit0],
            1,
            &[&[&[], &public_inputs0]],
            OsRng,
            &mut transcript,
        )
        .expect("failed to create step-0 IVC proof");
        transcript.finalize()
    };
    println!("generated IVC proof step 0 (Poseidon) in {:?}", start.elapsed());

    let proof_acc0: Accumulator<S> = {
        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&proof0);
        let dual_msm = prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
            &vk,
            &[&[C::default()]],
            &[&[&public_inputs0]],
            &mut transcript,
        )
        .expect("native step-0 prepare/verification failed");
        assert!(
            dual_msm.clone().check(&srs.verifier_params()),
            "step-0 proof did not satisfy native pairing check"
        );
        let mut proof_acc: Accumulator<S> = dual_msm.into();
        proof_acc.extract_fixed_bases(&fixed_bases);
        proof_acc.collapse();
        proof_acc
    };

    let mut acc1 = Accumulator::accumulate(&[proof_acc0, acc0.clone()]);
    acc1.collapse();
    assert!(acc1.check(&srs.s_g2().into(), &fixed_bases), "step-0 accumulator check failed");

    // Step 1: create an EVM-transcript proof that verifies step 0 in-circuit.
    let state1 = state0 + F::ONE;
    let circuit1 = IvcCircuit {
        self_vk: (self_domain.clone(), self_cs.clone(), Value::known(vk.transcript_repr())),
        prev_state: Value::known(state0),
        prev_proof: Value::known(proof0),
        prev_acc: Value::known(acc0),
        fixed_bases: fixed_bases.clone(),
    };
    let mut public_inputs1 = AssignedVk::<S>::as_public_input(&vk);
    public_inputs1.extend(AssignedNative::<F>::as_public_input(&state1));
    let collapsed_acc1_pi = fully_collapsed_accumulator_as_public_input(&acc1, &fixed_bases);
    println!(
        "collapsed accumulator (step 1): {} field elements ({} bytes)",
        collapsed_acc1_pi.len(),
        collapsed_acc1_pi.len() * field_bytes
    );
    public_inputs1.extend(collapsed_acc1_pi);

    let start = Instant::now();
    let proof = {
        let mut transcript = CircuitTranscript::<MidnightEvmHash>::init();
        create_proof::<F, KZGCommitmentScheme<E>, CircuitTranscript<MidnightEvmHash>, IvcCircuit>(
            &srs,
            &pk,
            &[circuit1],
            1,
            &[&[&[], &public_inputs1]],
            OsRng,
            &mut transcript,
        )
        .expect("failed to create step-1 EVM IVC proof");
        transcript.finalize()
    };
    println!("generated IVC proof step 1 (EVM) in {:?}", start.elapsed());

    let proof_acc1: Accumulator<S> = {
        let mut transcript = CircuitTranscript::<MidnightEvmHash>::init_from_bytes(&proof);
        let dual_msm = prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<MidnightEvmHash>>(
            &vk,
            &[&[C::default()]],
            &[&[&public_inputs1]],
            &mut transcript,
        )
        .expect("native step-1 prepare/verification failed");
        assert!(
            dual_msm.clone().check(&srs.verifier_params()),
            "step-1 proof did not satisfy native pairing check"
        );
        let mut proof_acc: Accumulator<S> = dual_msm.into();
        proof_acc.extract_fixed_bases(&fixed_bases);
        proof_acc.collapse();
        proof_acc
    };

    acc1 = Accumulator::accumulate(&[proof_acc1, acc1]);
    acc1.collapse();
    assert!(acc1.check(&srs.s_g2().into(), &fixed_bases), "step-1 accumulator check failed");

    let public_inputs = public_inputs1;

    let bundle = MidnightProofBundle::new_unchecked(
        srs.verifier_params(),
        vk.clone(),
        proof.clone(),
        vec![public_inputs],
    )
    .expect("bundle creation should succeed");

    bundle
        .verify_with_snark_verifier_evm_transcript()
        .expect("snark-verifier EVM-transcript path should succeed");

    {
        let accumulators = bundle
            .evm_transcript_accumulators()
            .expect("EVM transcript accumulators should be computable natively");
        println!("native evm accumulators: {}", accumulators.len());
        let as_words = |repr: &[u8]| -> (String, String) {
            let mut be = repr.to_vec();
            be.reverse();
            let mut padded = [0u8; 64];
            let offset = 64 - be.len();
            padded[offset..].copy_from_slice(&be);
            (hex::encode(&padded[..32]), hex::encode(&padded[32..]))
        };
        for (idx, acc) in accumulators.iter().enumerate() {
            let lhs: HaloCoordinates<_> =
                Option::from(acc.lhs.coordinates()).expect("lhs should not be infinity");
            let rhs: HaloCoordinates<_> =
                Option::from(acc.rhs.coordinates()).expect("rhs should not be infinity");
            let (lhs_x_hi, lhs_x_lo) = as_words(lhs.x().to_repr().as_ref());
            let (lhs_y_hi, lhs_y_lo) = as_words(lhs.y().to_repr().as_ref());
            let (rhs_x_hi, rhs_x_lo) = as_words(rhs.x().to_repr().as_ref());
            let (rhs_y_hi, rhs_y_lo) = as_words(rhs.y().to_repr().as_ref());
            println!("native evm acc[{idx}] lhs: {lhs_x_hi} {lhs_x_lo} {lhs_y_hi} {lhs_y_lo}");
            println!("native evm acc[{idx}] rhs: {rhs_x_hi} {rhs_x_lo} {rhs_y_hi} {rhs_y_lo}");
        }
    }

    let solidity = bundle
        .generate_evm_verifier_solidity()
        .expect("failed to generate Solidity verifier source");
    let bytecode =
        bundle.generate_evm_verifier_bytecode().expect("failed to compile Solidity verifier");
    let runtime_bytecode =
        snark_verifier_sdk::snark_verifier::loader::evm::compile_solidity_runtime(&solidity);
    let compact = bundle
        .generate_evm_verifier_compact_artifacts()
        .expect("failed to generate compact verifier artifacts");
    let compact_runtime_deployment =
        snark_verifier_sdk::snark_verifier::loader::evm::compile_solidity_via_ir(
            &compact.runtime_solidity,
        );
    let compact_runtime_code =
        snark_verifier_sdk::snark_verifier::loader::evm::compile_solidity_runtime_via_ir(
            &compact.runtime_solidity,
        );
    let compact_page_sizes =
        compact.page_runtime_codes.iter().map(|page| page.len()).collect::<Vec<_>>();
    let compact_total_deployed_code =
        compact_runtime_code.len() + compact_page_sizes.iter().sum::<usize>();
    let hybrid = bundle
        .generate_evm_verifier_hybrid_artifacts()
        .expect("failed to generate hybrid verifier artifacts");
    let hybrid_runtime_deployment =
        snark_verifier_sdk::snark_verifier::loader::evm::compile_solidity_via_ir(
            &hybrid.runtime_solidity,
        );
    let hybrid_runtime_code =
        snark_verifier_sdk::snark_verifier::loader::evm::compile_solidity_runtime_via_ir(
            &hybrid.runtime_solidity,
        );
    let hybrid_page_sizes =
        hybrid.page_runtime_codes.iter().map(|page| page.len()).collect::<Vec<_>>();
    let hybrid_total_deployed_code =
        hybrid_runtime_code.len() + hybrid_page_sizes.iter().sum::<usize>();
    let calldata = bundle.encode_evm_calldata().expect("failed to encode EVM calldata");

    let out_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples");
    let solidity_path = out_dir.join("MidnightIvcVerifier.sol");
    let bytecode_path = out_dir.join("midnight_ivc.bytecode");
    let calldata_path = out_dir.join("midnight_ivc.calldata");
    let compact_solidity_path = out_dir.join("MidnightIvcVerifierCompact.sol");
    let compact_runtime_path = out_dir.join("midnight_ivc_compact_runtime.bytecode");
    let compact_pages_path = out_dir.join("midnight_ivc_compact_pages.bytecode");
    let compact_manifest_path = out_dir.join("midnight_ivc_compact_manifest.txt");
    let hybrid_solidity_path = out_dir.join("MidnightIvcVerifierHybrid.sol");
    let hybrid_runtime_path = out_dir.join("midnight_ivc_hybrid_runtime.bytecode");
    let hybrid_pages_path = out_dir.join("midnight_ivc_hybrid_pages.bytecode");
    let hybrid_manifest_path = out_dir.join("midnight_ivc_hybrid_manifest.txt");

    std::fs::write(&solidity_path, &solidity).expect("failed to write Solidity verifier");
    std::fs::write(&bytecode_path, format!("0x{}", hex::encode(&bytecode)))
        .expect("failed to write verifier bytecode");
    std::fs::write(&calldata_path, hex::encode(&calldata)).expect("failed to write calldata");
    std::fs::write(&compact_solidity_path, &compact.runtime_solidity)
        .expect("failed to write compact Solidity verifier");
    std::fs::write(
        &compact_runtime_path,
        format!("0x{}", hex::encode(&compact_runtime_deployment)),
    )
    .expect("failed to write compact verifier runtime deployment bytecode");
    let compact_pages_lines = compact
        .page_deployment_codes
        .iter()
        .enumerate()
        .map(|(idx, code)| format!("page[{idx}] = 0x{}", hex::encode(code)))
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(&compact_pages_path, compact_pages_lines)
        .expect("failed to write compact page deployment bytecodes");
    let compact_manifest = format!(
        "opcode_version: {}\npage_size_bytes: {}\nprogram_words: {}\npage_word_offsets: {:?}\npage_word_counts: {:?}\n",
        compact.manifest.opcode_version,
        compact.manifest.page_size_bytes,
        compact.manifest.program_words,
        compact.manifest.page_word_offsets,
        compact.manifest.page_word_counts,
    );
    std::fs::write(&compact_manifest_path, compact_manifest)
        .expect("failed to write compact manifest");
    std::fs::write(&hybrid_solidity_path, &hybrid.runtime_solidity)
        .expect("failed to write hybrid Solidity verifier");
    std::fs::write(
        &hybrid_runtime_path,
        format!("0x{}", hex::encode(&hybrid_runtime_deployment)),
    )
    .expect("failed to write hybrid verifier runtime deployment bytecode");
    let hybrid_pages_lines = hybrid
        .page_deployment_codes
        .iter()
        .enumerate()
        .map(|(idx, code)| format!("page[{idx}] = 0x{}", hex::encode(code)))
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(&hybrid_pages_path, hybrid_pages_lines)
        .expect("failed to write hybrid page deployment bytecodes");
    let hybrid_manifest = format!(
        "opcode_version: {}\npage_size_bytes: {}\nprogram_words: {}\npage_word_offsets: {:?}\npage_word_counts: {:?}\n",
        hybrid.manifest.opcode_version,
        hybrid.manifest.page_size_bytes,
        hybrid.manifest.program_words,
        hybrid.manifest.page_word_offsets,
        hybrid.manifest.page_word_counts,
    );
    std::fs::write(&hybrid_manifest_path, hybrid_manifest)
        .expect("failed to write hybrid manifest");

    println!("proof bytes: {}", proof.len());
    println!("unrolled deployment code bytes: {}", bytecode.len());
    println!("unrolled runtime code bytes: {}", runtime_bytecode.len());
    println!("compact runtime deployment code bytes: {}", compact_runtime_deployment.len());
    println!("compact verifier runtime code bytes: {}", compact_runtime_code.len());
    println!("compact page runtime sizes (bytes): {:?}", compact_page_sizes);
    println!(
        "compact total deployed runtime code bytes (verifier + pages): {}",
        compact_total_deployed_code
    );
    println!("hybrid runtime deployment code bytes: {}", hybrid_runtime_deployment.len());
    println!("hybrid verifier runtime code bytes: {}", hybrid_runtime_code.len());
    println!("hybrid page runtime sizes (bytes): {:?}", hybrid_page_sizes);
    println!(
        "hybrid total deployed runtime code bytes (verifier + pages): {}",
        hybrid_total_deployed_code
    );
    println!("calldata bytes: {}", calldata.len());
    println!("wrote {}", solidity_path.display());
    println!("wrote {}", bytecode_path.display());
    println!("wrote {}", calldata_path.display());
    println!("wrote {}", compact_solidity_path.display());
    println!("wrote {}", compact_runtime_path.display());
    println!("wrote {}", compact_pages_path.display());
    println!("wrote {}", compact_manifest_path.display());
    println!("wrote {}", hybrid_solidity_path.display());
    println!("wrote {}", hybrid_runtime_path.display());
    println!("wrote {}", hybrid_pages_path.display());
    println!("wrote {}", hybrid_manifest_path.display());

    #[cfg(feature = "revm")]
    {
        match bundle.verify_with_generated_solidity_revm() {
            Ok(gas) => println!("revm gas: {gas}"),
            Err(err) => {
                let err_message = err.to_string();
                if let Some(gas) = extract_revm_gas(&err_message) {
                    println!("revm gas (reverted): {gas}");
                }
                println!("revm verification failed: {err_message}");
                println!(
                    "note: native snark-verifier EVM-transcript verification succeeded above; this indicates a local revm/precompile divergence for this large IVC verifier"
                );
            }
        }

        match bundle.verify_with_generated_solidity_revm_compact() {
            Ok(gas) => println!("revm compact gas: {gas}"),
            Err(err) => {
                let err_message = err.to_string();
                if let Some(gas) = extract_revm_gas(&err_message) {
                    println!("revm compact gas (reverted): {gas}");
                }
                println!("revm compact verification failed: {err_message}");
            }
        }

        match bundle.verify_with_generated_solidity_revm_hybrid() {
            Ok(gas) => println!("revm hybrid gas: {gas}"),
            Err(err) => {
                let err_message = err.to_string();
                if let Some(gas) = extract_revm_gas(&err_message) {
                    println!("revm hybrid gas (reverted): {gas}");
                }
                println!("revm hybrid verification failed: {err_message}");
            }
        }
    }
}
