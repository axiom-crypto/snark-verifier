use ark_std::{end_timer, start_timer};
use halo2_base::halo2_proofs;
use halo2_base::utils::fs::gen_srs;
use halo2_proofs::halo2curves::bn256::Fr;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use snark_verifier::loader::native::NativeLoader;
use snark_verifier_sdk::{
    self,
    evm::{
        evm_verify, gen_evm_proof_gwc, gen_evm_proof_shplonk, gen_evm_verifier_gwc,
        gen_evm_verifier_shplonk,
    },
    gen_pk,
    halo2::{
        aggregation::load_verify_circuit_degree, aggregation::AggregationCircuit, gen_proof_gwc,
        gen_proof_shplonk, gen_snark_gwc, gen_snark_shplonk, PoseidonTranscript, POSEIDON_SPEC,
    },
    CircuitExt,
};
use std::env::{set_var, var};
use std::path::Path;

use criterion::{criterion_group, criterion_main};
use criterion::{BenchmarkId, Criterion};
use pprof::criterion::{Output, PProfProfiler};

pub mod zkevm {
    use super::Fr;
    use bus_mapping::{circuit_input_builder::CircuitsParams, mock::BlockData};
    use eth_types::geth_types::GethData;
    use mock::TestContext;
    use zkevm_circuits::{
        evm_circuit::{witness::block_convert, EvmCircuit},
        state_circuit::StateCircuit,
        witness::RwMap,
    };

    pub fn test_evm_circuit() -> EvmCircuit<Fr> {
        let empty_data: GethData =
            TestContext::<0, 0>::new(None, |_| {}, |_, _| {}, |b, _| b).unwrap().into();

        let mut builder = BlockData::new_from_geth_data_with_params(
            empty_data.clone(),
            CircuitsParams::default(),
        )
        .new_circuit_input_builder();

        builder.handle_block(&empty_data.eth_block, &empty_data.geth_traces).unwrap();

        let block = block_convert(&builder.block, &builder.code_db).unwrap();

        EvmCircuit::<Fr>::new(block)
    }

    pub fn test_state_circuit() -> StateCircuit<Fr> {
        StateCircuit::new(RwMap::default(), 1 << 16)
    }
}

fn bench(c: &mut Criterion) {
    let mut rng = ChaCha20Rng::from_entropy();
    let mut transcript =
        PoseidonTranscript::<NativeLoader, _>::from_spec(vec![], POSEIDON_SPEC.clone());

    // === create zkevm evm circuit snark ===
    let k: u32 = var("DEGREE")
        .unwrap_or_else(|_| {
            set_var("DEGREE", "18");
            "18".to_owned()
        })
        .parse()
        .unwrap();
    let evm_circuit = zkevm::test_evm_circuit();
    let state_circuit = zkevm::test_state_circuit();
    let params_app = gen_srs(k);
    let evm_snark = {
        let pk = gen_pk(&params_app, &evm_circuit, Some(Path::new("data/zkevm_evm.pkey")));
        gen_snark_gwc(
            &params_app,
            &pk,
            evm_circuit,
            &mut transcript,
            &mut rng,
            Some(Path::new("data/zkevm_evm.snark")),
        )
    };
    let state_snark = {
        let pk = gen_pk(&params_app, &state_circuit, Some(Path::new("data/zkevm_state.pkey")));
        gen_snark_shplonk(
            &params_app,
            &pk,
            state_circuit,
            &mut transcript,
            &mut rng,
            Some(Path::new("data/zkevm_state.snark")),
        )
    };
    let snarks = [evm_snark, state_snark];
    // === finished zkevm evm circuit ===

    // === now to do aggregation ===
    set_var("VERIFY_CONFIG", "./configs/bench_zkevm_plus_state.config");
    let k = load_verify_circuit_degree();
    let params = gen_srs(k);

    let start1 = start_timer!(|| "Create aggregation circuit");
    let agg_circuit = AggregationCircuit::new(&params, snarks, &mut transcript, &mut rng);
    end_timer!(start1);

    let pk = gen_pk(&params, &agg_circuit, None);

    let mut group = c.benchmark_group("shplonk-proof");
    group.sample_size(10);
    group.bench_with_input(
        BenchmarkId::new("zkevm-evm-state-agg", k),
        &(&params, &pk, &agg_circuit),
        |b, &(params, pk, agg_circuit)| {
            b.iter(|| {
                let instances = agg_circuit.instances();
                gen_proof_shplonk(
                    params,
                    pk,
                    agg_circuit.clone(),
                    instances,
                    &mut transcript,
                    &mut rng,
                    None,
                );
            })
        },
    );
    group.finish();

    let mut group = c.benchmark_group("gwc-proof");
    group.sample_size(10);
    group.bench_with_input(
        BenchmarkId::new("zkevm-evm-state-agg", k),
        &(&params, &pk, &agg_circuit),
        |b, &(params, pk, agg_circuit)| {
            b.iter(|| {
                let instances = agg_circuit.instances();
                gen_proof_gwc(
                    params,
                    pk,
                    agg_circuit.clone(),
                    instances,
                    &mut transcript,
                    &mut rng,
                    None,
                );
            })
        },
    );
    group.finish();

    #[cfg(feature = "loader_evm")]
    {
        let deployment_code =
            gen_evm_verifier_shplonk::<AggregationCircuit>(&params, pk.get_vk(), &(), None::<&str>);

        let start2 = start_timer!(|| "Create EVM SHPLONK proof");
        let proof = gen_evm_proof_shplonk(
            &params,
            &pk,
            agg_circuit.clone(),
            agg_circuit.instances(),
            &mut rng,
        );
        end_timer!(start2);

        evm_verify(deployment_code, agg_circuit.instances(), proof);

        let deployment_code =
            gen_evm_verifier_shplonk::<AggregationCircuit>(&params, pk.get_vk(), &(), None::<&str>);

        let start2 = start_timer!(|| "Create EVM GWC proof");
        let proof =
            gen_evm_proof_gwc(&params, &pk, agg_circuit.clone(), agg_circuit.instances(), &mut rng);
        end_timer!(start2);

        evm_verify(deployment_code, agg_circuit.instances(), proof);
    }
}

criterion_group!(benches, bench);
criterion_main!(benches);
