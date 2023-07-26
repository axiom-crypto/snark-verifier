use ark_std::{end_timer, start_timer};
use halo2_base::gates::builder::{CircuitBuilderStage, BASE_CONFIG_PARAMS};
use halo2_base::utils::fs::gen_srs;

use snark_verifier_sdk::halo2::read_snark;
use snark_verifier_sdk::SHPLONK;
use snark_verifier_sdk::{
    gen_pk,
    halo2::{aggregation::AggregationCircuit, gen_snark_shplonk},
    Snark,
};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;

fn read_snark_from_file(file_name: &str) -> Snark {
    let snark_path = Path::new(file_name);
    let snark = read_snark(snark_path)
        .unwrap_or_else(|e| panic!("Snark not found at {snark_path:?}. {e:?}"));
    snark
}

fn gen_agg_break_points(agg_circuit: AggregationCircuit, path: &Path) -> Vec<Vec<usize>> {
    let file = File::open(path);
    let break_points = match file {
        Ok(file) => {
            let reader = BufReader::new(file);
            let break_points: Vec<Vec<usize>> = serde_json::from_reader(reader).unwrap();
            break_points
        }
        Err(_) => {
            let break_points = agg_circuit.break_points();
            let file = File::create(path).unwrap();
            let writer = BufWriter::new(file);
            serde_json::to_writer(writer, &break_points).unwrap();
            break_points
        }
    };
    break_points
}

fn main() {
    let dummy_snark = read_snark_from_file("./examples/halo2_lib_snarks/range.snark");

    let k = 14u32;
    let params = gen_srs(k);
    let lookup_bits = k as usize - 1;
    BASE_CONFIG_PARAMS.with(|config| {
        config.borrow_mut().lookup_bits = Some(lookup_bits);
        config.borrow_mut().k = k as usize;
    });
    let agg_circuit = AggregationCircuit::new::<SHPLONK>(
        CircuitBuilderStage::Keygen,
        None,
        lookup_bits,
        &params,
        vec![dummy_snark.clone()],
        true,
    );
    agg_circuit.config(k, Some(10));

    let start0 = start_timer!(|| "gen vk & pk");
    let pk = gen_pk(&params, &agg_circuit, Some(Path::new("./examples/agg.pk")));
    end_timer!(start0);
    let break_points = gen_agg_break_points(agg_circuit, Path::new("./examples/break_points.json"));

    let snarks = [
        "./examples/halo2_lib_snarks/range.snark",
        "./examples/halo2_lib_snarks/halo2_lib.snark",
        "./examples/halo2_lib_snarks/poseidon.snark",
    ]
    .map(|file| read_snark_from_file(file));
    // let snarks = [dummy_snark];
    for (i, snark) in snarks.into_iter().enumerate() {
        let agg_circuit = AggregationCircuit::new::<SHPLONK>(
            CircuitBuilderStage::Prover,
            Some(break_points.clone()),
            lookup_bits,
            &params,
            vec![snark],
            true,
        );
        let _snark = gen_snark_shplonk(&params, &pk, agg_circuit, None::<&str>);
        println!("snark {i} success");
    }

    /*
    #[cfg(feature = "loader_evm")]
    {
        // do one more time to verify
        let num_instances = agg_circuit.num_instance();
        let instances = agg_circuit.instances();
        let proof_calldata = gen_evm_proof_shplonk(&params, &pk, agg_circuit, instances.clone());

        let deployment_code = gen_evm_verifier_shplonk::<AggregationCircuit<SHPLONK>>(
            &params,
            pk.get_vk(),
            num_instances,
            Some(Path::new("./examples/standard_plonk.yul")),
        );
        evm_verify(deployment_code, instances, proof_calldata);
    }
    */
}
