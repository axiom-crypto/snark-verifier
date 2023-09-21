use ark_std::{end_timer, start_timer};
use halo2_base::gates::circuit::builder::BaseCircuitBuilder;
use halo2_base::gates::circuit::{BaseCircuitParams, CircuitBuilderStage};
use halo2_base::gates::{GateInstructions, RangeInstructions};
use halo2_base::halo2_proofs::halo2curves::bn256::Fr;
use halo2_base::utils::fs::gen_srs;

use itertools::Itertools;
use snark_verifier_sdk::halo2::aggregation::{AggregationConfigParams, VerifierUniversality};
use snark_verifier_sdk::SHPLONK;
use snark_verifier_sdk::{
    gen_pk,
    halo2::{aggregation::AggregationCircuit, gen_snark_shplonk},
    Snark,
};

fn generate_circuit(k: u32, fill: bool) -> Snark {
    let lookup_bits = k as usize - 1;
    let circuit_params = BaseCircuitParams {
        k: k as usize,
        num_advice_per_phase: vec![10],
        num_lookup_advice_per_phase: vec![5],
        num_fixed: 1,
        lookup_bits: Some(lookup_bits),
        num_instance_columns: 1,
    };
    let mut builder = BaseCircuitBuilder::new(false).use_params(circuit_params);
    let range = builder.range_chip();

    let ctx = builder.main(0);

    let x = ctx.load_witness(Fr::from(14));
    if fill {
        for _ in 0..2 << k {
            range.gate().add(ctx, x, x);
        }
    }

    let params = gen_srs(k);
    // do not call calculate_params, we want to use fixed params
    let pk = gen_pk(&params, &builder, None);
    // std::fs::remove_file(Path::new("examples/app.pk")).ok();
    // let _pk = gen_pk(&params, &builder, Some(Path::new("examples/app.pk")));
    // let pk = read_pk::<BaseCircuitBuilder<_>>(
    //     Path::new("examples/app.pk"),
    //     builder.config_params.clone(),
    // )
    // .unwrap();
    // std::fs::remove_file(Path::new("examples/app.pk")).ok();
    // builder now has break_point set
    gen_snark_shplonk(&params, &pk, builder, None::<&str>)
}

fn main() {
    let dummy_snark = generate_circuit(9, false);

    let k = 16u32;
    let lookup_bits = k as usize - 1;
    let params = gen_srs(k);
    let mut agg_circuit = AggregationCircuit::new::<SHPLONK>(
        CircuitBuilderStage::Keygen,
        AggregationConfigParams { degree: k, lookup_bits, ..Default::default() },
        &params,
        vec![dummy_snark],
        VerifierUniversality::Full,
    );
    let agg_config = agg_circuit.calculate_params(Some(10));

    let start0 = start_timer!(|| "gen vk & pk");
    let pk = gen_pk(&params, &agg_circuit, None);
    // std::fs::remove_file(Path::new("examples/agg.pk")).ok();
    // let _pk = gen_pk(&params, &agg_circuit, Some(Path::new("examples/agg.pk")));
    end_timer!(start0);
    // let pk = read_pk::<AggregationCircuit>(Path::new("examples/agg.pk"), agg_config).unwrap();
    // std::fs::remove_file(Path::new("examples/agg.pk")).ok();
    let break_points = agg_circuit.break_points();

    let snarks = (10..16).map(|k| generate_circuit(k, true)).collect_vec();
    for (i, snark) in snarks.into_iter().enumerate() {
        let agg_circuit = AggregationCircuit::new::<SHPLONK>(
            CircuitBuilderStage::Prover,
            agg_config,
            &params,
            vec![snark],
            VerifierUniversality::Full,
        )
        .use_break_points(break_points.clone());
        let _snark = gen_snark_shplonk(&params, &pk, agg_circuit, None::<&str>);
        println!("snark {i} success");
    }
}
