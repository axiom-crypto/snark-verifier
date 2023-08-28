use application::ComputeFlag;

use halo2_base::gates::circuit::CircuitBuilderStage;
use halo2_base::halo2_proofs;
use halo2_base::halo2_proofs::arithmetic::Field;
use halo2_base::halo2_proofs::halo2curves::bn256::Fr;
use halo2_base::utils::fs::gen_srs;
use halo2_proofs::halo2curves as halo2_curves;

use halo2_proofs::{halo2curves::bn256::Bn256, poly::kzg::commitment::ParamsKZG};
use rand::rngs::OsRng;
use snark_verifier_sdk::halo2::aggregation::{AggregationConfigParams, VerifierUniversality};
use snark_verifier_sdk::SHPLONK;
use snark_verifier_sdk::{
    gen_pk,
    halo2::{aggregation::AggregationCircuit, gen_snark_shplonk},
    Snark,
};

mod application {
    use super::halo2_curves::bn256::Fr;
    use super::halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance},
        poly::Rotation,
    };

    use snark_verifier_sdk::CircuitExt;

    #[derive(Clone, Copy)]
    pub struct StandardPlonkConfig {
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
        q_a: Column<Fixed>,
        q_b: Column<Fixed>,
        q_c: Column<Fixed>,
        q_ab: Column<Fixed>,
        constant: Column<Fixed>,
        #[allow(dead_code)]
        instance: Column<Instance>,
    }

    impl StandardPlonkConfig {
        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self {
            let [a, b, c] = [(); 3].map(|_| meta.advice_column());
            let [q_a, q_b, q_c, q_ab, constant] = [(); 5].map(|_| meta.fixed_column());
            let instance = meta.instance_column();

            [a, b, c].map(|column| meta.enable_equality(column));

            meta.create_gate(
                "q_a·a + q_b·b + q_c·c + q_ab·a·b + constant + instance = 0",
                |meta| {
                    let [a, b, c] =
                        [a, b, c].map(|column| meta.query_advice(column, Rotation::cur()));
                    let [q_a, q_b, q_c, q_ab, constant] = [q_a, q_b, q_c, q_ab, constant]
                        .map(|column| meta.query_fixed(column, Rotation::cur()));
                    let instance = meta.query_instance(instance, Rotation::cur());
                    Some(
                        q_a * a.clone()
                            + q_b * b.clone()
                            + q_c * c
                            + q_ab * a * b
                            + constant
                            + instance,
                    )
                },
            );

            StandardPlonkConfig { a, b, c, q_a, q_b, q_c, q_ab, constant, instance }
        }
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    pub enum ComputeFlag {
        All,
        SkipFixed,
        SkipCopy,
    }

    #[derive(Clone)]
    pub struct StandardPlonk(pub Fr, pub ComputeFlag);

    impl CircuitExt<Fr> for StandardPlonk {
        fn num_instance(&self) -> Vec<usize> {
            vec![1]
        }

        fn instances(&self) -> Vec<Vec<Fr>> {
            vec![vec![self.0]]
        }
    }

    impl Circuit<Fr> for StandardPlonk {
        type Config = StandardPlonkConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self(Fr::zero(), self.1)
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            meta.set_minimum_degree(4);
            StandardPlonkConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "",
                |mut region| {
                    region.assign_advice(config.a, 0, Value::known(self.0));
                    region.assign_fixed(config.q_a, 0, -Fr::one());
                    region.assign_advice(config.a, 1, Value::known(-Fr::from(5u64)));
                    if self.1 != ComputeFlag::SkipFixed {
                        for (idx, column) in (1..).zip([
                            config.q_a,
                            config.q_b,
                            config.q_c,
                            config.q_ab,
                            config.constant,
                        ]) {
                            region.assign_fixed(column, 1, Fr::from(idx as u64));
                        }
                    }
                    let a = region.assign_advice(config.a, 2, Value::known(Fr::one()));
                    if self.1 != ComputeFlag::SkipCopy {
                        a.copy_advice(&mut region, config.b, 3);
                        a.copy_advice(&mut region, config.c, 4);
                    }

                    Ok(())
                },
            )
        }
    }
}

fn gen_application_snark(params: &ParamsKZG<Bn256>, flag: ComputeFlag) -> Snark {
    let circuit = application::StandardPlonk(Fr::random(OsRng), flag);

    let pk = gen_pk(params, &circuit, None);
    gen_snark_shplonk(params, &pk, circuit, None::<&str>)
}

fn main() {
    let params_app = gen_srs(8);
    let dummy_snark = gen_application_snark(&params_app, ComputeFlag::All);

    let k = 15u32;
    let params = gen_srs(k);
    let lookup_bits = k as usize - 1;
    let mut agg_circuit = AggregationCircuit::new::<SHPLONK>(
        CircuitBuilderStage::Keygen,
        AggregationConfigParams { degree: k, lookup_bits, ..Default::default() },
        &params,
        vec![dummy_snark],
        VerifierUniversality::PreprocessedAsWitness,
    );
    let agg_config = agg_circuit.calculate_params(Some(10));

    let pk = gen_pk(&params, &agg_circuit, None);
    let break_points = agg_circuit.break_points();

    let snarks = [ComputeFlag::All, ComputeFlag::SkipFixed, ComputeFlag::SkipCopy]
        .map(|flag| gen_application_snark(&params_app, flag));
    for (i, snark) in snarks.into_iter().enumerate() {
        let agg_circuit = AggregationCircuit::new::<SHPLONK>(
            CircuitBuilderStage::Prover,
            agg_config,
            &params,
            vec![snark],
            VerifierUniversality::PreprocessedAsWitness,
        )
        .use_break_points(break_points.clone());
        let _snark = gen_snark_shplonk(&params, &pk, agg_circuit, None::<&str>);
        println!("snark {i} success");
    }
}
