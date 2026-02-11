use std::path::Path;

use halo2_base::halo2_proofs;
use halo2_proofs::halo2curves as halo2_curves;
use halo2_proofs::{halo2curves::bls12_381::Bls12, poly::kzg::commitment::ParamsKZG};
use rand::rngs::OsRng;
#[cfg(feature = "revm")]
use snark_verifier_sdk::evm::evm_verify;
use snark_verifier_sdk::evm::{gen_evm_proof_gwc, gen_evm_verifier_gwc, write_calldata};
use snark_verifier_sdk::{gen_pk, CircuitExt};

mod application {
    use super::halo2_curves::bls12_381::Fr;
    use super::halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance},
        poly::Rotation,
    };
    use rand::RngCore;
    use snark_verifier_sdk::CircuitExt;

    const NUM_ADVICE_COLUMNS: usize = 16;

    #[derive(Clone, Copy)]
    pub struct StandardPlonkConfig {
        #[allow(dead_code)]
        advice: [Column<Advice>; NUM_ADVICE_COLUMNS],
        a: Column<Advice>,
        q_a: Column<Fixed>,
        instance: Column<Instance>,
    }

    impl StandardPlonkConfig {
        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self {
            let advice = [(); NUM_ADVICE_COLUMNS].map(|_| meta.advice_column());
            let a = advice[0];
            let q_a = meta.fixed_column();
            let instance = meta.instance_column();
            for column in advice {
                meta.enable_equality(column);
            }

            meta.create_gate("q_a * a + instance = 0", |meta| {
                let a = meta.query_advice(a, Rotation::cur());
                let q_a = meta.query_fixed(q_a, Rotation::cur());
                let instance = meta.query_instance(instance, Rotation::cur());
                Some(q_a * a + instance)
            });

            StandardPlonkConfig { advice, a, q_a, instance }
        }
    }

    #[derive(Clone, Default)]
    pub struct StandardPlonk(Fr);

    impl StandardPlonk {
        pub fn rand<R: RngCore>(mut rng: R) -> Self {
            Self(Fr::from(rng.next_u32() as u64))
        }
    }

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
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            StandardPlonkConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let _ = config.instance;
            layouter.assign_region(
                || "assign",
                |mut region| {
                    #[cfg(feature = "halo2-pse")]
                    {
                        region.assign_advice(|| "a", config.a, 0, || Value::known(self.0))?;
                        region.assign_fixed(|| "q_a", config.q_a, 0, || Value::known(-Fr::one()))
                    }
                    #[cfg(feature = "halo2-axiom")]
                    {
                        region.assign_advice(config.a, 0, Value::known(self.0));
                        region.assign_fixed(config.q_a, 0, -Fr::one());
                        Ok(())
                    }
                },
            )
        }
    }
}

fn main() {
    let k = 12;
    let params = ParamsKZG::<Bls12>::setup(k, OsRng);
    let circuit = application::StandardPlonk::rand(OsRng);
    let num_instance = circuit.num_instance();
    let instances = circuit.instances();

    let pk = gen_pk(&params, &circuit, None);
    let proof = gen_evm_proof_gwc(&params, &pk, circuit, instances.clone());

    let deployment_code = gen_evm_verifier_gwc::<application::StandardPlonk>(
        &params,
        pk.get_vk(),
        num_instance,
        Some(Path::new("examples/StandardPlonkVerifier.sol")),
    );

    let deployment_bytecode = format!("0x{}", hex::encode(&deployment_code));
    std::fs::write("examples/standard_plonk.bytecode", &deployment_bytecode).unwrap();
    let calldata =
        write_calldata(&instances, &proof, Path::new("examples/standard_plonk.calldata")).unwrap();

    println!("proof size: {}", proof.len());
    println!("deployment code len: {}", deployment_code.len());
    println!("wrote examples/standard_plonk.bytecode");
    println!("wrote examples/standard_plonk.calldata ({} hex chars)", calldata.len());

    #[cfg(feature = "revm")]
    {
        if std::env::var("RUN_REVM").ok().as_deref() == Some("1") {
            match evm_verify(deployment_code, instances, proof) {
                Ok(gas_cost) => println!("gas cost: {}", gas_cost),
                Err(err) => {
                    println!("revm verification failed: {}", err);
                    println!(
                        "note: local revm simulation still reverted; validate against a known BLS-enabled client/node for authoritative verification"
                    );
                }
            }
        } else {
            println!(
                "revm verification skipped (set RUN_REVM=1 to run local revm simulation)"
            );
        }
    }
}
