#[cfg(feature = "display")]
use ark_std::{end_timer, start_timer};
use halo2_base::halo2_proofs;
use halo2_proofs::{
    circuit::Value,
    halo2curves::{
        bn256::{Bn256, Fr, G1Affine},
        group::ff::Field,
    },
    plonk::{keygen_pk, keygen_vk, Circuit, ProvingKey, Selector},
    poly::kzg::commitment::ParamsKZG,
};
use itertools::Itertools;
use snark_verifier::{pcs::kzg::LimbsEncoding, verifier, Protocol};
use std::{
    fs::{self, File},
    io::{BufReader, BufWriter},
    path::Path,
};

#[cfg(feature = "loader_evm")]
pub mod evm;
#[cfg(feature = "loader_halo2")]
pub mod halo2;

const LIMBS: usize = 3;
const BITS: usize = 88;

/// PCS be either `Kzg<Bn256, Gwc19>` or `Kzg<Bn256, Bdfg21>`
pub type Plonk<PCS> = verifier::Plonk<PCS, LimbsEncoding<LIMBS, BITS>>;

pub struct Snark {
    pub protocol: Protocol<G1Affine>,
    pub instances: Vec<Vec<Fr>>,
    pub proof: Vec<u8>,
}

impl Snark {
    pub fn new(protocol: Protocol<G1Affine>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) -> Self {
        Self { protocol, instances, proof }
    }
}

impl From<Snark> for SnarkWitness {
    fn from(snark: Snark) -> Self {
        Self {
            protocol: snark.protocol,
            instances: snark
                .instances
                .into_iter()
                .map(|instances| instances.into_iter().map(Value::known).collect_vec())
                .collect(),
            proof: Value::known(snark.proof),
        }
    }
}

#[derive(Clone)]
pub struct SnarkWitness {
    pub protocol: Protocol<G1Affine>,
    pub instances: Vec<Vec<Value<Fr>>>,
    pub proof: Value<Vec<u8>>,
}

impl SnarkWitness {
    pub fn without_witnesses(&self) -> Self {
        SnarkWitness {
            protocol: self.protocol.clone(),
            instances: self
                .instances
                .iter()
                .map(|instances| vec![Value::unknown(); instances.len()])
                .collect(),
            proof: Value::unknown(),
        }
    }

    pub fn proof(&self) -> Value<&[u8]> {
        self.proof.as_ref().map(Vec::as_slice)
    }
}

pub trait CircuitExt<F: Field>: Circuit<F> {
    fn num_instance() -> Vec<usize>;

    fn instances(&self) -> Vec<Vec<F>>;

    fn accumulator_indices() -> Option<Vec<(usize, usize)>> {
        None
    }

    /// Output the simple selector columns (before selector compression) of the circuit
    fn selectors(_: &Self::Config) -> Vec<Selector> {
        vec![]
    }
}

pub fn gen_pk<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    circuit: &C,
    path: Option<&Path>,
) -> ProvingKey<G1Affine> {
    if let Some(path) = path {
        match File::open(path) {
            Ok(f) => {
                #[cfg(feature = "display")]
                let read_time = start_timer!(|| format!("Reading pkey from {path:?}"));

                // TODO: bench if BufReader is indeed faster than Read
                let mut bufreader = BufReader::new(f);
                let pk = ProvingKey::read::<_, C>(&mut bufreader, params)
                    .expect("Reading pkey should not fail");

                #[cfg(feature = "display")]
                end_timer!(read_time);

                pk
            }
            Err(_) => {
                #[cfg(feature = "display")]
                let pk_time = start_timer!(|| "Generating vkey & pkey");

                let vk = keygen_vk(params, circuit).unwrap();
                let pk = keygen_pk(params, vk, circuit).unwrap();

                #[cfg(feature = "display")]
                end_timer!(pk_time);

                #[cfg(feature = "display")]
                let write_time = start_timer!(|| format!("Writing pkey to {path:?}"));

                path.parent().and_then(|dir| fs::create_dir_all(dir).ok()).unwrap();
                let mut f = BufWriter::new(File::create(path).unwrap());
                pk.write(&mut f).unwrap();

                #[cfg(feature = "display")]
                end_timer!(write_time);

                pk
            }
        }
    } else {
        #[cfg(feature = "display")]
        let pk_time = start_timer!(|| "Generating vkey & pkey");

        let vk = keygen_vk(params, circuit).unwrap();
        let pk = keygen_pk(params, vk, circuit).unwrap();

        #[cfg(feature = "display")]
        end_timer!(pk_time);

        pk
    }
}

pub fn read_instances(path: impl AsRef<Path>) -> Result<Vec<Vec<Fr>>, bincode::Error> {
    let f = File::open(path)?;
    let reader = BufReader::new(f);
    let instances: Vec<Vec<[u8; 32]>> = bincode::deserialize_from(reader)?;
    instances
        .into_iter()
        .map(|instance_column| {
            instance_column
                .iter()
                .map(|bytes| {
                    Option::from(Fr::from_bytes(bytes)).ok_or(Box::new(bincode::ErrorKind::Custom(
                        "Invalid finite field point".to_owned(),
                    )))
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect()
}

pub fn write_instances(instances: &[&[Fr]], path: impl AsRef<Path>) {
    let instances: Vec<Vec<[u8; 32]>> = instances
        .iter()
        .map(|instance_column| instance_column.iter().map(|x| x.to_bytes()).collect_vec())
        .collect_vec();
    let f = BufWriter::new(File::create(path).unwrap());
    bincode::serialize_into(f, &instances).unwrap();
}

#[cfg(feature = "zkevm")]
mod zkevm {
    use super::CircuitExt;
    use eth_types::Field;
    use zkevm_circuits::evm_circuit::EvmCircuit;

    impl<F: Field> CircuitExt<F> for EvmCircuit<F> {
        fn instances(&self) -> Vec<Vec<F>> {
            vec![]
        }
        fn num_instance() -> Vec<usize> {
            vec![]
        }
    }
}
