use crate::halo2_proofs::poly::kzg::commitment::ParamsKZG;
use crate::util::arithmetic::MultiMillerLoop;
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

mod native;

#[cfg(feature = "loader_evm")]
mod evm;

#[cfg(feature = "loader_halo2")]
pub(crate) mod halo2;

#[allow(dead_code)]
pub const TESTDATA_DIR: &str = "./src/system/halo2/test/data";

pub const LIMBS: usize = 3;
pub const BITS: usize = 88;

pub fn setup<M: MultiMillerLoop>(k: u32) -> ParamsKZG<M> {
    ParamsKZG::<M>::setup(k, ChaCha20Rng::from_seed(Default::default()))
}

macro_rules! halo2_kzg_config {
    ($zk:expr, $num_proof:expr) => {
        $crate::system::halo2::Config::kzg().set_zk($zk).with_num_proof($num_proof)
    };
    ($zk:expr, $num_proof:expr, $accumulator_indices:expr) => {
        $crate::system::halo2::Config::kzg()
            .set_zk($zk)
            .with_num_proof($num_proof)
            .with_accumulator_indices($accumulator_indices)
    };
}

macro_rules! halo2_kzg_prepare {
    ($k:expr, $config:expr, $create_circuit:expr) => {{
        use $crate::halo2_curves::bn256::Bn256;
        #[allow(unused_imports)]
        use $crate::system::halo2::test::{
            halo2_prepare,
            kzg::{setup, TESTDATA_DIR},
        };

        halo2_prepare!(TESTDATA_DIR, $k, setup::<Bn256>, $config, $create_circuit)
    }};
}

macro_rules! halo2_kzg_create_snark {
    (
        $prover:ty,
        $verifier:ty,
        $transcript_read:ty,
        $transcript_write:ty,
        $encoded_challenge:ty,
        $params:expr,
        $pk:expr,
        $protocol:expr,
        $circuits:expr
    ) => {{
        use $crate::halo2_proofs::poly::kzg::{
            commitment::KZGCommitmentScheme, strategy::SingleStrategy,
        };
        use $crate::system::halo2::test::halo2_create_snark;

        halo2_create_snark!(
            KZGCommitmentScheme<_>,
            $prover,
            $verifier,
            SingleStrategy<_>,
            $transcript_read,
            $transcript_write,
            $encoded_challenge,
            |proof, _| proof,
            $params,
            $pk,
            $protocol,
            $circuits
        )
    }};
}

macro_rules! halo2_kzg_native_verify {
    (
        $plonk_verifier:ty,
        $params:expr,
        $protocol:expr,
        $instances:expr,
        $transcript:expr
    ) => {{
        use $crate::system::halo2::test::halo2_native_verify;

        halo2_native_verify!(
            $plonk_verifier,
            $params,
            $protocol,
            $instances,
            $transcript,
            &$params.get_g()[0].into(),
            &($params.g2(), $params.s_g2()).into()
        )
    }};
}

pub(crate) use {
    halo2_kzg_config, halo2_kzg_create_snark, halo2_kzg_native_verify, halo2_kzg_prepare,
};
