//! Bridge helpers for Midnight (halo2 fork) artifacts.
//!
//! This module is feature-gated (`--features midnight`) so Midnight crates are
//! only pulled when explicitly requested. It currently focuses on parsing and
//! *verifying* Midnight proofs with Midnight's own verifier, returning a typed
//! bundle you can later translate into snark-verifier structures.

#![cfg(feature = "midnight")]

use anyhow::Result;
use blake2b_simd::State as Blake2bState;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    plonk::{prepare, VerifyingKey},
    poly::commitment::{Guard, PolynomialCommitmentScheme},
    poly::kzg::{params::ParamsVerifierKZG, KZGCommitmentScheme},
    transcript::{CircuitTranscript, Transcript},
    utils::SerdeFormat,
};

/// Parsed Midnight artifacts plus a convenience verifier.
#[derive(Clone, Debug)]
pub struct MidnightProofBundle {
    pub params: ParamsVerifierKZG<Bls12>,
    pub vk: VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
    pub instances: Vec<Vec<Fq>>, // outer = instance columns, inner = values
    pub proof: Vec<u8>,
}

impl MidnightProofBundle {
    /// Construct a bundle from already materialized params, verifying key, proof bytes, and instances.
    /// Verification is performed eagerly; any failure returns an error.
    pub fn new(
        params: ParamsVerifierKZG<Bls12>,
        vk: VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
        proof: Vec<u8>,
        instances: Vec<Vec<Fq>>,
    ) -> Result<Self> {
        let bundle = MidnightProofBundle { params, vk, instances, proof };
        bundle.verify()?;
        Ok(bundle)
    }

    /// Deserialize from bytes (VK encoded with RawBytesUnchecked).
    pub fn from_bytes(
        params: ParamsVerifierKZG<Bls12>,
        vk_bytes: &[u8],
        proof: Vec<u8>,
        instances: Vec<Vec<Fq>>,
    ) -> Result<Self> {
        let vk = VerifyingKey::from_bytes::<DummyCircuit>(
            vk_bytes,
            SerdeFormat::RawBytesUnchecked,
            (),
        )?;
        Self::new(params, vk, proof, instances)
    }

    /// Verify the proof using Midnight's native verifier. Instances are assumed non-committed.
    pub fn verify(&self) -> Result<()> {
        // transcript over blake2b like zk-stdlib examples
        let mut transcript = CircuitTranscript::<Blake2bState>::init_from_bytes(&self.proof);

        // committed_instances: none for now (all public inputs are uncommitted here)
        let committed_instances: Vec<
            Vec<<KZGCommitmentScheme<Bls12> as PolynomialCommitmentScheme<Fq>>::Commitment>,
        > = vec![vec![]];
        let committed_slices: Vec<
            &[<KZGCommitmentScheme<Bls12> as PolynomialCommitmentScheme<Fq>>::Commitment],
        > = committed_instances.iter().map(|row| row.as_slice()).collect();

        // shape instances into &[&[&[Fq]]]
        let instance_refs: Vec<Vec<&[Fq]>> =
            vec![self.instances.iter().map(|col| col.as_slice()).collect()];
        let instance_slices: Vec<&[&[Fq]]> = instance_refs.iter().map(|v| v.as_slice()).collect();

        let guard = prepare(
            &self.vk,
            &committed_slices,
            &instance_slices,
            &mut transcript,
        )?;
        guard.verify(&self.params).map_err(|e| anyhow::anyhow!("{:?}", e))?;
        Ok(())
    }
}

/// Dummy circuit type to satisfy VK deserialization. We don't use params.
#[derive(Clone, Debug)]
struct DummyCircuit;

impl midnight_proofs::plonk::Circuit<Fq> for DummyCircuit {
    type Config = ();
    type FloorPlanner = midnight_proofs::circuit::SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        DummyCircuit
    }

    fn configure(_: &mut midnight_proofs::plonk::ConstraintSystem<Fq>) -> Self::Config {}

    fn synthesize(
        &self,
        _config: Self::Config,
        _layouter: impl midnight_proofs::circuit::Layouter<Fq>,
    ) -> Result<(), midnight_proofs::plonk::Error> {
        Ok(())
    }
}
