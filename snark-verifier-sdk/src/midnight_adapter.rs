//! Bridge helpers for Midnight (halo2 fork) artifacts.
//!
//! This module is feature-gated (`--features midnight`) so Midnight crates are
//! only pulled when explicitly requested.
//!
//! It exposes:
//! - Native Midnight proof verification (`verify`), and
//! - A bridge path (`verify_with_snark_decider`) that reuses Midnight parsing /
//!   algebraic checks and finalizes the KZG pairing check through
//!   `snark-verifier`'s decider.

#![cfg(feature = "midnight")]

use anyhow::{anyhow, bail, Result};
use blake2b_simd::State as Blake2bState;
use halo2_base::halo2_proofs::halo2curves::{
    bls12_381::{
        Bls12 as HaloBls12, Fq as HaloFq, Fq2 as HaloFq2, Fr as HaloFr, G1Affine as HaloG1Affine,
        G2Affine as HaloG2Affine,
    },
    ff::{Field, PrimeField},
    group::{prime::PrimeCurveAffine, Curve},
    CurveAffine as HaloCurveAffine,
};
use itertools::Itertools;
use midnight_curves::{
    bls12_381::Fp2 as MidnightFp2, Bls12, CurveAffine as MidnightCurveAffine, Fp as MidnightFp, Fq,
    G1Affine as MidnightG1Affine, G1Projective, G2Projective,
};
use midnight_proofs::{
    plonk::{
        prepare, Any, Expression as MidnightExpression, FirstPhase, SecondPhase, ThirdPhase,
        VerifyingKey,
    },
    poly::commitment::{Guard, PolynomialCommitmentScheme},
    poly::kzg::{params::ParamsVerifierKZG, KZGCommitmentScheme},
    transcript::{CircuitTranscript, Transcript as MidnightTranscript},
    utils::{helpers::ProcessedSerdeObject, SerdeFormat},
};
use snark_verifier::{
    loader::native::NativeLoader,
    pcs::{
        kzg::{Gwc19, KzgAccumulator, KzgAs, KzgDecidingKey, LimbsEncoding, Midnight},
        AccumulationDecider,
    },
    util::{
        arithmetic::{Domain, Rotation},
        transcript::{Transcript as SvTranscript, TranscriptRead as SvTranscriptRead},
    },
    verifier::{
        plonk::{
            CommonPolynomial, Expression, PlonkProof, PlonkProtocol, Query, QuotientChunkBase,
            QuotientPolynomial,
        },
        SnarkVerifier,
    },
    Error as SnarkVerifierError,
};
#[cfg(feature = "loader_evm")]
use snark_verifier::{
    loader::{
        evm::{
            compile_solidity, compile_solidity_via_ir, encode_calldata, CompactVerifierArtifacts,
            EvmCodegenMode, EvmLoader,
        },
        EcPointLoader,
    },
    system::halo2::transcript::evm::{EvmProofPointEncoding, EvmTranscript},
};
use std::io;
#[cfg(feature = "loader_evm")]
use std::rc::Rc;

type MidnightCommitment =
    <KZGCommitmentScheme<Bls12> as PolynomialCommitmentScheme<Fq>>::Commitment;
type MidnightGuard = midnight_proofs::poly::kzg::msm::DualMSM<Bls12>;
type HaloAs = KzgAs<HaloBls12, Midnight>;

/// Parsed Midnight artifacts plus a convenience verifier.
#[derive(Clone, Debug)]
pub struct MidnightProofBundle {
    pub params: ParamsVerifierKZG<Bls12>,
    pub vk: VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
    pub committed_instances: Vec<MidnightCommitment>,
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
        Self::new_with_committed_instances(params, vk, proof, vec![], instances)
    }

    /// Construct a bundle without verifying the proof bytes.
    pub fn new_unchecked(
        params: ParamsVerifierKZG<Bls12>,
        vk: VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
        proof: Vec<u8>,
        instances: Vec<Vec<Fq>>,
    ) -> Result<Self> {
        Self::new_unchecked_with_committed_instances(params, vk, proof, vec![], instances)
    }

    /// Construct a bundle with committed and non-committed public instances.
    pub fn new_with_committed_instances(
        params: ParamsVerifierKZG<Bls12>,
        vk: VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
        proof: Vec<u8>,
        committed_instances: Vec<MidnightCommitment>,
        instances: Vec<Vec<Fq>>,
    ) -> Result<Self> {
        let bundle = Self::new_unchecked_with_committed_instances(
            params,
            vk,
            proof,
            committed_instances,
            instances,
        )?;
        bundle.verify()?;
        Ok(bundle)
    }

    /// Construct a bundle with committed and non-committed public instances
    /// without verifying the proof bytes.
    pub fn new_unchecked_with_committed_instances(
        params: ParamsVerifierKZG<Bls12>,
        vk: VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
        proof: Vec<u8>,
        committed_instances: Vec<MidnightCommitment>,
        instances: Vec<Vec<Fq>>,
    ) -> Result<Self> {
        let committed_instances =
            normalize_committed_instances(&vk, committed_instances, instances.len())?;
        Ok(MidnightProofBundle { params, vk, committed_instances, instances, proof })
    }

    /// Deserialize from bytes (VK encoded with RawBytesUnchecked).
    pub fn from_bytes(
        params: ParamsVerifierKZG<Bls12>,
        vk_bytes: &[u8],
        proof: Vec<u8>,
        instances: Vec<Vec<Fq>>,
    ) -> Result<Self> {
        Self::from_bytes_with_committed_instances(params, vk_bytes, proof, vec![], instances)
    }

    /// Deserialize from bytes and include committed instance commitments.
    pub fn from_bytes_with_committed_instances(
        params: ParamsVerifierKZG<Bls12>,
        vk_bytes: &[u8],
        proof: Vec<u8>,
        committed_instances: Vec<MidnightCommitment>,
        instances: Vec<Vec<Fq>>,
    ) -> Result<Self> {
        let vk =
            VerifyingKey::from_bytes::<DummyCircuit>(vk_bytes, SerdeFormat::RawBytesUnchecked, ())?;
        Self::new_with_committed_instances(params, vk, proof, committed_instances, instances)
    }

    /// Deserialize a bundle from bytes without verifying the proof bytes.
    pub fn from_bytes_unchecked(
        params: ParamsVerifierKZG<Bls12>,
        vk_bytes: &[u8],
        proof: Vec<u8>,
        instances: Vec<Vec<Fq>>,
    ) -> Result<Self> {
        Self::from_bytes_unchecked_with_committed_instances(
            params,
            vk_bytes,
            proof,
            vec![],
            instances,
        )
    }

    /// Deserialize from bytes with committed instances without verifying the proof bytes.
    pub fn from_bytes_unchecked_with_committed_instances(
        params: ParamsVerifierKZG<Bls12>,
        vk_bytes: &[u8],
        proof: Vec<u8>,
        committed_instances: Vec<MidnightCommitment>,
        instances: Vec<Vec<Fq>>,
    ) -> Result<Self> {
        let vk =
            VerifyingKey::from_bytes::<DummyCircuit>(vk_bytes, SerdeFormat::RawBytesUnchecked, ())?;
        Self::new_unchecked_with_committed_instances(
            params,
            vk,
            proof,
            committed_instances,
            instances,
        )
    }

    /// Parse proof and derive Midnight's KZG verification guard.
    pub fn prepare_guard(&self) -> Result<MidnightGuard> {
        let mut transcript = CircuitTranscript::<Blake2bState>::init_from_bytes(&self.proof);

        let committed_slices: Vec<&[MidnightCommitment]> =
            vec![self.committed_instances.as_slice()];
        let instance_refs: Vec<Vec<&[Fq]>> =
            vec![self.instances.iter().map(|col| col.as_slice()).collect()];
        let instance_slices: Vec<&[&[Fq]]> = instance_refs.iter().map(|v| v.as_slice()).collect();

        let guard = prepare(&self.vk, &committed_slices, &instance_slices, &mut transcript)?;
        Ok(guard)
    }

    /// Verify the proof using Midnight's native verifier.
    pub fn verify(&self) -> Result<()> {
        let guard = self.prepare_guard()?;
        guard.verify(&self.params).map_err(|e| anyhow!("{e:?}"))?;
        Ok(())
    }

    /// Return a `snark-verifier` native KZG accumulator derived from Midnight's guard.
    pub fn snark_accumulator(&self) -> Result<KzgAccumulator<HaloG1Affine, NativeLoader>> {
        let guard = self.prepare_guard()?;
        let (left_terms, right_terms) = guard.split();

        // Midnight checks e(left, s_g2) * e(right, -g2) == 1, while snark-verifier
        // decider checks e(lhs, g2) * e(rhs, -s_g2) == 1.
        // Map channels accordingly: lhs := right, rhs := left.
        let lhs = evaluate_midnight_msm(right_terms);
        let rhs = evaluate_midnight_msm(left_terms);

        Ok(KzgAccumulator::new(midnight_g1_to_halo_affine(lhs)?, midnight_g1_to_halo_affine(rhs)?))
    }

    /// Build a `snark-verifier` deciding key from Midnight verifier params.
    pub fn snark_deciding_key(&self) -> Result<KzgDecidingKey<HaloBls12>> {
        let s_g2 = self.decode_midnight_s_g2()?;
        Ok(KzgDecidingKey::new(
            HaloG1Affine::generator(),
            HaloG2Affine::generator(),
            midnight_g2_to_halo_affine(s_g2)?,
        ))
    }

    /// Verify the final KZG accumulator using `snark-verifier`'s native decider.
    ///
    /// This path reuses Midnight parsing and algebraic constraints, then delegates
    /// the pairing check to `snark-verifier`.
    pub fn verify_with_snark_decider(&self) -> Result<()> {
        let accumulator = self.snark_accumulator()?;
        let dk = self.snark_deciding_key()?;

        <KzgAs<HaloBls12, Gwc19> as AccumulationDecider<HaloG1Affine, NativeLoader>>::decide_all(
            &dk,
            vec![accumulator],
        )
        .map_err(|e| anyhow!("snark-verifier deciding check failed: {e:?}"))?;
        Ok(())
    }

    /// Fully verify through snark-verifier (protocol + proof + PCS + decider).
    pub fn verify_with_snark_verifier(&self) -> Result<()> {
        let protocol = self.to_snark_protocol()?;
        let dk = self.snark_deciding_key()?;
        let svk = dk.svk();
        let instances = self.full_instances_as_halo_fr()?;
        let committed_instances = self.committed_instances_as_halo_points()?;

        let mut transcript = MidnightSnarkTranscript::init_from_bytes(&self.proof);
        let proof =
            PlonkProof::<HaloG1Affine, NativeLoader, HaloAs>::read_with_committed_instances::<
                _,
                LimbsEncoding<{ crate::LIMBS }, { crate::BITS }>,
            >(&svk, &protocol, &instances, Some(&committed_instances), &mut transcript)
            .map_err(|e| {
                anyhow!("failed to parse midnight proof into snark-verifier proof: {e:?}")
            })?;

        <crate::PlonkVerifier<HaloAs> as SnarkVerifier<HaloG1Affine, NativeLoader>>::verify(
            &dk, &protocol, &instances, &proof,
        )
        .map_err(|e| anyhow!("snark-verifier full verification failed: {e:?}"))?;

        Ok(())
    }

    /// Fully verify through snark-verifier using EVM transcript semantics.
    ///
    /// The proof bytes must be produced with `MidnightEvmHash`.
    #[cfg(feature = "loader_evm")]
    pub fn verify_with_snark_verifier_evm_transcript(&self) -> Result<()> {
        let protocol = self.to_snark_protocol()?;
        let dk = self.snark_deciding_key()?;
        let svk = dk.svk();
        let instances = self.full_instances_as_halo_fr()?;
        let committed_instances = self.committed_instances_as_halo_points()?;

        let mut transcript =
            EvmTranscript::<HaloG1Affine, NativeLoader, _, _>::new(self.proof.as_slice());
        let proof = PlonkProof::<HaloG1Affine, NativeLoader, HaloAs>::read_with_committed_instances::<
            _,
            LimbsEncoding<{ crate::LIMBS }, { crate::BITS }>,
        >(
            &svk,
            &protocol,
            &instances,
            Some(&committed_instances),
            &mut transcript,
        )
        .map_err(|e| {
            anyhow!("failed to parse midnight EVM-transcript proof into snark-verifier proof: {e:?}")
        })?;

        <crate::PlonkVerifier<HaloAs> as SnarkVerifier<HaloG1Affine, NativeLoader>>::verify(
            &dk, &protocol, &instances, &proof,
        )
        .map_err(|e| anyhow!("snark-verifier EVM-transcript verification failed: {e:?}"))?;

        Ok(())
    }

    /// Return KZG accumulators computed via snark-verifier using EVM transcript semantics.
    ///
    /// Useful for debugging EVM verifier/runtime mismatches.
    #[cfg(feature = "loader_evm")]
    pub fn evm_transcript_accumulators(
        &self,
    ) -> Result<Vec<KzgAccumulator<HaloG1Affine, NativeLoader>>> {
        let protocol = self.to_snark_protocol()?;
        let dk = self.snark_deciding_key()?;
        let svk = dk.svk();
        let instances = self.full_instances_as_halo_fr()?;
        let committed_instances = self.committed_instances_as_halo_points()?;

        let mut transcript =
            EvmTranscript::<HaloG1Affine, NativeLoader, _, _>::new(self.proof.as_slice());
        let proof =
            PlonkProof::<HaloG1Affine, NativeLoader, HaloAs>::read_with_committed_instances::<
                _,
                LimbsEncoding<{ crate::LIMBS }, { crate::BITS }>,
            >(&svk, &protocol, &instances, Some(&committed_instances), &mut transcript)
            .map_err(|e| {
                anyhow!(
                "failed to parse midnight EVM-transcript proof into snark-verifier proof: {e:?}"
            )
            })?;

        <crate::PlonkSuccinctVerifier<HaloAs> as SnarkVerifier<HaloG1Affine, NativeLoader>>::verify(
            &svk, &protocol, &instances, &proof,
        )
        .map_err(|e| anyhow!("snark-verifier EVM-transcript succinct verification failed: {e:?}"))
    }

    /// Generate Solidity verifier source code for this Midnight proof protocol.
    ///
    /// The generated contract expects calldata encoded as: instances (32-byte
    /// big-endian words) followed by proof bytes produced with `MidnightEvmHash`.
    #[cfg(feature = "loader_evm")]
    pub fn generate_evm_verifier_solidity(&self) -> Result<String> {
        let loader = self.build_evm_verifier_loader(EvmProofPointEncoding::Uncompressed)?;
        Ok(loader.solidity_code())
    }

    /// Generate Solidity verifier source code expecting compressed proof points
    /// encoded as `[sign_byte || x_coordinate_bytes]`.
    #[cfg(feature = "loader_evm")]
    pub fn generate_evm_verifier_solidity_compressed_proof(&self) -> Result<String> {
        let loader = self.build_evm_verifier_loader(EvmProofPointEncoding::XSignCompressed)?;
        Ok(loader.solidity_code())
    }

    /// Generate deployment bytecode for the Midnight Solidity verifier.
    #[cfg(feature = "loader_evm")]
    pub fn generate_evm_verifier_bytecode(&self) -> Result<Vec<u8>> {
        let solidity = self.generate_evm_verifier_solidity()?;
        Ok(compile_solidity(&solidity))
    }

    /// Generate deployment bytecode for a verifier expecting compressed proof points.
    #[cfg(feature = "loader_evm")]
    pub fn generate_evm_verifier_bytecode_compressed_proof(&self) -> Result<Vec<u8>> {
        let solidity = self.generate_evm_verifier_solidity_compressed_proof()?;
        Ok(compile_solidity(&solidity))
    }

    /// Generate compact verifier runtime + data-page artifacts.
    #[cfg(feature = "loader_evm")]
    pub fn generate_evm_verifier_compact_artifacts(&self) -> Result<CompactVerifierArtifacts> {
        let loader = self.build_evm_verifier_loader_with_mode(
            EvmProofPointEncoding::Uncompressed,
            EvmCodegenMode::Compact,
        )?;
        Ok(loader.compact_verifier_artifacts())
    }

    /// Generate hybrid verifier runtime + data-page artifacts.
    ///
    /// Hybrid mode keeps compact paging/interpreter structure while emitting
    /// dedicated hot scalar memory-memory arithmetic opcodes.
    #[cfg(feature = "loader_evm")]
    pub fn generate_evm_verifier_hybrid_artifacts(&self) -> Result<CompactVerifierArtifacts> {
        let loader = self.build_evm_verifier_loader_with_mode(
            EvmProofPointEncoding::Uncompressed,
            EvmCodegenMode::Hybrid,
        )?;
        Ok(loader.compact_verifier_artifacts())
    }

    /// Encode calldata expected by the generated Solidity verifier.
    ///
    /// The proof bytes must be produced with `MidnightEvmHash`.
    #[cfg(feature = "loader_evm")]
    pub fn encode_evm_calldata(&self) -> Result<Vec<u8>> {
        let instances = self.full_instances_as_halo_fr()?;
        Ok(encode_calldata(&instances, &self.proof))
    }

    /// Deploy and call the generated verifier in local revm.
    ///
    /// Returns gas used by the verification call.
    #[cfg(all(feature = "loader_evm", feature = "revm"))]
    pub fn verify_with_generated_solidity_revm(&self) -> Result<u64> {
        let bytecode = self.generate_evm_verifier_bytecode()?;
        let calldata = self.encode_evm_calldata()?;
        snark_verifier::loader::evm::deploy_and_call(bytecode, calldata)
            .map_err(|err| anyhow!("revm deployment/call failed: {err}"))
    }

    /// Deploy and call a verifier expecting compressed proof points in local revm.
    ///
    /// Returns gas used by the verification call.
    #[cfg(all(feature = "loader_evm", feature = "revm"))]
    pub fn verify_with_generated_solidity_revm_compressed_proof(&self) -> Result<u64> {
        let bytecode = self.generate_evm_verifier_bytecode_compressed_proof()?;
        let calldata = self.encode_evm_calldata()?;
        snark_verifier::loader::evm::deploy_and_call(bytecode, calldata)
            .map_err(|err| anyhow!("revm deployment/call failed: {err}"))
    }

    /// Deploy and call compact verifier/runtime pages in local revm.
    ///
    /// Returns gas used by the verification call.
    #[cfg(all(feature = "loader_evm", feature = "revm"))]
    pub fn verify_with_generated_solidity_revm_compact(&self) -> Result<u64> {
        let compact = self.generate_evm_verifier_compact_artifacts()?;
        let runtime_deployment_code = compile_solidity_via_ir(&compact.runtime_solidity);
        let calldata = self.encode_evm_calldata()?;
        snark_verifier::loader::evm::deploy_compact_and_call(
            compact.page_deployment_codes,
            runtime_deployment_code,
            compact.manifest.program_words,
            calldata,
        )
        .map_err(|err| anyhow!("revm compact deployment/call failed: {err}"))
    }

    /// Deploy and call hybrid verifier/runtime pages in local revm.
    ///
    /// Returns gas used by the verification call.
    #[cfg(all(feature = "loader_evm", feature = "revm"))]
    pub fn verify_with_generated_solidity_revm_hybrid(&self) -> Result<u64> {
        let hybrid = self.generate_evm_verifier_hybrid_artifacts()?;
        let runtime_deployment_code = compile_solidity_via_ir(&hybrid.runtime_solidity);
        let calldata = self.encode_evm_calldata()?;
        snark_verifier::loader::evm::deploy_compact_and_call(
            hybrid.page_deployment_codes,
            runtime_deployment_code,
            hybrid.manifest.program_words,
            calldata,
        )
        .map_err(|err| anyhow!("revm hybrid deployment/call failed: {err}"))
    }

    /// Convert non-committed instances into halo2-axiom `Fr`.
    ///
    /// This is useful for the remaining protocol/proof-level adapter work.
    pub fn instances_as_halo_fr(&self) -> Result<Vec<Vec<HaloFr>>> {
        self.instances
            .iter()
            .map(|column| column.iter().copied().map(midnight_fq_to_halo_fr).collect())
            .collect()
    }

    fn committed_instance_count(&self) -> usize {
        self.vk.cs().num_instance_columns().saturating_sub(self.instances.len())
    }

    fn full_instances_as_halo_fr(&self) -> Result<Vec<Vec<HaloFr>>> {
        let committed_count = self.committed_instance_count();
        let mut full = vec![Vec::new(); committed_count];
        full.extend(self.instances_as_halo_fr()?);
        Ok(full)
    }

    fn committed_instances_as_halo_points(&self) -> Result<Vec<HaloG1Affine>> {
        self.committed_instances.iter().cloned().map(midnight_g1_to_halo_affine).collect()
    }

    fn to_snark_protocol(&self) -> Result<PlonkProtocol<HaloG1Affine>> {
        let committed_instance_count = self.committed_instance_count();
        let num_instance =
            self.full_instances_as_halo_fr()?.into_iter().map(|column| column.len()).collect_vec();
        let builder =
            MidnightProtocolBuilder::new(&self.vk, num_instance, committed_instance_count);
        builder.build()
    }

    fn decode_midnight_s_g2(&self) -> Result<G2Projective> {
        let mut encoded = Vec::new();
        self.params.write(&mut encoded, SerdeFormat::Processed)?;
        let mut slice = encoded.as_slice();
        let s_g2 = G2Projective::read(&mut slice, SerdeFormat::Processed)?;
        if !slice.is_empty() {
            bail!("unexpected trailing bytes while decoding midnight verifier params");
        }
        Ok(s_g2)
    }

    #[cfg(feature = "loader_evm")]
    fn build_evm_verifier_loader(
        &self,
        proof_point_encoding: EvmProofPointEncoding,
    ) -> Result<Rc<EvmLoader>> {
        self.build_evm_verifier_loader_with_mode(proof_point_encoding, EvmCodegenMode::Unrolled)
    }

    #[cfg(feature = "loader_evm")]
    fn build_evm_verifier_loader_with_mode(
        &self,
        proof_point_encoding: EvmProofPointEncoding,
        codegen_mode: EvmCodegenMode,
    ) -> Result<Rc<EvmLoader>> {
        let protocol = self.to_snark_protocol()?;
        let num_instance = protocol.num_instance.clone();
        let dk = self.snark_deciding_key()?;
        let svk = dk.svk();

        let loader = EvmLoader::new_with_mode::<HaloFq, HaloFr>(codegen_mode);
        let protocol = protocol.loaded(&loader);
        let mut transcript = EvmTranscript::<HaloG1Affine, Rc<EvmLoader>, _, _>::new_with_encoding(
            &loader,
            proof_point_encoding,
        );

        let committed_instances = self
            .committed_instances_as_halo_points()?
            .iter()
            .map(|point| loader.ec_point_load_const(point))
            .collect_vec();
        let committed_instances = (!committed_instances.is_empty()).then_some(committed_instances);
        let instances = transcript.load_instances(num_instance);

        let proof =
            PlonkProof::<HaloG1Affine, Rc<EvmLoader>, HaloAs>::read_with_committed_instances::<
                _,
                LimbsEncoding<{ crate::LIMBS }, { crate::BITS }>,
            >(
                &svk, &protocol, &instances, committed_instances.as_deref(), &mut transcript
            )
            .map_err(|e| anyhow!("failed to parse Midnight proof with EVM transcript: {e:?}"))?;

        <crate::PlonkVerifier<HaloAs> as SnarkVerifier<HaloG1Affine, Rc<EvmLoader>>>::verify(
            &dk, &protocol, &instances, &proof,
        )
        .map_err(|e| anyhow!("failed to build EVM verifier for Midnight protocol: {e:?}"))?;

        Ok(loader)
    }
}

fn evaluate_midnight_msm(terms: Vec<(&Fq, &G1Projective)>) -> G1Projective {
    terms.into_iter().fold(G1Projective::default(), |mut acc, (scalar, base)| {
        acc += *base * *scalar;
        acc
    })
}

fn normalize_committed_instances(
    vk: &VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
    mut committed_instances: Vec<MidnightCommitment>,
    num_uncommitted_instances: usize,
) -> Result<Vec<MidnightCommitment>> {
    let total_instance_columns = vk.cs().num_instance_columns();
    if num_uncommitted_instances > total_instance_columns {
        bail!(
            "too many non-committed instance columns: got {num_uncommitted_instances}, max {total_instance_columns}"
        );
    }

    let expected_committed = total_instance_columns - num_uncommitted_instances;
    if committed_instances.is_empty() && expected_committed > 0 {
        committed_instances = vec![MidnightCommitment::default(); expected_committed];
    }
    if committed_instances.len() != expected_committed {
        bail!(
            "committed instance column mismatch: expected {expected_committed}, got {}",
            committed_instances.len()
        );
    }
    Ok(committed_instances)
}

fn midnight_fq_to_halo_fr(value: Fq) -> Result<HaloFr> {
    let source = value.to_repr();
    let source_bytes: &[u8] = source.as_ref();
    let mut target = <HaloFr as PrimeField>::Repr::default();
    let target_bytes = target.as_mut();
    if source_bytes.len() != target_bytes.len() {
        bail!(
            "scalar encoding length mismatch (midnight={}, halo={})",
            source_bytes.len(),
            target_bytes.len()
        );
    }
    target_bytes.copy_from_slice(source_bytes);
    Option::from(HaloFr::from_repr(target))
        .ok_or_else(|| anyhow!("invalid scalar encoding when converting midnight::Fq -> halo::Fr"))
}

fn midnight_g1_to_halo_affine(point: G1Projective) -> Result<HaloG1Affine> {
    let affine = point.to_affine();
    if bool::from(affine.is_identity()) {
        return Ok(HaloG1Affine::identity());
    }

    let coordinates = affine.coordinates().unwrap();
    let x = midnight_fp_to_halo_fq(*coordinates.x())?;
    let y = midnight_fp_to_halo_fq(*coordinates.y())?;
    Option::from(HaloG1Affine::from_xy(x, y))
        .ok_or_else(|| anyhow!("failed to map midnight G1 coordinates into halo G1"))
}

fn midnight_g2_to_halo_affine(point: G2Projective) -> Result<HaloG2Affine> {
    let affine = point.to_affine();
    if bool::from(affine.is_identity()) {
        return Ok(HaloG2Affine::identity());
    }

    let coordinates = affine.coordinates().unwrap();
    let x = midnight_fp2_to_halo_fq2(*coordinates.x())?;
    let y = midnight_fp2_to_halo_fq2(*coordinates.y())?;
    Option::from(HaloG2Affine::from_xy(x, y))
        .ok_or_else(|| anyhow!("failed to map midnight G2 coordinates into halo G2"))
}

fn midnight_fp_to_halo_fq(value: MidnightFp) -> Result<HaloFq> {
    let source = value.to_repr();
    let source_bytes: &[u8] = source.as_ref();
    let mut target = <HaloFq as PrimeField>::Repr::default();
    let target_bytes = target.as_mut();
    if source_bytes.len() != target_bytes.len() {
        bail!(
            "base-field encoding length mismatch (midnight={}, halo={})",
            source_bytes.len(),
            target_bytes.len()
        );
    }
    target_bytes.copy_from_slice(source_bytes);
    Option::from(HaloFq::from_repr(target))
        .ok_or_else(|| anyhow!("invalid base-field encoding during midnight->halo conversion"))
}

fn midnight_fp2_to_halo_fq2(value: MidnightFp2) -> Result<HaloFq2> {
    Ok(HaloFq2 { c0: midnight_fp_to_halo_fq(value.c0())?, c1: midnight_fp_to_halo_fq(value.c1())? })
}

fn halo_fr_to_midnight_fq(value: HaloFr) -> Result<Fq> {
    let source = value.to_repr();
    let source_bytes: &[u8] = source.as_ref();
    let mut target = <Fq as PrimeField>::Repr::default();
    let target_bytes = target.as_mut();
    if source_bytes.len() != target_bytes.len() {
        bail!(
            "scalar encoding length mismatch (halo={}, midnight={})",
            source_bytes.len(),
            target_bytes.len()
        );
    }
    target_bytes.copy_from_slice(source_bytes);
    Option::from(Fq::from_repr(target))
        .ok_or_else(|| anyhow!("invalid scalar encoding when converting halo::Fr -> midnight::Fq"))
}

fn halo_fq_to_midnight_fp(value: HaloFq) -> Result<MidnightFp> {
    let source = value.to_repr();
    let source_bytes: &[u8] = source.as_ref();
    let mut target = <MidnightFp as PrimeField>::Repr::default();
    let target_bytes = target.as_mut();
    if source_bytes.len() != target_bytes.len() {
        bail!(
            "base-field encoding length mismatch (halo={}, midnight={})",
            source_bytes.len(),
            target_bytes.len()
        );
    }
    target_bytes.copy_from_slice(source_bytes);
    Option::from(MidnightFp::from_repr(target))
        .ok_or_else(|| anyhow!("invalid base-field encoding during halo->midnight conversion"))
}

fn halo_g1_to_midnight_projective(point: HaloG1Affine) -> Result<G1Projective> {
    if bool::from(point.is_identity()) {
        return Ok(G1Projective::default());
    }

    let coordinates = point.coordinates().unwrap();
    let x = halo_fq_to_midnight_fp(*coordinates.x())?;
    let y = halo_fq_to_midnight_fp(*coordinates.y())?;
    let affine: MidnightG1Affine = Option::from(MidnightG1Affine::from_xy(x, y))
        .ok_or_else(|| anyhow!("failed to map halo G1 coordinates into midnight G1"))?;
    Ok(affine.to_curve())
}

#[derive(Clone, Debug)]
struct MidnightSnarkTranscript {
    inner: CircuitTranscript<Blake2bState>,
    read_ec_points: usize,
    read_scalars: usize,
}

impl MidnightSnarkTranscript {
    fn init_from_bytes(bytes: &[u8]) -> Self {
        Self {
            inner: CircuitTranscript::<Blake2bState>::init_from_bytes(bytes),
            read_ec_points: 0,
            read_scalars: 0,
        }
    }

    fn map_io_error(err: io::Error) -> SnarkVerifierError {
        SnarkVerifierError::Transcript(err.kind(), err.to_string())
    }

    fn map_conversion_error(err: anyhow::Error) -> SnarkVerifierError {
        SnarkVerifierError::Transcript(io::ErrorKind::InvalidData, err.to_string())
    }
}

impl SvTranscript<HaloG1Affine, NativeLoader> for MidnightSnarkTranscript {
    fn loader(&self) -> &NativeLoader {
        &snark_verifier::loader::native::LOADER
    }

    fn squeeze_challenge(&mut self) -> HaloFr {
        let challenge: Fq = self.inner.squeeze_challenge();
        midnight_fq_to_halo_fr(challenge).expect("midnight challenge must map to halo scalar")
    }

    fn common_ec_point(&mut self, ec_point: &HaloG1Affine) -> Result<(), SnarkVerifierError> {
        let point =
            halo_g1_to_midnight_projective(*ec_point).map_err(Self::map_conversion_error)?;
        self.inner.common(&point).map_err(Self::map_io_error)
    }

    fn common_scalar(&mut self, scalar: &HaloFr) -> Result<(), SnarkVerifierError> {
        let scalar = halo_fr_to_midnight_fq(*scalar).map_err(Self::map_conversion_error)?;
        self.inner.common(&scalar).map_err(Self::map_io_error)
    }
}

impl SvTranscriptRead<HaloG1Affine, NativeLoader> for MidnightSnarkTranscript {
    fn read_scalar(&mut self) -> Result<HaloFr, SnarkVerifierError> {
        let value: Fq = self.inner.read().map_err(|err| {
            SnarkVerifierError::Transcript(
                err.kind(),
                format!("scalar read #{} failed: {}", self.read_scalars, err),
            )
        })?;
        self.read_scalars += 1;
        midnight_fq_to_halo_fr(value).map_err(Self::map_conversion_error)
    }

    fn read_ec_point(&mut self) -> Result<HaloG1Affine, SnarkVerifierError> {
        let value: G1Projective = self.inner.read().map_err(|err| {
            SnarkVerifierError::Transcript(
                err.kind(),
                format!("ec-point read #{} failed: {}", self.read_ec_points, err),
            )
        })?;
        self.read_ec_points += 1;
        midnight_g1_to_halo_affine(value).map_err(Self::map_conversion_error)
    }
}

#[derive(Clone, Debug)]
struct MidnightProtocolBuilder<'a> {
    vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
    cs: &'a midnight_proofs::plonk::ConstraintSystem<Fq>,
    num_instance: Vec<usize>,
    committed_instance_count: usize,
    num_advice: Vec<usize>,
    num_challenge: Vec<usize>,
    advice_index: Vec<usize>,
    challenge_index: Vec<usize>,
    num_fixed: usize,
    num_permutation_fixed: usize,
    num_lookup_z: usize,
    num_trash: usize,
    permutation_chunk_size: usize,
    num_permutation_z: usize,
}

impl<'a> MidnightProtocolBuilder<'a> {
    fn new(
        vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
        num_instance: Vec<usize>,
        committed_instance_count: usize,
    ) -> Self {
        let cs = vk.cs();

        let num_phase =
            cs.advice_column_phase().iter().max().copied().unwrap_or_default() as usize + 1;
        let remap = |phase: Vec<u8>| {
            let num = phase.iter().fold(vec![0; num_phase], |mut acc, phase| {
                acc[*phase as usize] += 1;
                acc
            });
            let index = phase
                .iter()
                .scan(vec![0; num_phase], |state, phase| {
                    let index = state[*phase as usize];
                    state[*phase as usize] += 1;
                    Some(index)
                })
                .collect_vec();
            (num, index)
        };

        let (num_advice, advice_index) = remap(cs.advice_column_phase());
        let (num_challenge, challenge_index) = remap(cs.challenge_phase());
        let num_permutation_fixed = cs.permutation().get_columns().len();
        let permutation_chunk_size = cs.degree() - 2;
        let num_permutation_z = if num_permutation_fixed == 0 {
            0
        } else {
            (num_permutation_fixed + permutation_chunk_size - 1) / permutation_chunk_size
        };

        Self {
            vk,
            cs,
            num_instance,
            committed_instance_count,
            num_advice,
            num_challenge,
            advice_index,
            challenge_index,
            num_fixed: cs.num_fixed_columns(),
            num_permutation_fixed,
            num_lookup_z: cs.lookups().len(),
            num_trash: cs.trashcans().len(),
            permutation_chunk_size,
            num_permutation_z,
        }
    }

    fn build(&self) -> Result<PlonkProtocol<HaloG1Affine>> {
        if self.num_instance.len() != self.cs.num_instance_columns() {
            bail!(
                "instance column mismatch: protocol has {}, provided {}",
                self.cs.num_instance_columns(),
                self.num_instance.len()
            );
        }
        if self.committed_instance_count > self.num_instance.len() {
            bail!(
                "committed instance count {} exceeds total instance columns {}",
                self.committed_instance_count,
                self.num_instance.len()
            );
        }

        let k = self.vk.get_domain().k() as usize;
        let gen = midnight_fq_to_halo_fr(self.vk.get_domain().get_omega())?;
        let domain = Domain::new(k, gen);

        let preprocessed = self
            .vk
            .fixed_commitments()
            .iter()
            .chain(self.vk.permutation().commitments().iter())
            .cloned()
            .map(midnight_g1_to_halo_affine)
            .collect::<Result<Vec<_>>>()?;
        let committed_instance_queries = self.committed_instance_queries();
        let advice_queries = self.advice_queries()?;
        let fixed_queries = self.fixed_queries();

        let evaluations = self
            .committed_instance_queries()
            .into_iter()
            .chain(advice_queries.clone())
            .chain(fixed_queries.clone())
            .chain(self.random_query())
            .chain(self.permutation_fixed_queries())
            .chain(self.permutation_z_queries(true))
            .chain(self.lookup_queries(true))
            .chain(self.trash_queries())
            .collect_vec();

        let queries = committed_instance_queries
            .into_iter()
            .chain(advice_queries)
            .chain(self.permutation_z_queries(false))
            .chain(self.lookup_queries(false))
            .chain(self.trash_queries())
            .chain(fixed_queries)
            .chain(self.permutation_fixed_queries())
            .chain(Some(self.quotient_query()))
            .chain(self.random_query())
            .collect_vec();

        let quotient = self.quotient()?;

        Ok(PlonkProtocol {
            domain,
            domain_as_witness: None,
            preprocessed,
            num_instance: self.num_instance.clone(),
            num_witness: self.num_witness(),
            num_challenge: self.num_challenge_with_system(),
            committed_instance_count: self.committed_instance_count,
            hash_instance_lengths: true,
            trailing_challenges: 0,
            extra_commitments: 0,
            evaluations,
            queries,
            quotient,
            transcript_initial_state: Some(midnight_fq_to_halo_fr(self.vk.transcript_repr())?),
            instance_committing_key: None,
            linearization: None,
            accumulator_indices: vec![],
        })
    }

    fn num_preprocessed(&self) -> usize {
        self.num_fixed + self.num_permutation_fixed
    }

    fn instance_offset(&self) -> usize {
        self.num_preprocessed()
    }

    fn witness_offset(&self) -> usize {
        self.instance_offset() + self.num_instance.len()
    }

    fn advice_offset(&self) -> usize {
        self.witness_offset()
    }

    fn lookup_permuted_offset(&self) -> usize {
        self.advice_offset() + self.num_advice.iter().sum::<usize>()
    }

    fn perm_lookup_offset(&self) -> usize {
        self.lookup_permuted_offset() + 2 * self.num_lookup_z
    }

    fn trash_random_offset(&self) -> usize {
        self.perm_lookup_offset() + self.num_permutation_z + self.num_lookup_z
    }

    fn random_poly_index(&self) -> usize {
        self.trash_random_offset() + self.num_trash
    }

    fn num_witness(&self) -> Vec<usize> {
        self.num_advice
            .iter()
            .copied()
            .chain([
                2 * self.num_lookup_z,
                self.num_permutation_z + self.num_lookup_z,
                self.num_trash + 1,
            ])
            .collect()
    }

    fn num_challenge_with_system(&self) -> Vec<usize> {
        let mut phase_challenges = self.num_challenge.clone();
        *phase_challenges.last_mut().unwrap() += 1; // theta
        phase_challenges.into_iter().chain([2, 1, 1]).collect()
    }

    fn system_challenge_offset(&self) -> usize {
        self.num_challenge.iter().sum()
    }

    fn theta(&self) -> Expression<HaloFr> {
        Expression::Challenge(self.system_challenge_offset())
    }

    fn beta(&self) -> Expression<HaloFr> {
        Expression::Challenge(self.system_challenge_offset() + 1)
    }

    fn gamma(&self) -> Expression<HaloFr> {
        Expression::Challenge(self.system_challenge_offset() + 2)
    }

    fn trash_challenge(&self) -> Expression<HaloFr> {
        Expression::Challenge(self.system_challenge_offset() + 3)
    }

    fn alpha(&self) -> Expression<HaloFr> {
        Expression::Challenge(self.system_challenge_offset() + 4)
    }

    fn rotation_last(&self) -> Rotation {
        Rotation(-((self.cs.blinding_factors() + 1) as i32))
    }

    fn query(
        &self,
        column_type: Any,
        column_index: usize,
        rotation: midnight_proofs::poly::Rotation,
    ) -> Query {
        match column_type {
            Any::Fixed => Query::new(column_index, Rotation(rotation.0)),
            Any::Instance => {
                Query::new(self.instance_offset() + column_index, Rotation(rotation.0))
            }
            Any::Advice(advice) => {
                let phase = advice.phase() as usize;
                let phase_offset = self.num_advice[..phase].iter().sum::<usize>();
                Query::new(
                    self.witness_offset() + phase_offset + self.advice_index[column_index],
                    Rotation(rotation.0),
                )
            }
        }
    }

    fn advice_query_any(phase: u8) -> Result<Any> {
        match phase {
            0 => Ok(Any::advice_in(FirstPhase)),
            1 => Ok(Any::advice_in(SecondPhase)),
            2 => Ok(Any::advice_in(ThirdPhase)),
            _ => bail!("unsupported midnight advice phase {phase}"),
        }
    }

    fn convert_expression(
        &self,
        expression: &MidnightExpression<Fq>,
    ) -> Result<Expression<HaloFr>> {
        match expression {
            MidnightExpression::Constant(scalar) => {
                Ok(Expression::Constant(midnight_fq_to_halo_fr(*scalar)?))
            }
            MidnightExpression::Selector(_) => {
                bail!("unexpected selector in midnight expression (selectors should be fixed)")
            }
            MidnightExpression::Fixed(query) => {
                Ok(self.query(Any::Fixed, query.column_index(), query.rotation()).into())
            }
            MidnightExpression::Advice(query) => {
                let any = Self::advice_query_any(query.phase())?;
                Ok(self.query(any, query.column_index(), query.rotation()).into())
            }
            MidnightExpression::Instance(query) => {
                Ok(self.query(Any::Instance, query.column_index(), query.rotation()).into())
            }
            MidnightExpression::Challenge(challenge) => {
                let phase_offset =
                    self.num_challenge[..challenge.phase() as usize].iter().sum::<usize>();
                Ok(Expression::Challenge(phase_offset + self.challenge_index[challenge.index()]))
            }
            MidnightExpression::Negated(a) => Ok(-self.convert_expression(a)?),
            MidnightExpression::Sum(a, b) => {
                Ok(self.convert_expression(a)? + self.convert_expression(b)?)
            }
            MidnightExpression::Product(a, b) => {
                Ok(self.convert_expression(a)? * self.convert_expression(b)?)
            }
            MidnightExpression::Scaled(a, scalar) => {
                Ok(self.convert_expression(a)? * midnight_fq_to_halo_fr(*scalar)?)
            }
        }
    }

    fn committed_instance_queries(&self) -> Vec<Query> {
        self.cs
            .instance_queries()
            .iter()
            .filter(|(column, _)| column.index() < self.committed_instance_count)
            .map(|(column, rotation)| self.query(Any::Instance, column.index(), *rotation))
            .collect()
    }

    fn advice_queries(&self) -> Result<Vec<Query>> {
        self.cs
            .advice_queries()
            .iter()
            .map(|(column, rotation)| {
                let any = Self::advice_query_any(column.column_type().phase())?;
                Ok(self.query(any, column.index(), *rotation))
            })
            .collect()
    }

    fn fixed_queries(&self) -> Vec<Query> {
        self.cs
            .fixed_queries()
            .iter()
            .map(|(column, rotation)| self.query(Any::Fixed, column.index(), *rotation))
            .collect()
    }

    fn permutation_fixed_queries(&self) -> Vec<Query> {
        (0..self.num_permutation_fixed)
            .map(|i| Query::new(self.num_fixed + i, Rotation(0)))
            .collect()
    }

    fn permutation_poly(&self, i: usize) -> usize {
        self.perm_lookup_offset() + i
    }

    fn permutation_z_queries(&self, eval: bool) -> Vec<Query> {
        if self.num_permutation_z == 0 {
            return vec![];
        }
        if eval {
            (0..self.num_permutation_z)
                .flat_map(|i| {
                    let z = self.permutation_poly(i);
                    let mut queries = vec![Query::new(z, Rotation(0)), Query::new(z, Rotation(1))];
                    if i != self.num_permutation_z - 1 {
                        queries.push(Query::new(z, self.rotation_last()));
                    }
                    queries
                })
                .collect()
        } else {
            (0..self.num_permutation_z)
                .flat_map(|i| {
                    let z = self.permutation_poly(i);
                    vec![Query::new(z, Rotation(0)), Query::new(z, Rotation(1))]
                })
                .chain((0..self.num_permutation_z).rev().skip(1).map(|i| {
                    let z = self.permutation_poly(i);
                    Query::new(z, self.rotation_last())
                }))
                .collect()
        }
    }

    fn lookup_poly(&self, i: usize) -> (usize, usize, usize) {
        let z = self.perm_lookup_offset() + self.num_permutation_z + i;
        let permuted_input = self.lookup_permuted_offset() + 2 * i;
        let permuted_table = permuted_input + 1;
        (z, permuted_input, permuted_table)
    }

    fn lookup_queries(&self, eval: bool) -> Vec<Query> {
        (0..self.num_lookup_z)
            .flat_map(|i| {
                let (z, permuted_input, permuted_table) = self.lookup_poly(i);
                if eval {
                    vec![
                        Query::new(z, Rotation(0)),
                        Query::new(z, Rotation(1)),
                        Query::new(permuted_input, Rotation(0)),
                        Query::new(permuted_input, Rotation(-1)),
                        Query::new(permuted_table, Rotation(0)),
                    ]
                } else {
                    vec![
                        Query::new(z, Rotation(0)),
                        Query::new(permuted_input, Rotation(0)),
                        Query::new(permuted_table, Rotation(0)),
                        Query::new(permuted_input, Rotation(-1)),
                        Query::new(z, Rotation(1)),
                    ]
                }
            })
            .collect()
    }

    fn trash_poly(&self, i: usize) -> usize {
        self.trash_random_offset() + i
    }

    fn trash_queries(&self) -> Vec<Query> {
        (0..self.num_trash).map(|i| Query::new(self.trash_poly(i), Rotation(0))).collect()
    }

    fn random_query(&self) -> Option<Query> {
        Some(Query::new(self.random_poly_index(), Rotation(0)))
    }

    fn quotient_query(&self) -> Query {
        Query::new(self.random_poly_index() + 1, Rotation(0))
    }

    fn l_last(&self) -> Expression<HaloFr> {
        Expression::CommonPolynomial(CommonPolynomial::Lagrange(self.rotation_last().0))
    }

    fn l_blind(&self) -> Expression<HaloFr> {
        (self.rotation_last().0 + 1..0)
            .map(CommonPolynomial::Lagrange)
            .map(Expression::CommonPolynomial)
            .sum()
    }

    fn l_active(&self) -> Expression<HaloFr> {
        Expression::Constant(HaloFr::ONE) - self.l_last() - self.l_blind()
    }

    fn gate_constraints(&self) -> Result<Vec<Expression<HaloFr>>> {
        self.cs
            .gates()
            .iter()
            .flat_map(|gate| gate.polynomials().iter())
            .map(|expr| self.convert_expression(expr))
            .collect()
    }

    fn permutation_constraints(&self) -> Vec<Expression<HaloFr>> {
        let one = Expression::Constant(HaloFr::ONE);
        let l_0 = Expression::<HaloFr>::CommonPolynomial(CommonPolynomial::Lagrange(0));
        let l_last = self.l_last();
        let l_active = self.l_active();
        let identity = Expression::<HaloFr>::CommonPolynomial(CommonPolynomial::Identity);
        let beta = self.beta();
        let gamma = self.gamma();

        let polys = self
            .cs
            .permutation()
            .get_columns()
            .iter()
            .map(|column| {
                self.query(
                    *column.column_type(),
                    column.index(),
                    midnight_proofs::poly::Rotation(0),
                )
            })
            .map(Expression::<HaloFr>::Polynomial)
            .collect_vec();
        let permutation_fixeds = (0..self.num_permutation_fixed)
            .map(|i| Query::new(self.num_fixed + i, Rotation(0)))
            .map(Expression::<HaloFr>::Polynomial)
            .collect_vec();
        let zs = (0..self.num_permutation_z)
            .map(|i| {
                let z = self.permutation_poly(i);
                (
                    Expression::<HaloFr>::Polynomial(Query::new(z, Rotation(0))),
                    Expression::<HaloFr>::Polynomial(Query::new(z, Rotation(1))),
                    Expression::<HaloFr>::Polynomial(Query::new(z, self.rotation_last())),
                )
            })
            .collect_vec();

        let mut constraints = Vec::new();
        if let Some((z_0, _, _)) = zs.first() {
            constraints.push(&l_0 * (&one - z_0));
        }
        if let Some((z_l, _, _)) = zs.last() {
            constraints.push(&l_last * (z_l * z_l - z_l));
        }

        constraints.extend(
            zs.iter()
                .skip(1)
                .zip(zs.iter())
                .map(|((z, _, _), (_, _, z_prev_last))| &l_0 * (z - z_prev_last)),
        );

        constraints.extend(
            zs.iter()
                .zip(polys.chunks(self.permutation_chunk_size))
                .zip(permutation_fixeds.chunks(self.permutation_chunk_size))
                .enumerate()
                .map(|(i, (((z, z_omega, _), polys), permutation_fixeds))| {
                    let left = z_omega
                        * polys
                            .iter()
                            .zip(permutation_fixeds.iter())
                            .map(|(poly, permutation_fixed)| {
                                poly + &beta * permutation_fixed + &gamma
                            })
                            .reduce(|acc, expr| acc * expr)
                            .unwrap();
                    let right = z * polys
                        .iter()
                        .zip(
                            std::iter::successors(
                                Some(HaloFr::DELTA.pow_vartime(&[
                                    (i * self.permutation_chunk_size) as u64,
                                    0,
                                    0,
                                    0,
                                ])),
                                |delta| Some(HaloFr::DELTA * delta),
                            )
                            .map(Expression::Constant),
                        )
                        .map(|(poly, delta)| poly + &beta * &delta * &identity + &gamma)
                        .reduce(|acc, expr| acc * expr)
                        .unwrap();
                    &l_active * (left - right)
                }),
        );

        constraints
    }

    fn lookup_constraints(&self) -> Result<Vec<Expression<HaloFr>>> {
        let one = Expression::Constant(HaloFr::ONE);
        let l_0 = Expression::<HaloFr>::CommonPolynomial(CommonPolynomial::Lagrange(0));
        let l_last = self.l_last();
        let l_active = self.l_active();
        let beta = self.beta();
        let gamma = self.gamma();

        let polys = (0..self.num_lookup_z)
            .map(|i| {
                let (z, permuted_input, permuted_table) = self.lookup_poly(i);
                (
                    Expression::<HaloFr>::Polynomial(Query::new(z, Rotation(0))),
                    Expression::<HaloFr>::Polynomial(Query::new(z, Rotation(1))),
                    Expression::<HaloFr>::Polynomial(Query::new(permuted_input, Rotation(0))),
                    Expression::<HaloFr>::Polynomial(Query::new(permuted_input, Rotation(-1))),
                    Expression::<HaloFr>::Polynomial(Query::new(permuted_table, Rotation(0))),
                )
            })
            .collect_vec();

        let mut constraints = Vec::new();
        for (lookup, (z, z_omega, permuted_input, permuted_input_omega_inv, permuted_table)) in
            self.cs.lookups().iter().zip(polys.iter())
        {
            let input = self.distribute_powers(
                lookup
                    .input_expressions()
                    .iter()
                    .map(|expr| self.convert_expression(expr))
                    .collect::<Result<Vec<_>>>()?,
                self.theta(),
            );
            let table = self.distribute_powers(
                lookup
                    .table_expressions()
                    .iter()
                    .map(|expr| self.convert_expression(expr))
                    .collect::<Result<Vec<_>>>()?,
                self.theta(),
            );

            constraints.push(&l_0 * (&one - z));
            constraints.push(&l_last * (z * z - z));
            constraints.push(
                &l_active
                    * (z_omega * (permuted_input + &beta) * (permuted_table + &gamma)
                        - z * (input + &beta) * (table + &gamma)),
            );
            constraints.push(&l_0 * (permuted_input - permuted_table));
            constraints.push(
                &l_active
                    * (permuted_input - permuted_table)
                    * (permuted_input - permuted_input_omega_inv),
            );
        }
        Ok(constraints)
    }

    fn trash_constraints(&self) -> Result<Vec<Expression<HaloFr>>> {
        self.cs
            .trashcans()
            .iter()
            .enumerate()
            .map(|(i, trash)| {
                let selector = self.convert_expression(trash.selector())?;
                let compressed = self.distribute_powers(
                    trash
                        .constraint_expressions()
                        .iter()
                        .map(|expr| self.convert_expression(expr))
                        .collect::<Result<Vec<_>>>()?,
                    self.trash_challenge(),
                );
                let trash_eval =
                    Expression::Polynomial(Query::new(self.trash_poly(i), Rotation(0)));
                Ok(compressed - (Expression::Constant(HaloFr::ONE) - selector) * trash_eval)
            })
            .collect()
    }

    fn distribute_powers(
        &self,
        expressions: Vec<Expression<HaloFr>>,
        challenge: Expression<HaloFr>,
    ) -> Expression<HaloFr> {
        if expressions.is_empty() {
            Expression::Constant(HaloFr::ZERO)
        } else if expressions.len() == 1 {
            expressions.into_iter().next().unwrap()
        } else {
            Expression::DistributePowers(expressions, challenge.into())
        }
    }

    fn quotient(&self) -> Result<QuotientPolynomial<HaloFr>> {
        let constraints = self
            .gate_constraints()?
            .into_iter()
            .chain(self.permutation_constraints())
            .chain(self.lookup_constraints()?)
            .chain(self.trash_constraints()?)
            .collect_vec();

        Ok(QuotientPolynomial {
            chunk_degree: 1,
            chunk_base: QuotientChunkBase::ZnMinusOne,
            num_chunk_override: Some(self.vk.get_domain().get_quotient_poly_degree()),
            numerator: self.distribute_powers(constraints, self.alpha()),
        })
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
