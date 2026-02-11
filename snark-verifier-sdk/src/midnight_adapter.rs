//! Bridge helpers for verifying Midnight (halo2 fork) proofs with snark-verifier.
//!
//! This module is intentionally feature-gated (`--features midnight`) so it
//! does not pull Midnight crates unless explicitly requested. The actual glue
//! logic should:
//! - parse Midnight VK/proof artifacts,
//! - map transcript order (committed instances + trash argument),
//! - build a `snark_verifier::verifier::plonk::PlonkProtocol` and `PlonkProof`.
//!
//! The scaffolding below keeps the interface stable while you flesh out the
//! conversions.

#![cfg(feature = "midnight")]

use anyhow::{bail, Result};
use snark_verifier::verifier::plonk::PlonkProtocol;
use snark_verifier::util::arithmetic::CurveAffine;

/// Placeholder for a fully converted Midnight proof bundle.
pub struct MidnightProofBundle<C: CurveAffine> {
    pub protocol: PlonkProtocol<C>,
    pub instances: Vec<Vec<C::Scalar>>,
    /// Serialized proof bytes (conversion to `PlonkProof` pending).
    pub proof: Vec<u8>,
}

impl<C: CurveAffine> MidnightProofBundle<C> {
    /// TODO: implement by reading Midnight artifacts and converting to snark-verifier types.
    pub fn from_midnight_artifacts(
        _vk_bytes: &[u8],
        _proof_bytes: &[u8],
        _instances: Vec<Vec<C::Scalar>>,
    ) -> Result<Self> {
        bail!("midnight adapter not implemented yet")
    }
}
