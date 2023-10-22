//! Generic (S)NARK verifier.

#![allow(clippy::type_complexity, clippy::too_many_arguments, clippy::upper_case_acronyms)]
#![deny(missing_debug_implementations, missing_docs, unsafe_code, rustdoc::all)]

pub mod cost;
pub mod loader;
pub mod pcs;
pub mod system;
pub mod util;
pub mod verifier;

pub(crate) use halo2_base::halo2_proofs;
pub(crate) use halo2_proofs::halo2curves as halo2_curves;

pub use halo2_base;
#[cfg(feature = "loader_halo2")]
pub use halo2_ecc;

/// Error that could happen while verification.
#[derive(Clone, Debug)]
pub enum Error {
    /// Instances that don't match the amount specified in protocol.
    InvalidInstances,
    /// Protocol that is unreasonable for a verifier.
    InvalidProtocol(String),
    /// Assertion failure while verification.
    AssertionFailure(String),
    /// Transcript error.
    Transcript(std::io::ErrorKind, String),
}
