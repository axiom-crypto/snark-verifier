//! Hash algorithms.

mod poseidon;

pub use crate::util::hash::poseidon::Poseidon;
#[cfg(feature = "loader_halo2")]
pub(crate) use halo2_base::poseidon::hasher::spec::OptimizedPoseidonSpec;

#[cfg(feature = "loader_evm")]
pub use sha3::{Digest, Keccak256};
