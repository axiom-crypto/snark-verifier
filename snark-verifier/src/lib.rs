#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::upper_case_acronyms)]

pub mod cost;
pub mod loader;
pub mod pcs;
pub mod system;
pub mod util;
pub mod verifier;

pub(crate) use halo2_base::halo2_proofs;
pub(crate) use halo2_base::poseidon;
pub(crate) use halo2_proofs::halo2curves as halo2_curves;
use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Debug)]
pub enum Error {
    InvalidInstances,
    InvalidLinearization,
    InvalidQuery(util::protocol::Query),
    InvalidChallenge(usize),
    AssertionFailure(String),
    Transcript(std::io::ErrorKind, String),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Protocol<C, L = loader::native::NativeLoader>
where
    C: util::arithmetic::CurveAffine,
    L: loader::Loader<C>,
{
    // Common description
    #[serde(bound(
        serialize = "C::Scalar: Serialize",
        deserialize = "C::Scalar: Deserialize<'de>"
    ))]
    pub domain: util::arithmetic::Domain<C::Scalar>,
    #[serde(bound(
        serialize = "L::LoadedEcPoint: Serialize",
        deserialize = "L::LoadedEcPoint: Deserialize<'de>"
    ))]
    pub preprocessed: Vec<L::LoadedEcPoint>,
    pub num_instance: Vec<usize>,
    pub num_witness: Vec<usize>,
    pub num_challenge: Vec<usize>,
    pub evaluations: Vec<util::protocol::Query>,
    pub queries: Vec<util::protocol::Query>,
    pub quotient: util::protocol::QuotientPolynomial<C::Scalar>,
    // Minor customization
    #[serde(bound(
        serialize = "L::LoadedScalar: Serialize",
        deserialize = "L::LoadedScalar: Deserialize<'de>"
    ))]
    pub transcript_initial_state: Option<L::LoadedScalar>,
    pub instance_committing_key: Option<util::protocol::InstanceCommittingKey<C>>,
    pub linearization: Option<util::protocol::LinearizationStrategy>,
    pub accumulator_indices: Vec<Vec<(usize, usize)>>,
}
