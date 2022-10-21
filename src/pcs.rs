use crate::{
    loader::{native::NativeLoader, Loader},
    util::{
        arithmetic::{CurveAffine, PrimeField},
        msm::Msm,
        transcript::{TranscriptRead, TranscriptWrite},
    },
    Error,
};
use rand::Rng;
use std::fmt::Debug;

pub mod kzg;

pub trait PolynomialCommitmentScheme<C, L>: Clone + Debug
where
    C: CurveAffine,
    L: Loader<C>,
{
    type Accumulator: Clone + Debug;
}

#[derive(Clone, Debug)]
pub struct Query<F: PrimeField, T = ()> {
    pub poly: usize,
    pub shift: F,
    pub eval: T,
}

impl<F: PrimeField> Query<F> {
    pub fn with_evaluation<T>(self, eval: T) -> Query<F, T> {
        Query { poly: self.poly, shift: self.shift, eval }
    }
}

pub trait MultiOpenScheme<C, L>: PolynomialCommitmentScheme<C, L>
where
    C: CurveAffine,
    L: Loader<C>,
{
    type SuccinctVerifyingKey: Clone + Debug;
    type Proof: Clone + Debug;

    fn read_proof<T>(
        svk: &Self::SuccinctVerifyingKey,
        queries: &[Query<C::Scalar>],
        transcript: &mut T,
    ) -> Result<Self::Proof, Error>
    where
        T: TranscriptRead<C, L>;

    fn succinct_verify(
        svk: &Self::SuccinctVerifyingKey,
        commitments: &[Msm<C, L>],
        point: &L::LoadedScalar,
        queries: &[Query<C::Scalar, L::LoadedScalar>],
        proof: &Self::Proof,
    ) -> Result<Self::Accumulator, Error>;

    // same as succinct_verify except `use_dummy` is boolean loaded scalar
    // if `use_dummy` is 1, then put in dummy values to MSM so constraints are satisfies regardless of `proof` values
    fn succinct_verify_or_dummy(
        _svk: &Self::SuccinctVerifyingKey,
        _commitments: &[Msm<C, L>],
        _point: &L::LoadedScalar,
        _queries: &[Query<C::Scalar, L::LoadedScalar>],
        _proof: &Self::Proof,
        _use_dummy: &L::LoadedScalar,
    ) -> Result<Self::Accumulator, Error> {
        todo!()
    }
}

pub trait Decider<C, L>: PolynomialCommitmentScheme<C, L>
where
    C: CurveAffine,
    L: Loader<C>,
{
    type DecidingKey: Clone + Debug;
    type Output: Clone + Debug;

    fn decide(dk: &Self::DecidingKey, accumulator: Self::Accumulator) -> Self::Output;

    fn decide_all(dk: &Self::DecidingKey, accumulators: Vec<Self::Accumulator>) -> Self::Output;
}

pub trait AccumulationScheme<C, L, PCS>: Clone + Debug
where
    C: CurveAffine,
    L: Loader<C>,
    PCS: PolynomialCommitmentScheme<C, L>,
{
    type VerifyingKey: Clone + Debug;
    type Proof: Clone + Debug;

    fn read_proof<T>(
        vk: &Self::VerifyingKey,
        instances: &[PCS::Accumulator],
        transcript: &mut T,
    ) -> Result<Self::Proof, Error>
    where
        T: TranscriptRead<C, L>;

    fn verify(
        vk: &Self::VerifyingKey,
        instances: &[PCS::Accumulator],
        proof: &Self::Proof,
    ) -> Result<PCS::Accumulator, Error>;
}

pub trait AccumulationSchemeProver<C, PCS>: AccumulationScheme<C, NativeLoader, PCS>
where
    C: CurveAffine,
    PCS: PolynomialCommitmentScheme<C, NativeLoader>,
{
    type ProvingKey: Clone + Debug;

    fn create_proof<T, R>(
        pk: &Self::ProvingKey,
        instances: &[PCS::Accumulator],
        transcript: &mut T,
        rng: R,
    ) -> Result<PCS::Accumulator, Error>
    where
        T: TranscriptWrite<C>,
        R: Rng;
}

pub trait AccumulatorEncoding<C, L, PCS>: Clone + Debug
where
    C: CurveAffine,
    L: Loader<C>,
    PCS: PolynomialCommitmentScheme<C, L>,
{
    fn from_repr(repr: Vec<L::LoadedScalar>) -> Result<PCS::Accumulator, Error>;
}

impl<C, L, PCS> AccumulatorEncoding<C, L, PCS> for ()
where
    C: CurveAffine,
    L: Loader<C>,
    PCS: PolynomialCommitmentScheme<C, L>,
{
    fn from_repr(_: Vec<L::LoadedScalar>) -> Result<PCS::Accumulator, Error> {
        unimplemented!()
    }
}
