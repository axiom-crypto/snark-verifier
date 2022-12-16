use crate::{
    loader::Loader,
    pcs::{Decider, MultiOpenScheme},
    util::{arithmetic::CurveAffine, transcript::TranscriptRead},
    Protocol,
};
use std::fmt::Debug;

mod plonk;

pub use plonk::{Plonk, PlonkProof};

pub trait PlonkVerifier<C, L, MOS>
where
    C: CurveAffine,
    L: Loader<C>,
    MOS: MultiOpenScheme<C, L>,
{
    type Proof: Clone + Debug;

    fn read_proof<T>(
        svk: &MOS::SuccinctVerifyingKey,
        protocol: &Protocol<C, L>,
        instances: &[Vec<L::LoadedScalar>],
        transcript: &mut T,
    ) -> Self::Proof
    where
        T: TranscriptRead<C, L>;

    fn succinct_verify(
        svk: &MOS::SuccinctVerifyingKey,
        protocol: &Protocol<C, L>,
        instances: &[Vec<L::LoadedScalar>],
        proof: &Self::Proof,
    ) -> Vec<MOS::Accumulator>;

    fn verify(
        svk: &MOS::SuccinctVerifyingKey,
        dk: &MOS::DecidingKey,
        protocol: &Protocol<C, L>,
        instances: &[Vec<L::LoadedScalar>],
        proof: &Self::Proof,
    ) -> MOS::Output
    where
        MOS: Decider<C, L>,
    {
        let accumulators = Self::succinct_verify(svk, protocol, instances, proof);
        MOS::decide_all(dk, accumulators)
    }
}
