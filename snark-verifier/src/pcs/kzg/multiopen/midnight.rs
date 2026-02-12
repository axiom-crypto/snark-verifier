#[cfg(feature = "loader_evm")]
use crate::loader::evm::{EcPoint, EvmLoader, Scalar};
use crate::loader::native::NativeLoader;
use crate::{
    cost::{Cost, CostEstimation},
    loader::{LoadedScalar, Loader, ScalarLoader},
    pcs::{
        kzg::{KzgAccumulator, KzgAs, KzgSuccinctVerifyingKey},
        PolynomialCommitmentScheme, Query,
    },
    util::{
        arithmetic::{CurveAffine, MultiMillerLoop, PrimeField, Rotation},
        msm::Msm,
        transcript::TranscriptRead,
        Itertools,
    },
    Error,
};
use std::collections::{BTreeMap, BTreeSet};
#[cfg(feature = "loader_evm")]
use std::rc::Rc;

/// Verifier of Midnight's KZG multi-open proof format.
///
/// This format differs from halo2's GWC/BDFG encodings and follows the
/// `f_com`, `q_eval_on_x3...`, `pi` layout used in Midnight proofs.
#[derive(Clone, Debug)]
pub struct Midnight;

/// Structured proof of Midnight's KZG multi-open.
#[derive(Clone, Debug)]
pub struct MidnightProof<S, P> {
    x1: S,
    x2: S,
    f_com: P,
    x3: S,
    q_evals_on_x3: Vec<S>,
    x4: S,
    pi: P,
}

impl<M> PolynomialCommitmentScheme<M::G1Affine, NativeLoader> for KzgAs<M, Midnight>
where
    M: MultiMillerLoop,
    M::G1Affine: CurveAffine<ScalarExt = M::Fr, CurveExt = M::G1>,
    M::Fr: PrimeField + Ord,
{
    type VerifyingKey = KzgSuccinctVerifyingKey<M::G1Affine>;
    type Proof = MidnightProof<M::Fr, M::G1Affine>;
    type Output = KzgAccumulator<M::G1Affine, NativeLoader>;

    fn read_proof<T>(
        _: &Self::VerifyingKey,
        queries: &[Query<Rotation>],
        transcript: &mut T,
    ) -> Result<Self::Proof, Error>
    where
        T: TranscriptRead<M::G1Affine, NativeLoader>,
    {
        read_midnight_proof(queries, transcript)
    }

    fn verify(
        svk: &Self::VerifyingKey,
        commitments: &[Msm<M::G1Affine, NativeLoader>],
        z: &M::Fr,
        queries: &[Query<Rotation, M::Fr>],
        proof: &Self::Proof,
    ) -> Result<Self::Output, Error> {
        verify_midnight(svk, commitments, z, queries, proof)
    }
}

#[cfg(feature = "loader_evm")]
impl<M> PolynomialCommitmentScheme<M::G1Affine, Rc<EvmLoader>> for KzgAs<M, Midnight>
where
    M: MultiMillerLoop,
    M::G1Affine: CurveAffine<ScalarExt = M::Fr, CurveExt = M::G1>,
    M::Fr: PrimeField<Repr = [u8; 32]> + Ord,
{
    type VerifyingKey = KzgSuccinctVerifyingKey<M::G1Affine>;
    type Proof = MidnightProof<Scalar, EcPoint>;
    type Output = KzgAccumulator<M::G1Affine, Rc<EvmLoader>>;

    fn read_proof<T>(
        _: &Self::VerifyingKey,
        queries: &[Query<Rotation>],
        transcript: &mut T,
    ) -> Result<Self::Proof, Error>
    where
        T: TranscriptRead<M::G1Affine, Rc<EvmLoader>>,
    {
        read_midnight_proof(queries, transcript)
    }

    fn verify(
        svk: &Self::VerifyingKey,
        commitments: &[Msm<M::G1Affine, Rc<EvmLoader>>],
        z: &Scalar,
        queries: &[Query<Rotation, Scalar>],
        proof: &Self::Proof,
    ) -> Result<Self::Output, Error> {
        verify_midnight(svk, commitments, z, queries, proof)
    }
}

fn read_midnight_proof<C, L, T>(
    queries: &[Query<Rotation>],
    transcript: &mut T,
) -> Result<MidnightProof<L::LoadedScalar, L::LoadedEcPoint>, Error>
where
    C: CurveAffine,
    L: Loader<C>,
    T: TranscriptRead<C, L>,
{
    let (_, point_sets) = construct_intermediate_sets(queries)?;
    let x1 = transcript.squeeze_challenge();
    let x2 = transcript.squeeze_challenge();
    let f_com = transcript.read_ec_point()?;
    let x3 = transcript.squeeze_challenge();
    let q_evals_on_x3 = transcript.read_n_scalars(point_sets.len())?;
    let x4 = transcript.squeeze_challenge();
    let pi = transcript.read_ec_point()?;
    Ok(MidnightProof { x1, x2, f_com, x3, q_evals_on_x3, x4, pi })
}

fn verify_midnight<C, L>(
    svk: &KzgSuccinctVerifyingKey<C>,
    commitments: &[Msm<C, L>],
    z: &L::LoadedScalar,
    queries: &[Query<Rotation, L::LoadedScalar>],
    proof: &MidnightProof<L::LoadedScalar, L::LoadedEcPoint>,
) -> Result<KzgAccumulator<C, L>, Error>
where
    C: CurveAffine,
    L: Loader<C>,
{
    let (commitment_map, point_sets) = construct_intermediate_sets(queries)?;
    if point_sets.len() != proof.q_evals_on_x3.len() {
        return Err(Error::InvalidProtocol(format!(
            "midnight pcs point-set mismatch: expected {}, got {}",
            point_sets.len(),
            proof.q_evals_on_x3.len()
        )));
    }

    let loader = z.loader().clone();
    let shift_points =
        queries.iter().map(|query| (query.shift, z.clone() * &query.loaded_shift)).collect_vec();

    let mut q_coms: Vec<Vec<Msm<C, L>>> = vec![Vec::new(); point_sets.len()];
    let mut q_eval_sets: Vec<Vec<Vec<L::LoadedScalar>>> = vec![Vec::new(); point_sets.len()];
    for com_data in commitment_map.iter() {
        if com_data.poly >= commitments.len() {
            return Err(Error::InvalidProtocol(format!(
                "query references polynomial {}, but commitments has length {}",
                com_data.poly,
                commitments.len()
            )));
        }
        let shifts = &point_sets[com_data.set_index];
        let evals = shifts
            .iter()
            .map(|shift| {
                queries
                    .iter()
                    .find(|query| query.poly == com_data.poly && query.shift == *shift)
                    .map(|query| query.eval.clone())
                    .ok_or_else(|| {
                        Error::InvalidProtocol(format!(
                            "missing evaluation for (poly={}, shift={})",
                            com_data.poly, shift.0
                        ))
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        q_coms[com_data.set_index].push(commitments[com_data.poly].clone());
        q_eval_sets[com_data.set_index].push(evals);
    }

    let num_x1_powers = q_coms.iter().map(|set| set.len()).max().unwrap_or_default();
    let powers_x1 = proof.x1.powers(num_x1_powers);
    let q_coms = q_coms
        .into_iter()
        .map(|msms| {
            msms.into_iter()
                .zip(powers_x1.iter())
                .map(|(msm, scalar)| msm * scalar)
                .sum::<Msm<_, _>>()
        })
        .collect_vec();
    let q_eval_sets = q_eval_sets
        .into_iter()
        .map(|eval_set| evals_inner_product_loaded::<C, L>(&eval_set, &powers_x1, &loader))
        .collect_vec();

    // Reconstruct f(x3) from q-evals and point sets.
    let mut f_eval = loader.load_zero();
    for ((shifts, evals), proof_eval) in
        point_sets.iter().zip(q_eval_sets.iter()).zip(proof.q_evals_on_x3.iter()).rev()
    {
        let points = shifts
            .iter()
            .map(|shift| {
                shift_points
                    .iter()
                    .find(|(candidate, _)| candidate == shift)
                    .map(|(_, point)| point.clone())
                    .ok_or_else(|| {
                        Error::InvalidProtocol(format!("missing query point for shift {}", shift.0))
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let r_eval = lagrange_interpolate_eval_loaded::<C, L>(&points, evals, &proof.x3)?;

        let den =
            points.iter().fold(loader.load_one(), |acc, point| acc * &(proof.x3.clone() - point));
        let den_inv = den.invert().ok_or_else(|| {
            Error::InvalidProtocol(
                "encountered non-invertible denominator while computing f(x3)".to_string(),
            )
        })?;
        let eval = (proof_eval.clone() - r_eval) * &den_inv;
        f_eval = f_eval * &proof.x2 + &eval;
    }

    let final_com = {
        let mut coms = q_coms;
        coms.push(Msm::base(&proof.f_com));
        let powers_x4 = proof.x4.powers(coms.len());
        coms.into_iter().zip(powers_x4.iter()).map(|(msm, scalar)| msm * scalar).sum::<Msm<_, _>>()
    };
    let v = {
        let mut evals = proof.q_evals_on_x3.clone();
        evals.push(f_eval);
        let powers_x4 = proof.x4.powers(evals.len());
        evals
            .into_iter()
            .zip(powers_x4.into_iter())
            .fold(loader.load_zero(), |acc, (eval, pow)| acc + eval * &pow)
    };

    // Midnight verifies: e(pi, s_g2) * e(final_com + x3*pi - v*g, -g2) == 1.
    // snark-verifier accumulator convention is:
    //   e(lhs, g2) * e(rhs, -s_g2) == 1
    // so map lhs <- right term, rhs <- left term.
    let rhs = Msm::base(&proof.pi);
    let lhs = final_com + rhs.clone() * &proof.x3 - Msm::constant(v);
    Ok(KzgAccumulator::new(lhs.evaluate(Some(svk.g)), rhs.evaluate(Some(svk.g))))
}

#[derive(Clone, Debug)]
struct CommitmentData {
    poly: usize,
    set_index: usize,
    point_indices: Vec<usize>,
}

fn construct_intermediate_sets<T>(
    queries: &[Query<Rotation, T>],
) -> Result<(Vec<CommitmentData>, Vec<Vec<Rotation>>), Error> {
    let mut commitment_map: Vec<CommitmentData> = Vec::new();
    let mut points = Vec::<Rotation>::new();

    for query in queries {
        let point_idx =
            points.iter().position(|point| *point == query.shift).unwrap_or_else(|| {
                points.push(query.shift);
                points.len() - 1
            });

        if let Some(pos) = commitment_map.iter().position(|com| com.poly == query.poly) {
            if commitment_map[pos].point_indices.contains(&point_idx) {
                return Err(Error::InvalidProtocol(format!(
                    "duplicated query for poly {} at shift {}",
                    query.poly, query.shift.0
                )));
            }
            commitment_map[pos].point_indices.push(point_idx);
        } else {
            commitment_map.push(CommitmentData {
                poly: query.poly,
                set_index: 0,
                point_indices: vec![point_idx],
            });
        }
    }

    let mut point_idx_sets = BTreeMap::<BTreeSet<usize>, usize>::new();
    for com_data in commitment_map.iter_mut() {
        let point_set = BTreeSet::from_iter(com_data.point_indices.iter().copied());
        let num_sets = point_idx_sets.len();
        let set_index = *point_idx_sets.entry(point_set).or_insert(num_sets);
        com_data.set_index = set_index;
    }

    let mut point_sets = vec![Vec::new(); point_idx_sets.len()];
    for (point_set, set_index) in point_idx_sets.into_iter() {
        point_sets[set_index] = point_set.into_iter().map(|idx| points[idx]).collect();
    }

    Ok((commitment_map, point_sets))
}

fn evals_inner_product_loaded<C, L>(
    evals_set: &[Vec<L::LoadedScalar>],
    scalars: &[L::LoadedScalar],
    loader: &L,
) -> Vec<L::LoadedScalar>
where
    C: CurveAffine,
    L: Loader<C>,
{
    if evals_set.is_empty() {
        return Vec::new();
    }
    let mut result = vec![loader.load_zero(); evals_set[0].len()];
    for (poly_evals, scalar) in evals_set.iter().zip(scalars.iter()) {
        for (acc, eval) in result.iter_mut().zip(poly_evals.iter()) {
            *acc += &(eval.clone() * scalar);
        }
    }
    result
}

fn lagrange_interpolate_eval_loaded<C, L>(
    points: &[L::LoadedScalar],
    evals: &[L::LoadedScalar],
    at: &L::LoadedScalar,
) -> Result<L::LoadedScalar, Error>
where
    C: CurveAffine,
    L: Loader<C>,
{
    if points.len() != evals.len() {
        return Err(Error::InvalidProtocol(format!(
            "lagrange interpolation size mismatch: points={}, evals={}",
            points.len(),
            evals.len()
        )));
    }
    let loader = at.loader().clone();
    if points.is_empty() {
        return Ok(loader.load_zero());
    }
    if points.len() == 1 {
        return Ok(evals[0].clone());
    }

    let mut denom = (0..points.len())
        .map(|j| {
            points
                .iter()
                .enumerate()
                .filter(|(k, _)| *k != j)
                .fold(loader.load_one(), |acc, (_, x_k)| acc * &(points[j].clone() - x_k))
        })
        .collect_vec();
    <L as ScalarLoader<C::ScalarExt>>::batch_invert(denom.iter_mut());

    let value = evals.iter().enumerate().fold(loader.load_zero(), |acc, (j, eval)| {
        let numer = points
            .iter()
            .enumerate()
            .filter(|(k, _)| *k != j)
            .fold(loader.load_one(), |acc, (_, point)| acc * &(at.clone() - point));
        acc + eval.clone() * &numer * &denom[j]
    });
    Ok(value)
}

impl<M> CostEstimation<M::G1Affine> for KzgAs<M, Midnight>
where
    M: MultiMillerLoop,
{
    type Input = Vec<Query<Rotation>>;

    fn estimate_cost(queries: &Vec<Query<Rotation>>) -> Cost {
        let (_, point_sets) = construct_intermediate_sets(queries).unwrap_or_default();
        let num_commitment = point_sets.len() + 2; // f_com and pi are extra points in proof.
        Cost {
            num_commitment,
            num_evaluation: point_sets.len(),
            num_msm: point_sets.len() + 2,
            ..Default::default()
        }
    }
}
