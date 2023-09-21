use crate::{
    loader::{native::NativeLoader, LoadedScalar, Loader},
    util::{
        arithmetic::{CurveAffine, Domain, Field, Fraction, PrimeField, Rotation},
        Itertools,
    },
};
use num_integer::Integer;
use num_traits::One;
use serde::{Deserialize, Serialize};
use std::{
    cmp::{max, Ordering},
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
    iter::{self, Sum},
    ops::{Add, Mul, Neg, Sub},
};

/// Domain parameters to be optionally loaded as witnesses
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DomainAsWitness<C, L>
where
    C: CurveAffine,
    L: Loader<C>,
{
    /// 2<sup>k</sup> is the number of rows in the domain
    pub k: L::LoadedScalar,
    /// n = 2<sup>k</sup> is the number of rows in the domain
    pub n: L::LoadedScalar,
    /// Generator of the domain
    pub gen: L::LoadedScalar,
    /// Inverse generator of the domain
    pub gen_inv: L::LoadedScalar,
}

impl<C, L> DomainAsWitness<C, L>
where
    C: CurveAffine,
    L: Loader<C>,
{
    /// Rotate `F::one()` to given `rotation`.
    pub fn rotate_one(&self, rotation: Rotation) -> L::LoadedScalar {
        let loader = self.gen.loader();
        match rotation.0.cmp(&0) {
            Ordering::Equal => loader.load_one(),
            Ordering::Greater => self.gen.pow_const(rotation.0 as u64),
            Ordering::Less => self.gen_inv.pow_const(-rotation.0 as u64),
        }
    }
}

/// Protocol specifying configuration of a PLONK.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PlonkProtocol<C, L = NativeLoader>
where
    C: CurveAffine,
    L: Loader<C>,
{
    #[serde(bound(
        serialize = "C::Scalar: Serialize",
        deserialize = "C::Scalar: Deserialize<'de>"
    ))]
    /// Working domain.
    pub domain: Domain<C::Scalar>,

    #[serde(bound(
        serialize = "L::LoadedScalar: Serialize",
        deserialize = "L::LoadedScalar: Deserialize<'de>"
    ))]
    /// Optional: load `domain.n` and `domain.gen` as a witness
    pub domain_as_witness: Option<DomainAsWitness<C, L>>,

    #[serde(bound(
        serialize = "L::LoadedEcPoint: Serialize",
        deserialize = "L::LoadedEcPoint: Deserialize<'de>"
    ))]
    /// Commitments of preprocessed polynomials.
    pub preprocessed: Vec<L::LoadedEcPoint>,
    /// Number of instances in each instance polynomial.
    pub num_instance: Vec<usize>,
    /// Number of witness polynomials in each phase.
    pub num_witness: Vec<usize>,
    /// Number of challenges to squeeze from transcript after each phase.
    pub num_challenge: Vec<usize>,
    /// Evaluations to read from transcript.
    pub evaluations: Vec<Query>,
    /// [`crate::pcs::PolynomialCommitmentScheme`] queries to verify.
    pub queries: Vec<Query>,
    /// Structure of quotient polynomial.
    pub quotient: QuotientPolynomial<C::Scalar>,
    #[serde(bound(
        serialize = "L::LoadedScalar: Serialize",
        deserialize = "L::LoadedScalar: Deserialize<'de>"
    ))]
    /// Prover and verifier common initial state to write to transcript if any.
    pub transcript_initial_state: Option<L::LoadedScalar>,
    /// Instance polynomials commiting key if any.
    pub instance_committing_key: Option<InstanceCommittingKey<C>>,
    /// Linearization strategy.
    pub linearization: Option<LinearizationStrategy>,
    /// Indices (instance polynomial index, row) of encoded
    /// [`crate::pcs::AccumulationScheme::Accumulator`]s.
    pub accumulator_indices: Vec<Vec<(usize, usize)>>,
}

impl<C, L> PlonkProtocol<C, L>
where
    C: CurveAffine,
    L: Loader<C>,
{
    pub(super) fn langranges(&self) -> impl IntoIterator<Item = i32> {
        let instance_eval_lagrange = self.instance_committing_key.is_none().then(|| {
            let queries = {
                let offset = self.preprocessed.len();
                let range = offset..offset + self.num_instance.len();
                self.quotient
                    .numerator
                    .used_query()
                    .into_iter()
                    .filter(move |query| range.contains(&query.poly))
            };
            let (min_rotation, max_rotation) = queries.fold((0, 0), |(min, max), query| {
                if query.rotation.0 < min {
                    (query.rotation.0, max)
                } else if query.rotation.0 > max {
                    (min, query.rotation.0)
                } else {
                    (min, max)
                }
            });
            let max_instance_len = self.num_instance.iter().max().copied().unwrap_or_default();
            -max_rotation..max_instance_len as i32 + min_rotation.abs()
        });
        self.quotient
            .numerator
            .used_langrange()
            .into_iter()
            .chain(instance_eval_lagrange.into_iter().flatten())
    }
}
impl<C> PlonkProtocol<C>
where
    C: CurveAffine,
{
    /// Loaded `PlonkProtocol` with `preprocessed` and
    /// `transcript_initial_state` loaded as constant.
    pub fn loaded<L: Loader<C>>(&self, loader: &L) -> PlonkProtocol<C, L> {
        let preprocessed = self
            .preprocessed
            .iter()
            .map(|preprocessed| loader.ec_point_load_const(preprocessed))
            .collect();
        let transcript_initial_state = self
            .transcript_initial_state
            .as_ref()
            .map(|transcript_initial_state| loader.load_const(transcript_initial_state));
        PlonkProtocol {
            domain: self.domain.clone(),
            domain_as_witness: None,
            preprocessed,
            num_instance: self.num_instance.clone(),
            num_witness: self.num_witness.clone(),
            num_challenge: self.num_challenge.clone(),
            evaluations: self.evaluations.clone(),
            queries: self.queries.clone(),
            quotient: self.quotient.clone(),
            transcript_initial_state,
            instance_committing_key: self.instance_committing_key.clone(),
            linearization: self.linearization,
            accumulator_indices: self.accumulator_indices.clone(),
        }
    }
}

#[cfg(feature = "loader_halo2")]
mod halo2 {
    use crate::{
        loader::{
            halo2::{EccInstructions, Halo2Loader},
            LoadedScalar, ScalarLoader,
        },
        util::arithmetic::CurveAffine,
        verifier::plonk::PlonkProtocol,
    };
    use halo2_base::utils::bit_length;
    use std::rc::Rc;

    use super::{DomainAsWitness, PrimeField};

    impl<C> PlonkProtocol<C>
    where
        C: CurveAffine,
    {
        /// Loaded `PlonkProtocol` with `preprocessed` and
        /// `transcript_initial_state` loaded as witness, which is useful when
        /// doing recursion.
        pub fn loaded_preprocessed_as_witness<EccChip: EccInstructions<C>>(
            &self,
            loader: &Rc<Halo2Loader<C, EccChip>>,
            load_k_as_witness: bool,
        ) -> PlonkProtocol<C, Rc<Halo2Loader<C, EccChip>>> {
            let domain_as_witness = load_k_as_witness.then(|| {
                let k = loader.assign_scalar(C::Scalar::from(self.domain.k as u64));
                // n = 2^k
                let two = loader.load_const(&C::Scalar::from(2));
                let n = two.pow_var(&k, bit_length(C::Scalar::S as u64) + 1);
                // gen = omega = ROOT_OF_UNITY ^ {2^{S - k}}, where ROOT_OF_UNITY is primitive 2^S root of unity
                // this makes omega a 2^k root of unity
                let root_of_unity = loader.load_const(&C::Scalar::ROOT_OF_UNITY);
                let s = loader.load_const(&C::Scalar::from(C::Scalar::S as u64));
                let exp = two.pow_var(&(s - &k), bit_length(C::Scalar::S as u64)); // if S - k < 0, constraint on max bits will fail
                let gen = root_of_unity.pow_var(&exp, C::Scalar::S as usize); // 2^{S - k} < 2^S for k > 0
                let gen_inv = gen.invert().expect("subgroup generation is invertible");
                DomainAsWitness { k, n, gen, gen_inv }
            });

            let preprocessed = self
                .preprocessed
                .iter()
                .map(|preprocessed| loader.assign_ec_point(*preprocessed))
                .collect();
            let transcript_initial_state = self
                .transcript_initial_state
                .as_ref()
                .map(|transcript_initial_state| loader.assign_scalar(*transcript_initial_state));
            PlonkProtocol {
                domain: self.domain.clone(),
                domain_as_witness,
                preprocessed,
                num_instance: self.num_instance.clone(),
                num_witness: self.num_witness.clone(),
                num_challenge: self.num_challenge.clone(),
                evaluations: self.evaluations.clone(),
                queries: self.queries.clone(),
                quotient: self.quotient.clone(),
                transcript_initial_state,
                instance_committing_key: self.instance_committing_key.clone(),
                linearization: self.linearization,
                accumulator_indices: self.accumulator_indices.clone(),
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum CommonPolynomial {
    Identity,
    Lagrange(i32),
}

#[derive(Clone, Debug)]
pub struct CommonPolynomialEvaluation<C, L>
where
    C: CurveAffine,
    L: Loader<C>,
{
    zn: L::LoadedScalar,
    zn_minus_one: L::LoadedScalar,
    zn_minus_one_inv: Fraction<L::LoadedScalar>,
    identity: L::LoadedScalar,
    lagrange: BTreeMap<i32, Fraction<L::LoadedScalar>>,
}

impl<C, L> CommonPolynomialEvaluation<C, L>
where
    C: CurveAffine,
    L: Loader<C>,
{
    // if `n_as_witness` is Some, then we assume `n_as_witness` has value equal to `domain.n` (i.e., number of rows in the circuit)
    // and is loaded as a witness instead of a constant.
    // The generator of `domain` also depends on `n`.
    pub fn new(
        domain: &Domain<C::Scalar>,
        lagranges: impl IntoIterator<Item = i32>,
        z: &L::LoadedScalar,
        domain_as_witness: &Option<DomainAsWitness<C, L>>,
    ) -> Self {
        let loader = z.loader();

        let lagranges = lagranges.into_iter().sorted().dedup().collect_vec();
        let one = loader.load_one();

        let (zn, n_inv, omegas) = if let Some(domain) = domain_as_witness.as_ref() {
            let zn = z.pow_var(&domain.n, C::Scalar::S as usize + 1);
            let n_inv = domain.n.invert().expect("n is not zero");
            let omegas = lagranges.iter().map(|&i| domain.rotate_one(Rotation(i))).collect_vec();
            (zn, n_inv, omegas)
        } else {
            let zn = z.pow_const(domain.n as u64);
            let n_inv = loader.load_const(&domain.n_inv);
            let omegas = lagranges
                .iter()
                .map(|&i| loader.load_const(&domain.rotate_scalar(C::Scalar::ONE, Rotation(i))))
                .collect_vec();
            (zn, n_inv, omegas)
        };

        let zn_minus_one = zn.clone() - &one;
        let zn_minus_one_inv = Fraction::one_over(zn_minus_one.clone());

        let numer = zn_minus_one.clone() * &n_inv;
        let lagrange_evals = omegas
            .iter()
            .map(|omega| Fraction::new(numer.clone() * omega, z.clone() - omega))
            .collect_vec();

        Self {
            zn,
            zn_minus_one,
            zn_minus_one_inv,
            identity: z.clone(),
            lagrange: lagranges.into_iter().zip(lagrange_evals).collect(),
        }
    }

    pub fn zn(&self) -> &L::LoadedScalar {
        &self.zn
    }

    pub fn zn_minus_one(&self) -> &L::LoadedScalar {
        &self.zn_minus_one
    }

    pub fn zn_minus_one_inv(&self) -> &L::LoadedScalar {
        self.zn_minus_one_inv.evaluated()
    }

    pub fn get(&self, poly: CommonPolynomial) -> &L::LoadedScalar {
        match poly {
            CommonPolynomial::Identity => &self.identity,
            CommonPolynomial::Lagrange(i) => self.lagrange.get(&i).unwrap().evaluated(),
        }
    }

    pub fn denoms(&mut self) -> impl IntoIterator<Item = &'_ mut L::LoadedScalar> {
        self.lagrange
            .iter_mut()
            .map(|(_, value)| value.denom_mut())
            .chain(iter::once(self.zn_minus_one_inv.denom_mut()))
            .flatten()
    }

    pub fn evaluate(&mut self) {
        self.lagrange
            .iter_mut()
            .map(|(_, value)| value)
            .chain(iter::once(&mut self.zn_minus_one_inv))
            .for_each(Fraction::evaluate)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QuotientPolynomial<F: Clone> {
    pub chunk_degree: usize,
    pub numerator: Expression<F>,
}

impl<F: Clone> QuotientPolynomial<F> {
    pub fn num_chunk(&self) -> usize {
        Integer::div_ceil(
            &(self.numerator.degree().checked_sub(1).unwrap_or_default()),
            &self.chunk_degree,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Query {
    pub poly: usize,
    pub rotation: Rotation,
}

impl Query {
    pub fn new<R: Into<Rotation>>(poly: usize, rotation: R) -> Self {
        Self { poly, rotation: rotation.into() }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Expression<F> {
    Constant(F),
    CommonPolynomial(CommonPolynomial),
    Polynomial(Query),
    Challenge(usize),
    Negated(Box<Expression<F>>),
    Sum(Box<Expression<F>>, Box<Expression<F>>),
    Product(Box<Expression<F>>, Box<Expression<F>>),
    Scaled(Box<Expression<F>>, F),
    DistributePowers(Vec<Expression<F>>, Box<Expression<F>>),
}

impl<F: Clone> Expression<F> {
    pub fn evaluate<T: Clone>(
        &self,
        constant: &impl Fn(F) -> T,
        common_poly: &impl Fn(CommonPolynomial) -> T,
        poly: &impl Fn(Query) -> T,
        challenge: &impl Fn(usize) -> T,
        negated: &impl Fn(T) -> T,
        sum: &impl Fn(T, T) -> T,
        product: &impl Fn(T, T) -> T,
        scaled: &impl Fn(T, F) -> T,
    ) -> T {
        let evaluate = |expr: &Expression<F>| {
            expr.evaluate(constant, common_poly, poly, challenge, negated, sum, product, scaled)
        };
        match self {
            Expression::Constant(scalar) => constant(scalar.clone()),
            Expression::CommonPolynomial(poly) => common_poly(*poly),
            Expression::Polynomial(query) => poly(*query),
            Expression::Challenge(index) => challenge(*index),
            Expression::Negated(a) => {
                let a = evaluate(a);
                negated(a)
            }
            Expression::Sum(a, b) => {
                let a = evaluate(a);
                let b = evaluate(b);
                sum(a, b)
            }
            Expression::Product(a, b) => {
                let a = evaluate(a);
                let b = evaluate(b);
                product(a, b)
            }
            Expression::Scaled(a, scalar) => {
                let a = evaluate(a);
                scaled(a, scalar.clone())
            }
            Expression::DistributePowers(exprs, scalar) => {
                assert!(!exprs.is_empty());
                if exprs.len() == 1 {
                    return evaluate(exprs.first().unwrap());
                }
                let mut exprs = exprs.iter();
                let first = evaluate(exprs.next().unwrap());
                let scalar = evaluate(scalar);
                exprs.fold(first, |acc, expr| sum(product(acc, scalar.clone()), evaluate(expr)))
            }
        }
    }

    pub fn degree(&self) -> usize {
        match self {
            Expression::Constant(_) => 0,
            Expression::CommonPolynomial(_) => 1,
            Expression::Polynomial { .. } => 1,
            Expression::Challenge { .. } => 0,
            Expression::Negated(a) => a.degree(),
            Expression::Sum(a, b) => max(a.degree(), b.degree()),
            Expression::Product(a, b) => a.degree() + b.degree(),
            Expression::Scaled(a, _) => a.degree(),
            Expression::DistributePowers(a, b) => {
                a.iter().chain(Some(b.as_ref())).map(Self::degree).max().unwrap_or_default()
            }
        }
    }

    pub fn used_langrange(&self) -> BTreeSet<i32> {
        self.evaluate(
            &|_| None,
            &|poly| match poly {
                CommonPolynomial::Lagrange(i) => Some(BTreeSet::from_iter([i])),
                _ => None,
            },
            &|_| None,
            &|_| None,
            &|a| a,
            &merge_left_right,
            &merge_left_right,
            &|a, _| a,
        )
        .unwrap_or_default()
    }

    pub fn used_query(&self) -> BTreeSet<Query> {
        self.evaluate(
            &|_| None,
            &|_| None,
            &|query| Some(BTreeSet::from_iter([query])),
            &|_| None,
            &|a| a,
            &merge_left_right,
            &merge_left_right,
            &|a, _| a,
        )
        .unwrap_or_default()
    }
}

impl<F: Clone> From<Query> for Expression<F> {
    fn from(query: Query) -> Self {
        Self::Polynomial(query)
    }
}

impl<F: Clone> From<CommonPolynomial> for Expression<F> {
    fn from(common_poly: CommonPolynomial) -> Self {
        Self::CommonPolynomial(common_poly)
    }
}

macro_rules! impl_expression_ops {
    ($trait:ident, $op:ident, $variant:ident, $rhs:ty, $rhs_expr:expr) => {
        impl<F: Clone> $trait<$rhs> for Expression<F> {
            type Output = Expression<F>;
            fn $op(self, rhs: $rhs) -> Self::Output {
                Expression::$variant((self).into(), $rhs_expr(rhs).into())
            }
        }
        impl<F: Clone> $trait<$rhs> for &Expression<F> {
            type Output = Expression<F>;
            fn $op(self, rhs: $rhs) -> Self::Output {
                Expression::$variant((self.clone()).into(), $rhs_expr(rhs).into())
            }
        }
        impl<F: Clone> $trait<&$rhs> for Expression<F> {
            type Output = Expression<F>;
            fn $op(self, rhs: &$rhs) -> Self::Output {
                Expression::$variant((self).into(), $rhs_expr(rhs.clone()).into())
            }
        }
        impl<F: Clone> $trait<&$rhs> for &Expression<F> {
            type Output = Expression<F>;
            fn $op(self, rhs: &$rhs) -> Self::Output {
                Expression::$variant((self.clone()).into(), $rhs_expr(rhs.clone()).into())
            }
        }
    };
}

impl_expression_ops!(Mul, mul, Product, Expression<F>, std::convert::identity);
impl_expression_ops!(Mul, mul, Scaled, F, std::convert::identity);
impl_expression_ops!(Add, add, Sum, Expression<F>, std::convert::identity);
impl_expression_ops!(Sub, sub, Sum, Expression<F>, Neg::neg);

impl<F: Clone> Neg for Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        Expression::Negated(Box::new(self))
    }
}

impl<F: Clone> Neg for &Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        Expression::Negated(Box::new(self.clone()))
    }
}

impl<F: Clone + Default> Sum for Expression<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, item| acc + item).unwrap_or_else(|| Expression::Constant(F::default()))
    }
}

impl<F: Field> One for Expression<F> {
    fn one() -> Self {
        Expression::Constant(F::ONE)
    }
}

fn merge_left_right<T: Ord>(a: Option<BTreeSet<T>>, b: Option<BTreeSet<T>>) -> Option<BTreeSet<T>> {
    match (a, b) {
        (Some(a), None) | (None, Some(a)) => Some(a),
        (Some(mut a), Some(b)) => {
            a.extend(b);
            Some(a)
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum LinearizationStrategy {
    /// Older linearization strategy of GWC19, which has linearization
    /// polynomial that doesn't evaluate to 0, and requires prover to send extra
    /// evaluation of it to verifier.
    WithoutConstant,
    /// Current linearization strategy of GWC19, which has linearization
    /// polynomial that evaluate to 0 by subtracting product of vanishing and
    /// quotient polynomials.
    MinusVanishingTimesQuotient,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct InstanceCommittingKey<C> {
    pub bases: Vec<C>,
    pub constant: Option<C>,
}
