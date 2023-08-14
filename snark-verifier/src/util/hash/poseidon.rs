#![allow(clippy::needless_range_loop)] // for clarity of matrix operations
use crate::{
    loader::{LoadedScalar, ScalarLoader},
    util::{
        arithmetic::{FieldExt, PrimeField},
        Itertools,
    },
};
use poseidon_rs::poseidon::primitives::Spec as PoseidonSpec; // trait
use std::{iter, marker::PhantomData, mem};

#[cfg(test)]
mod tests;

// struct so we can use PoseidonSpec trait to generate round constants and MDS matrix
#[derive(Debug)]
pub struct Poseidon128Pow5Gen<
    F: PrimeField,
    const T: usize,
    const RATE: usize,
    const R_F: usize,
    const R_P: usize,
    const SECURE_MDS: usize,
> {
    _marker: PhantomData<F>,
}

impl<
        F: PrimeField,
        const T: usize,
        const RATE: usize,
        const R_F: usize,
        const R_P: usize,
        const SECURE_MDS: usize,
    > PoseidonSpec<F, T, RATE> for Poseidon128Pow5Gen<F, T, RATE, R_F, R_P, SECURE_MDS>
{
    fn full_rounds() -> usize {
        R_F
    }

    fn partial_rounds() -> usize {
        R_P
    }

    fn sbox(val: F) -> F {
        val.pow_vartime([5])
    }

    // see "Avoiding insecure matrices" in Section 2.3 of https://eprint.iacr.org/2019/458.pdf
    // most Specs used in practice have SECURE_MDS = 0
    fn secure_mds() -> usize {
        SECURE_MDS
    }
}

// We use the optimized Poseidon implementation described in Supplementary Material Section B of https://eprint.iacr.org/2019/458.pdf
// This involves some further computation of optimized constants and sparse MDS matrices beyond what the Scroll PoseidonSpec generates
// The implementation below is adapted from https://github.com/privacy-scaling-explorations/poseidon

/// `OptimizedPoseidonSpec` holds construction parameters as well as constants that are used in
/// permutation step.
#[derive(Debug, Clone)]
pub struct OptimizedPoseidonSpec<F: PrimeField, const T: usize, const RATE: usize> {
    pub(crate) r_f: usize,
    pub(crate) mds_matrices: MDSMatrices<F, T, RATE>,
    pub(crate) constants: OptimizedConstants<F, T>,
}

/// `OptimizedConstants` has round constants that are added each round. While
/// full rounds has T sized constants there is a single constant for each
/// partial round
#[derive(Debug, Clone)]
pub struct OptimizedConstants<F: PrimeField, const T: usize> {
    pub(crate) start: Vec<[F; T]>,
    pub(crate) partial: Vec<F>,
    pub(crate) end: Vec<[F; T]>,
}

/// The type used to hold the MDS matrix
pub(crate) type Mds<F, const T: usize> = [[F; T]; T];

/// `MDSMatrices` holds the MDS matrix as well as transition matrix which is
/// also called `pre_sparse_mds` and sparse matrices that enables us to reduce
/// number of multiplications in apply MDS step
#[derive(Debug, Clone)]
pub struct MDSMatrices<F: PrimeField, const T: usize, const RATE: usize> {
    pub(crate) mds: MDSMatrix<F, T, RATE>,
    pub(crate) pre_sparse_mds: MDSMatrix<F, T, RATE>,
    pub(crate) sparse_matrices: Vec<SparseMDSMatrix<F, T, RATE>>,
}

/// `SparseMDSMatrix` are in `[row], [hat | identity]` form and used in linear
/// layer of partial rounds instead of the original MDS
#[derive(Debug, Clone)]
pub struct SparseMDSMatrix<F: PrimeField, const T: usize, const RATE: usize> {
    pub(crate) row: [F; T],
    pub(crate) col_hat: [F; RATE],
}

/// `MDSMatrix` is applied to `State` to achive linear layer of Poseidon
#[derive(Clone, Debug)]
pub struct MDSMatrix<F: PrimeField, const T: usize, const RATE: usize>(pub(crate) Mds<F, T>);

impl<F: PrimeField, const T: usize, const RATE: usize> MDSMatrix<F, T, RATE> {
    pub(crate) fn mul_vector(&self, v: &[F; T]) -> [F; T] {
        let mut res = [F::ZERO; T];
        for i in 0..T {
            for j in 0..T {
                res[i] += self.0[i][j] * v[j];
            }
        }
        res
    }

    fn identity() -> Mds<F, T> {
        let mut mds = [[F::ZERO; T]; T];
        for i in 0..T {
            mds[i][i] = F::ONE;
        }
        mds
    }

    /// Multiplies two MDS matrices. Used in sparse matrix calculations
    fn mul(&self, other: &Self) -> Self {
        let mut res = [[F::ZERO; T]; T];
        for i in 0..T {
            for j in 0..T {
                for k in 0..T {
                    res[i][j] += self.0[i][k] * other.0[k][j];
                }
            }
        }
        Self(res)
    }

    fn transpose(&self) -> Self {
        let mut res = [[F::ZERO; T]; T];
        for i in 0..T {
            for j in 0..T {
                res[i][j] = self.0[j][i];
            }
        }
        Self(res)
    }

    fn determinant<const N: usize>(m: [[F; N]; N]) -> F {
        let mut res = F::ONE;
        let mut m = m;
        for i in 0..N {
            let mut pivot = i;
            while m[pivot][i] == F::ZERO {
                pivot += 1;
                assert!(pivot < N, "matrix is not invertible");
            }
            if pivot != i {
                res = -res;
                m.swap(pivot, i);
            }
            res *= m[i][i];
            let inv = m[i][i].invert().unwrap();
            for j in i + 1..N {
                let factor = m[j][i] * inv;
                for k in i + 1..N {
                    m[j][k] -= m[i][k] * factor;
                }
            }
        }
        res
    }

    /// See Section B in Supplementary Material https://eprint.iacr.org/2019/458.pdf
    /// Factorises an MDS matrix `M` into `M'` and `M''` where `M = M' *  M''`.
    /// Resulted `M''` matrices are the sparse ones while `M'` will contribute
    /// to the accumulator of the process
    fn factorise(&self) -> (Self, SparseMDSMatrix<F, T, RATE>) {
        assert_eq!(RATE + 1, T);
        // Given `(t-1 * t-1)` MDS matrix called `hat` constructs the `t * t` matrix in
        // form `[[1 | 0], [0 | m]]`, ie `hat` is the right bottom sub-matrix
        let prime = |hat: Mds<F, RATE>| -> Self {
            let mut prime = Self::identity();
            for (prime_row, hat_row) in prime.iter_mut().skip(1).zip(hat.iter()) {
                for (el_prime, el_hat) in prime_row.iter_mut().skip(1).zip(hat_row.iter()) {
                    *el_prime = *el_hat;
                }
            }
            Self(prime)
        };

        // Given `(t-1)` sized `w_hat` vector constructs the matrix in form
        // `[[m_0_0 | m_0_i], [w_hat | identity]]`
        let prime_prime = |w_hat: [F; RATE]| -> Mds<F, T> {
            let mut prime_prime = Self::identity();
            prime_prime[0] = self.0[0];
            for (row, w) in prime_prime.iter_mut().skip(1).zip(w_hat.iter()) {
                row[0] = *w
            }
            prime_prime
        };

        let w = self.0.iter().skip(1).map(|row| row[0]).collect::<Vec<_>>();
        // m_hat is the `(t-1 * t-1)` right bottom sub-matrix of m := self.0
        let mut m_hat = [[F::ZERO; RATE]; RATE];
        for i in 0..RATE {
            for j in 0..RATE {
                m_hat[i][j] = self.0[i + 1][j + 1];
            }
        }
        // w_hat = m_hat^{-1} * w, where m_hat^{-1} is matrix inverse and * is matrix mult
        // we avoid computing m_hat^{-1} explicitly by using Cramer's rule: https://en.wikipedia.org/wiki/Cramer%27s_rule
        let mut w_hat = [F::ZERO; RATE];
        let det = Self::determinant(m_hat);
        let det_inv = Option::<F>::from(det.invert()).expect("matrix is not invertible");
        for j in 0..RATE {
            let mut m_hat_j = m_hat;
            for i in 0..RATE {
                m_hat_j[i][j] = w[i];
            }
            w_hat[j] = Self::determinant(m_hat_j) * det_inv;
        }
        let m_prime = prime(m_hat);
        let m_prime_prime = prime_prime(w_hat);
        // row = first row of m_prime_prime.transpose() = first column of m_prime_prime
        let row: [F; T] =
            m_prime_prime.iter().map(|row| row[0]).collect::<Vec<_>>().try_into().unwrap();
        // col_hat = first column of m_prime_prime.transpose() without first element = first row of m_prime_prime without first element
        let col_hat: [F; RATE] = m_prime_prime[0][1..].try_into().unwrap();
        (m_prime, SparseMDSMatrix { row, col_hat })
    }
}

impl<F: PrimeField, const T: usize, const RATE: usize> OptimizedPoseidonSpec<F, T, RATE> {
    /// Generate new spec with specific number of full and partial rounds. `SECURE_MDS` is usually 0, but may need to be specified because insecure matrices may sometimes be generated
    pub fn new<const R_F: usize, const R_P: usize, const SECURE_MDS: usize>() -> Self
    where
        F: FieldExt,
    {
        let (round_constants, mds, mds_inv) =
            Poseidon128Pow5Gen::<F, T, RATE, R_F, R_P, SECURE_MDS>::constants();
        let mds = MDSMatrix(mds);
        let inverse_mds = MDSMatrix(mds_inv);

        let constants =
            Self::calculate_optimized_constants(R_F, R_P, round_constants, &inverse_mds);
        let (sparse_matrices, pre_sparse_mds) = Self::calculate_sparse_matrices(R_P, &mds);

        Self {
            r_f: R_F,
            constants,
            mds_matrices: MDSMatrices { mds, sparse_matrices, pre_sparse_mds },
        }
    }

    fn calculate_optimized_constants(
        r_f: usize,
        r_p: usize,
        constants: Vec<[F; T]>,
        inverse_mds: &MDSMatrix<F, T, RATE>,
    ) -> OptimizedConstants<F, T> {
        let (number_of_rounds, r_f_half) = (r_f + r_p, r_f / 2);
        assert_eq!(constants.len(), number_of_rounds);

        // Calculate optimized constants for first half of the full rounds
        let mut constants_start: Vec<[F; T]> = vec![[F::ZERO; T]; r_f_half];
        constants_start[0] = constants[0];
        for (optimized, constants) in
            constants_start.iter_mut().skip(1).zip(constants.iter().skip(1))
        {
            *optimized = inverse_mds.mul_vector(constants);
        }

        // Calculate constants for partial rounds
        let mut acc = constants[r_f_half + r_p];
        let mut constants_partial = vec![F::ZERO; r_p];
        for (optimized, constants) in constants_partial
            .iter_mut()
            .rev()
            .zip(constants.iter().skip(r_f_half).rev().skip(r_f_half))
        {
            let mut tmp = inverse_mds.mul_vector(&acc);
            *optimized = tmp[0];

            tmp[0] = F::ZERO;
            for ((acc, tmp), constant) in acc.iter_mut().zip(tmp).zip(constants.iter()) {
                *acc = tmp + constant
            }
        }
        constants_start.push(inverse_mds.mul_vector(&acc));

        // Calculate optimized constants for ending half of the full rounds
        let mut constants_end: Vec<[F; T]> = vec![[F::ZERO; T]; r_f_half - 1];
        for (optimized, constants) in
            constants_end.iter_mut().zip(constants.iter().skip(r_f_half + r_p + 1))
        {
            *optimized = inverse_mds.mul_vector(constants);
        }

        OptimizedConstants {
            start: constants_start,
            partial: constants_partial,
            end: constants_end,
        }
    }

    fn calculate_sparse_matrices(
        r_p: usize,
        mds: &MDSMatrix<F, T, RATE>,
    ) -> (Vec<SparseMDSMatrix<F, T, RATE>>, MDSMatrix<F, T, RATE>) {
        let mds = mds.transpose();
        let mut acc = mds.clone();
        let mut sparse_matrices = (0..r_p)
            .map(|_| {
                let (m_prime, m_prime_prime) = acc.factorise();
                acc = mds.mul(&m_prime);
                m_prime_prime
            })
            .collect::<Vec<SparseMDSMatrix<F, T, RATE>>>();

        sparse_matrices.reverse();
        (sparse_matrices, acc.transpose())
    }
}

// ================ END OF CONSTRUCTION OF POSEIDON SPEC ====================

// now we get to actual trait based implementation of Poseidon permutation
// this works for any loader, where the two loaders used are NativeLoader (native rust) and Halo2Loader (ZK circuit)
#[derive(Clone, Debug)]
struct State<F: PrimeField, L, const T: usize, const RATE: usize> {
    inner: [L; T],
    _marker: PhantomData<F>,
}

// the transcript hash implementation is the one suggested in the original paper https://eprint.iacr.org/2019/458.pdf
// another reference implementation is https://github.com/privacy-scaling-explorations/halo2wrong/tree/master/transcript/src
impl<F: PrimeField, L: LoadedScalar<F>, const T: usize, const RATE: usize> State<F, L, T, RATE> {
    fn new(inner: [L; T]) -> Self {
        Self { inner, _marker: PhantomData }
    }

    fn default(loader: &L::Loader) -> Self {
        let mut default_state = [F::ZERO; T];
        // from Section 4.2 of https://eprint.iacr.org/2019/458.pdf
        // • Variable-Input-Length Hashing. The capacity value is 2^64 + (o−1) where o the output length.
        // for our transcript use cases, o = 1
        default_state[0] = F::from_u128(1u128 << 64);
        Self::new(default_state.map(|state| loader.load_const(&state)))
    }

    fn loader(&self) -> &L::Loader {
        self.inner[0].loader()
    }

    fn power5_with_constant(value: &L, constant: &F) -> L {
        value.loader().sum_products_with_const(&[(value, &value.square().square())], *constant)
    }

    fn sbox_full(&mut self, constants: &[F; T]) {
        for (state, constant) in self.inner.iter_mut().zip(constants.iter()) {
            *state = Self::power5_with_constant(state, constant);
        }
    }

    fn sbox_part(&mut self, constant: &F) {
        self.inner[0] = Self::power5_with_constant(&self.inner[0], constant);
    }

    fn absorb_with_pre_constants(&mut self, inputs: &[L], pre_constants: &[F; T]) {
        assert!(inputs.len() < T);

        self.inner[0] = self.loader().sum_with_const(&[&self.inner[0]], pre_constants[0]);
        self.inner.iter_mut().zip(pre_constants.iter()).skip(1).zip(inputs).for_each(
            |((state, constant), input)| {
                *state = state.loader().sum_with_const(&[state, input], *constant);
            },
        );
        self.inner
            .iter_mut()
            .zip(pre_constants.iter())
            .skip(1 + inputs.len())
            .enumerate()
            .for_each(|(idx, (state, constant))| {
                *state = state.loader().sum_with_const(
                    &[state],
                    if idx == 0 { F::ONE + constant } else { *constant },
                    // the if idx == 0 { F::ONE } else { F::ZERO } is to pad the input with a single 1 and then 0s
                    // this is the padding suggested in pg 31 of https://eprint.iacr.org/2019/458.pdf and in Section 4.2 (Variable-Input-Length Hashing. The padding consists of one field element being 1, and the remaining elements being 0.)
                );
            });
    }

    fn apply_mds(&mut self, mds: &[[F; T]; T]) {
        self.inner = mds
            .iter()
            .map(|row| {
                self.loader()
                    .sum_with_coeff(&row.iter().cloned().zip(self.inner.iter()).collect_vec())
            })
            .collect_vec()
            .try_into()
            .unwrap();
    }

    fn apply_sparse_mds(&mut self, mds: &SparseMDSMatrix<F, T, RATE>) {
        self.inner = iter::once(
            self.loader()
                .sum_with_coeff(&mds.row.iter().cloned().zip(self.inner.iter()).collect_vec()),
        )
        .chain(mds.col_hat.iter().zip(self.inner.iter().skip(1)).map(|(coeff, state)| {
            self.loader().sum_with_coeff(&[(*coeff, &self.inner[0]), (F::ONE, state)])
        }))
        .collect_vec()
        .try_into()
        .unwrap();
    }
}

/// Poseidon hasher with configurable `RATE`.
#[derive(Debug)]
pub struct Poseidon<F: PrimeField, L, const T: usize, const RATE: usize> {
    spec: OptimizedPoseidonSpec<F, T, RATE>,
    default_state: State<F, L, T, RATE>,
    state: State<F, L, T, RATE>,
    buf: Vec<L>,
}

impl<F: PrimeField, L: LoadedScalar<F>, const T: usize, const RATE: usize> Poseidon<F, L, T, RATE> {
    /// Initialize a poseidon hasher.
    /// Generates a new spec with specific number of full and partial rounds. `SECURE_MDS` is usually 0, but may need to be specified because insecure matrices may sometimes be generated
    pub fn new<const R_F: usize, const R_P: usize, const SECURE_MDS: usize>(
        loader: &L::Loader,
    ) -> Self
    where
        F: FieldExt,
    {
        let default_state = State::default(loader);
        Self {
            spec: OptimizedPoseidonSpec::new::<R_F, R_P, SECURE_MDS>(),
            state: default_state.clone(),
            default_state,
            buf: Vec::new(),
        }
    }

    /// Initialize a poseidon hasher from an existing spec.
    pub fn from_spec(loader: &L::Loader, spec: OptimizedPoseidonSpec<F, T, RATE>) -> Self {
        let default_state = State::default(loader);
        Self { spec, state: default_state.clone(), default_state, buf: Vec::new() }
    }

    /// Reset state to default and clear the buffer.
    pub fn clear(&mut self) {
        self.state = self.default_state.clone();
        self.buf.clear();
    }

    /// Store given `elements` into buffer.
    pub fn update(&mut self, elements: &[L]) {
        self.buf.extend_from_slice(elements);
    }

    /// Consume buffer and perform permutation, then output second element of
    /// state.
    pub fn squeeze(&mut self) -> L {
        let buf = mem::take(&mut self.buf);
        let exact = buf.len() % RATE == 0;

        for chunk in buf.chunks(RATE) {
            self.permutation(chunk);
        }
        if exact {
            self.permutation(&[]);
        }

        self.state.inner[1].clone()
    }

    fn permutation(&mut self, inputs: &[L]) {
        let r_f = self.spec.r_f / 2;
        let mds = self.spec.mds_matrices.mds.0;
        let pre_sparse_mds = self.spec.mds_matrices.pre_sparse_mds.0;
        let sparse_matrices = &self.spec.mds_matrices.sparse_matrices;

        // First half of the full rounds
        let constants = &self.spec.constants.start;
        self.state.absorb_with_pre_constants(inputs, &constants[0]);
        for constants in constants.iter().skip(1).take(r_f - 1) {
            self.state.sbox_full(constants);
            self.state.apply_mds(&mds);
        }
        self.state.sbox_full(constants.last().unwrap());
        self.state.apply_mds(&pre_sparse_mds);

        // Partial rounds
        let constants = &self.spec.constants.partial;
        for (constant, sparse_mds) in constants.iter().zip(sparse_matrices.iter()) {
            self.state.sbox_part(constant);
            self.state.apply_sparse_mds(sparse_mds);
        }

        // Second half of the full rounds
        let constants = &self.spec.constants.end;
        for constants in constants.iter() {
            self.state.sbox_full(constants);
            self.state.apply_mds(&mds);
        }
        self.state.sbox_full(&[F::ZERO; T]);
        self.state.apply_mds(&mds);
    }
}
