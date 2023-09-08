//! Trait based implementation of Poseidon permutation

use halo2_base::poseidon::hasher::{mds::SparseMDSMatrix, spec::OptimizedPoseidonSpec};

use crate::{
    loader::{LoadedScalar, ScalarLoader},
    util::{
        arithmetic::{FieldExt, PrimeField},
        Itertools,
    },
};
use std::{iter, marker::PhantomData, mem};

#[cfg(test)]
mod tests;

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
                .sum_with_coeff(&mds.row().iter().cloned().zip(self.inner.iter()).collect_vec()),
        )
        .chain(mds.col_hat().iter().zip(self.inner.iter().skip(1)).map(|(coeff, state)| {
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
        let r_f = self.spec.r_f() / 2;
        let mds = self.spec.mds_matrices().mds().as_ref();
        let pre_sparse_mds = self.spec.mds_matrices().pre_sparse_mds().as_ref();
        let sparse_matrices = &self.spec.mds_matrices().sparse_matrices();

        // First half of the full rounds
        let constants = self.spec.constants().start();
        self.state.absorb_with_pre_constants(inputs, &constants[0]);
        for constants in constants.iter().skip(1).take(r_f - 1) {
            self.state.sbox_full(constants);
            self.state.apply_mds(mds);
        }
        self.state.sbox_full(constants.last().unwrap());
        self.state.apply_mds(pre_sparse_mds);

        // Partial rounds
        let constants = self.spec.constants().partial();
        for (constant, sparse_mds) in constants.iter().zip(sparse_matrices.iter()) {
            self.state.sbox_part(constant);
            self.state.apply_sparse_mds(sparse_mds);
        }

        // Second half of the full rounds
        let constants = self.spec.constants().end();
        for constants in constants.iter() {
            self.state.sbox_full(constants);
            self.state.apply_mds(mds);
        }
        self.state.sbox_full(&[F::ZERO; T]);
        self.state.apply_mds(mds);
    }
}
