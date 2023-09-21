//! `Loader` implementation in native rust.

use crate::{
    loader::{EcPointLoader, LoadedEcPoint, LoadedScalar, Loader, ScalarLoader},
    util::arithmetic::{fe_to_big, Curve, CurveAffine, FieldOps, PrimeField},
    Error,
};
use lazy_static::lazy_static;
use std::fmt::Debug;

lazy_static! {
    /// NativeLoader instance for [`LoadedEcPoint::loader`] and
    /// [`LoadedScalar::loader`] referencing.
    pub static ref LOADER: NativeLoader = NativeLoader;
}

/// `Loader` implementation in native rust.
#[derive(Clone, Debug)]
pub struct NativeLoader;

impl<C: CurveAffine> LoadedEcPoint<C> for C {
    type Loader = NativeLoader;

    fn loader(&self) -> &NativeLoader {
        &LOADER
    }
}

impl<F: PrimeField> FieldOps for F {
    fn invert(&self) -> Option<F> {
        self.invert().into()
    }
}

impl<F: PrimeField> LoadedScalar<F> for F {
    type Loader = NativeLoader;

    fn loader(&self) -> &NativeLoader {
        &LOADER
    }

    fn pow_var(&self, exp: &Self, _: usize) -> Self {
        let exp = fe_to_big(*exp).to_u64_digits();
        self.pow_vartime(exp)
    }
}

impl<C: CurveAffine> EcPointLoader<C> for NativeLoader {
    type LoadedEcPoint = C;

    fn ec_point_load_const(&self, value: &C) -> Self::LoadedEcPoint {
        *value
    }

    fn ec_point_assert_eq(
        &self,
        annotation: &str,
        lhs: &Self::LoadedEcPoint,
        rhs: &Self::LoadedEcPoint,
    ) {
        lhs.eq(rhs)
            .then_some(())
            .unwrap_or_else(|| panic!("{:?}", Error::AssertionFailure(annotation.to_string())))
    }

    fn multi_scalar_multiplication(
        pairs: &[(&<Self as ScalarLoader<C::Scalar>>::LoadedScalar, &C)],
    ) -> C {
        pairs
            .iter()
            .cloned()
            .map(|(scalar, base)| *base * scalar)
            .reduce(|acc, value| acc + value)
            .expect("pairs should not be empty")
            .to_affine()
    }
}

impl<F: PrimeField> ScalarLoader<F> for NativeLoader {
    type LoadedScalar = F;

    fn load_const(&self, value: &F) -> Self::LoadedScalar {
        *value
    }

    fn assert_eq(&self, annotation: &str, lhs: &Self::LoadedScalar, rhs: &Self::LoadedScalar) {
        lhs.eq(rhs)
            .then_some(())
            .unwrap_or_else(|| panic!("{:?}", Error::AssertionFailure(annotation.to_string())))
    }
}

impl<C: CurveAffine> Loader<C> for NativeLoader {}
