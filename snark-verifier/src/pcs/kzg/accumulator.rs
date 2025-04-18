use crate::{loader::Loader, util::arithmetic::CurveAffine};
use std::fmt::Debug;

/// KZG accumulator, containing lhs G1 and rhs G1 of pairing.
#[derive(Clone, Debug)]
pub struct KzgAccumulator<C, L>
where
    C: CurveAffine,
    L: Loader<C>,
{
    /// Left-hand side G1 of pairing.
    pub lhs: L::LoadedEcPoint,
    /// Right-hand side G1 of pairing.
    pub rhs: L::LoadedEcPoint,
}

impl<C, L> KzgAccumulator<C, L>
where
    C: CurveAffine,
    L: Loader<C>,
{
    /// Initialize a [`KzgAccumulator`].
    pub fn new(lhs: L::LoadedEcPoint, rhs: L::LoadedEcPoint) -> Self {
        Self { lhs, rhs }
    }
}

/// `AccumulatorEncoding` that encodes `Accumulator` into limbs.
///
/// Since in circuit everything are in scalar field, but `Accumulator` might contain base field elements, so we split them into limbs.
/// The const generic `LIMBS` and `BITS` respectively represents how many limbs
/// a base field element are split into and how many bits each limbs could have.
#[derive(Clone, Debug)]
pub struct LimbsEncoding<const LIMBS: usize, const BITS: usize>;

mod native {
    use crate::{
        loader::native::NativeLoader,
        pcs::{
            kzg::{KzgAccumulator, LimbsEncoding},
            AccumulatorEncoding,
        },
        util::{
            arithmetic::{fe_from_limbs, CurveAffine},
            Itertools,
        },
        Error,
    };

    impl<C, const LIMBS: usize, const BITS: usize> AccumulatorEncoding<C, NativeLoader>
        for LimbsEncoding<LIMBS, BITS>
    where
        C: CurveAffine,
    {
        type Accumulator = KzgAccumulator<C, NativeLoader>;

        fn from_repr(limbs: &[&C::Scalar]) -> Result<Self::Accumulator, Error> {
            assert_eq!(limbs.len(), 4 * LIMBS);

            let [lhs_x, lhs_y, rhs_x, rhs_y]: [_; 4] = limbs
                .chunks(LIMBS)
                .map(|limbs| {
                    fe_from_limbs::<_, _, LIMBS, BITS>(
                        limbs.iter().map(|limb| **limb).collect_vec().try_into().unwrap(),
                    )
                })
                .collect_vec()
                .try_into()
                .unwrap();
            let accumulator = KzgAccumulator::new(
                C::from_xy(lhs_x, lhs_y).unwrap(),
                C::from_xy(rhs_x, rhs_y).unwrap(),
            );

            Ok(accumulator)
        }
    }
}

#[cfg(feature = "loader_evm")]
mod evm {
    use crate::{
        loader::evm::{EvmLoader, Scalar},
        pcs::{
            kzg::{KzgAccumulator, LimbsEncoding},
            AccumulatorEncoding,
        },
        util::{
            arithmetic::{CurveAffine, PrimeField},
            Itertools,
        },
        Error,
    };
    use std::rc::Rc;

    impl<C, const LIMBS: usize, const BITS: usize> AccumulatorEncoding<C, Rc<EvmLoader>>
        for LimbsEncoding<LIMBS, BITS>
    where
        C: CurveAffine,
        C::Scalar: PrimeField<Repr = [u8; 0x20]>,
    {
        type Accumulator = KzgAccumulator<C, Rc<EvmLoader>>;

        fn from_repr(limbs: &[&Scalar]) -> Result<Self::Accumulator, Error> {
            assert_eq!(limbs.len(), 4 * LIMBS);

            let loader = limbs[0].loader();

            let [lhs_x, lhs_y, rhs_x, rhs_y]: [[_; LIMBS]; 4] = limbs
                .chunks(LIMBS)
                .map(|limbs| limbs.to_vec().try_into().unwrap())
                .collect_vec()
                .try_into()
                .unwrap();
            let accumulator = KzgAccumulator::new(
                loader.ec_point_from_limbs::<LIMBS, BITS>(lhs_x, lhs_y),
                loader.ec_point_from_limbs::<LIMBS, BITS>(rhs_x, rhs_y),
            );

            Ok(accumulator)
        }
    }
}

#[cfg(feature = "loader_halo2")]
pub use halo2::LimbsEncodingInstructions;

#[cfg(feature = "loader_halo2")]
mod halo2 {
    use crate::{
        loader::halo2::{EccInstructions, Halo2Loader, Scalar},
        pcs::{
            kzg::{KzgAccumulator, LimbsEncoding},
            AccumulatorEncoding,
        },
        util::{
            arithmetic::{fe_from_limbs, CurveAffine},
            Itertools,
        },
        Error,
    };
    use std::{iter, ops::Deref, rc::Rc};

    fn ec_point_from_limbs<C: CurveAffine, const LIMBS: usize, const BITS: usize>(
        limbs: &[&C::Scalar],
    ) -> C {
        assert_eq!(limbs.len(), 2 * LIMBS);

        let [x, y] = [&limbs[..LIMBS], &limbs[LIMBS..]].map(|limbs| {
            fe_from_limbs::<_, _, LIMBS, BITS>(
                limbs.iter().map(|limb| **limb).collect_vec().try_into().unwrap(),
            )
        });

        C::from_xy(x, y).unwrap()
    }

    /// Instructions to encode/decode a elliptic curve point into/from limbs.
    pub trait LimbsEncodingInstructions<C: CurveAffine, const LIMBS: usize, const BITS: usize>:
        EccInstructions<C>
    {
        /// Decode and assign an elliptic curve point from limbs.
        fn assign_ec_point_from_limbs(
            &self,
            ctx: &mut Self::Context,
            limbs: &[impl Deref<Target = Self::AssignedScalar>],
        ) -> Self::AssignedEcPoint;

        /// Encode an elliptic curve point into limbs.
        fn assign_ec_point_to_limbs(
            &self,
            ctx: &mut Self::Context,
            ec_point: impl Deref<Target = Self::AssignedEcPoint>,
        ) -> Vec<Self::AssignedCell>;
    }

    impl<C, EccChip, const LIMBS: usize, const BITS: usize>
        AccumulatorEncoding<C, Rc<Halo2Loader<C, EccChip>>> for LimbsEncoding<LIMBS, BITS>
    where
        C: CurveAffine,
        EccChip: LimbsEncodingInstructions<C, LIMBS, BITS>,
    {
        type Accumulator = KzgAccumulator<C, Rc<Halo2Loader<C, EccChip>>>;

        fn from_repr(limbs: &[&Scalar<C, EccChip>]) -> Result<Self::Accumulator, Error> {
            assert_eq!(limbs.len(), 4 * LIMBS);

            let loader = limbs[0].loader();

            let [lhs, rhs] = [&limbs[..2 * LIMBS], &limbs[2 * LIMBS..]].map(|limbs| {
                let assigned = loader.ecc_chip().assign_ec_point_from_limbs(
                    &mut loader.ctx_mut(),
                    &limbs.iter().map(|limb| limb.assigned()).collect_vec(),
                );
                loader.ec_point_from_assigned(assigned)
            });

            Ok(KzgAccumulator::new(lhs, rhs))
        }
    }

    mod halo2_lib {
        use super::*;
        use halo2_base::utils::BigPrimeField;
        use halo2_base::utils::CurveAffineExt;
        use halo2_ecc::ecc::BaseFieldEccChip;

        impl<C, const LIMBS: usize, const BITS: usize> LimbsEncodingInstructions<C, LIMBS, BITS>
            for BaseFieldEccChip<'_, C>
        where
            C: CurveAffineExt,
            C::ScalarExt: BigPrimeField,
            C::Base: BigPrimeField,
        {
            fn assign_ec_point_from_limbs(
                &self,
                ctx: &mut Self::Context,
                limbs: &[impl Deref<Target = Self::AssignedScalar>],
            ) -> Self::AssignedEcPoint {
                assert_eq!(limbs.len(), 2 * LIMBS);

                let ec_point = self.assign_point::<C>(
                    ctx.main(),
                    ec_point_from_limbs::<_, LIMBS, BITS>(
                        &limbs.iter().map(|limb| limb.value()).collect_vec(),
                    ),
                );

                for (src, dst) in limbs
                    .iter()
                    .zip_eq(iter::empty().chain(ec_point.x().limbs()).chain(ec_point.y().limbs()))
                {
                    ctx.main().constrain_equal(src, dst);
                }

                ec_point
            }

            fn assign_ec_point_to_limbs(
                &self,
                _: &mut Self::Context,
                ec_point: impl Deref<Target = Self::AssignedEcPoint>,
            ) -> Vec<Self::AssignedCell> {
                iter::empty()
                    .chain(ec_point.x().limbs())
                    .chain(ec_point.y().limbs())
                    .copied()
                    .collect()
            }
        }
    }
}
