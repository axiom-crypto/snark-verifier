use crate::{
    loader::{
        halo2::shim::{EccInstructions, IntegerInstructions},
        EcPointLoader, LoadedEcPoint, LoadedScalar, Loader, ScalarLoader,
    },
    util::{
        arithmetic::{CurveAffine, Field, FieldOps},
        Itertools,
    },
};
use std::{
    cell::{Ref, RefCell, RefMut},
    fmt::{self, Debug},
    marker::PhantomData,
    ops::{Add, AddAssign, Deref, Mul, MulAssign, Neg, Sub, SubAssign},
    rc::Rc,
};

/// `Loader` implementation for generating verifier in [`halo2_proofs`] circuit.
#[derive(Debug)]
pub struct Halo2Loader<C: CurveAffine, EccChip: EccInstructions<C>> {
    ecc_chip: RefCell<EccChip>,
    ctx: RefCell<EccChip::Context>,
    num_scalar: RefCell<usize>,
    num_ec_point: RefCell<usize>,
    _marker: PhantomData<C>,
    #[cfg(test)]
    #[allow(dead_code)]
    row_meterings: RefCell<Vec<(String, usize)>>,
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> Halo2Loader<C, EccChip> {
    /// Initialize a [`Halo2Loader`] with given [`EccInstructions`] and
    /// [`EccInstructions::Context`].
    pub fn new(ecc_chip: EccChip, ctx: EccChip::Context) -> Rc<Self> {
        Rc::new(Self {
            ecc_chip: RefCell::new(ecc_chip),
            ctx: RefCell::new(ctx),
            num_scalar: RefCell::default(),
            num_ec_point: RefCell::default(),
            #[cfg(test)]
            row_meterings: RefCell::default(),
            _marker: PhantomData,
        })
    }

    /// Into [`EccInstructions::Context`].
    pub fn into_ctx(self) -> EccChip::Context {
        self.ctx.into_inner()
    }

    /// Takes [`EccInstructions::Context`] from the [`RefCell`], leaving with Default value
    pub fn take_ctx(&self) -> EccChip::Context {
        self.ctx.take()
    }

    /// Returns reference of [`EccInstructions`].
    pub fn ecc_chip(&self) -> Ref<EccChip> {
        self.ecc_chip.borrow()
    }

    /// Returns reference of [`EccInstructions::ScalarChip`].
    pub fn scalar_chip(&self) -> Ref<EccChip::ScalarChip> {
        Ref::map(self.ecc_chip(), |ecc_chip| ecc_chip.scalar_chip())
    }

    /// Returns reference of [`EccInstructions::Context`].
    pub fn ctx(&self) -> Ref<EccChip::Context> {
        self.ctx.borrow()
    }

    /// Returns mutable reference of [`EccInstructions::Context`].
    pub fn ctx_mut(&self) -> RefMut<'_, EccChip::Context> {
        self.ctx.borrow_mut()
    }

    fn assign_const_scalar(self: &Rc<Self>, constant: C::Scalar) -> EccChip::AssignedScalar {
        self.scalar_chip().assign_constant(&mut self.ctx_mut(), constant)
    }

    /// Assign a field element witness.
    pub fn assign_scalar(self: &Rc<Self>, scalar: C::Scalar) -> Scalar<C, EccChip> {
        let assigned = self.scalar_chip().assign_integer(&mut self.ctx_mut(), scalar);
        self.scalar_from_assigned(assigned)
    }

    /// Returns [`Scalar`] with assigned field element.
    pub fn scalar_from_assigned(
        self: &Rc<Self>,
        assigned: EccChip::AssignedScalar,
    ) -> Scalar<C, EccChip> {
        self.scalar(Value::Assigned(assigned))
    }

    fn scalar(
        self: &Rc<Self>,
        value: Value<C::Scalar, EccChip::AssignedScalar>,
    ) -> Scalar<C, EccChip> {
        let index = *self.num_scalar.borrow();
        *self.num_scalar.borrow_mut() += 1;
        Scalar { loader: self.clone(), index, value: value.into() }
    }

    fn assign_const_ec_point(self: &Rc<Self>, constant: C) -> EccChip::AssignedEcPoint {
        self.ecc_chip().assign_constant(&mut self.ctx_mut(), constant)
    }

    /// Assign an elliptic curve point witness.
    pub fn assign_ec_point(self: &Rc<Self>, ec_point: C) -> EcPoint<C, EccChip> {
        let assigned = self.ecc_chip().assign_point(&mut self.ctx_mut(), ec_point);
        self.ec_point_from_assigned(assigned)
    }

    /// Returns [`EcPoint`] with assigned elliptic curve point.
    pub fn ec_point_from_assigned(
        self: &Rc<Self>,
        assigned: EccChip::AssignedEcPoint,
    ) -> EcPoint<C, EccChip> {
        self.ec_point(Value::Assigned(assigned))
    }

    fn ec_point(self: &Rc<Self>, value: Value<C, EccChip::AssignedEcPoint>) -> EcPoint<C, EccChip> {
        let index = *self.num_ec_point.borrow();
        *self.num_ec_point.borrow_mut() += 1;
        EcPoint { loader: self.clone(), index, value: value.into() }
    }

    fn add(
        self: &Rc<Self>,
        lhs: &Scalar<C, EccChip>,
        rhs: &Scalar<C, EccChip>,
    ) -> Scalar<C, EccChip> {
        let output = match (lhs.value().deref(), rhs.value().deref()) {
            (Value::Constant(lhs), Value::Constant(rhs)) => Value::Constant(*lhs + rhs),
            (Value::Assigned(assigned), Value::Constant(constant))
            | (Value::Constant(constant), Value::Assigned(assigned)) => {
                Value::Assigned(self.scalar_chip().sum_with_coeff_and_const(
                    &mut self.ctx_mut(),
                    &[(C::Scalar::ONE, assigned)],
                    *constant,
                ))
            }
            (Value::Assigned(lhs), Value::Assigned(rhs)) => {
                Value::Assigned(self.scalar_chip().sum_with_coeff_and_const(
                    &mut self.ctx_mut(),
                    &[(C::Scalar::ONE, lhs), (C::Scalar::ONE, rhs)],
                    C::Scalar::ZERO,
                ))
            }
        };
        self.scalar(output)
    }

    fn sub(
        self: &Rc<Self>,
        lhs: &Scalar<C, EccChip>,
        rhs: &Scalar<C, EccChip>,
    ) -> Scalar<C, EccChip> {
        let output = match (lhs.value().deref(), rhs.value().deref()) {
            (Value::Constant(lhs), Value::Constant(rhs)) => Value::Constant(*lhs - rhs),
            (Value::Constant(constant), Value::Assigned(assigned)) => {
                Value::Assigned(self.scalar_chip().sum_with_coeff_and_const(
                    &mut self.ctx_mut(),
                    &[(-C::Scalar::ONE, assigned)],
                    *constant,
                ))
            }
            (Value::Assigned(assigned), Value::Constant(constant)) => {
                Value::Assigned(self.scalar_chip().sum_with_coeff_and_const(
                    &mut self.ctx_mut(),
                    &[(C::Scalar::ONE, assigned)],
                    -*constant,
                ))
            }
            (Value::Assigned(lhs), Value::Assigned(rhs)) => Value::Assigned(
                IntegerInstructions::sub(self.scalar_chip().deref(), &mut self.ctx_mut(), lhs, rhs),
            ),
        };
        self.scalar(output)
    }

    fn mul(
        self: &Rc<Self>,
        lhs: &Scalar<C, EccChip>,
        rhs: &Scalar<C, EccChip>,
    ) -> Scalar<C, EccChip> {
        let output = match (lhs.value().deref(), rhs.value().deref()) {
            (Value::Constant(lhs), Value::Constant(rhs)) => Value::Constant(*lhs * rhs),
            (Value::Assigned(assigned), Value::Constant(constant))
            | (Value::Constant(constant), Value::Assigned(assigned)) => {
                Value::Assigned(self.scalar_chip().sum_with_coeff_and_const(
                    &mut self.ctx_mut(),
                    &[(*constant, assigned)],
                    C::Scalar::ZERO,
                ))
            }
            (Value::Assigned(lhs), Value::Assigned(rhs)) => {
                Value::Assigned(self.scalar_chip().sum_products_with_coeff_and_const(
                    &mut self.ctx_mut(),
                    &[(C::Scalar::ONE, lhs, rhs)],
                    C::Scalar::ZERO,
                ))
            }
        };
        self.scalar(output)
    }

    fn neg(self: &Rc<Self>, scalar: &Scalar<C, EccChip>) -> Scalar<C, EccChip> {
        let output = match scalar.value().deref() {
            Value::Constant(constant) => Value::Constant(constant.neg()),
            Value::Assigned(assigned) => Value::Assigned(IntegerInstructions::neg(
                self.scalar_chip().deref(),
                &mut self.ctx_mut(),
                assigned,
            )),
        };
        self.scalar(output)
    }

    fn invert(self: &Rc<Self>, scalar: &Scalar<C, EccChip>) -> Scalar<C, EccChip> {
        let output = match scalar.value().deref() {
            Value::Constant(constant) => Value::Constant(Field::invert(constant).unwrap()),
            Value::Assigned(assigned) => Value::Assigned(IntegerInstructions::invert(
                self.scalar_chip().deref(),
                &mut self.ctx_mut(),
                assigned,
            )),
        };
        self.scalar(output)
    }
}

#[derive(Clone, Debug)]
pub enum Value<T, L> {
    Constant(T),
    Assigned(L),
}

impl<T, L> Value<T, L> {
    fn maybe_const(&self) -> Option<T>
    where
        T: Copy,
    {
        match self {
            Value::Constant(constant) => Some(*constant),
            _ => None,
        }
    }

    fn assigned(&self) -> &L {
        match self {
            Value::Assigned(assigned) => assigned,
            _ => unreachable!(),
        }
    }
}

/// Field element
#[derive(Clone)]
pub struct Scalar<C: CurveAffine, EccChip: EccInstructions<C>> {
    loader: Rc<Halo2Loader<C, EccChip>>,
    index: usize,
    value: RefCell<Value<C::Scalar, EccChip::AssignedScalar>>,
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> Scalar<C, EccChip> {
    /// Returns reference of [`Rc<Halo2Loader>`]
    pub fn loader(&self) -> &Rc<Halo2Loader<C, EccChip>> {
        &self.loader
    }

    /// Returns reference of [`EccInstructions::AssignedScalar`].
    pub fn into_assigned(self) -> EccChip::AssignedScalar {
        match self.value.into_inner() {
            Value::Constant(constant) => self.loader.assign_const_scalar(constant),
            Value::Assigned(assigned) => assigned,
        }
    }

    /// Returns reference of [`EccInstructions::AssignedScalar`].
    pub fn assigned(&self) -> Ref<EccChip::AssignedScalar> {
        if let Some(constant) = self.maybe_const() {
            *self.value.borrow_mut() = Value::Assigned(self.loader.assign_const_scalar(constant))
        }
        Ref::map(self.value.borrow(), Value::assigned)
    }

    fn value(&self) -> Ref<Value<C::Scalar, EccChip::AssignedScalar>> {
        self.value.borrow()
    }

    fn maybe_const(&self) -> Option<C::Scalar> {
        self.value().deref().maybe_const()
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> PartialEq for Scalar<C, EccChip> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> LoadedScalar<C::Scalar> for Scalar<C, EccChip> {
    type Loader = Rc<Halo2Loader<C, EccChip>>;

    fn loader(&self) -> &Self::Loader {
        &self.loader
    }

    fn pow_var(&self, exp: &Self, max_bits: usize) -> Self {
        let loader = self.loader();
        let base = self.clone().into_assigned();
        let exp = exp.clone().into_assigned();
        let res = loader.scalar_chip().pow_var(&mut loader.ctx_mut(), &base, &exp, max_bits);
        loader.scalar_from_assigned(res)
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> Debug for Scalar<C, EccChip> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Scalar").field("value", &self.value).finish()
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> FieldOps for Scalar<C, EccChip> {
    fn invert(&self) -> Option<Self> {
        Some(self.loader.invert(self))
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> Add for Scalar<C, EccChip> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Halo2Loader::add(&self.loader, &self, &rhs)
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> Sub for Scalar<C, EccChip> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Halo2Loader::sub(&self.loader, &self, &rhs)
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> Mul for Scalar<C, EccChip> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Halo2Loader::mul(&self.loader, &self, &rhs)
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> Neg for Scalar<C, EccChip> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Halo2Loader::neg(&self.loader, &self)
    }
}

impl<'b, C: CurveAffine, EccChip: EccInstructions<C>> Add<&'b Self> for Scalar<C, EccChip> {
    type Output = Self;

    fn add(self, rhs: &'b Self) -> Self::Output {
        Halo2Loader::add(&self.loader, &self, rhs)
    }
}

impl<'b, C: CurveAffine, EccChip: EccInstructions<C>> Sub<&'b Self> for Scalar<C, EccChip> {
    type Output = Self;

    fn sub(self, rhs: &'b Self) -> Self::Output {
        Halo2Loader::sub(&self.loader, &self, rhs)
    }
}

impl<'b, C: CurveAffine, EccChip: EccInstructions<C>> Mul<&'b Self> for Scalar<C, EccChip> {
    type Output = Self;

    fn mul(self, rhs: &'b Self) -> Self::Output {
        Halo2Loader::mul(&self.loader, &self, rhs)
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> AddAssign for Scalar<C, EccChip> {
    fn add_assign(&mut self, rhs: Self) {
        *self = Halo2Loader::add(&self.loader, self, &rhs)
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> SubAssign for Scalar<C, EccChip> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = Halo2Loader::sub(&self.loader, self, &rhs)
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> MulAssign for Scalar<C, EccChip> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = Halo2Loader::mul(&self.loader, self, &rhs)
    }
}

impl<'b, C: CurveAffine, EccChip: EccInstructions<C>> AddAssign<&'b Self> for Scalar<C, EccChip> {
    fn add_assign(&mut self, rhs: &'b Self) {
        *self = Halo2Loader::add(&self.loader, self, rhs)
    }
}

impl<'b, C: CurveAffine, EccChip: EccInstructions<C>> SubAssign<&'b Self> for Scalar<C, EccChip> {
    fn sub_assign(&mut self, rhs: &'b Self) {
        *self = Halo2Loader::sub(&self.loader, self, rhs)
    }
}

impl<'b, C: CurveAffine, EccChip: EccInstructions<C>> MulAssign<&'b Self> for Scalar<C, EccChip> {
    fn mul_assign(&mut self, rhs: &'b Self) {
        *self = Halo2Loader::mul(&self.loader, self, rhs)
    }
}

/// Elliptic curve point
#[derive(Clone)]
pub struct EcPoint<C: CurveAffine, EccChip: EccInstructions<C>> {
    loader: Rc<Halo2Loader<C, EccChip>>,
    index: usize,
    value: RefCell<Value<C, EccChip::AssignedEcPoint>>,
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> EcPoint<C, EccChip> {
    /// Into [`EccInstructions::AssignedEcPoint`].
    pub fn into_assigned(self) -> EccChip::AssignedEcPoint {
        match self.value.into_inner() {
            Value::Constant(constant) => self.loader.assign_const_ec_point(constant),
            Value::Assigned(assigned) => assigned,
        }
    }

    /// Returns reference of [`EccInstructions::AssignedEcPoint`].
    pub fn assigned(&self) -> Ref<EccChip::AssignedEcPoint> {
        if let Some(constant) = self.maybe_const() {
            *self.value.borrow_mut() = Value::Assigned(self.loader.assign_const_ec_point(constant))
        }
        Ref::map(self.value.borrow(), Value::assigned)
    }

    fn value(&self) -> Ref<Value<C, EccChip::AssignedEcPoint>> {
        self.value.borrow()
    }

    fn maybe_const(&self) -> Option<C> {
        self.value().deref().maybe_const()
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> PartialEq for EcPoint<C, EccChip> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> LoadedEcPoint<C> for EcPoint<C, EccChip> {
    type Loader = Rc<Halo2Loader<C, EccChip>>;

    fn loader(&self) -> &Self::Loader {
        &self.loader
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> Debug for EcPoint<C, EccChip> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EcPoint").field("index", &self.index).field("value", &self.value).finish()
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> ScalarLoader<C::Scalar>
    for Rc<Halo2Loader<C, EccChip>>
{
    type LoadedScalar = Scalar<C, EccChip>;

    fn load_const(&self, value: &C::Scalar) -> Scalar<C, EccChip> {
        self.scalar(Value::Constant(*value))
    }

    fn assert_eq(&self, _annotation: &str, lhs: &Scalar<C, EccChip>, rhs: &Scalar<C, EccChip>) {
        self.scalar_chip().assert_equal(&mut self.ctx_mut(), &lhs.assigned(), &rhs.assigned());
    }

    fn sum_with_coeff_and_const(
        &self,
        values: &[(C::Scalar, &Scalar<C, EccChip>)],
        constant: C::Scalar,
    ) -> Scalar<C, EccChip> {
        let values = values.iter().map(|(coeff, value)| (*coeff, value.assigned())).collect_vec();
        self.scalar(Value::Assigned(self.scalar_chip().sum_with_coeff_and_const(
            &mut self.ctx_mut(),
            &values,
            constant,
        )))
    }

    fn sum_products_with_coeff_and_const(
        &self,
        values: &[(C::Scalar, &Scalar<C, EccChip>, &Scalar<C, EccChip>)],
        constant: C::Scalar,
    ) -> Scalar<C, EccChip> {
        let values = values
            .iter()
            .map(|(coeff, lhs, rhs)| (*coeff, lhs.assigned(), rhs.assigned()))
            .collect_vec();
        self.scalar(Value::Assigned(self.scalar_chip().sum_products_with_coeff_and_const(
            &mut self.ctx_mut(),
            &values,
            constant,
        )))
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> EcPointLoader<C> for Rc<Halo2Loader<C, EccChip>> {
    type LoadedEcPoint = EcPoint<C, EccChip>;

    fn ec_point_load_const(&self, ec_point: &C) -> EcPoint<C, EccChip> {
        self.ec_point(Value::Constant(*ec_point))
    }

    fn ec_point_assert_eq(
        &self,
        _annotation: &str,
        lhs: &EcPoint<C, EccChip>,
        rhs: &EcPoint<C, EccChip>,
    ) {
        if let (Value::Constant(lhs), Value::Constant(rhs)) =
            (lhs.value().deref(), rhs.value().deref())
        {
            assert_eq!(lhs, rhs);
        } else {
            let lhs = lhs.assigned();
            let rhs = rhs.assigned();
            self.ecc_chip().assert_equal(&mut self.ctx_mut(), lhs.deref(), rhs.deref());
        }
    }

    fn multi_scalar_multiplication(
        pairs: &[(&<Self as ScalarLoader<C::Scalar>>::LoadedScalar, &EcPoint<C, EccChip>)],
    ) -> EcPoint<C, EccChip> {
        assert!(!pairs.is_empty(), "multi_scalar_multiplication: pairs is empty");
        let loader = &pairs[0].0.loader;

        let (constant, fixed_base, variable_base_non_scaled, variable_base_scaled) =
            pairs.iter().cloned().fold(
                (C::identity(), Vec::new(), Vec::new(), Vec::new()),
                |(
                    mut constant,
                    mut fixed_base,
                    mut variable_base_non_scaled,
                    mut variable_base_scaled,
                ),
                 (scalar, base)| {
                    match (scalar.value().deref(), base.value().deref()) {
                        (Value::Constant(scalar), Value::Constant(base)) => {
                            constant = (*base * scalar + constant).into()
                        }
                        (Value::Assigned(_), Value::Constant(base)) => {
                            fixed_base.push((scalar, *base))
                        }
                        (Value::Constant(scalar), Value::Assigned(_))
                            if scalar.eq(&C::Scalar::ONE) =>
                        {
                            variable_base_non_scaled.push(base);
                        }
                        _ => variable_base_scaled.push((scalar, base)),
                    };
                    (constant, fixed_base, variable_base_non_scaled, variable_base_scaled)
                },
            );

        let fixed_base_msm = (!fixed_base.is_empty())
            .then(|| {
                let fixed_base = fixed_base
                    .into_iter()
                    .map(|(scalar, base)| (scalar.assigned(), base))
                    .collect_vec();
                loader.ecc_chip.borrow_mut().fixed_base_msm(&mut loader.ctx_mut(), &fixed_base)
            })
            .map(RefCell::new);
        let variable_base_msm = (!variable_base_scaled.is_empty())
            .then(|| {
                let variable_base_scaled = variable_base_scaled
                    .into_iter()
                    .map(|(scalar, base)| (scalar.assigned(), base.assigned()))
                    .collect_vec();
                loader
                    .ecc_chip
                    .borrow_mut()
                    .variable_base_msm(&mut loader.ctx_mut(), &variable_base_scaled)
            })
            .map(RefCell::new);
        let output = loader.ecc_chip().sum_with_const(
            &mut loader.ctx_mut(),
            &variable_base_non_scaled
                .into_iter()
                .map(EcPoint::assigned)
                .chain(fixed_base_msm.as_ref().map(RefCell::borrow))
                .chain(variable_base_msm.as_ref().map(RefCell::borrow))
                .collect_vec(),
            constant,
        );

        loader.ec_point_from_assigned(output)
    }
}

impl<C: CurveAffine, EccChip: EccInstructions<C>> Loader<C> for Rc<Halo2Loader<C, EccChip>> {}
