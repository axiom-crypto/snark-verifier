use crate::{
    loader::{EcPointLoader, LoadedEcPoint, LoadedScalar, Loader, ScalarLoader},
    util::{
        arithmetic::{Curve, CurveAffine, Field, FieldOps, PrimeCurveAffine, PrimeField},
        Itertools,
    },
};
use halo2_base::{
    self,
    gates::{flex_gate::FlexGateConfig, range::RangeConfig, GateInstructions, RangeInstructions},
    utils::fe_to_bigint,
    Context,
    QuantumCell::{self, Constant, Existing, Witness},
};
use halo2_ecc::{
    bigint::{CRTInteger, OverflowInteger},
    ecc::{fixed::FixedEccPoint, EccChip, EccPoint},
    fields::{fp::FpConfig, FieldChip},
};
use halo2_proofs::circuit;
use num_bigint::{BigInt, BigUint};
use std::{
    cell::RefCell,
    fmt::{self, Debug},
    ops::{Add, AddAssign, Deref, DerefMut, Mul, MulAssign, Neg, Sub, SubAssign},
    rc::Rc,
};

pub type AssignedValue<C> = halo2_base::AssignedValue<<C as PrimeCurveAffine>::Scalar>;
pub type BaseFieldChip<C> = FpConfig<<C as CurveAffine>::ScalarExt, <C as CurveAffine>::Base>;
pub type AssignedInteger<C> = CRTInteger<<C as CurveAffine>::ScalarExt>;
pub type AssignedEcPoint<C> = EccPoint<<C as CurveAffine>::ScalarExt, AssignedInteger<C>>;

// Sometimes it is useful to know that a cell is really a constant, for optimization purposes
#[derive(Clone, Debug)]
pub enum Value<T, L> {
    Constant(T),
    Assigned(L),
}

pub struct Halo2Loader<'a, 'b, C: CurveAffine> {
    pub ecc_chip: EccChip<'a, C::Scalar, BaseFieldChip<C>>,
    ctx: RefCell<Context<'b, C::Scalar>>,
    num_ec_point: RefCell<usize>,
    num_scalar: RefCell<usize>,
}
impl<'a, 'b, C: CurveAffine> Debug for Halo2Loader<'a, 'b, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Halo2Loader")
            .field("num_ec_point", &self.num_ec_point)
            .field("num_scalar", &self.num_scalar)
            .finish()
    }
}

impl<'a, 'b, C: CurveAffine> Halo2Loader<'a, 'b, C>
where
    C::Base: PrimeField,
{
    pub fn new(field_chip: &'a BaseFieldChip<C>, ctx: Context<'b, C::Scalar>) -> Rc<Self> {
        Rc::new(Self {
            ecc_chip: EccChip::construct(field_chip),
            ctx: RefCell::new(ctx),
            num_ec_point: RefCell::new(0),
            num_scalar: RefCell::new(0),
        })
    }

    pub fn ecc_chip(&self) -> &EccChip<'a, C::Scalar, BaseFieldChip<C>> {
        &self.ecc_chip
    }

    pub fn field_chip(&self) -> &BaseFieldChip<C> {
        &self.ecc_chip.field_chip
    }

    pub fn range(&self) -> &RangeConfig<C::Scalar> {
        self.field_chip().range()
    }

    pub fn gate(&self) -> &FlexGateConfig<C::Scalar> {
        &self.range().gate
    }

    pub fn ctx(&self) -> impl Deref<Target = Context<'b, C::Scalar>> + '_ {
        self.ctx.borrow()
    }

    pub fn ctx_mut(&self) -> impl DerefMut<Target = Context<'b, C::Scalar>> + '_ {
        self.ctx.borrow_mut()
    }

    pub fn finalize(&self) {
        let stats = self
            .field_chip()
            .finalize(&mut self.ctx_mut())
            .expect("finalizing constants and lookups");
        println!("stats (max rows fixed, total fixed cells, max rows lookup) {:?}", stats);

        let total_cells =
            self.ctx.borrow().advice_rows[&self.range().context_id].iter().sum::<usize>();
        println!("total non-lookup advice cells used: {}", total_cells);
        println!(
            "total cells used in special lookup advice columns: {}",
            self.ctx.borrow().cells_to_lookup.len()
        );
    }

    pub fn assign_const_scalar(self: &Rc<Self>, constant: C::Scalar) -> Scalar<'a, 'b, C> {
        let output = if constant == C::Scalar::zero() {
            self.gate().load_zero(&mut self.ctx_mut()).unwrap()
        } else {
            let assigned = self
                .gate()
                .assign_region_smart(
                    &mut self.ctx_mut(),
                    vec![Constant(constant)],
                    vec![],
                    vec![],
                    vec![],
                )
                .unwrap();
            assigned[0].clone()
        };
        self.scalar(Value::Assigned(output))
    }

    pub fn assign_scalar(self: &Rc<Self>, scalar: circuit::Value<C::Scalar>) -> Scalar<'a, 'b, C> {
        let assigned = self
            .gate()
            .assign_region_smart(&mut self.ctx_mut(), vec![Witness(scalar)], vec![], vec![], vec![])
            .unwrap();
        self.scalar(Value::Assigned(assigned[0].clone()))
    }

    pub fn scalar(self: &Rc<Self>, value: Value<C::Scalar, AssignedValue<C>>) -> Scalar<'a, 'b, C> {
        let index = *self.num_scalar.borrow();
        *self.num_scalar.borrow_mut() += 1;
        Scalar { loader: self.clone(), index, value }
    }

    pub fn scalar_from_assigned(self: &Rc<Self>, assigned: AssignedValue<C>) -> Scalar<'a, 'b, C> {
        self.scalar(Value::Assigned(assigned))
    }

    pub fn ec_point(self: &Rc<Self>, assigned: AssignedEcPoint<C>) -> EcPoint<'a, 'b, C> {
        let index = *self.num_ec_point.borrow();
        *self.num_ec_point.borrow_mut() += 1;
        EcPoint { loader: self.clone(), value: Value::Assigned(assigned), index }
    }

    pub fn assign_const_ec_point(self: &Rc<Self>, ec_point: C) -> EcPoint<'a, 'b, C> {
        let index = *self.num_ec_point.borrow();
        *self.num_ec_point.borrow_mut() += 1;
        EcPoint { loader: self.clone(), value: Value::Constant(ec_point), index }
    }

    pub fn assign_ec_point(self: &Rc<Self>, ec_point: circuit::Value<C>) -> EcPoint<'a, 'b, C> {
        let assigned = self.ecc_chip.assign_point(&mut self.ctx_mut(), ec_point).unwrap();
        let is_on_curve_or_infinity =
            self.ecc_chip.is_on_curve_or_infinity::<C>(&mut self.ctx_mut(), &assigned).unwrap();
        self.gate().assert_is_const(
            &mut self.ctx_mut(),
            &is_on_curve_or_infinity,
            C::Scalar::one(),
        );

        self.ec_point(assigned)
    }

    pub fn assign_ec_point_from_limbs(
        self: &Rc<Self>,
        x_limbs: Vec<AssignedValue<C>>,
        y_limbs: Vec<AssignedValue<C>>,
    ) -> EcPoint<'a, 'b, C> {
        let limbs_to_crt = |limbs| {
            let native = OverflowInteger::evaluate(
                self.gate(),
                &mut self.ctx_mut(),
                &limbs,
                self.field_chip().limb_bits,
            )
            .unwrap();
            let mut big_value = circuit::Value::known(BigInt::from(0));
            for limb in limbs.iter().rev() {
                let limb_big = limb.value().map(|v| fe_to_bigint(v));
                big_value = big_value.map(|acc| acc << self.field_chip().limb_bits) + limb_big;
            }
            let truncation = OverflowInteger::construct(
                limbs,
                (BigUint::from(1u64) << self.field_chip().limb_bits) - 1usize,
                self.field_chip().limb_bits,
                self.field_chip().p.clone() - 1usize,
            );
            CRTInteger::construct(truncation, native, big_value)
        };

        let ec_point = EccPoint::construct(limbs_to_crt(x_limbs), limbs_to_crt(y_limbs));
        self.ecc_chip
            .assert_is_on_curve::<C>(&mut self.ctx_mut(), &ec_point)
            .expect("ec point should lie on curve");

        self.ec_point(ec_point)
    }

    fn add(self: &Rc<Self>, lhs: &Scalar<'a, 'b, C>, rhs: &Scalar<'a, 'b, C>) -> Scalar<'a, 'b, C> {
        let output = match (&lhs.value, &rhs.value) {
            (Value::Constant(lhs), Value::Constant(rhs)) => Value::Constant(*lhs + rhs),
            (Value::Assigned(assigned), Value::Constant(constant))
            | (Value::Constant(constant), Value::Assigned(assigned)) => Value::Assigned(
                GateInstructions::add(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Existing(assigned),
                    &Constant(*constant),
                )
                .expect("add should not fail"),
            ),
            (Value::Assigned(lhs), Value::Assigned(rhs)) => Value::Assigned(
                GateInstructions::add(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Existing(lhs),
                    &Existing(rhs),
                )
                .expect("add should not fail"),
            ),
        };
        self.scalar(output)
    }

    fn sub(self: &Rc<Self>, lhs: &Scalar<'a, 'b, C>, rhs: &Scalar<'a, 'b, C>) -> Scalar<'a, 'b, C> {
        let output = match (&lhs.value, &rhs.value) {
            (Value::Constant(lhs), Value::Constant(rhs)) => Value::Constant(*lhs - rhs),
            (Value::Constant(constant), Value::Assigned(assigned)) => Value::Assigned(
                GateInstructions::sub(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Constant(*constant),
                    &Existing(assigned),
                )
                .expect("sub should not fail"),
            ),
            (Value::Assigned(assigned), Value::Constant(constant)) => Value::Assigned(
                GateInstructions::sub(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Existing(assigned),
                    &Constant(*constant),
                )
                .expect("sub should not fail"),
            ),
            (Value::Assigned(lhs), Value::Assigned(rhs)) => Value::Assigned(
                GateInstructions::sub(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Existing(lhs),
                    &Existing(rhs),
                )
                .expect("sub should not fail"),
            ),
        };
        self.scalar(output)
    }

    fn mul(self: &Rc<Self>, lhs: &Scalar<'a, 'b, C>, rhs: &Scalar<'a, 'b, C>) -> Scalar<'a, 'b, C> {
        let output = match (&lhs.value, &rhs.value) {
            (Value::Constant(lhs), Value::Constant(rhs)) => Value::Constant(*lhs * rhs),
            (Value::Assigned(assigned), Value::Constant(constant))
            | (Value::Constant(constant), Value::Assigned(assigned)) => Value::Assigned(
                GateInstructions::mul(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Existing(assigned),
                    &Constant(*constant),
                )
                .expect("mul should not fail"),
            ),
            (Value::Assigned(lhs), Value::Assigned(rhs)) => Value::Assigned(
                GateInstructions::mul(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Existing(lhs),
                    &Existing(rhs),
                )
                .expect("mul should not fail"),
            ),
        };
        self.scalar(output)
    }

    fn mul_add(
        self: &Rc<Self>,
        a: &Scalar<'a, 'b, C>,
        b: &Scalar<'a, 'b, C>,
        c: &Scalar<'a, 'b, C>,
    ) -> Scalar<'a, 'b, C> {
        if let (Value::Constant(a), Value::Constant(b), Value::Constant(c)) =
            (&a.value, &b.value, &c.value)
        {
            return self.scalar(Value::Constant(*a * b + c));
        }
        let a = match &a.value {
            Value::Constant(constant) => Constant(*constant),
            Value::Assigned(assigned) => Existing(assigned),
        };
        let b = match &b.value {
            Value::Constant(constant) => Constant(*constant),
            Value::Assigned(assigned) => Existing(assigned),
        };
        let c = match &c.value {
            Value::Constant(constant) => Constant(*constant),
            Value::Assigned(assigned) => Existing(assigned),
        };
        let output = self.gate().mul_add(&mut self.ctx_mut(), &a, &b, &c).unwrap();
        self.scalar(Value::Assigned(output))
    }

    fn neg(self: &Rc<Self>, scalar: &Scalar<'a, 'b, C>) -> Scalar<'a, 'b, C> {
        let output = match &scalar.value {
            Value::Constant(constant) => Value::Constant(constant.neg()),
            Value::Assigned(assigned) => Value::Assigned(
                GateInstructions::neg(self.gate(), &mut self.ctx_mut(), &Existing(assigned))
                    .expect("neg should not fail"),
            ),
        };
        self.scalar(output)
    }

    fn invert(self: &Rc<Self>, scalar: &Scalar<'a, 'b, C>) -> Scalar<'a, 'b, C> {
        let output = match &scalar.value {
            Value::Constant(constant) => Value::Constant(Field::invert(constant).unwrap()),
            Value::Assigned(assigned) => Value::Assigned({
                // make sure scalar != 0
                let is_zero =
                    RangeInstructions::is_zero(self.range(), &mut self.ctx_mut(), assigned)
                        .unwrap();
                self.gate().assert_is_const(&mut self.ctx_mut(), &is_zero, C::Scalar::zero());
                GateInstructions::div_unsafe(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Constant(C::Scalar::one()),
                    &Existing(assigned),
                )
                .expect("invert should not fail")
            }),
        };
        self.scalar(output)
    }

    fn div(self: &Rc<Self>, lhs: &Scalar<'a, 'b, C>, rhs: &Scalar<'a, 'b, C>) -> Scalar<'a, 'b, C> {
        let output = match (&lhs.value, &rhs.value) {
            (Value::Constant(lhs), Value::Constant(rhs)) => {
                Value::Constant(*lhs * Field::invert(rhs).unwrap())
            }
            (Value::Constant(constant), Value::Assigned(assigned)) => Value::Assigned(
                GateInstructions::div_unsafe(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Constant(*constant),
                    &Existing(assigned),
                )
                .expect("div should not fail"),
            ),
            (Value::Assigned(assigned), Value::Constant(constant)) => Value::Assigned(
                GateInstructions::div_unsafe(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Existing(assigned),
                    &Constant(*constant),
                )
                .expect("div should not fail"),
            ),
            (Value::Assigned(lhs), Value::Assigned(rhs)) => Value::Assigned(
                GateInstructions::div_unsafe(
                    self.gate(),
                    &mut self.ctx_mut(),
                    &Existing(lhs),
                    &Existing(rhs),
                )
                .expect("div should not fail"),
            ),
        };
        self.scalar(output)
    }
}

#[derive(Clone)]
pub struct Scalar<'a, 'b, C: CurveAffine> {
    loader: Rc<Halo2Loader<'a, 'b, C>>,
    index: usize,
    value: Value<C::Scalar, AssignedValue<C>>,
}

impl<'a, 'b, C: CurveAffine> Scalar<'a, 'b, C> {
    pub fn assigned(&self) -> AssignedValue<C> {
        match &self.value {
            Value::Constant(constant) => self.loader.assign_const_scalar(*constant).assigned(),
            Value::Assigned(assigned) => assigned.clone(),
        }
    }

    pub fn to_quantum(&self) -> QuantumCell<C::Scalar> {
        match &self.value {
            Value::Constant(constant) => Constant(*constant),
            Value::Assigned(assigned) => Existing(assigned),
        }
    }
}

impl<'a, 'b, C: CurveAffine> PartialEq for Scalar<'a, 'b, C> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<'a, 'b, C: CurveAffine> LoadedScalar<C::Scalar> for Scalar<'a, 'b, C> {
    type Loader = Rc<Halo2Loader<'a, 'b, C>>;

    fn loader(&self) -> &Self::Loader {
        &self.loader
    }

    fn mul_add(a: &Self, b: &Self, c: &Self) -> Self {
        let loader = a.loader();
        Halo2Loader::mul_add(loader, a, b, c)
    }

    fn mul_add_constant(a: &Self, b: &Self, c: &C::Scalar) -> Self {
        Self::mul_add(a, b, &a.loader().scalar(Value::Constant(*c)))
    }

    fn pow_const(&self, exp: u64) -> Self {
        fn get_naf(mut e: u64) -> Vec<i8> {
            // https://en.wikipedia.org/wiki/Non-adjacent_form
            // NAF for exp:
            let mut naf: Vec<i8> = Vec::with_capacity(32);

            // generate the NAF for exp
            for _ in 0..64 {
                if e & 1 == 1 {
                    let z = 2i8 - (e % 4) as i8;
                    e = e / 2;
                    if z == -1 {
                        e += 1;
                    }
                    naf.push(z);
                } else {
                    naf.push(0);
                    e = e / 2;
                }
            }
            if e != 0 {
                assert_eq!(e, 1);
                naf.push(1);
            }
            naf
        }

        assert!(exp > 0);
        let is_zero = RangeInstructions::is_zero(
            self.loader().range(),
            &mut self.loader.ctx_mut(),
            &self.assigned(),
        )
        .unwrap();
        self.loader.gate().assert_is_const(&mut self.loader.ctx_mut(), &is_zero, C::Scalar::zero());

        let naf = get_naf(exp);
        let mut acc = self.clone();
        let mut is_started = false;

        for &z in naf.iter().rev() {
            if is_started {
                acc = acc.clone() * &acc;
            }
            if z != 0 {
                if is_started {
                    acc = if z == 1 { acc * self } else { (&self.loader).div(&acc, self) };
                } else {
                    is_started = true;
                }
            }
        }
        acc
    }
}

impl<'a, 'b, C: CurveAffine> Debug for Scalar<'a, 'b, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Scalar").field("value", &self.value).finish()
    }
}

impl<'a, 'b, C: CurveAffine> FieldOps for Scalar<'a, 'b, C> {
    fn invert(&self) -> Option<Self> {
        Some(self.loader.invert(self))
    }
}

impl<'a, 'b, C: CurveAffine> Add for Scalar<'a, 'b, C> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Halo2Loader::add(&self.loader, &self, &rhs)
    }
}
impl<'a, 'b, C: CurveAffine> Sub for Scalar<'a, 'b, C> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Halo2Loader::sub(&self.loader, &self, &rhs)
    }
}

impl<'a, 'b, C: CurveAffine> Mul for Scalar<'a, 'b, C> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Halo2Loader::mul(&self.loader, &self, &rhs)
    }
}

impl<'a, 'b, C: CurveAffine> Neg for Scalar<'a, 'b, C> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Halo2Loader::neg(&self.loader, &self)
    }
}

impl<'a, 'b, 'c, C: CurveAffine> Add<&'c Self> for Scalar<'a, 'b, C> {
    type Output = Self;

    fn add(self, rhs: &'c Self) -> Self::Output {
        Halo2Loader::add(&self.loader, &self, rhs)
    }
}

impl<'a, 'b, 'c, C: CurveAffine> Sub<&'c Self> for Scalar<'a, 'b, C> {
    type Output = Self;

    fn sub(self, rhs: &'c Self) -> Self::Output {
        Halo2Loader::sub(&self.loader, &self, rhs)
    }
}

impl<'a, 'b, 'c, C: CurveAffine> Mul<&'c Self> for Scalar<'a, 'b, C> {
    type Output = Self;

    fn mul(self, rhs: &'c Self) -> Self::Output {
        Halo2Loader::mul(&self.loader, &self, rhs)
    }
}

impl<'a, 'b, C: CurveAffine> AddAssign for Scalar<'a, 'b, C> {
    fn add_assign(&mut self, rhs: Self) {
        *self = Halo2Loader::add(&self.loader, self, &rhs)
    }
}

impl<'a, 'b, C: CurveAffine> SubAssign for Scalar<'a, 'b, C> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = Halo2Loader::sub(&self.loader, self, &rhs)
    }
}

impl<'a, 'b, C: CurveAffine> MulAssign for Scalar<'a, 'b, C> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = Halo2Loader::mul(&self.loader, self, &rhs)
    }
}

impl<'a, 'b, 'c, C: CurveAffine> AddAssign<&'c Self> for Scalar<'a, 'b, C> {
    fn add_assign(&mut self, rhs: &'c Self) {
        *self = (&self.loader).add(self, rhs)
    }
}

impl<'a, 'b, 'c, C: CurveAffine> SubAssign<&'c Self> for Scalar<'a, 'b, C> {
    fn sub_assign(&mut self, rhs: &'c Self) {
        *self = (&self.loader).sub(self, rhs)
    }
}

impl<'a, 'b, 'c, C: CurveAffine> MulAssign<&'c Self> for Scalar<'a, 'b, C> {
    fn mul_assign(&mut self, rhs: &'c Self) {
        *self = (&self.loader).mul(self, rhs)
    }
}

#[derive(Clone)]
pub struct EcPoint<'a, 'b, C: CurveAffine> {
    loader: Rc<Halo2Loader<'a, 'b, C>>,
    index: usize,
    pub value: Value<C, AssignedEcPoint<C>>,
}

impl<'a, 'b, C: CurveAffine> EcPoint<'a, 'b, C> {
    pub fn assigned(&self) -> AssignedEcPoint<C> {
        match &self.value {
            Value::Constant(constant) => {
                let point = FixedEccPoint::from_g1(
                    constant,
                    self.loader.field_chip().num_limbs,
                    self.loader.field_chip().limb_bits,
                );
                point.assign(self.loader.field_chip(), &mut self.loader.ctx_mut()).unwrap()
            }
            Value::Assigned(assigned) => assigned.clone(),
        }
    }
}

impl<'a, 'b, C: CurveAffine> PartialEq for EcPoint<'a, 'b, C> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<'a, 'b, C: CurveAffine> LoadedEcPoint<C> for EcPoint<'a, 'b, C>
where
    C::Base: PrimeField,
{
    type Loader = Rc<Halo2Loader<'a, 'b, C>>;

    fn loader(&self) -> &Self::Loader {
        &self.loader
    }

    fn multi_scalar_multiplication(
        pairs: impl IntoIterator<Item = (Scalar<'a, 'b, C>, Self)>,
    ) -> Self {
        let pairs = pairs.into_iter().collect_vec();
        let loader = &pairs[0].0.loader;

        let mut sum_constants = None;

        let (mut non_scaled, fixed, scaled) = pairs.iter().fold(
            (Vec::new(), Vec::new(), Vec::new()),
            |(mut non_scaled, mut fixed, mut scaled), (scalar, ec_point)| {
                if matches!(scalar.value, Value::Constant(constant) if constant == C::Scalar::one())
                {
                    non_scaled.push(ec_point.assigned());
                } else {
                    match &ec_point.value {
                        Value::Constant(constant_pt) => {
                            if let Value::Constant(constant_scalar) = scalar.value {
                                let prod = (constant_pt.clone() * constant_scalar).to_affine();
                                sum_constants = if let Some(sum) = sum_constants {
                                    Some(C::Curve::to_affine(&(sum + prod)))
                                } else {
                                    Some(prod)
                                };
                            }
                            fixed.push((constant_pt.clone(), scalar.assigned()));
                        }
                        Value::Assigned(assigned_pt) => {
                            scaled.push((assigned_pt.clone(), scalar.assigned()));
                        }
                    }
                }
                (non_scaled, fixed, scaled)
            },
        );
        if let Some(sum) = sum_constants {
            non_scaled.push(loader.assign_const_ec_point(sum).assigned());
        }

        let mut sum = None;
        if !scaled.is_empty() {
            sum = loader
                .ecc_chip
                .multi_scalar_mult::<C>(
                    &mut loader.ctx_mut(),
                    &scaled.iter().map(|pair| pair.0.clone()).collect(),
                    &scaled.into_iter().map(|pair| vec![pair.1]).collect(),
                    <C::Scalar as PrimeField>::NUM_BITS as usize,
                    4,
                )
                .ok();
        }
        if !non_scaled.is_empty() || !fixed.is_empty() {
            let rand_point = loader.ecc_chip.load_random_point::<C>(&mut loader.ctx_mut()).unwrap();
            let mut acc = if let Some(prev) = sum {
                loader
                    .ecc_chip
                    .add_unequal(&mut loader.ctx_mut(), &prev, &rand_point, true)
                    .unwrap()
            } else {
                rand_point.clone()
            };
            for point in non_scaled.into_iter() {
                acc =
                    loader.ecc_chip.add_unequal(&mut loader.ctx_mut(), &acc, &point, true).unwrap();
            }
            for (constant_point, scalar) in fixed.iter() {
                if constant_point.is_identity().into() {
                    continue;
                }
                let fixed_point = FixedEccPoint::from_g1(
                    constant_point,
                    loader.field_chip().num_limbs,
                    loader.field_chip().limb_bits,
                );
                let fixed_msm = loader
                    .ecc_chip
                    .fixed_base_scalar_mult(
                        &mut loader.ctx_mut(),
                        &fixed_point,
                        &vec![scalar.clone()],
                        C::Scalar::NUM_BITS as usize,
                        4,
                    )
                    .expect("fixed msms should not fail");
                acc = loader
                    .ecc_chip
                    .add_unequal(&mut loader.ctx_mut(), &acc, &fixed_msm, true)
                    .unwrap();
            }
            acc = loader
                .ecc_chip
                .sub_unequal(&mut loader.ctx_mut(), &acc, &rand_point, true)
                .unwrap();
            sum = Some(acc);
        }
        loader.ec_point(sum.unwrap())
    }
}

impl<'a, 'b, C: CurveAffine> Debug for EcPoint<'a, 'b, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EcPoint").field("assigned", &self.assigned()).finish()
    }
}

impl<'a, 'b, C: CurveAffine> Add for EcPoint<'a, 'b, C> {
    type Output = Self;

    fn add(self, _: Self) -> Self::Output {
        todo!()
    }
}

impl<'a, 'b, C: CurveAffine> Sub for EcPoint<'a, 'b, C> {
    type Output = Self;

    fn sub(self, _: Self) -> Self::Output {
        todo!()
    }
}

impl<'a, 'b, C: CurveAffine> Neg for EcPoint<'a, 'b, C> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        todo!()
    }
}

impl<'a, 'b, 'c, C: CurveAffine> Add<&'c Self> for EcPoint<'a, 'b, C> {
    type Output = Self;

    fn add(self, rhs: &'c Self) -> Self::Output {
        self + rhs.clone()
    }
}

impl<'a, 'b, 'c, C: CurveAffine> Sub<&'c Self> for EcPoint<'a, 'b, C> {
    type Output = Self;

    fn sub(self, rhs: &'c Self) -> Self::Output {
        self - rhs.clone()
    }
}

impl<'a, 'b, C: CurveAffine> AddAssign for EcPoint<'a, 'b, C> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs
    }
}

impl<'a, 'b, C: CurveAffine> SubAssign for EcPoint<'a, 'b, C> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs
    }
}

impl<'a, 'b, 'c, C: CurveAffine> AddAssign<&'c Self> for EcPoint<'a, 'b, C> {
    fn add_assign(&mut self, rhs: &'c Self) {
        *self = self.clone() + rhs
    }
}

impl<'a, 'b, 'c, C: CurveAffine> SubAssign<&'c Self> for EcPoint<'a, 'b, C> {
    fn sub_assign(&mut self, rhs: &'c Self) {
        *self = self.clone() - rhs
    }
}

impl<'a, 'b, C: CurveAffine> ScalarLoader<C::Scalar> for Rc<Halo2Loader<'a, 'b, C>> {
    type LoadedScalar = Scalar<'a, 'b, C>;

    fn load_const(&self, value: &C::Scalar) -> Scalar<'a, 'b, C> {
        self.scalar(Value::Constant(*value))
    }

    fn assert_eq(
        &self,
        annotation: &str,
        lhs: &Self::LoadedScalar,
        rhs: &Self::LoadedScalar,
    ) -> Result<(), crate::Error> {
        match (&lhs.value, &rhs.value) {
            (Value::Constant(lhs), Value::Constant(rhs)) => {
                assert_eq!(*lhs, *rhs);
            }
            _ => {
                let loader = lhs.loader();
                loader
                    .gate()
                    .assert_equal(&mut loader.ctx_mut(), &lhs.to_quantum(), &rhs.to_quantum())
                    .expect(annotation);
            }
        }
        Ok(())
    }

    fn sum_with_coeff_and_constant(
        &self,
        values: &[(C::Scalar, &Self::LoadedScalar)],
        constant: C::Scalar,
    ) -> Self::LoadedScalar {
        let mut a = Vec::with_capacity(values.len() + 1);
        let mut b = Vec::with_capacity(values.len() + 1);
        if constant != C::Scalar::zero() {
            a.push(Constant(C::Scalar::one()));
            b.push(Constant(constant));
        }
        a.extend(values.iter().map(|(_, a)| match &a.value {
            Value::Constant(constant) => Constant(*constant),
            Value::Assigned(assigned) => Existing(assigned),
        }));
        b.extend(values.iter().map(|(c, _)| Constant(*c)));
        let (_, _, sum) = self.gate().inner_product(&mut self.ctx_mut(), &a, &b).unwrap();

        self.scalar(Value::Assigned(sum))
    }

    fn sum_products_with_coeff_and_constant(
        &self,
        values: &[(C::Scalar, &Self::LoadedScalar, &Self::LoadedScalar)],
        constant: C::Scalar,
    ) -> Self::LoadedScalar {
        let mut prods = Vec::with_capacity(values.len());
        for (c, a, b) in values {
            let a = match &a.value {
                Value::Assigned(assigned) => Existing(assigned),
                Value::Constant(constant) => Constant(*constant),
            };
            let b = match &b.value {
                Value::Assigned(assigned) => Existing(assigned),
                Value::Constant(constant) => Constant(*constant),
            };
            prods.push((*c, a, b));
        }
        let output = self
            .gate()
            .sum_products_with_coeff_and_var(&mut self.ctx_mut(), &prods[..], &Constant(constant))
            .unwrap();
        self.scalar(Value::Assigned(output))
    }
}

impl<'a, 'b, C: CurveAffine> EcPointLoader<C> for Rc<Halo2Loader<'a, 'b, C>> {
    type LoadedEcPoint = EcPoint<'a, 'b, C>;

    fn ec_point_load_const(&self, ec_point: &C) -> EcPoint<'a, 'b, C> {
        self.assign_const_ec_point(*ec_point)
    }

    fn ec_point_load_one(&self) -> Self::LoadedEcPoint {
        self.ec_point(self.assign_const_ec_point(C::generator()).assigned())
    }

    fn ec_point_assert_eq(
        &self,
        annotation: &str,
        lhs: &Self::LoadedEcPoint,
        rhs: &Self::LoadedEcPoint,
    ) -> Result<(), crate::Error> {
        let loader = lhs.loader();
        match (&lhs.value, &rhs.value) {
            (Value::Constant(lhs), Value::Constant(rhs)) => {
                assert_eq!(*lhs, *rhs);
            }
            _ => {
                loader
                    .ecc_chip
                    .assert_equal(&mut loader.ctx_mut(), &lhs.assigned(), &rhs.assigned())
                    .expect(annotation);
            }
        }
        Ok(())
    }
}

impl<'a, 'b, C: CurveAffine> Loader<C> for Rc<Halo2Loader<'a, 'b, C>> {
    // only using this when `sel = use_dummy` and `a` is dummy
    // you should never use dummy if `b` is constant
    fn ec_point_select(
        &self,
        a: &Self::LoadedEcPoint,
        b: &Self::LoadedEcPoint,
        sel: &Self::LoadedScalar,
    ) -> Result<Self::LoadedEcPoint, crate::Error> {
        if matches!(b.value, Value::Constant(_)) {
            return Ok(b.clone());
        }
        let a = a.assigned();
        let b = b.assigned();
        let sel = sel.assigned();
        let assigned = halo2_ecc::ecc::select(self.field_chip(), &mut self.ctx_mut(), &a, &b, &sel)
            .expect("ec_point_select should not fail");
        Ok(self.ec_point(assigned))
    }
}
