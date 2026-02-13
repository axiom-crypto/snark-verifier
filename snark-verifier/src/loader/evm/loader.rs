use crate::{
    loader::{
        evm::{
            code::{EvmCodegenMode, Precompiled, SolidityAssemblyCode},
            compact_codegen::{build_compact_verifier_artifacts, CompactVerifierArtifacts},
            compact_ir::{
                CompactInstruction, CompactOperand, CompactProgram, CompactProgramBuilder,
            },
            fe_to_u256, modulus, u256_to_fe, U256, U512,
        },
        EcPointLoader, LoadedEcPoint, LoadedScalar, Loader, ScalarLoader,
    },
    util::{
        arithmetic::{Coordinates, CurveAffine, FieldOps, PrimeField},
        Itertools,
    },
};
use hex;
use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::{self, Debug},
    iter,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    rc::Rc,
};

/// Memory pointer starts at 0x80, which is the end of the Solidity memory layout scratch space.
pub const MEM_PTR_START: usize = 0x80;
const BLS_ENCODED_FP_BYTES: usize = 0x40;
const BLS_G1_BYTES: usize = 2 * BLS_ENCODED_FP_BYTES;
const BLS_G2_BYTES: usize = 4 * BLS_ENCODED_FP_BYTES;
const PROOF_COMPRESSED_SIGN_BYTES: usize = 0x01;
const COMPRESSED_SCRATCH_MODEXP_BYTES: usize = 0x120;

#[derive(Clone, Debug)]
pub enum Value<T> {
    Constant(T),
    Memory(usize),
    Negated(Box<Value<T>>),
    Sum(Box<Value<T>>, Box<Value<T>>),
    Product(Box<Value<T>>, Box<Value<T>>),
}

impl<T: Debug> PartialEq for Value<T> {
    fn eq(&self, other: &Self) -> bool {
        self.identifier() == other.identifier()
    }
}

impl<T: Debug> Value<T> {
    fn identifier(&self) -> String {
        match self {
            Value::Constant(_) | Value::Memory(_) => format!("{self:?}"),
            Value::Negated(value) => format!("-({value:?})"),
            Value::Sum(lhs, rhs) => format!("({lhs:?} + {rhs:?})"),
            Value::Product(lhs, rhs) => format!("({lhs:?} * {rhs:?})"),
        }
    }
}

/// `Loader` implementation for generating yul code as EVM verifier.
#[derive(Clone, Debug)]
pub struct EvmLoader {
    scalar_modulus: U256,
    codegen_mode: EvmCodegenMode,
    base_field_bytes: usize,
    base_modulus_words: [U256; 2],
    base_sqrt_exp_words: [U256; 2],
    compressed_modexp_input_ptr: usize,
    compressed_rhs_ptr: usize,
    compressed_y_sq_ptr: usize,
    code: RefCell<SolidityAssemblyCode>,
    compact_program: RefCell<CompactProgramBuilder>,
    ptr: RefCell<usize>,
    cache: RefCell<HashMap<String, usize>>,
}

fn hex_encode_u256(value: &U256) -> String {
    format!("0x{}", hex::encode(value.to_be_bytes::<32>()))
}

fn be_bytes_to_u256(bytes: &[u8]) -> U256 {
    let word: [u8; 32] = bytes.try_into().expect("word must be 32 bytes");
    U256::from_be_bytes(word)
}

fn le_bytes_to_padded_be_words(bytes_le: &[u8]) -> [U256; 2] {
    assert!(bytes_le.len() <= BLS_ENCODED_FP_BYTES);
    let mut padded = [0u8; BLS_ENCODED_FP_BYTES];
    let be = bytes_le.iter().rev().copied().collect_vec();
    let offset = BLS_ENCODED_FP_BYTES - be.len();
    padded[offset..].copy_from_slice(&be);
    [be_bytes_to_u256(&padded[..0x20]), be_bytes_to_u256(&padded[0x20..BLS_ENCODED_FP_BYTES])]
}

fn modulus_u512<F>() -> U512
where
    F: PrimeField,
{
    let repr = (-F::ONE).to_repr();
    let repr = repr.as_ref();
    assert!(
        repr.len() <= 64,
        "Field encoding length must be <= 64 bytes for EVM compressed-point support"
    );
    let mut le = [0u8; 64];
    le[..repr.len()].copy_from_slice(repr);
    U512::from_le_bytes(le) + U512::from(1)
}

fn u512_to_be_words(value: U512) -> [U256; 2] {
    let bytes = value.to_be_bytes::<64>();
    [be_bytes_to_u256(&bytes[..0x20]), be_bytes_to_u256(&bytes[0x20..])]
}

impl EvmLoader {
    /// Initialize a [`EvmLoader`] with base and scalar field.
    pub fn new<Base, Scalar>() -> Rc<Self>
    where
        Base: PrimeField,
        Scalar: PrimeField<Repr = [u8; 32]>,
    {
        Self::new_with_mode::<Base, Scalar>(EvmCodegenMode::Unrolled)
    }

    /// Initialize a [`EvmLoader`] with the selected EVM codegen mode.
    pub fn new_with_mode<Base, Scalar>(codegen_mode: EvmCodegenMode) -> Rc<Self>
    where
        Base: PrimeField,
        Scalar: PrimeField<Repr = [u8; 32]>,
    {
        let base_field_bytes = Base::Repr::default().as_ref().len();
        assert!(
            base_field_bytes <= BLS_ENCODED_FP_BYTES,
            "Base field encoding length must be <= 64 bytes"
        );
        let scalar_modulus = modulus::<Scalar>();
        let base_modulus = modulus_u512::<Base>();
        let base_modulus_words = u512_to_be_words(base_modulus);
        let base_sqrt_exp_words = u512_to_be_words((base_modulus + U512::from(1)) / U512::from(4));
        let code = SolidityAssemblyCode::new();
        // Reserve a small fixed scratch area for compressed-point decompression so
        // transcript allocations remain monotonic and non-overlapping.
        let compressed_modexp_input_ptr = MEM_PTR_START;
        let compressed_rhs_ptr = compressed_modexp_input_ptr + COMPRESSED_SCRATCH_MODEXP_BYTES;
        let compressed_y_sq_ptr = compressed_rhs_ptr + BLS_ENCODED_FP_BYTES;
        let ptr = compressed_y_sq_ptr + BLS_ENCODED_FP_BYTES;

        Rc::new(Self {
            scalar_modulus,
            codegen_mode,
            base_field_bytes,
            base_modulus_words,
            base_sqrt_exp_words,
            compressed_modexp_input_ptr,
            compressed_rhs_ptr,
            compressed_y_sq_ptr,
            code: RefCell::new(code),
            compact_program: RefCell::new(CompactProgramBuilder::new()),
            ptr: RefCell::new(ptr),
            cache: Default::default(),
        })
    }

    /// Returns generated Solidity code. This is "Solidity" code that is wrapped in an assembly block.
    /// In other words, it's basically just assembly (equivalently, Yul).
    pub fn solidity_code(self: &Rc<Self>) -> String {
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                let code = "
                    // Revert if anything fails
                    if iszero(success) { revert(0, 0) }

                    // Return empty bytes on success
                    return(0, 0)"
                    .to_string();
                self.code.borrow_mut().runtime_append(code);
                self.code.borrow().code(hex_encode_u256(&self.scalar_modulus))
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_verifier_artifacts().runtime_solidity
            }
        }
    }

    /// Returns the selected codegen mode.
    pub fn codegen_mode(&self) -> EvmCodegenMode {
        self.codegen_mode
    }

    fn is_compact_codegen(&self) -> bool {
        matches!(self.codegen_mode, EvmCodegenMode::Compact | EvmCodegenMode::Hybrid)
    }

    fn is_hybrid_codegen(&self) -> bool {
        self.codegen_mode == EvmCodegenMode::Hybrid
    }

    /// Returns the compact encoded program, if compact mode is enabled.
    pub fn compact_program(&self) -> Option<CompactProgram> {
        self.is_compact_codegen().then(|| self.compact_program.borrow().encode())
    }

    /// Returns compact verifier runtime source plus data-page artifacts.
    pub fn compact_verifier_artifacts(&self) -> CompactVerifierArtifacts {
        assert!(
            self.is_compact_codegen(),
            "compact verifier artifacts are only available in compact/hybrid mode"
        );
        let program = self.compact_program.borrow().encode();
        build_compact_verifier_artifacts(self.scalar_modulus, &program, self.ptr())
    }

    /// Allocates memory chunk with given `size` and returns pointer.
    pub fn allocate(self: &Rc<Self>, size: usize) -> usize {
        let ptr = *self.ptr.borrow();
        *self.ptr.borrow_mut() += size;
        ptr
    }

    pub(crate) fn ptr(&self) -> usize {
        *self.ptr.borrow()
    }

    pub(crate) fn proof_ec_point_bytes(&self) -> usize {
        2 * self.base_field_bytes
    }

    pub(crate) fn proof_ec_point_compressed_bytes(&self) -> usize {
        self.base_field_bytes + PROOF_COMPRESSED_SIGN_BYTES
    }

    pub(crate) fn evm_ec_point_bytes(&self) -> usize {
        BLS_G1_BYTES
    }

    fn compact_emit(&self, instruction: CompactInstruction) {
        self.compact_program.borrow_mut().push(instruction);
    }

    fn emit_mstore_const(self: &Rc<Self>, ptr: usize, value: U256) {
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                self.code
                    .borrow_mut()
                    .runtime_append(format!("mstore({ptr:#x}, {})", hex_encode_u256(&value)));
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_emit(CompactInstruction::MstoreConst { dst: ptr, value });
            }
        }
    }

    pub(crate) fn emit_mstore_mem(self: &Rc<Self>, dst: usize, src: usize) {
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                self.code.borrow_mut().runtime_append(format!("mstore({dst:#x}, mload({src:#x}))"));
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_emit(CompactInstruction::MstoreMem { dst, src });
            }
        }
    }

    pub(crate) fn emit_mstore8(self: &Rc<Self>, dst: usize, value: u8) {
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                self.code.borrow_mut().runtime_append(format!("mstore8({dst:#x}, {value})"));
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_emit(CompactInstruction::Mstore8 { dst, value });
            }
        }
    }

    pub(crate) fn emit_mod_from_mem(self: &Rc<Self>, dst: usize, src: usize) {
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                self.code
                    .borrow_mut()
                    .runtime_append(format!("mstore({dst:#x}, mod(mload({src:#x}), f_q))"));
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_emit(CompactInstruction::ModFromMem { dst, src });
            }
        }
    }

    fn compact_operand(self: &Rc<Self>, value: &Value<U256>) -> CompactOperand {
        match value {
            Value::Constant(constant) => CompactOperand::Constant(*constant),
            Value::Memory(ptr) => CompactOperand::Memory(*ptr),
            _ => {
                let scalar = self.scalar(value.clone());
                CompactOperand::Memory(scalar.ptr())
            }
        }
    }

    fn compact_emit_scalar_value(self: &Rc<Self>, dst: usize, value: &Value<U256>) {
        match value {
            Value::Constant(constant) => {
                self.compact_emit(CompactInstruction::MstoreConst { dst, value: *constant })
            }
            Value::Memory(src) => {
                if *src != dst {
                    self.compact_emit(CompactInstruction::MstoreMem { dst, src: *src });
                }
            }
            Value::Negated(inner) => {
                if self.is_hybrid_codegen() {
                    if let Value::Memory(src) = inner.as_ref() {
                        self.compact_emit(CompactInstruction::ScalarNegMem { dst, src: *src });
                        return;
                    }
                }
                let operand = self.compact_operand(inner);
                self.compact_emit(CompactInstruction::ScalarNeg { dst, operand });
            }
            Value::Sum(lhs, rhs) => {
                if self.is_hybrid_codegen() {
                    if let (Value::Memory(lhs_ptr), Value::Memory(rhs_ptr)) =
                        (lhs.as_ref(), rhs.as_ref())
                    {
                        self.compact_emit(CompactInstruction::ScalarAddMemMem {
                            dst,
                            lhs: *lhs_ptr,
                            rhs: *rhs_ptr,
                        });
                        return;
                    }
                }
                let lhs = self.compact_operand(lhs);
                let rhs = self.compact_operand(rhs);
                self.compact_emit(CompactInstruction::ScalarAdd { dst, lhs, rhs });
            }
            Value::Product(lhs, rhs) => {
                if self.is_hybrid_codegen() {
                    if let (Value::Memory(lhs_ptr), Value::Memory(rhs_ptr)) =
                        (lhs.as_ref(), rhs.as_ref())
                    {
                        self.compact_emit(CompactInstruction::ScalarMulMemMem {
                            dst,
                            lhs: *lhs_ptr,
                            rhs: *rhs_ptr,
                        });
                        return;
                    }
                }
                let lhs = self.compact_operand(lhs);
                let rhs = self.compact_operand(rhs);
                self.compact_emit(CompactInstruction::ScalarMul { dst, lhs, rhs });
            }
        }
    }

    fn push(self: &Rc<Self>, scalar: &Scalar) -> String {
        match scalar.value.clone() {
            Value::Constant(constant) => {
                format!("{constant}")
            }
            Value::Memory(ptr) => {
                format!("mload({ptr:#x})")
            }
            Value::Negated(value) => {
                let v = self.push(&self.scalar(*value));
                format!("sub(f_q, {v})")
            }
            Value::Sum(lhs, rhs) => {
                let lhs = self.push(&self.scalar(*lhs));
                let rhs = self.push(&self.scalar(*rhs));
                format!("addmod({lhs}, {rhs}, f_q)")
            }
            Value::Product(lhs, rhs) => {
                let lhs = self.push(&self.scalar(*lhs));
                let rhs = self.push(&self.scalar(*rhs));
                format!("mulmod({lhs}, {rhs}, f_q)")
            }
        }
    }

    /// Calldata load a field element.
    pub fn calldataload_scalar(self: &Rc<Self>, offset: usize) -> Scalar {
        let ptr = self.allocate(0x20);
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                let code = format!("mstore({ptr:#x}, mod(calldataload({offset:#x}), f_q))");
                self.code.borrow_mut().runtime_append(code);
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_emit(CompactInstruction::CalldataScalar { dst: ptr, offset });
            }
        }
        self.scalar(Value::Memory(ptr))
    }

    /// Calldata load an elliptic curve point and validate it's on affine plane.
    /// Note that identity will cause the verification to fail.
    pub fn calldataload_ec_point(self: &Rc<Self>, offset: usize) -> EcPoint {
        let x_ptr = self.allocate(BLS_G1_BYTES);
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                let y_ptr = x_ptr + BLS_ENCODED_FP_BYTES;
                let coord_bytes = self.base_field_bytes;
                let pad = BLS_ENCODED_FP_BYTES - coord_bytes;
                let x_cd_ptr = offset;
                let y_cd_ptr = offset + coord_bytes;
                let code = format!(
                    "
                {{
                    mstore({x_ptr:#x}, 0)
                    mstore({:#x}, 0)
                    mstore({y_ptr:#x}, 0)
                    mstore({:#x}, 0)
                    calldatacopy({:#x}, {x_cd_ptr:#x}, {coord_bytes:#x})
                    calldatacopy({:#x}, {y_cd_ptr:#x}, {coord_bytes:#x})
                }}",
                    x_ptr + 0x20,
                    y_ptr + 0x20,
                    x_ptr + pad,
                    y_ptr + pad
                );
                self.code.borrow_mut().runtime_append(code);
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_emit(CompactInstruction::CalldataPointUncompressed {
                    dst: x_ptr,
                    offset,
                    coord_bytes: self.base_field_bytes,
                });
            }
        }
        self.ec_point(Value::Memory(x_ptr))
    }

    /// Calldata load an elliptic curve point encoded as `[sign_byte || x_coordinate]`,
    /// where:
    /// - `sign_byte bit0` encodes whether y is odd,
    /// - `sign_byte bit1` encodes point-at-infinity.
    ///
    /// This decompresses into EIP-2537 uncompressed `(x, y)` form in memory.
    pub fn calldataload_ec_point_compressed(self: &Rc<Self>, offset: usize) -> EcPoint {
        if self.is_compact_codegen() {
            panic!("compact EVM codegen does not support compressed proof-point encoding yet");
        }

        let point_ptr = self.allocate(BLS_G1_BYTES);
        let x_ptr = point_ptr;
        let y_ptr = point_ptr + BLS_ENCODED_FP_BYTES;
        let modexp_input_ptr = self.compressed_modexp_input_ptr;
        let rhs_ptr = self.compressed_rhs_ptr;
        let y_sq_ptr = self.compressed_y_sq_ptr;

        let coord_bytes = self.base_field_bytes;
        let pad = BLS_ENCODED_FP_BYTES - coord_bytes;
        let x_cd_ptr = offset + PROOF_COMPRESSED_SIGN_BYTES;

        let p_hi = hex_encode_u256(&self.base_modulus_words[0]);
        let p_lo = hex_encode_u256(&self.base_modulus_words[1]);
        let sqrt_exp_hi = hex_encode_u256(&self.base_sqrt_exp_words[0]);
        let sqrt_exp_lo = hex_encode_u256(&self.base_sqrt_exp_words[1]);

        let code = format!(
            "
        {{
            let flag := byte(0, calldataload({offset:#x}))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore({x_ptr:#x}, 0)
            mstore({:#x}, 0)
            mstore({y_ptr:#x}, 0)
            mstore({:#x}, 0)
            calldatacopy({:#x}, {x_cd_ptr:#x}, {coord_bytes:#x})

            let x_hi := mload({x_ptr:#x})
            let x_lo := mload({:#x})

            if is_inf {{
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }}

            if iszero(is_inf) {{
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, {p_hi}), and(eq(x_hi, {p_hi}), lt(x_lo, {p_lo}))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore({modexp_input_ptr:#x}, 0x40)
                mstore({:#x}, 0x40)
                mstore({:#x}, 0x40)
                mstore({:#x}, x_hi)
                mstore({:#x}, x_lo)
                mstore({:#x}, 0)
                mstore({:#x}, 3)
                mstore({:#x}, {p_hi})
                mstore({:#x}, {p_lo})
                success := and(
                    eq(staticcall(gas(), 0x5, {modexp_input_ptr:#x}, 0x120, {rhs_ptr:#x}, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload({rhs_ptr:#x})
                let rhs_lo0 := mload({:#x})
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, {p_hi}), and(eq(rhs_hi, {p_hi}), iszero(lt(rhs_lo, {p_lo})))) {{
                    rhs_hi := sub(rhs_hi, {p_hi})
                    let borrow := lt(rhs_lo, {p_lo})
                    rhs_lo := sub(rhs_lo, {p_lo})
                    rhs_hi := sub(rhs_hi, borrow)
                }}
                mstore({rhs_ptr:#x}, rhs_hi)
                mstore({:#x}, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore({modexp_input_ptr:#x}, 0x40)
                mstore({:#x}, 0x40)
                mstore({:#x}, 0x40)
                mstore({:#x}, rhs_hi)
                mstore({:#x}, rhs_lo)
                mstore({:#x}, {sqrt_exp_hi})
                mstore({:#x}, {sqrt_exp_lo})
                mstore({:#x}, {p_hi})
                mstore({:#x}, {p_lo})
                success := and(
                    eq(staticcall(gas(), 0x5, {modexp_input_ptr:#x}, 0x120, {y_ptr:#x}, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore({modexp_input_ptr:#x}, 0x40)
                mstore({:#x}, 0x40)
                mstore({:#x}, 0x40)
                mstore({:#x}, mload({y_ptr:#x}))
                mstore({:#x}, mload({:#x}))
                mstore({:#x}, 0)
                mstore({:#x}, 2)
                mstore({:#x}, {p_hi})
                mstore({:#x}, {p_lo})
                success := and(
                    eq(staticcall(gas(), 0x5, {modexp_input_ptr:#x}, 0x120, {y_sq_ptr:#x}, 0x40), 1),
                    success
                )
                success := and(eq(mload({y_sq_ptr:#x}), mload({rhs_ptr:#x})), success)
                success := and(eq(mload({:#x}), mload({:#x})), success)

                // Select y root by oddness bit.
                let y_lo := mload({:#x})
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {{
                    let neg_y_lo := sub({p_lo}, y_lo)
                    let borrow := lt({p_lo}, y_lo)
                    let neg_y_hi := sub(sub({p_hi}, mload({y_ptr:#x})), borrow)
                    mstore({y_ptr:#x}, neg_y_hi)
                    mstore({:#x}, neg_y_lo)
                }}
            }}
        }}",
            x_ptr + 0x20,
            y_ptr + 0x20,
            x_ptr + pad,
            x_ptr + 0x20,
            modexp_input_ptr + 0x20,
            modexp_input_ptr + 0x40,
            modexp_input_ptr + 0x60,
            modexp_input_ptr + 0x80,
            modexp_input_ptr + 0xa0,
            modexp_input_ptr + 0xc0,
            modexp_input_ptr + 0xe0,
            modexp_input_ptr + 0x100,
            rhs_ptr + 0x20,
            rhs_ptr + 0x20,
            modexp_input_ptr + 0x20,
            modexp_input_ptr + 0x40,
            modexp_input_ptr + 0x60,
            modexp_input_ptr + 0x80,
            modexp_input_ptr + 0xa0,
            modexp_input_ptr + 0xc0,
            modexp_input_ptr + 0xe0,
            modexp_input_ptr + 0x100,
            modexp_input_ptr + 0x20,
            modexp_input_ptr + 0x40,
            modexp_input_ptr + 0x60,
            modexp_input_ptr + 0x80,
            y_ptr + 0x20,
            modexp_input_ptr + 0xa0,
            modexp_input_ptr + 0xc0,
            modexp_input_ptr + 0xe0,
            modexp_input_ptr + 0x100,
            y_sq_ptr + 0x20,
            rhs_ptr + 0x20,
            y_ptr + 0x20,
            y_ptr + 0x20,
        );
        self.code.borrow_mut().runtime_append(code);
        self.ec_point(Value::Memory(point_ptr))
    }

    /// Decode an elliptic curve point from limbs.
    pub fn ec_point_from_limbs<const LIMBS: usize, const BITS: usize>(
        self: &Rc<Self>,
        x_limbs: [&Scalar; LIMBS],
        y_limbs: [&Scalar; LIMBS],
    ) -> EcPoint {
        let ptr = self.allocate(BLS_G1_BYTES);
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                let mut code = String::new();
                let x_ptr = ptr;
                code.push_str("let x_lo := 0\n");
                code.push_str("let x_hi := 0\n");
                for (idx, limb) in x_limbs.iter().enumerate() {
                    let limb_i = self.push(limb);
                    let shift = idx * BITS;
                    assert!(shift < 512, "limb decomposition exceeds 512 bits");
                    if shift < 256 {
                        code.push_str(
                            format!("x_lo := add(x_lo, shl({shift}, {limb_i}))\n").as_str(),
                        );
                    } else {
                        code.push_str(
                            format!("x_hi := add(x_hi, shl({}, {limb_i}))\n", shift - 256).as_str(),
                        );
                    }
                }
                code.push_str(format!("mstore({x_ptr:#x}, x_hi)\n").as_str());
                code.push_str(format!("mstore({:#x}, x_lo)\n", x_ptr + 0x20).as_str());

                let y_ptr = ptr + BLS_ENCODED_FP_BYTES;
                code.push_str("let y_lo := 0\n");
                code.push_str("let y_hi := 0\n");
                for (idx, limb) in y_limbs.iter().enumerate() {
                    let limb_i = self.push(limb);
                    let shift = idx * BITS;
                    assert!(shift < 512, "limb decomposition exceeds 512 bits");
                    if shift < 256 {
                        code.push_str(
                            format!("y_lo := add(y_lo, shl({shift}, {limb_i}))\n").as_str(),
                        );
                    } else {
                        code.push_str(
                            format!("y_hi := add(y_hi, shl({}, {limb_i}))\n", shift - 256).as_str(),
                        );
                    }
                }
                code.push_str(format!("mstore({y_ptr:#x}, y_hi)\n").as_str());
                code.push_str(format!("mstore({:#x}, y_lo)\n", y_ptr + 0x20).as_str());

                let code = format!(
                    "{{
                    {code}
                }}"
                );
                self.code.borrow_mut().runtime_append(code);
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                let x_limbs = x_limbs
                    .iter()
                    .map(|limb| self.compact_operand(&limb.value))
                    .collect::<Vec<_>>();
                let y_limbs = y_limbs
                    .iter()
                    .map(|limb| self.compact_operand(&limb.value))
                    .collect::<Vec<_>>();
                self.compact_emit(CompactInstruction::PointFromLimbs {
                    dst: ptr,
                    bits: BITS,
                    x_limbs,
                    y_limbs,
                });
            }
        }
        self.ec_point(Value::Memory(ptr))
    }

    pub(crate) fn scalar(self: &Rc<Self>, value: Value<U256>) -> Scalar {
        let value = if matches!(value, Value::Constant(_) | Value::Memory(_))
            || (self.codegen_mode == EvmCodegenMode::Unrolled && matches!(value, Value::Negated(_)))
        {
            value
        } else {
            let identifier = value.identifier();
            let some_ptr = self.cache.borrow().get(&identifier).cloned();
            let ptr = if let Some(ptr) = some_ptr {
                ptr
            } else {
                let ptr = self.allocate(0x20);
                match self.codegen_mode {
                    EvmCodegenMode::Unrolled => {
                        let v = self.push(&Scalar { loader: self.clone(), value });
                        self.code.borrow_mut().runtime_append(format!("mstore({ptr:#x}, {v})"));
                    }
                    EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                        self.compact_emit_scalar_value(ptr, &value);
                    }
                }
                self.cache.borrow_mut().insert(identifier, ptr);
                ptr
            };
            Value::Memory(ptr)
        };
        Scalar { loader: self.clone(), value }
    }

    fn ec_point(self: &Rc<Self>, value: Value<(U256, U256)>) -> EcPoint {
        EcPoint { loader: self.clone(), value }
    }

    /// Performs `KECCAK256` on `memory[ptr..ptr+len]` and returns pointer of
    /// hash.
    pub fn keccak256(self: &Rc<Self>, ptr: usize, len: usize) -> usize {
        let hash_ptr = self.allocate(0x20);
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                let code = format!("mstore({hash_ptr:#x}, keccak256({ptr:#x}, {len}))");
                self.code.borrow_mut().runtime_append(code);
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_emit(CompactInstruction::Keccak { dst: hash_ptr, ptr, len });
            }
        }
        hash_ptr
    }

    /// Copies a field element into given `ptr`.
    pub fn copy_scalar(self: &Rc<Self>, scalar: &Scalar, ptr: usize) {
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                let scalar = self.push(scalar);
                self.code.borrow_mut().runtime_append(format!("mstore({ptr:#x}, {scalar})"));
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_emit_scalar_value(ptr, &scalar.value);
            }
        }
    }

    /// Allocates a new field element and copies the given value into it.
    pub fn dup_scalar(self: &Rc<Self>, scalar: &Scalar) -> Scalar {
        let ptr = self.allocate(0x20);
        self.copy_scalar(scalar, ptr);
        self.scalar(Value::Memory(ptr))
    }

    /// Allocates a new elliptic curve point and copies the given value into it.
    pub fn copy_ec_point(self: &Rc<Self>, value: &EcPoint, ptr: usize) {
        match value.value {
            Value::Memory(src_ptr) => match self.codegen_mode {
                EvmCodegenMode::Unrolled => {
                    let src_words = (0..(BLS_G1_BYTES / 0x20)).map(|idx| src_ptr + idx * 0x20);
                    let dst_words = (0..(BLS_G1_BYTES / 0x20)).map(|idx| ptr + idx * 0x20);
                    let stores = dst_words
                        .zip(src_words)
                        .map(|(dst, src)| format!("mstore({dst:#x}, mload({src:#x}))"))
                        .join("\n");
                    let code = format!(
                        "{{
                            {stores}
                        }}"
                    );
                    self.code.borrow_mut().runtime_append(code);
                }
                EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                    self.compact_emit(CompactInstruction::CopyPoint { dst: ptr, src: src_ptr });
                }
            },
            Value::Constant(_) | Value::Negated(_) | Value::Sum(_, _) | Value::Product(_, _) => {
                unreachable!()
            }
        }
    }

    /// Allocates a new elliptic curve point and copies the given value into it.
    pub fn dup_ec_point(self: &Rc<Self>, value: &EcPoint) -> EcPoint {
        let ptr = self.allocate(BLS_G1_BYTES);
        self.copy_ec_point(value, ptr);
        self.ec_point(Value::Memory(ptr))
    }

    fn staticcall(self: &Rc<Self>, precompile: Precompiled, cd_ptr: usize, rd_ptr: usize) {
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                let (cd_len, rd_len) = match precompile {
                    Precompiled::BigModExp => (0xc0, 0x20),
                    Precompiled::Bls12_381G1Add => (2 * BLS_G1_BYTES, BLS_G1_BYTES),
                    // We use G1MSM with a single pair: [G1 point (128 bytes) || scalar (32 bytes)].
                    Precompiled::Bls12_381G1Msm => (BLS_G1_BYTES + 0x20, BLS_G1_BYTES),
                    // 2 pairings in one call:
                    //   [G1 (128) || G2 (256)] * 2 = 768 bytes
                    Precompiled::Bls12_381Pairing => (2 * (BLS_G1_BYTES + BLS_G2_BYTES), 0x20),
                };
                let a = precompile as usize;
                let code = format!("success := and(eq(staticcall(gas(), {a:#x}, {cd_ptr:#x}, {cd_len:#x}, {rd_ptr:#x}, {rd_len:#x}), 1), success)");
                self.code.borrow_mut().runtime_append(code);
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_emit(CompactInstruction::StaticCall {
                    precompile: precompile as usize,
                    cd_ptr,
                    rd_ptr,
                });
            }
        }
    }

    fn invert(self: &Rc<Self>, scalar: &Scalar) -> Scalar {
        let rd_ptr = self.allocate(0x20);
        let [cd_ptr, ..] = [
            &self.scalar(Value::Constant(U256::from(0x20))),
            &self.scalar(Value::Constant(U256::from(0x20))),
            &self.scalar(Value::Constant(U256::from(0x20))),
            scalar,
            &self.scalar(Value::Constant(self.scalar_modulus - U256::from(2))),
            &self.scalar(Value::Constant(self.scalar_modulus)),
        ]
        .map(|value| self.dup_scalar(value).ptr());
        self.staticcall(Precompiled::BigModExp, cd_ptr, rd_ptr);
        self.scalar(Value::Memory(rd_ptr))
    }

    fn ec_point_add(self: &Rc<Self>, lhs: &EcPoint, rhs: &EcPoint) -> EcPoint {
        let rd_ptr = self.dup_ec_point(lhs).ptr();
        self.dup_ec_point(rhs);
        self.staticcall(Precompiled::Bls12_381G1Add, rd_ptr, rd_ptr);
        self.ec_point(Value::Memory(rd_ptr))
    }

    fn ec_point_scalar_mul(self: &Rc<Self>, ec_point: &EcPoint, scalar: &Scalar) -> EcPoint {
        let rd_ptr = self.dup_ec_point(ec_point).ptr();
        self.dup_scalar(scalar);
        self.staticcall(Precompiled::Bls12_381G1Msm, rd_ptr, rd_ptr);
        self.ec_point(Value::Memory(rd_ptr))
    }

    /// Performs pairing.
    pub fn pairing(
        self: &Rc<Self>,
        lhs: &EcPoint,
        g2: &[U256],
        rhs: &EcPoint,
        minus_s_g2: &[U256],
    ) {
        assert_eq!(g2.len(), BLS_G2_BYTES / 0x20, "g2 must contain exactly 8 words (256 bytes)");
        assert_eq!(
            minus_s_g2.len(),
            BLS_G2_BYTES / 0x20,
            "minus_s_g2 must contain exactly 8 words (256 bytes)"
        );

        let rd_ptr = self.dup_ec_point(lhs).ptr();
        self.allocate(BLS_G2_BYTES);
        for (idx, word) in g2.iter().enumerate() {
            self.emit_mstore_const(rd_ptr + BLS_G1_BYTES + idx * 0x20, *word);
        }

        self.dup_ec_point(rhs);
        self.allocate(BLS_G2_BYTES);
        for (idx, word) in minus_s_g2.iter().enumerate() {
            self.emit_mstore_const(
                rd_ptr + (BLS_G1_BYTES + BLS_G2_BYTES) + BLS_G1_BYTES + idx * 0x20,
                *word,
            );
        }

        self.staticcall(Precompiled::Bls12_381Pairing, rd_ptr, rd_ptr);
        match self.codegen_mode {
            EvmCodegenMode::Unrolled => {
                let code = format!("success := and(eq(mload({rd_ptr:#x}), 1), success)");
                self.code.borrow_mut().runtime_append(code);
            }
            EvmCodegenMode::Compact | EvmCodegenMode::Hybrid => {
                self.compact_emit(CompactInstruction::AssertOne { ptr: rd_ptr });
            }
        }
    }

    fn add(self: &Rc<Self>, lhs: &Scalar, rhs: &Scalar) -> Scalar {
        if let (Value::Constant(lhs), Value::Constant(rhs)) = (&lhs.value, &rhs.value) {
            let out = (U512::from(*lhs) + U512::from(*rhs)) % U512::from(self.scalar_modulus);
            return self.scalar(Value::Constant(U256::from(out)));
        }

        self.scalar(Value::Sum(Box::new(lhs.value.clone()), Box::new(rhs.value.clone())))
    }

    fn sub(self: &Rc<Self>, lhs: &Scalar, rhs: &Scalar) -> Scalar {
        if rhs.is_const() {
            return self.add(lhs, &self.neg(rhs));
        }

        self.scalar(Value::Sum(
            Box::new(lhs.value.clone()),
            Box::new(Value::Negated(Box::new(rhs.value.clone()))),
        ))
    }

    fn mul(self: &Rc<Self>, lhs: &Scalar, rhs: &Scalar) -> Scalar {
        if let (Value::Constant(lhs), Value::Constant(rhs)) = (&lhs.value, &rhs.value) {
            let out = (U512::from(*lhs) * U512::from(*rhs)) % U512::from(self.scalar_modulus);
            return self.scalar(Value::Constant(U256::from(out)));
        }

        self.scalar(Value::Product(Box::new(lhs.value.clone()), Box::new(rhs.value.clone())))
    }

    fn neg(self: &Rc<Self>, scalar: &Scalar) -> Scalar {
        if let Value::Constant(constant) = scalar.value {
            return self.scalar(Value::Constant(self.scalar_modulus - constant));
        }

        self.scalar(Value::Negated(Box::new(scalar.value.clone())))
    }
}

#[cfg(test)]
impl EvmLoader {
    fn start_gas_metering(self: &Rc<Self>, _: &str) {
        //  unimplemented
    }

    fn end_gas_metering(self: &Rc<Self>) {
        //  unimplemented
    }

    #[allow(dead_code)]
    fn print_gas_metering(self: &Rc<Self>, _: Vec<u64>) {
        //  unimplemented
    }
}

/// Elliptic curve point.
#[derive(Clone)]
pub struct EcPoint {
    loader: Rc<EvmLoader>,
    value: Value<(U256, U256)>,
}

impl EcPoint {
    pub(crate) fn loader(&self) -> &Rc<EvmLoader> {
        &self.loader
    }

    pub(crate) fn value(&self) -> Value<(U256, U256)> {
        self.value.clone()
    }

    pub(crate) fn ptr(&self) -> usize {
        match self.value {
            Value::Memory(ptr) => ptr,
            _ => unreachable!(),
        }
    }
}

impl Debug for EcPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EcPoint").field("value", &self.value).finish()
    }
}

impl PartialEq for EcPoint {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<C> LoadedEcPoint<C> for EcPoint
where
    C: CurveAffine,
    C::ScalarExt: PrimeField<Repr = [u8; 0x20]>,
{
    type Loader = Rc<EvmLoader>;

    fn loader(&self) -> &Rc<EvmLoader> {
        &self.loader
    }
}

/// Field element.
#[derive(Clone)]
pub struct Scalar {
    loader: Rc<EvmLoader>,
    value: Value<U256>,
}

impl Scalar {
    pub(crate) fn loader(&self) -> &Rc<EvmLoader> {
        &self.loader
    }

    pub(crate) fn value(&self) -> Value<U256> {
        self.value.clone()
    }

    pub(crate) fn is_const(&self) -> bool {
        matches!(self.value, Value::Constant(_))
    }

    pub(crate) fn ptr(&self) -> usize {
        match self.value {
            Value::Memory(ptr) => ptr,
            _ => *self.loader.cache.borrow().get(&self.value.identifier()).unwrap(),
        }
    }
}

impl Debug for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Scalar").field("value", &self.value).finish()
    }
}

impl Add for Scalar {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self.loader.add(&self, &rhs)
    }
}

impl Sub for Scalar {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self.loader.sub(&self, &rhs)
    }
}

impl Mul for Scalar {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        self.loader.mul(&self, &rhs)
    }
}

impl Neg for Scalar {
    type Output = Self;

    fn neg(self) -> Self {
        self.loader.neg(&self)
    }
}

impl<'a> Add<&'a Self> for Scalar {
    type Output = Self;

    fn add(self, rhs: &'a Self) -> Self {
        self.loader.add(&self, rhs)
    }
}

impl<'a> Sub<&'a Self> for Scalar {
    type Output = Self;

    fn sub(self, rhs: &'a Self) -> Self {
        self.loader.sub(&self, rhs)
    }
}

impl<'a> Mul<&'a Self> for Scalar {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self {
        self.loader.mul(&self, rhs)
    }
}

impl AddAssign for Scalar {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.loader.add(self, &rhs);
    }
}

impl SubAssign for Scalar {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.loader.sub(self, &rhs);
    }
}

impl MulAssign for Scalar {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.loader.mul(self, &rhs);
    }
}

impl<'a> AddAssign<&'a Self> for Scalar {
    fn add_assign(&mut self, rhs: &'a Self) {
        *self = self.loader.add(self, rhs);
    }
}

impl<'a> SubAssign<&'a Self> for Scalar {
    fn sub_assign(&mut self, rhs: &'a Self) {
        *self = self.loader.sub(self, rhs);
    }
}

impl<'a> MulAssign<&'a Self> for Scalar {
    fn mul_assign(&mut self, rhs: &'a Self) {
        *self = self.loader.mul(self, rhs);
    }
}

impl FieldOps for Scalar {
    fn invert(&self) -> Option<Scalar> {
        Some(self.loader.invert(self))
    }
}

impl PartialEq for Scalar {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<F: PrimeField<Repr = [u8; 0x20]>> LoadedScalar<F> for Scalar {
    type Loader = Rc<EvmLoader>;

    fn loader(&self) -> &Self::Loader {
        &self.loader
    }

    fn pow_var(&self, _exp: &Self, _exp_max_bits: usize) -> Self {
        todo!()
    }
}

impl<C> EcPointLoader<C> for Rc<EvmLoader>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    type LoadedEcPoint = EcPoint;

    fn ec_point_load_const(&self, value: &C) -> EcPoint {
        let [x_words, y_words] = match Option::<Coordinates<C>>::from(value.coordinates()) {
            Some(coordinates) => [coordinates.x(), coordinates.y()]
                .map(|coordinate| le_bytes_to_padded_be_words(coordinate.to_repr().as_ref())),
            // EVM precompiles encode point-at-infinity as (0, 0).
            None => [[U256::ZERO, U256::ZERO], [U256::ZERO, U256::ZERO]],
        };

        let ptr = self.allocate(BLS_G1_BYTES);
        self.emit_mstore_const(ptr, x_words[0]);
        self.emit_mstore_const(ptr + 0x20, x_words[1]);
        self.emit_mstore_const(ptr + BLS_ENCODED_FP_BYTES, y_words[0]);
        self.emit_mstore_const(ptr + BLS_ENCODED_FP_BYTES + 0x20, y_words[1]);
        self.ec_point(Value::Memory(ptr))
    }

    fn ec_point_assert_eq(&self, _: &str, _: &EcPoint, _: &EcPoint) {
        unimplemented!()
    }

    fn multi_scalar_multiplication(
        pairs: &[(&<Self as ScalarLoader<C::Scalar>>::LoadedScalar, &EcPoint)],
    ) -> EcPoint {
        pairs
            .iter()
            .cloned()
            .map(|(scalar, ec_point)| match scalar.value {
                Value::Constant(constant) if U256::from(1) == constant => ec_point.clone(),
                _ => ec_point.loader.ec_point_scalar_mul(ec_point, scalar),
            })
            .reduce(|acc, ec_point| acc.loader.ec_point_add(&acc, &ec_point))
            .expect("pairs should not be empty")
    }
}

impl<F: PrimeField<Repr = [u8; 0x20]>> ScalarLoader<F> for Rc<EvmLoader> {
    type LoadedScalar = Scalar;

    fn load_const(&self, value: &F) -> Scalar {
        self.scalar(Value::Constant(fe_to_u256(*value)))
    }

    fn assert_eq(&self, _: &str, _: &Scalar, _: &Scalar) {
        unimplemented!()
    }

    fn sum_with_coeff_and_const(&self, values: &[(F, &Scalar)], constant: F) -> Scalar {
        if self.is_compact_codegen() {
            let mut result = self.load_const(&constant);
            for (coeff, value) in values {
                assert_ne!(*coeff, F::ZERO);
                let addend = if *coeff == F::ONE {
                    (*value).clone()
                } else {
                    self.load_const(coeff) * *value
                };
                result += &addend;
            }
            return result;
        }

        if values.is_empty() {
            return self.load_const(&constant);
        }

        let push_addend = |(coeff, value): &(F, &Scalar)| {
            assert_ne!(*coeff, F::ZERO);
            match (*coeff == F::ONE, &value.value) {
                (true, _) => self.push(value),
                (false, Value::Constant(value)) => self.push(
                    &self.scalar(Value::Constant(fe_to_u256(*coeff * u256_to_fe::<F>(*value)))),
                ),
                (false, _) => {
                    let value = self.push(value);
                    let coeff = self.push(&self.scalar(Value::Constant(fe_to_u256(*coeff))));
                    format!("mulmod({value}, {coeff}, f_q)")
                }
            }
        };

        let mut values = values.iter();
        let initial_value = if constant == F::ZERO {
            push_addend(values.next().unwrap())
        } else {
            self.push(&self.scalar(Value::Constant(fe_to_u256(constant))))
        };

        let mut code = format!("let result := {initial_value}\n");
        for value in values {
            let v = push_addend(value);
            let addend = format!("result := addmod({v}, result, f_q)\n");
            code.push_str(addend.as_str());
        }

        let ptr = self.allocate(0x20);
        code.push_str(format!("mstore({ptr}, result)").as_str());
        self.code.borrow_mut().runtime_append(format!(
            "{{
            {code}
        }}"
        ));

        self.scalar(Value::Memory(ptr))
    }

    fn sum_products_with_coeff_and_const(
        &self,
        values: &[(F, &Scalar, &Scalar)],
        constant: F,
    ) -> Scalar {
        if self.is_compact_codegen() {
            let mut result = self.load_const(&constant);
            for (coeff, lhs, rhs) in values {
                assert_ne!(*coeff, F::ZERO);
                let product = if *coeff == F::ONE {
                    (*lhs).clone() * *rhs
                } else {
                    self.load_const(coeff) * *lhs * *rhs
                };
                result += &product;
            }
            return result;
        }

        if values.is_empty() {
            return self.load_const(&constant);
        }

        let push_addend = |(coeff, lhs, rhs): &(F, &Scalar, &Scalar)| {
            assert_ne!(*coeff, F::ZERO);
            match (*coeff == F::ONE, &lhs.value, &rhs.value) {
                (_, Value::Constant(lhs), Value::Constant(rhs)) => {
                    self.push(&self.scalar(Value::Constant(fe_to_u256(
                        *coeff * u256_to_fe::<F>(*lhs) * u256_to_fe::<F>(*rhs),
                    ))))
                }
                (_, value @ Value::Memory(_), Value::Constant(constant))
                | (_, Value::Constant(constant), value @ Value::Memory(_)) => {
                    let v1 = self.push(&self.scalar(value.clone()));
                    let v2 =
                        self.push(&self.scalar(Value::Constant(fe_to_u256(
                            *coeff * u256_to_fe::<F>(*constant),
                        ))));
                    format!("mulmod({v1}, {v2}, f_q)")
                }
                (true, _, _) => {
                    let rhs = self.push(rhs);
                    let lhs = self.push(lhs);
                    format!("mulmod({rhs}, {lhs}, f_q)")
                }
                (false, _, _) => {
                    let rhs = self.push(rhs);
                    let lhs = self.push(lhs);
                    let value = self.push(&self.scalar(Value::Constant(fe_to_u256(*coeff))));
                    format!("mulmod({rhs}, mulmod({lhs}, {value}, f_q), f_q)")
                }
            }
        };

        let mut values = values.iter();
        let initial_value = if constant == F::ZERO {
            push_addend(values.next().unwrap())
        } else {
            self.push(&self.scalar(Value::Constant(fe_to_u256(constant))))
        };

        let mut code = format!("let result := {initial_value}\n");
        for value in values {
            let v = push_addend(value);
            let addend = format!("result := addmod({v}, result, f_q)\n");
            code.push_str(addend.as_str());
        }

        let ptr = self.allocate(0x20);
        code.push_str(format!("mstore({ptr}, result)").as_str());
        self.code.borrow_mut().runtime_append(format!(
            "{{
            {code}
        }}"
        ));

        self.scalar(Value::Memory(ptr))
    }

    // batch_invert algorithm
    // n := values.len() - 1
    // input : values[0], ..., values[n]
    // output : values[0]^{-1}, ..., values[n]^{-1}
    // 1. products[i] <- values[0] * ... * values[i], i = 1, ..., n
    // 2. inv <- (products[n])^{-1}
    // 3. v_n <- values[n]
    // 4. values[n] <- products[n - 1] * inv (values[n]^{-1})
    // 5. inv <- v_n * inv
    fn batch_invert<'a>(values: impl IntoIterator<Item = &'a mut Scalar>) {
        let values = values.into_iter().collect_vec();
        let loader = &values.first().unwrap().loader;
        if loader.is_compact_codegen() {
            values.into_iter().for_each(|value| {
                *value = FieldOps::invert(&*value).unwrap_or_else(|| value.clone())
            });
            return;
        }

        let products = iter::once(values[0].clone())
            .chain(
                iter::repeat_with(|| loader.allocate(0x20))
                    .map(|ptr| loader.scalar(Value::Memory(ptr)))
                    .take(values.len() - 1),
            )
            .collect_vec();

        let initial_value = loader.push(products.first().unwrap());
        let mut code = format!("let prod := {initial_value}\n");
        for (value, product) in values.iter().zip(products.iter()).skip(1) {
            let v = loader.push(value);
            let ptr = product.ptr();
            code.push_str(
                format!(
                    "
                prod := mulmod({v}, prod, f_q)
                mstore({ptr:#x}, prod)
            "
                )
                .as_str(),
            );
        }
        loader.code.borrow_mut().runtime_append(format!(
            "{{
            {code}
        }}"
        ));

        let inv = loader.push(&loader.invert(products.last().unwrap()));

        let mut code = format!(
            "
            let inv := {inv}
            let v
        "
        );
        for (value, product) in
            values.iter().rev().zip(products.iter().rev().skip(1).map(Some).chain(iter::once(None)))
        {
            if let Some(product) = product {
                let val_ptr = value.ptr();
                let prod_ptr = product.ptr();
                let v = loader.push(value);
                code.push_str(
                    format!(
                        "
                    v := {v}
                    mstore({val_ptr}, mulmod(mload({prod_ptr:#x}), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                "
                    )
                    .as_str(),
                );
            } else {
                let ptr = value.ptr();
                code.push_str(format!("mstore({ptr:#x}, inv)\n").as_str());
            }
        }
        loader.code.borrow_mut().runtime_append(format!(
            "{{
            {code}
        }}"
        ));
    }
}

impl<C> Loader<C> for Rc<EvmLoader>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    #[cfg(test)]
    fn start_cost_metering(&self, identifier: &str) {
        self.start_gas_metering(identifier)
    }

    #[cfg(test)]
    fn end_cost_metering(&self) {
        self.end_gas_metering()
    }
}
