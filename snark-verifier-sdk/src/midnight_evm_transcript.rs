#![cfg(feature = "midnight")]

use anyhow::{anyhow, Result};
use ff::{Field, PrimeField};
use midnight_curves::{
    CurveAffine as MidnightCurveAffine, Fp as MidnightFp, Fq, G1Affine as MidnightG1Affine,
    G1Projective, B as MidnightCurveB,
};
use midnight_proofs::transcript::{Hashable, Sampleable, TranscriptHash};
use num_bigint::BigUint;
use sha3::{Digest, Keccak256};
use std::io::{self, Read};

const EVM_ENCODED_FP_BYTES: usize = 64;
const COMPRESSED_FLAG_Y_ODD: u8 = 0x01;
const COMPRESSED_FLAG_INFINITY: u8 = 0x02;

/// Transcript hash compatible with snark-verifier's EVM transcript semantics.
#[derive(Clone, Debug, Default)]
pub struct MidnightEvmHash {
    state: Vec<u8>,
}

impl TranscriptHash for MidnightEvmHash {
    type Input = Vec<u8>;
    type Output = Vec<u8>;

    fn init() -> Self {
        Self { state: Vec::new() }
    }

    fn absorb(&mut self, input: &Self::Input) {
        self.state.extend_from_slice(input);
    }

    fn squeeze(&mut self) -> Self::Output {
        let mut data = self.state.clone();
        if data.len() == 32 {
            data.push(1);
        }
        let digest = Keccak256::digest(data);
        self.state = digest.to_vec();
        digest.to_vec()
    }
}

/// Transcript hash with the same Fiat-Shamir semantics as [`MidnightEvmHash`],
/// but with compressed proof point byte encoding (`[sign || x]`) to reduce
/// proof/calldata size.
#[derive(Clone, Debug, Default)]
pub struct MidnightEvmHashCompressed {
    state: Vec<u8>,
}

impl TranscriptHash for MidnightEvmHashCompressed {
    type Input = Vec<u8>;
    type Output = Vec<u8>;

    fn init() -> Self {
        Self { state: Vec::new() }
    }

    fn absorb(&mut self, input: &Self::Input) {
        self.state.extend_from_slice(input);
    }

    fn squeeze(&mut self) -> Self::Output {
        let mut data = self.state.clone();
        if data.len() == 32 {
            data.push(1);
        }
        let digest = Keccak256::digest(data);
        self.state = digest.to_vec();
        digest.to_vec()
    }
}

impl Hashable<MidnightEvmHash> for Fq {
    fn to_input(&self) -> Vec<u8> {
        scalar_to_evm_bytes(self)
    }

    fn to_bytes(&self) -> Vec<u8> {
        scalar_to_evm_bytes(self)
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut be = [0u8; 32];
        buffer.read_exact(&mut be)?;
        scalar_from_evm_bytes(&be).map_err(|err| io::Error::other(err.to_string()))
    }
}

impl Hashable<MidnightEvmHashCompressed> for Fq {
    fn to_input(&self) -> Vec<u8> {
        scalar_to_evm_bytes(self)
    }

    fn to_bytes(&self) -> Vec<u8> {
        scalar_to_evm_bytes(self)
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut be = [0u8; 32];
        buffer.read_exact(&mut be)?;
        scalar_from_evm_bytes(&be).map_err(|err| io::Error::other(err.to_string()))
    }
}

impl Sampleable<MidnightEvmHash> for Fq {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert_eq!(hash_output.len(), 32, "MidnightEvmHash outputs 32 bytes");
        let value = BigUint::from_bytes_be(&hash_output);
        let modulus = BigUint::from_bytes_le((-Fq::ONE).to_repr().as_ref()) + BigUint::from(1u8);
        let reduced = value % modulus;
        let mut repr = <Fq as PrimeField>::Repr::default();
        let repr_len = repr.as_ref().len();
        let mut reduced_le = reduced.to_bytes_le();
        reduced_le.resize(repr_len, 0);
        repr.as_mut().copy_from_slice(&reduced_le[..repr_len]);
        Fq::from_repr(repr).unwrap()
    }
}

impl Sampleable<MidnightEvmHashCompressed> for Fq {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert_eq!(hash_output.len(), 32, "MidnightEvmHashCompressed outputs 32 bytes");
        let value = BigUint::from_bytes_be(&hash_output);
        let modulus = BigUint::from_bytes_le((-Fq::ONE).to_repr().as_ref()) + BigUint::from(1u8);
        let reduced = value % modulus;
        let mut repr = <Fq as PrimeField>::Repr::default();
        let repr_len = repr.as_ref().len();
        let mut reduced_le = reduced.to_bytes_le();
        reduced_le.resize(repr_len, 0);
        repr.as_mut().copy_from_slice(&reduced_le[..repr_len]);
        Fq::from_repr(repr).unwrap()
    }
}

impl Hashable<MidnightEvmHash> for G1Projective {
    fn to_input(&self) -> Vec<u8> {
        let affine = MidnightG1Affine::from(self);
        let coordinates = match Option::<midnight_curves::Coordinates<MidnightG1Affine>>::from(
            affine.coordinates(),
        ) {
            Some(coordinates) => coordinates,
            None => {
                return vec![0u8; 2 * EVM_ENCODED_FP_BYTES];
            }
        };
        let mut bytes = Vec::with_capacity(2 * EVM_ENCODED_FP_BYTES);
        bytes.extend_from_slice(&fp_to_evm_word(coordinates.x()));
        bytes.extend_from_slice(&fp_to_evm_word(coordinates.y()));
        bytes
    }

    fn to_bytes(&self) -> Vec<u8> {
        let affine = MidnightG1Affine::from(self);
        let coordinates = match Option::<midnight_curves::Coordinates<MidnightG1Affine>>::from(
            affine.coordinates(),
        ) {
            Some(coordinates) => coordinates,
            None => {
                return vec![0u8; 2 * midnight_fp_num_bytes()];
            }
        };
        let mut bytes = Vec::with_capacity(2 * midnight_fp_num_bytes());
        bytes.extend_from_slice(&fp_to_be_bytes(coordinates.x()));
        bytes.extend_from_slice(&fp_to_be_bytes(coordinates.y()));
        bytes
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let coord_bytes = midnight_fp_num_bytes();
        let mut x_be = vec![0u8; coord_bytes];
        let mut y_be = vec![0u8; coord_bytes];
        buffer.read_exact(&mut x_be)?;
        buffer.read_exact(&mut y_be)?;

        let x = fp_from_be_bytes(&x_be).map_err(|err| io::Error::other(err.to_string()))?;
        let y = fp_from_be_bytes(&y_be).map_err(|err| io::Error::other(err.to_string()))?;
        let affine: MidnightG1Affine = Option::from(MidnightG1Affine::from_xy(x, y))
            .ok_or_else(|| io::Error::other("Invalid BLS12-381 point encoding in proof"))?;
        Ok(G1Projective::from(affine))
    }
}

impl Hashable<MidnightEvmHashCompressed> for G1Projective {
    fn to_input(&self) -> Vec<u8> {
        let affine = MidnightG1Affine::from(self);
        let coordinates = match Option::<midnight_curves::Coordinates<MidnightG1Affine>>::from(
            affine.coordinates(),
        ) {
            Some(coordinates) => coordinates,
            None => {
                return vec![0u8; 2 * EVM_ENCODED_FP_BYTES];
            }
        };
        let mut bytes = Vec::with_capacity(2 * EVM_ENCODED_FP_BYTES);
        bytes.extend_from_slice(&fp_to_evm_word(coordinates.x()));
        bytes.extend_from_slice(&fp_to_evm_word(coordinates.y()));
        bytes
    }

    fn to_bytes(&self) -> Vec<u8> {
        encode_compressed_point(self)
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut encoded = vec![0u8; compressed_point_num_bytes()];
        buffer.read_exact(&mut encoded)?;
        decode_compressed_point(&encoded).map_err(|err| io::Error::other(err.to_string()))
    }
}

fn midnight_fp_num_bytes() -> usize {
    <MidnightFp as PrimeField>::Repr::default().as_ref().len()
}

fn compressed_point_num_bytes() -> usize {
    midnight_fp_num_bytes() + 1
}

fn scalar_to_evm_bytes(value: &Fq) -> Vec<u8> {
    let mut bytes = value.to_repr().as_ref().to_vec();
    bytes.reverse();
    bytes
}

fn scalar_from_evm_bytes(bytes_be: &[u8]) -> Result<Fq> {
    let expected = <Fq as PrimeField>::Repr::default().as_ref().len();
    if bytes_be.len() != expected {
        return Err(anyhow!(
            "invalid scalar length: expected {expected} bytes, got {}",
            bytes_be.len()
        ));
    }
    let mut le = bytes_be.to_vec();
    le.reverse();
    let mut repr = <Fq as PrimeField>::Repr::default();
    repr.as_mut().copy_from_slice(&le);
    Option::from(Fq::from_repr(repr)).ok_or_else(|| anyhow!("invalid scalar encoding"))
}

fn fp_to_be_bytes(value: &MidnightFp) -> Vec<u8> {
    let mut bytes = value.to_repr().as_ref().to_vec();
    bytes.reverse();
    bytes
}

fn fp_to_evm_word(value: &MidnightFp) -> [u8; EVM_ENCODED_FP_BYTES] {
    let be = fp_to_be_bytes(value);
    let mut out = [0u8; EVM_ENCODED_FP_BYTES];
    let offset = EVM_ENCODED_FP_BYTES - be.len();
    out[offset..].copy_from_slice(&be);
    out
}

fn fp_from_be_bytes(bytes_be: &[u8]) -> Result<MidnightFp> {
    let expected = midnight_fp_num_bytes();
    if bytes_be.len() != expected {
        return Err(anyhow!(
            "invalid base-field coordinate length: expected {expected} bytes, got {}",
            bytes_be.len()
        ));
    }
    let mut le = bytes_be.to_vec();
    le.reverse();
    let mut repr = <MidnightFp as PrimeField>::Repr::default();
    repr.as_mut().copy_from_slice(&le);
    Option::from(MidnightFp::from_repr(repr)).ok_or_else(|| anyhow!("invalid base-field encoding"))
}

fn fp_is_odd(value: &MidnightFp) -> bool {
    let repr = value.to_repr();
    repr.as_ref()[0] & 1 == 1
}

fn encode_compressed_point(point: &G1Projective) -> Vec<u8> {
    let affine = MidnightG1Affine::from(point);
    let mut out = Vec::with_capacity(compressed_point_num_bytes());
    let coordinates = match Option::<midnight_curves::Coordinates<MidnightG1Affine>>::from(
        affine.coordinates(),
    ) {
        Some(coordinates) => coordinates,
        None => {
            out.push(COMPRESSED_FLAG_INFINITY);
            out.extend(std::iter::repeat(0u8).take(midnight_fp_num_bytes()));
            return out;
        }
    };

    let y_is_odd = fp_is_odd(coordinates.y());
    out.push(if y_is_odd { COMPRESSED_FLAG_Y_ODD } else { 0u8 });
    out.extend_from_slice(&fp_to_be_bytes(coordinates.x()));
    out
}

fn decode_compressed_point(encoded: &[u8]) -> Result<G1Projective> {
    if encoded.len() != compressed_point_num_bytes() {
        return Err(anyhow!(
            "invalid compressed point length: expected {} bytes, got {}",
            compressed_point_num_bytes(),
            encoded.len()
        ));
    }

    let flag = encoded[0];
    if flag & !((COMPRESSED_FLAG_Y_ODD) | (COMPRESSED_FLAG_INFINITY)) != 0 {
        return Err(anyhow!("invalid compressed point flag byte: 0x{flag:02x}"));
    }

    let y_is_odd = flag & COMPRESSED_FLAG_Y_ODD != 0;
    let is_infinity = flag & COMPRESSED_FLAG_INFINITY != 0;
    let x = fp_from_be_bytes(&encoded[1..])?;

    if is_infinity {
        if y_is_odd || encoded[1..].iter().any(|&byte| byte != 0) {
            return Err(anyhow!("invalid infinity encoding in compressed point"));
        }
        return Ok(G1Projective::default());
    }

    let rhs = x.square() * x + MidnightCurveB;
    let mut y = Option::from(rhs.sqrt()).ok_or_else(|| anyhow!("compressed point has no square root"))?;
    if fp_is_odd(&y) != y_is_odd {
        y = -y;
    }

    let affine: MidnightG1Affine = Option::from(MidnightG1Affine::from_xy(x, y))
        .ok_or_else(|| anyhow!("invalid curve point from compressed encoding"))?;
    Ok(G1Projective::from(affine))
}
