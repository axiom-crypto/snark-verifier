//! Transcript for verifier on EVM.

use crate::halo2_proofs;
use crate::{
    loader::{
        evm::{loader::Value, u256_to_fe, util::MemoryChunk, EcPoint, EvmLoader, Scalar, U256},
        native::{self, NativeLoader},
        Loader,
    },
    util::{
        arithmetic::{Coordinates, CurveAffine, Field, PrimeField},
        hash::{Digest, Keccak256},
        transcript::{Transcript, TranscriptRead},
        Itertools,
    },
    Error,
};
use halo2_proofs::transcript::EncodedChallenge;
use std::{
    io::{self, Read, Write},
    iter,
    marker::PhantomData,
    rc::Rc,
};

/// Transcript for verifier on EVM using keccak256 as hasher.
#[derive(Debug)]
pub struct EvmTranscript<C: CurveAffine, L: Loader<C>, S, B> {
    loader: L,
    stream: S,
    buf: B,
    _marker: PhantomData<C>,
}

impl<C> EvmTranscript<C, Rc<EvmLoader>, usize, MemoryChunk>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    /// Initialize [`EvmTranscript`] given [`Rc<EvmLoader>`] and pre-allocate an
    /// u256 for `transcript_initial_state`.
    pub fn new(loader: &Rc<EvmLoader>) -> Self {
        let ptr = loader.allocate(0x20);
        let mut buf = MemoryChunk::new(ptr);
        buf.extend(0x20);
        Self { loader: loader.clone(), stream: 0, buf, _marker: PhantomData }
    }

    /// Load `num_instance` instances from calldata to memory.
    pub fn load_instances(&mut self, num_instance: Vec<usize>) -> Vec<Vec<Scalar>> {
        let instances = num_instance
            .into_iter()
            .map(|len| {
                iter::repeat_with(|| {
                    let scalar = self.loader.calldataload_scalar(self.stream);
                    self.stream += 0x20;
                    scalar
                })
                .take(len)
                .collect_vec()
            })
            .collect();

        // Keep transcript bytes in a dedicated contiguous region after
        // preloaded calldata values.
        if self.buf.end() != self.loader.ptr() {
            let ptr = self.loader.allocate(0x20);
            self.buf.reset(ptr);
            self.buf.extend(0x20);
        }

        instances
    }
}

impl<C> Transcript<C, Rc<EvmLoader>> for EvmTranscript<C, Rc<EvmLoader>, usize, MemoryChunk>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    fn loader(&self) -> &Rc<EvmLoader> {
        &self.loader
    }

    /// Does not allow the input to be a one-byte sequence, because the Transcript trait only supports writing scalars and elliptic curve points.
    /// If the one-byte sequence `[0x01]` is a valid input to the transcript, the empty input `[]` will have the same transcript result as `[0x01]`.
    fn squeeze_challenge(&mut self) -> Scalar {
        let len = if self.buf.len() == 0x20 {
            assert_eq!(self.loader.ptr(), self.buf.end());
            let buf_end = self.buf.end();
            let code = format!("mstore8({buf_end}, 1)");
            self.loader.code_mut().runtime_append(code);
            0x21
        } else {
            self.buf.len()
        };
        let hash_ptr = self.loader.keccak256(self.buf.ptr(), len);

        let challenge_ptr = self.loader.allocate(0x20);
        let dup_hash_ptr = self.loader.allocate(0x20);
        let code = format!(
            "{{
            let hash := mload({hash_ptr:#x})
            mstore({challenge_ptr:#x}, mod(hash, f_q))
            mstore({dup_hash_ptr:#x}, hash)
        }}"
        );
        self.loader.code_mut().runtime_append(code);

        self.buf.reset(dup_hash_ptr);
        self.buf.extend(0x20);

        self.loader.scalar(Value::Memory(challenge_ptr))
    }

    fn common_ec_point(&mut self, ec_point: &EcPoint) -> Result<(), Error> {
        if let Value::Memory(ptr) = ec_point.value() {
            if self.buf.end() == ptr {
                self.buf.extend(self.loader.evm_ec_point_bytes());
            } else {
                let dst = self.loader.dup_ec_point(ec_point);
                if let Value::Memory(dst_ptr) = dst.value() {
                    assert_eq!(self.buf.end(), dst_ptr);
                    self.buf.extend(self.loader.evm_ec_point_bytes());
                } else {
                    unreachable!()
                }
            }
        } else {
            unreachable!()
        }
        Ok(())
    }

    fn common_scalar(&mut self, scalar: &Scalar) -> Result<(), Error> {
        match scalar.value() {
            Value::Constant(_) if self.buf.len() == 0x20 => {
                self.loader.copy_scalar(scalar, self.buf.ptr());
            }
            Value::Constant(_) => {
                let ptr = self.loader.allocate(0x20);
                assert_eq!(self.buf.end(), ptr);
                self.loader.copy_scalar(scalar, ptr);
                self.buf.extend(0x20);
            }
            Value::Memory(ptr) => {
                if self.buf.end() == ptr {
                    self.buf.extend(0x20);
                } else {
                    let dst = self.loader.allocate(0x20);
                    assert_eq!(self.buf.end(), dst);
                    self.loader
                        .code_mut()
                        .runtime_append(format!("mstore({dst:#x}, mload({ptr:#x}))"));
                    self.buf.extend(0x20);
                }
            }
            _ => unreachable!(),
        }
        Ok(())
    }
}

impl<C> TranscriptRead<C, Rc<EvmLoader>> for EvmTranscript<C, Rc<EvmLoader>, usize, MemoryChunk>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    fn read_scalar(&mut self) -> Result<Scalar, Error> {
        let scalar = self.loader.calldataload_scalar(self.stream);
        self.stream += 0x20;
        self.common_scalar(&scalar)?;
        Ok(scalar)
    }

    fn read_ec_point(&mut self) -> Result<EcPoint, Error> {
        let ec_point = self.loader.calldataload_ec_point(self.stream);
        self.stream += self.loader.proof_ec_point_bytes();
        self.common_ec_point(&ec_point)?;
        Ok(ec_point)
    }
}

impl<C, S> EvmTranscript<C, NativeLoader, S, Vec<u8>>
where
    C: CurveAffine,
{
    /// Initialize [`EvmTranscript`] given readable or writeable stream for
    /// verifying or proving with [`NativeLoader`].
    pub fn new(stream: S) -> Self {
        Self { loader: NativeLoader, stream, buf: Vec::new(), _marker: PhantomData }
    }
}

impl<C, S> Transcript<C, NativeLoader> for EvmTranscript<C, NativeLoader, S, Vec<u8>>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    fn loader(&self) -> &NativeLoader {
        &native::LOADER
    }

    fn squeeze_challenge(&mut self) -> C::Scalar {
        let data = self
            .buf
            .iter()
            .cloned()
            .chain(if self.buf.len() == 0x20 { Some(1) } else { None })
            .collect_vec();
        let hash: [u8; 32] = Keccak256::digest(data).into();
        self.buf = hash.to_vec();
        u256_to_fe(U256::from_be_bytes(hash))
    }

    fn common_ec_point(&mut self, ec_point: &C) -> Result<(), Error> {
        if let Some(coordinates) = Option::<Coordinates<C>>::from(ec_point.coordinates()) {
            [coordinates.x(), coordinates.y()].map(|coordinate| {
                let repr = coordinate.to_repr();
                let repr = repr.as_ref();
                let encoded_len = match repr.len() {
                    0..=0x20 => 0x20,
                    0x21..=0x40 => 0x40,
                    _ => unreachable!("unsupported base-field encoding length: {}", repr.len()),
                };
                self.buf.extend(iter::repeat(0).take(encoded_len - repr.len()));
                self.buf.extend(repr.iter().rev().copied());
            });
        } else {
            // EVM precompiles represent point-at-infinity as (0, 0).
            let repr_len = <C::Base as PrimeField>::Repr::default().as_ref().len();
            let encoded_len = match repr_len {
                0..=0x20 => 0x20,
                0x21..=0x40 => 0x40,
                _ => unreachable!("unsupported base-field encoding length: {}", repr_len),
            };
            self.buf.extend(iter::repeat(0).take(2 * encoded_len));
        }

        Ok(())
    }

    fn common_scalar(&mut self, scalar: &C::Scalar) -> Result<(), Error> {
        self.buf.extend(scalar.to_repr().as_ref().iter().rev());

        Ok(())
    }
}

impl<C, S> TranscriptRead<C, NativeLoader> for EvmTranscript<C, NativeLoader, S, Vec<u8>>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
    S: Read,
{
    fn read_scalar(&mut self) -> Result<C::Scalar, Error> {
        let mut data = [0; 32];
        self.stream
            .read_exact(data.as_mut())
            .map_err(|err| Error::Transcript(err.kind(), err.to_string()))?;
        data.reverse();
        let scalar = C::Scalar::from_repr_vartime(data).ok_or_else(|| {
            Error::Transcript(io::ErrorKind::Other, "Invalid scalar encoding in proof".to_string())
        })?;
        self.common_scalar(&scalar)?;
        Ok(scalar)
    }

    fn read_ec_point(&mut self) -> Result<C, Error> {
        let [mut x, mut y] = [<C::Base as PrimeField>::Repr::default(); 2];
        for repr in [&mut x, &mut y] {
            self.stream
                .read_exact(repr.as_mut())
                .map_err(|err| Error::Transcript(err.kind(), err.to_string()))?;
            repr.as_mut().reverse();
        }
        let x = Option::from(<C::Base as PrimeField>::from_repr(x)).ok_or_else(|| {
            Error::Transcript(
                io::ErrorKind::Other,
                "Invalid x-coordinate encoding in proof".to_string(),
            )
        })?;
        let y = Option::from(<C::Base as PrimeField>::from_repr(y)).ok_or_else(|| {
            Error::Transcript(
                io::ErrorKind::Other,
                "Invalid y-coordinate encoding in proof".to_string(),
            )
        })?;
        // EVM precompiles represent point-at-infinity as (0, 0).
        let ec_point = if x == C::Base::ZERO && y == C::Base::ZERO {
            C::identity()
        } else {
            Option::from(C::from_xy(x, y)).ok_or_else(|| {
                Error::Transcript(
                    io::ErrorKind::Other,
                    "Invalid elliptic curve point encoding in proof".to_string(),
                )
            })?
        };
        self.common_ec_point(&ec_point)?;
        Ok(ec_point)
    }
}

impl<C, S> EvmTranscript<C, NativeLoader, S, Vec<u8>>
where
    C: CurveAffine,
    S: Write,
{
    /// Returns mutable `stream`.
    pub fn stream_mut(&mut self) -> &mut S {
        &mut self.stream
    }

    /// Finalize transcript and returns `stream`.
    pub fn finalize(self) -> S {
        self.stream
    }
}

/// [`EncodedChallenge`] implemented for verifier on EVM, which use input in
/// big-endian as the challenge.
#[derive(Debug)]
pub struct ChallengeEvm<C>(C::Scalar)
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 32]>;

impl<C> EncodedChallenge<C> for ChallengeEvm<C>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 32]>,
{
    type Input = [u8; 32];

    fn new(challenge_input: &[u8; 32]) -> Self {
        ChallengeEvm(u256_to_fe(U256::from_be_bytes(*challenge_input)))
    }

    fn get_scalar(&self) -> C::Scalar {
        self.0
    }
}

impl<C, S> halo2_proofs::transcript::Transcript<C, ChallengeEvm<C>>
    for EvmTranscript<C, NativeLoader, S, Vec<u8>>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 32]>,
{
    fn squeeze_challenge(&mut self) -> ChallengeEvm<C> {
        ChallengeEvm(Transcript::squeeze_challenge(self))
    }

    fn common_point(&mut self, ec_point: C) -> io::Result<()> {
        match Transcript::common_ec_point(self, &ec_point) {
            Err(Error::Transcript(kind, msg)) => Err(io::Error::new(kind, msg)),
            Err(_) => unreachable!(),
            _ => Ok(()),
        }
    }

    fn common_scalar(&mut self, scalar: C::Scalar) -> io::Result<()> {
        match Transcript::common_scalar(self, &scalar) {
            Err(Error::Transcript(kind, msg)) => Err(io::Error::new(kind, msg)),
            Err(_) => unreachable!(),
            _ => Ok(()),
        }
    }
}

impl<C, R: Read> halo2_proofs::transcript::TranscriptRead<C, ChallengeEvm<C>>
    for EvmTranscript<C, NativeLoader, R, Vec<u8>>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 32]>,
{
    fn read_point(&mut self) -> io::Result<C> {
        match TranscriptRead::read_ec_point(self) {
            Err(Error::Transcript(kind, msg)) => Err(io::Error::new(kind, msg)),
            Err(_) => unreachable!(),
            Ok(value) => Ok(value),
        }
    }

    fn read_scalar(&mut self) -> io::Result<C::Scalar> {
        match TranscriptRead::read_scalar(self) {
            Err(Error::Transcript(kind, msg)) => Err(io::Error::new(kind, msg)),
            Err(_) => unreachable!(),
            Ok(value) => Ok(value),
        }
    }
}

impl<C, R: Read> halo2_proofs::transcript::TranscriptReadBuffer<R, C, ChallengeEvm<C>>
    for EvmTranscript<C, NativeLoader, R, Vec<u8>>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 32]>,
{
    fn init(reader: R) -> Self {
        Self::new(reader)
    }
}

impl<C, W: Write> halo2_proofs::transcript::TranscriptWrite<C, ChallengeEvm<C>>
    for EvmTranscript<C, NativeLoader, W, Vec<u8>>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 32]>,
{
    fn write_point(&mut self, ec_point: C) -> io::Result<()> {
        halo2_proofs::transcript::Transcript::<C, ChallengeEvm<C>>::common_point(self, ec_point)?;
        let coords: Coordinates<C> = Option::from(ec_point.coordinates()).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "Cannot write points at infinity to the transcript",
            )
        })?;
        let mut x = coords.x().to_repr();
        let mut y = coords.y().to_repr();
        x.as_mut().reverse();
        y.as_mut().reverse();
        self.stream_mut().write_all(x.as_ref())?;
        self.stream_mut().write_all(y.as_ref())
    }

    fn write_scalar(&mut self, scalar: C::Scalar) -> io::Result<()> {
        halo2_proofs::transcript::Transcript::<C, ChallengeEvm<C>>::common_scalar(self, scalar)?;
        let mut data = scalar.to_repr();
        data.as_mut().reverse();
        self.stream_mut().write_all(data.as_ref())
    }
}

impl<C, W: Write> halo2_proofs::transcript::TranscriptWriterBuffer<W, C, ChallengeEvm<C>>
    for EvmTranscript<C, NativeLoader, W, Vec<u8>>
where
    C: CurveAffine,
    C::Scalar: PrimeField<Repr = [u8; 32]>,
{
    fn init(writer: W) -> Self {
        Self::new(writer)
    }

    fn finalize(self) -> W {
        self.finalize()
    }
}
