//! `Loader` implementation for generating yul code as EVM verifier.

mod code;
/// Compact EVM verifier runtime/artifact generator.
pub mod compact_codegen;
/// Compact instruction set and program encoding for EVM verifier execution.
pub mod compact_ir;
pub(crate) mod loader;
pub(crate) mod util;

pub use code::EvmCodegenMode;
pub use compact_codegen::{
    build_compact_verifier_artifacts, data_page_deployment_code, encode_compact_constructor_args,
    CompactVerifierArtifacts,
};
pub use compact_ir::{CompactProgram, CompactProgramManifest, COMPACT_OPCODE_VERSION};
pub use loader::{EcPoint, EvmLoader, Scalar};
pub use util::{
    compile_solidity, compile_solidity_runtime, compile_solidity_runtime_via_ir,
    compile_solidity_via_ir, encode_calldata, estimate_gas, fe_to_u256, modulus, u256_to_fe,
    Address, B256, U256, U512,
};
#[cfg(feature = "revm")]
pub use util::{deploy_and_call, deploy_compact_and_call};
