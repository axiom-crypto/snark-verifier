use revm::{
    context::TxEnv,
    context_interface::result::{ExecutionResult, Output},
    database::InMemoryDB,
    primitives::{hardfork::SpecId, Bytes, TxKind},
    Context, ExecuteCommitEvm, MainBuilder, MainContext,
};

const BENCH_GAS_LIMIT: u64 = 1_000_000_000;

fn read_usize_from_abi_word(word: &[u8]) -> Option<usize> {
    if word.len() != 32 || word[..24].iter().any(|&b| b != 0) {
        return None;
    }
    Some(u64::from_be_bytes(word[24..32].try_into().ok()?) as usize)
}

fn decode_revert_output(output: &[u8]) -> String {
    if output.is_empty() {
        return "empty revert data".to_string();
    }

    if output.len() >= 4 {
        let selector = &output[..4];
        // Error(string)
        if selector == [0x08, 0xc3, 0x79, 0xa0] && output.len() >= 68 {
            let offset = match read_usize_from_abi_word(&output[4..36]) {
                Some(v) => v,
                None => return format!("0x{}", hex::encode(output)),
            };
            let len_pos = 4 + offset;
            if len_pos + 32 <= output.len() {
                if let Some(str_len) = read_usize_from_abi_word(&output[len_pos..len_pos + 32]) {
                    let str_start = len_pos + 32;
                    let str_end = str_start.saturating_add(str_len);
                    if str_end <= output.len() {
                        if let Ok(reason) = std::str::from_utf8(&output[str_start..str_end]) {
                            return format!("Error(\"{reason}\")");
                        }
                    }
                }
            }
        }
        // Panic(uint256)
        if selector == [0x4e, 0x48, 0x7b, 0x71] && output.len() >= 36 {
            if let Some(code) = read_usize_from_abi_word(&output[4..36]) {
                return format!("Panic(0x{code:x})");
            }
        }
    }

    format!("0x{}", hex::encode(output))
}

/// Deploy contract and then call with calldata.
/// Returns gas_used of call to deployed contract if both transactions are successful.
pub fn deploy_and_call(deployment_code: Vec<u8>, calldata: Vec<u8>) -> Result<u64, String> {
    let mut evm = Context::mainnet()
        .modify_cfg_chained(|cfg| {
            cfg.spec = SpecId::PRAGUE;
            // Allow oversized verifier contracts in local simulation.
            cfg.limit_contract_code_size = Some(usize::MAX);
            cfg.limit_contract_initcode_size = Some(usize::MAX);
            cfg.disable_nonce_check = true;
            // Disable Osaka tx gas cap (EIP-7825) in local simulation.
            cfg.tx_gas_limit_cap = Some(BENCH_GAS_LIMIT);
        })
        .with_db(InMemoryDB::default())
        .build_mainnet();

    let deployment_tx = TxEnv::builder()
        .gas_limit(BENCH_GAS_LIMIT)
        .kind(TxKind::Create)
        .data(Bytes::from(deployment_code))
        .build_fill();

    let result = evm
        .transact_commit(deployment_tx)
        .map_err(|err| format!("revm deployment error: {err}"))?;
    let contract = match result {
        ExecutionResult::Success {
            output: Output::Create(_, Some(contract)),
            ..
        } => contract,
        ExecutionResult::Revert { gas_used, output } => {
            let decoded = decode_revert_output(&output);
            return Err(format!(
                "Contract deployment transaction reverts with gas_used {gas_used}; output={decoded}"
            ))
        }
        ExecutionResult::Halt { reason, gas_used } => return Err(format!(
                "Contract deployment transaction halts unexpectedly with gas_used {gas_used} and reason {:?}",
                reason
            )),
        ExecutionResult::Success { output, .. } => {
            return Err(format!(
                "Contract deployment returned unexpected output variant: {:?}",
                output
            ))
        }
    };

    let call_tx = TxEnv::builder()
        .gas_limit(BENCH_GAS_LIMIT)
        .kind(TxKind::Call(contract))
        .data(Bytes::from(calldata))
        .build_fill();

    let result = evm
        .transact_commit(call_tx)
        .map_err(|err| format!("revm call error: {err}"))?;
    match result {
        ExecutionResult::Success { gas_used, .. } => Ok(gas_used),
        ExecutionResult::Revert { gas_used, output } => {
            let decoded = decode_revert_output(&output);
            Err(format!(
                "Contract call transaction reverts with gas_used {gas_used}; output={decoded}"
            ))
        }
        ExecutionResult::Halt { reason, gas_used } => Err(format!(
            "Contract call transaction halts unexpectedly with gas_used {gas_used} and reason {:?}",
            reason
        )),
    }
}
