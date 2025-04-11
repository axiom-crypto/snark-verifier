use revm::{
    context::{
        result::{ExecutionResult, Output},
        TxEnv,
    },
    database::InMemoryDB,
    primitives::TxKind,
    Context, ExecuteCommitEvm, MainBuilder, MainContext,
};

/// Deploy contract and then call with calldata.
/// Returns gas_used of call to deployed contract if both transactions are successful.
pub fn deploy_and_call(deployment_code: Vec<u8>, calldata: Vec<u8>) -> Result<u64, String> {
    let mut evm = Context::mainnet().with_db(InMemoryDB::default()).build_mainnet();

    let tx = TxEnv {
        gas_limit: u64::MAX,
        kind: TxKind::Create,
        data: deployment_code.into(),
        ..Default::default()
    };

    let result = evm.transact_commit(tx).unwrap();
    let contract = match result {
        ExecutionResult::Success {
            output: Output::Create(_, Some(contract)),
            ..
        } => contract,
        ExecutionResult::Revert { gas_used, output } => {
            return Err(format!(
                "Contract deployment transaction reverts with gas_used {gas_used} and output {:#x}",
                output
            ))
        }
        ExecutionResult::Halt { reason, gas_used } => return Err(format!(
                "Contract deployment transaction halts unexpectedly with gas_used {gas_used} and reason {:?}",
                reason
            )),
        _ => unreachable!(),
    };

    let tx = TxEnv {
        gas_limit: u64::MAX,
        kind: TxKind::Call(contract),
        data: calldata.into(),
        ..Default::default()
    };

    let result = evm.transact_commit(tx).unwrap();
    match result {
        ExecutionResult::Success { gas_used, .. } => Ok(gas_used),
        ExecutionResult::Revert { gas_used, output } => Err(format!(
            "Contract call transaction reverts with gas_used {gas_used} and output {:#x}",
            output
        )),
        ExecutionResult::Halt { reason, gas_used } => Err(format!(
            "Contract call transaction halts unexpectedly with gas_used {gas_used} and reason {:?}",
            reason
        )),
    }
}
