
// SPDX-License-Identifier: MIT

pragma solidity 0.8.30;

contract Halo2Verifier {
    // slot 0
    address[] private pages;
    // slot 1
    uint256 private programWords;

    constructor(address[] memory _pages, uint256 _programWords) {
        require(_pages.length > 0, "no pages");
        require(_programWords > 1, "empty program");
        pages = _pages;
        programWords = _programWords;
    }

    fallback(bytes calldata) external returns (bytes memory) {
        assembly ("memory-safe") {
            let data := mload(0x40)
            if lt(data, 0x80) {
                mstore(0, 0x31)
                revert(0, 0x20)
            }

            let pageCount := sload(0)
            let totalWords := sload(1)
            if or(iszero(pageCount), lt(totalWords, 2)) {
                mstore(0, 0x32)
                revert(0, 0x20)
            }

            let success := 1
            let f_q := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

            function fail(code) {
                mstore(0, code)
                revert(0, 0x20)
            }

            mstore(0x00, 0)
            let pagesBase := keccak256(0x00, 0x20)

            function pageAddr(idx, pageCountArg, pagesBaseArg) -> addr {
                if iszero(lt(idx, pageCountArg)) {
                    fail(0x01)
                }
                addr := and(
                    sload(add(pagesBaseArg, idx)),
                    0xffffffffffffffffffffffffffffffffffffffff
                )
                if iszero(addr) {
                    fail(0x02)
                }
            }

            function loadWord(wordIndex, pageCountArg, pagesBaseArg, scratch) -> word {
                let byteOffset := mul(wordIndex, 0x20)
                let pageIdx := div(byteOffset, 24576)
                let pageOff := mod(byteOffset, 24576)
                let addr := pageAddr(pageIdx, pageCountArg, pagesBaseArg)
                if lt(extcodesize(addr), add(pageOff, 0x20)) {
                    fail(0x03)
                }
                extcodecopy(addr, scratch, pageOff, 0x20)
                word := mload(scratch)
            }

            function operandValue(tag, value) -> out {
                switch tag
                case 0 {
                    out := mload(value)
                }
                case 1 {
                    out := value
                }
                default {
                    fail(0x04)
                }
            }

            if iszero(eq(loadWord(0, pageCount, pagesBase, data), 1)) {
                fail(0x05)
            }

            for { let ip := 1 } lt(ip, totalWords) {} {
                let header := loadWord(ip, pageCount, pagesBase, data)
                let opcode := byte(0, header)
                let len := byte(1, header)
                if or(iszero(len), gt(add(ip, len), totalWords)) {
                    fail(0x06)
                }

                switch opcode
                // mstore(dst, value)
                case 1 {
                    if iszero(eq(len, 3)) { fail(0x11) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let value := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    mstore(dst, value)
                }
                // mstore(dst, mload(src))
                case 2 {
                    if iszero(eq(len, 3)) { fail(0x12) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let src := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    mstore(dst, mload(src))
                }
                // mstore8(dst, value)
                case 3 {
                    if iszero(eq(len, 3)) { fail(0x13) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let value := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    mstore8(dst, and(value, 0xff))
                }
                // mstore(dst, sub(f_q, operand))
                case 4 {
                    if iszero(eq(len, 4)) { fail(0x14) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let tag := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    let value := loadWord(add(ip, 3), pageCount, pagesBase, data)
                    let v := operandValue(tag, value)
                    mstore(dst, sub(f_q, v))
                }
                // mstore(dst, addmod(lhs, rhs, f_q))
                case 5 {
                    if iszero(eq(len, 6)) { fail(0x15) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let lhsTag := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    let lhsValue := loadWord(add(ip, 3), pageCount, pagesBase, data)
                    let rhsTag := loadWord(add(ip, 4), pageCount, pagesBase, data)
                    let rhsValue := loadWord(add(ip, 5), pageCount, pagesBase, data)
                    mstore(dst, addmod(operandValue(lhsTag, lhsValue), operandValue(rhsTag, rhsValue), f_q))
                }
                // mstore(dst, mulmod(lhs, rhs, f_q))
                case 6 {
                    if iszero(eq(len, 6)) { fail(0x16) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let lhsTag := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    let lhsValue := loadWord(add(ip, 3), pageCount, pagesBase, data)
                    let rhsTag := loadWord(add(ip, 4), pageCount, pagesBase, data)
                    let rhsValue := loadWord(add(ip, 5), pageCount, pagesBase, data)
                    mstore(dst, mulmod(operandValue(lhsTag, lhsValue), operandValue(rhsTag, rhsValue), f_q))
                }
                // mstore(dst, mod(calldataload(offset), f_q))
                case 7 {
                    if iszero(eq(len, 3)) { fail(0x17) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let offset := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    mstore(dst, mod(calldataload(offset), f_q))
                }
                // uncompressed proof point load: zero limbs then copy x/y from calldata with left padding.
                case 8 {
                    if iszero(eq(len, 4)) { fail(0x18) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let offset := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    let coordBytes := loadWord(add(ip, 3), pageCount, pagesBase, data)
                    let yPtr := add(dst, 0x40)
                    let pad := sub(0x40, coordBytes)

                    mstore(dst, 0)
                    mstore(add(dst, 0x20), 0)
                    mstore(yPtr, 0)
                    mstore(add(yPtr, 0x20), 0)
                    calldatacopy(add(dst, pad), offset, coordBytes)
                    calldatacopy(add(yPtr, pad), add(offset, coordBytes), coordBytes)
                }
                // copy affine point (4 words)
                case 9 {
                    if iszero(eq(len, 3)) { fail(0x19) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let src := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    mstore(dst, mload(src))
                    mstore(add(dst, 0x20), mload(add(src, 0x20)))
                    mstore(add(dst, 0x40), mload(add(src, 0x40)))
                    mstore(add(dst, 0x60), mload(add(src, 0x60)))
                }
                // mstore(dst, keccak256(ptr, len))
                case 10 {
                    if iszero(eq(len, 4)) { fail(0x1a) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let ptr := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    let hashLen := loadWord(add(ip, 3), pageCount, pagesBase, data)
                    mstore(dst, keccak256(ptr, hashLen))
                }
                // success := success && staticcall(precompile, cd_ptr, rd_ptr)
                case 11 {
                    if iszero(eq(len, 4)) { fail(0x1b) }
                    let precompile := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let cdPtr := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    let rdPtr := loadWord(add(ip, 3), pageCount, pagesBase, data)
                    let cdLen := 0
                    let rdLen := 0
                    switch precompile
                    case 0x05 {
                        cdLen := 0xc0
                        rdLen := 0x20
                    }
                    case 0x0b {
                        cdLen := 0x100
                        rdLen := 0x80
                    }
                    case 0x0c {
                        cdLen := 0xa0
                        rdLen := 0x80
                    }
                    case 0x0f {
                        cdLen := 0x300
                        rdLen := 0x20
                    }
                    default {
                        fail(0x1c)
                    }
                    success := and(success, eq(staticcall(gas(), precompile, cdPtr, cdLen, rdPtr, rdLen), 1))
                }
                // success := success && (mload(ptr) == 1)
                case 12 {
                    if iszero(eq(len, 2)) { fail(0x1d) }
                    let ptr := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    success := and(success, eq(mload(ptr), 1))
                }
                // decode affine point from limbs.
                case 13 {
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let bits := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    let limbCount := loadWord(add(ip, 3), pageCount, pagesBase, data)
                    let expectedLen := add(4, mul(4, limbCount))
                    if iszero(eq(len, expectedLen)) { fail(0x1e) }

                    let cursor := add(ip, 4)
                    let xLo := 0
                    let xHi := 0
                    for { let i := 0 } lt(i, limbCount) { i := add(i, 1) } {
                        let tag := loadWord(cursor, pageCount, pagesBase, data)
                        let value := loadWord(add(cursor, 1), pageCount, pagesBase, data)
                        let limb := operandValue(tag, value)
                        let shift := mul(i, bits)
                        if lt(shift, 256) {
                            xLo := add(xLo, shl(shift, limb))
                        }
                        if iszero(lt(shift, 256)) {
                            xHi := add(xHi, shl(sub(shift, 256), limb))
                        }
                        cursor := add(cursor, 2)
                    }
                    mstore(dst, xHi)
                    mstore(add(dst, 0x20), xLo)

                    let yLo := 0
                    let yHi := 0
                    for { let j := 0 } lt(j, limbCount) { j := add(j, 1) } {
                        let tag := loadWord(cursor, pageCount, pagesBase, data)
                        let value := loadWord(add(cursor, 1), pageCount, pagesBase, data)
                        let limb := operandValue(tag, value)
                        let shift := mul(j, bits)
                        if lt(shift, 256) {
                            yLo := add(yLo, shl(shift, limb))
                        }
                        if iszero(lt(shift, 256)) {
                            yHi := add(yHi, shl(sub(shift, 256), limb))
                        }
                        cursor := add(cursor, 2)
                    }
                    mstore(add(dst, 0x40), yHi)
                    mstore(add(dst, 0x60), yLo)
                }
                // mstore(dst, mod(mload(src), f_q))
                case 14 {
                    if iszero(eq(len, 3)) { fail(0x1f) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase, data)
                    let src := loadWord(add(ip, 2), pageCount, pagesBase, data)
                    mstore(dst, mod(mload(src), f_q))
                }
                default {
                    fail(0x20)
                }

                ip := add(ip, len)
            }

            if iszero(success) {
                fail(0x21)
            }
            return(0, 0)
        }
    }
}
