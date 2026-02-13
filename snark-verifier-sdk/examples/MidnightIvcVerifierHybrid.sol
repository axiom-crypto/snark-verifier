
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
            // Cache metadata in low scratch words.
            mstore(0x20, not(0)) // loaded page index
            mstore(0x40, 0)      // loaded page word count

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

            function loadWord(wordIndex, pageCountArg, pagesBaseArg) -> word {
                let pageIdx := div(wordIndex, 768)
                let pageWordOff := mod(wordIndex, 768)

                if iszero(eq(pageIdx, mload(0x20))) {
                    let addr := pageAddr(pageIdx, pageCountArg, pagesBaseArg)
                    let size := extcodesize(addr)
                    if iszero(eq(mod(size, 0x20), 0)) {
                        fail(0x07)
                    }
                    extcodecopy(addr, 194432, 0, size)
                    mstore(0x20, pageIdx)
                    mstore(0x40, div(size, 0x20))
                }

                let loadedWords := mload(0x40)
                if iszero(lt(pageWordOff, loadedWords)) {
                    fail(0x03)
                }
                word := mload(add(194432, mul(pageWordOff, 0x20)))
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

            if iszero(eq(loadWord(0, pageCount, pagesBase), 1)) {
                fail(0x05)
            }

            for { let ip := 1 } lt(ip, totalWords) {} {
                let header := loadWord(ip, pageCount, pagesBase)
                let opcode := byte(0, header)
                let len := byte(1, header)
                if or(iszero(len), gt(add(ip, len), totalWords)) {
                    fail(0x06)
                }

                switch opcode
                // mstore(dst, value)
                case 1 {
                    if iszero(eq(len, 3)) { fail(0x11) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let value := loadWord(add(ip, 2), pageCount, pagesBase)
                    mstore(dst, value)
                }
                // mstore(dst, mload(src))
                case 2 {
                    if iszero(eq(len, 3)) { fail(0x12) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let src := loadWord(add(ip, 2), pageCount, pagesBase)
                    mstore(dst, mload(src))
                }
                // mstore8(dst, value)
                case 3 {
                    if iszero(eq(len, 3)) { fail(0x13) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let value := loadWord(add(ip, 2), pageCount, pagesBase)
                    mstore8(dst, and(value, 0xff))
                }
                // mstore(dst, sub(f_q, operand))
                case 4 {
                    if iszero(eq(len, 4)) { fail(0x14) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let tag := loadWord(add(ip, 2), pageCount, pagesBase)
                    let value := loadWord(add(ip, 3), pageCount, pagesBase)
                    let v := operandValue(tag, value)
                    mstore(dst, sub(f_q, v))
                }
                // mstore(dst, addmod(lhs, rhs, f_q))
                case 5 {
                    if iszero(eq(len, 6)) { fail(0x15) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let lhsTag := loadWord(add(ip, 2), pageCount, pagesBase)
                    let lhsValue := loadWord(add(ip, 3), pageCount, pagesBase)
                    let rhsTag := loadWord(add(ip, 4), pageCount, pagesBase)
                    let rhsValue := loadWord(add(ip, 5), pageCount, pagesBase)
                    mstore(dst, addmod(operandValue(lhsTag, lhsValue), operandValue(rhsTag, rhsValue), f_q))
                }
                // mstore(dst, mulmod(lhs, rhs, f_q))
                case 6 {
                    if iszero(eq(len, 6)) { fail(0x16) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let lhsTag := loadWord(add(ip, 2), pageCount, pagesBase)
                    let lhsValue := loadWord(add(ip, 3), pageCount, pagesBase)
                    let rhsTag := loadWord(add(ip, 4), pageCount, pagesBase)
                    let rhsValue := loadWord(add(ip, 5), pageCount, pagesBase)
                    mstore(dst, mulmod(operandValue(lhsTag, lhsValue), operandValue(rhsTag, rhsValue), f_q))
                }
                // mstore(dst, mod(calldataload(offset), f_q))
                case 7 {
                    if iszero(eq(len, 3)) { fail(0x17) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let offset := loadWord(add(ip, 2), pageCount, pagesBase)
                    mstore(dst, mod(calldataload(offset), f_q))
                }
                // uncompressed proof point load: zero limbs then copy x/y from calldata with left padding.
                case 8 {
                    if iszero(eq(len, 4)) { fail(0x18) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let offset := loadWord(add(ip, 2), pageCount, pagesBase)
                    let coordBytes := loadWord(add(ip, 3), pageCount, pagesBase)
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
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let src := loadWord(add(ip, 2), pageCount, pagesBase)
                    mstore(dst, mload(src))
                    mstore(add(dst, 0x20), mload(add(src, 0x20)))
                    mstore(add(dst, 0x40), mload(add(src, 0x40)))
                    mstore(add(dst, 0x60), mload(add(src, 0x60)))
                }
                // mstore(dst, keccak256(ptr, len))
                case 10 {
                    if iszero(eq(len, 4)) { fail(0x1a) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let ptr := loadWord(add(ip, 2), pageCount, pagesBase)
                    let hashLen := loadWord(add(ip, 3), pageCount, pagesBase)
                    mstore(dst, keccak256(ptr, hashLen))
                }
                // success := success && staticcall(precompile, cd_ptr, rd_ptr)
                case 11 {
                    if iszero(eq(len, 4)) { fail(0x1b) }
                    let precompile := loadWord(add(ip, 1), pageCount, pagesBase)
                    let cdPtr := loadWord(add(ip, 2), pageCount, pagesBase)
                    let rdPtr := loadWord(add(ip, 3), pageCount, pagesBase)
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
                    let ptr := loadWord(add(ip, 1), pageCount, pagesBase)
                    success := and(success, eq(mload(ptr), 1))
                }
                // decode affine point from limbs.
                case 13 {
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let bits := loadWord(add(ip, 2), pageCount, pagesBase)
                    let limbCount := loadWord(add(ip, 3), pageCount, pagesBase)
                    let expectedLen := add(4, mul(4, limbCount))
                    if iszero(eq(len, expectedLen)) { fail(0x1e) }

                    let cursor := add(ip, 4)
                    let xLo := 0
                    let xHi := 0
                    for { let i := 0 } lt(i, limbCount) { i := add(i, 1) } {
                        let tag := loadWord(cursor, pageCount, pagesBase)
                        let value := loadWord(add(cursor, 1), pageCount, pagesBase)
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
                        let tag := loadWord(cursor, pageCount, pagesBase)
                        let value := loadWord(add(cursor, 1), pageCount, pagesBase)
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
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let src := loadWord(add(ip, 2), pageCount, pagesBase)
                    mstore(dst, mod(mload(src), f_q))
                }
                // mstore(dst, sub(f_q, mload(src)))
                case 15 {
                    if iszero(eq(len, 3)) { fail(0x22) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let src := loadWord(add(ip, 2), pageCount, pagesBase)
                    mstore(dst, sub(f_q, mload(src)))
                }
                // mstore(dst, addmod(mload(lhs), mload(rhs), f_q))
                case 16 {
                    if iszero(eq(len, 4)) { fail(0x23) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let lhs := loadWord(add(ip, 2), pageCount, pagesBase)
                    let rhs := loadWord(add(ip, 3), pageCount, pagesBase)
                    mstore(dst, addmod(mload(lhs), mload(rhs), f_q))
                }
                // mstore(dst, mulmod(mload(lhs), mload(rhs), f_q))
                case 17 {
                    if iszero(eq(len, 4)) { fail(0x24) }
                    let dst := loadWord(add(ip, 1), pageCount, pagesBase)
                    let lhs := loadWord(add(ip, 2), pageCount, pagesBase)
                    let rhs := loadWord(add(ip, 3), pageCount, pagesBase)
                    mstore(dst, mulmod(mload(lhs), mload(rhs), f_q))
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
