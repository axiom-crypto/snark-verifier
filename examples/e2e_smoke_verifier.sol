
// SPDX-License-Identifier: MIT

pragma solidity 0.8.30;

contract Halo2Verifier {
    fallback(bytes calldata) external returns (bytes memory) {
        assembly ("memory-safe") {
            // Enforce that Solidity memory layout is respected
            let data := mload(0x40)
            if iszero(eq(data, 0x80)) {
                revert(0, 0)
            }

            let success := true
            let f_q := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
            
        {
            mstore(0x80, 0x0000000000000000000000000000000019bbef1efa3934a7df5aa40d858ce713)
            mstore(0xa0, 0xbf7b581214c5615f457b1aa6df751232550258c0a4b11013f845ebba49e46c46)
            mstore(0xc0, 0x000000000000000000000000000000001042c335f8d5850720ba03867123e3bc)
            mstore(0xe0, 0x961d14ca956c005328afdbc055a0c863406387bce9c9be0ac3075f9984980cd7)
        }

        {
            mstore(0x100, 0x000000000000000000000000000000000e27f533c9d853df5e2cf400d6e1cf69)
            mstore(0x120, 0xa39da77b8397effc65ccfa78082710784923bedab95665d8f29df4c989d9399a)
            mstore(0x140, 0x0000000000000000000000000000000012ace474b7cd9494b8fc95f88308499f)
            mstore(0x160, 0xfbc070eefc6b12d427e9c967d3180df6eb65c3beaf8484ba86a68b3a35a84594)
        }
mstore(0x1a0, mod(calldataload(0x0), f_q))
mstore(0x180, 37746883161491475686736803687791615668417123153050072654371598108288855988803)

        {
            mstore(0x1c0, 0)
            mstore(0x1e0, 0)
            mstore(0x200, 0)
            mstore(0x220, 0)
            calldatacopy(0x1d0, 0x20, 0x30)
            calldatacopy(0x210, 0x50, 0x30)
        }
mstore(0x240, keccak256(0x180, 192))
{
            let hash := mload(0x240)
            mstore(0x260, mod(hash, f_q))
            mstore(0x280, hash)
        }
mstore8(672, 1)
mstore(0x2a0, keccak256(0x280, 33))
{
            let hash := mload(0x2a0)
            mstore(0x2c0, mod(hash, f_q))
            mstore(0x2e0, hash)
        }
mstore8(768, 1)
mstore(0x300, keccak256(0x2e0, 33))
{
            let hash := mload(0x300)
            mstore(0x320, mod(hash, f_q))
            mstore(0x340, hash)
        }

        {
            mstore(0x360, 0)
            mstore(0x380, 0)
            mstore(0x3a0, 0)
            mstore(0x3c0, 0)
            calldatacopy(0x370, 0x80, 0x30)
            calldatacopy(0x3b0, 0xb0, 0x30)
        }

        {
            mstore(0x3e0, 0)
            mstore(0x400, 0)
            mstore(0x420, 0)
            mstore(0x440, 0)
            calldatacopy(0x3f0, 0xe0, 0x30)
            calldatacopy(0x430, 0x110, 0x30)
        }
mstore(0x460, keccak256(0x340, 288))
{
            let hash := mload(0x460)
            mstore(0x480, mod(hash, f_q))
            mstore(0x4a0, hash)
        }

        {
            mstore(0x4c0, 0)
            mstore(0x4e0, 0)
            mstore(0x500, 0)
            mstore(0x520, 0)
            calldatacopy(0x4d0, 0x140, 0x30)
            calldatacopy(0x510, 0x170, 0x30)
        }

        {
            mstore(0x540, 0)
            mstore(0x560, 0)
            mstore(0x580, 0)
            mstore(0x5a0, 0)
            calldatacopy(0x550, 0x1a0, 0x30)
            calldatacopy(0x590, 0x1d0, 0x30)
        }
mstore(0x5c0, keccak256(0x4a0, 288))
{
            let hash := mload(0x5c0)
            mstore(0x5e0, mod(hash, f_q))
            mstore(0x600, hash)
        }
mstore(0x620, mod(calldataload(0x200), f_q))
mstore(0x640, mod(calldataload(0x220), f_q))
mstore(0x660, mod(calldataload(0x240), f_q))
mstore(0x680, mod(calldataload(0x260), f_q))
mstore(0x6a0, mod(calldataload(0x280), f_q))
mstore(0x6c0, mod(calldataload(0x2a0), f_q))
mstore(0x6e0, keccak256(0x600, 224))
{
            let hash := mload(0x6e0)
            mstore(0x700, mod(hash, f_q))
            mstore(0x720, hash)
        }

        {
            mstore(0x740, 0)
            mstore(0x760, 0)
            mstore(0x780, 0)
            mstore(0x7a0, 0)
            calldatacopy(0x750, 0x2c0, 0x30)
            calldatacopy(0x790, 0x2f0, 0x30)
        }

        {
            mstore(0x7c0, 0)
            mstore(0x7e0, 0)
            mstore(0x800, 0)
            mstore(0x820, 0)
            calldatacopy(0x7d0, 0x320, 0x30)
            calldatacopy(0x810, 0x350, 0x30)
        }
mstore(0x840, keccak256(0x720, 288))
{
            let hash := mload(0x840)
            mstore(0x860, mod(hash, f_q))
            mstore(0x880, hash)
        }
mstore(0x8a0, mulmod(mload(0x5e0), mload(0x5e0), f_q))
mstore(0x8c0, mulmod(mload(0x8a0), mload(0x8a0), f_q))
mstore(0x8e0, mulmod(mload(0x8c0), mload(0x8c0), f_q))
mstore(0x900, mulmod(mload(0x8e0), mload(0x8e0), f_q))
mstore(0x920, mulmod(mload(0x900), mload(0x900), f_q))
mstore(0x940, mulmod(mload(0x920), mload(0x920), f_q))
mstore(0x960, mulmod(mload(0x940), mload(0x940), f_q))
mstore(0x980, mulmod(mload(0x960), mload(0x960), f_q))
mstore(0x9a0, mulmod(mload(0x980), mload(0x980), f_q))
mstore(0x9c0, mulmod(mload(0x9a0), mload(0x9a0), f_q))
mstore(0x9e0, mulmod(mload(0x9c0), mload(0x9c0), f_q))
mstore(0xa00, mulmod(mload(0x9e0), mload(0x9e0), f_q))
mstore(0xa20, addmod(mload(0xa00), 52435875175126190479447740508185965837690552500527637822603658699938581184512, f_q))
mstore(0xa40, mulmod(mload(0xa20), 52423073447788513186850219087163459498374710080483563692275874603576291491841, f_q))
mstore(0xa60, mulmod(mload(0xa40), 20090193668266119872620102064832883765253348140414125816117877893436209362462, f_q))
mstore(0xa80, addmod(mload(0x5e0), 32345681506860070606827638443353082072437204360113512006485780806502371822051, f_q))
mstore(0xaa0, mulmod(mload(0xa40), 32649132425011766248107187750088482855434888486916405379705025557137526796582, f_q))
mstore(0xac0, addmod(mload(0x5e0), 19786742750114424231340552758097482982255664013611232442898633142801054387931, f_q))
mstore(0xae0, mulmod(mload(0xa40), 36815421669481109810171413925233110915304823983913164224028689762034127238951, f_q))
mstore(0xb00, addmod(mload(0x5e0), 15620453505645080669276326582952854922385728516614473598574968937904453945562, f_q))
mstore(0xb20, mulmod(mload(0xa40), 15452603480080784356295137210386725334417616592955538195175950284291734913331, f_q))
mstore(0xb40, addmod(mload(0x5e0), 36983271695045406123152603297799240503272935907572099627427708415646846271182, f_q))
mstore(0xb60, mulmod(mload(0xa40), 38618283626480733637682686497654511901394394074436352158867102736890772187910, f_q))
mstore(0xb80, addmod(mload(0x5e0), 13817591548645456841765054010531453936296158426091285663736555963047808996603, f_q))
mstore(0xba0, mulmod(mload(0xa40), 25829815649260311651249373569448671287036547786131478959351418120540316250978, f_q))
mstore(0xbc0, addmod(mload(0x5e0), 26606059525865878828198366938737294550654004714396158863252240579398264933535, f_q))
mstore(0xbe0, mulmod(mload(0xa40), 1, f_q))
mstore(0xc00, addmod(mload(0x5e0), 52435875175126190479447740508185965837690552500527637822603658699938581184512, f_q))
{
            let prod := mload(0xa80)

                prod := mulmod(mload(0xac0), prod, f_q)
                mstore(0xc20, prod)
            
                prod := mulmod(mload(0xb00), prod, f_q)
                mstore(0xc40, prod)
            
                prod := mulmod(mload(0xb40), prod, f_q)
                mstore(0xc60, prod)
            
                prod := mulmod(mload(0xb80), prod, f_q)
                mstore(0xc80, prod)
            
                prod := mulmod(mload(0xbc0), prod, f_q)
                mstore(0xca0, prod)
            
                prod := mulmod(mload(0xc00), prod, f_q)
                mstore(0xcc0, prod)
            
                prod := mulmod(mload(0xa20), prod, f_q)
                mstore(0xce0, prod)
            
        }
mstore(0xd20, 32)
mstore(0xd40, 32)
mstore(0xd60, 32)
mstore(0xd80, mload(0xce0))
mstore(0xda0, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0xdc0, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0xd20, 0xc0, 0xd00, 0x20), 1), success)
{
            
            let inv := mload(0xd00)
            let v
        
                    v := mload(0xa20)
                    mstore(2592, mulmod(mload(0xcc0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0xc00)
                    mstore(3072, mulmod(mload(0xca0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0xbc0)
                    mstore(3008, mulmod(mload(0xc80), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0xb80)
                    mstore(2944, mulmod(mload(0xc60), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0xb40)
                    mstore(2880, mulmod(mload(0xc40), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0xb00)
                    mstore(2816, mulmod(mload(0xc20), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0xac0)
                    mstore(2752, mulmod(mload(0xa80), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                mstore(0xa80, inv)

        }
mstore(0xde0, mulmod(mload(0xa60), mload(0xa80), f_q))
mstore(0xe00, mulmod(mload(0xaa0), mload(0xac0), f_q))
mstore(0xe20, mulmod(mload(0xae0), mload(0xb00), f_q))
mstore(0xe40, mulmod(mload(0xb20), mload(0xb40), f_q))
mstore(0xe60, mulmod(mload(0xb60), mload(0xb80), f_q))
mstore(0xe80, mulmod(mload(0xba0), mload(0xbc0), f_q))
mstore(0xea0, mulmod(mload(0xbe0), mload(0xc00), f_q))
{
            let result := mulmod(mload(0xea0), mload(0x1a0), f_q)
mstore(3776, result)
        }
mstore(0xee0, mulmod(mload(0x620), mload(0x640), f_q))
mstore(0xf00, addmod(mload(0xee0), mload(0xec0), f_q))
mstore(0xf20, mulmod(mload(0x480), mload(0xf00), f_q))
mstore(0xf40, addmod(1, sub(f_q, mload(0x6a0)), f_q))
mstore(0xf60, mulmod(mload(0xf40), mload(0xea0), f_q))
mstore(0xf80, addmod(mload(0xf20), mload(0xf60), f_q))
mstore(0xfa0, mulmod(mload(0x480), mload(0xf80), f_q))
mstore(0xfc0, mulmod(mload(0x6a0), mload(0x6a0), f_q))
mstore(0xfe0, addmod(mload(0xfc0), sub(f_q, mload(0x6a0)), f_q))
mstore(0x1000, mulmod(mload(0xfe0), mload(0xde0), f_q))
mstore(0x1020, addmod(mload(0xfa0), mload(0x1000), f_q))
mstore(0x1040, mulmod(mload(0x480), mload(0x1020), f_q))
mstore(0x1060, addmod(1, sub(f_q, mload(0xde0)), f_q))
mstore(0x1080, addmod(mload(0xe00), mload(0xe20), f_q))
mstore(0x10a0, addmod(mload(0x1080), mload(0xe40), f_q))
mstore(0x10c0, addmod(mload(0x10a0), mload(0xe60), f_q))
mstore(0x10e0, addmod(mload(0x10c0), mload(0xe80), f_q))
mstore(0x1100, addmod(mload(0x1060), sub(f_q, mload(0x10e0)), f_q))
mstore(0x1120, mulmod(mload(0x680), mload(0x2c0), f_q))
mstore(0x1140, addmod(mload(0x620), mload(0x1120), f_q))
mstore(0x1160, addmod(mload(0x1140), mload(0x320), f_q))
mstore(0x1180, mulmod(mload(0x1160), mload(0x6c0), f_q))
mstore(0x11a0, mulmod(1, mload(0x2c0), f_q))
mstore(0x11c0, mulmod(mload(0x5e0), mload(0x11a0), f_q))
mstore(0x11e0, addmod(mload(0x620), mload(0x11c0), f_q))
mstore(0x1200, addmod(mload(0x11e0), mload(0x320), f_q))
mstore(0x1220, mulmod(mload(0x1200), mload(0x6a0), f_q))
mstore(0x1240, addmod(mload(0x1180), sub(f_q, mload(0x1220)), f_q))
mstore(0x1260, mulmod(mload(0x1240), mload(0x1100), f_q))
mstore(0x1280, addmod(mload(0x1040), mload(0x1260), f_q))
mstore(0x12a0, mulmod(mload(0xa00), mload(0xa00), f_q))
mstore(0x12c0, mulmod(1, mload(0xa00), f_q))
mstore(0x12e0, mulmod(mload(0x1280), mload(0xa20), f_q))
mstore(0x1300, mulmod(mload(0x860), mload(0x860), f_q))
mstore(0x1320, mulmod(mload(0x700), mload(0x700), f_q))
mstore(0x1340, mulmod(mload(0x1320), mload(0x700), f_q))
mstore(0x1360, mulmod(mload(0x1340), mload(0x700), f_q))
mstore(0x1380, mulmod(mload(0x1360), mload(0x700), f_q))
mstore(0x13a0, mulmod(mload(0x1380), mload(0x700), f_q))
mstore(0x13c0, mulmod(sub(f_q, mload(0x620)), 1, f_q))
mstore(0x13e0, mulmod(sub(f_q, mload(0x6a0)), mload(0x700), f_q))
mstore(0x1400, mulmod(1, mload(0x700), f_q))
mstore(0x1420, addmod(mload(0x13c0), mload(0x13e0), f_q))
mstore(0x1440, mulmod(sub(f_q, mload(0x640)), mload(0x1320), f_q))
mstore(0x1460, mulmod(1, mload(0x1320), f_q))
mstore(0x1480, addmod(mload(0x1420), mload(0x1440), f_q))
mstore(0x14a0, mulmod(sub(f_q, mload(0x680)), mload(0x1340), f_q))
mstore(0x14c0, mulmod(1, mload(0x1340), f_q))
mstore(0x14e0, addmod(mload(0x1480), mload(0x14a0), f_q))
mstore(0x1500, mulmod(sub(f_q, mload(0x12e0)), mload(0x1360), f_q))
mstore(0x1520, mulmod(1, mload(0x1360), f_q))
mstore(0x1540, mulmod(mload(0x12c0), mload(0x1360), f_q))
mstore(0x1560, addmod(mload(0x14e0), mload(0x1500), f_q))
mstore(0x1580, mulmod(sub(f_q, mload(0x660)), mload(0x1380), f_q))
mstore(0x15a0, mulmod(1, mload(0x1380), f_q))
mstore(0x15c0, addmod(mload(0x1560), mload(0x1580), f_q))
mstore(0x15e0, mulmod(mload(0x15c0), 1, f_q))
mstore(0x1600, mulmod(mload(0x1400), 1, f_q))
mstore(0x1620, mulmod(mload(0x1460), 1, f_q))
mstore(0x1640, mulmod(mload(0x14c0), 1, f_q))
mstore(0x1660, mulmod(mload(0x1520), 1, f_q))
mstore(0x1680, mulmod(mload(0x1540), 1, f_q))
mstore(0x16a0, mulmod(mload(0x15a0), 1, f_q))
mstore(0x16c0, mulmod(sub(f_q, mload(0x6c0)), 1, f_q))
mstore(0x16e0, mulmod(mload(0x16c0), mload(0x860), f_q))
mstore(0x1700, mulmod(1, mload(0x860), f_q))
mstore(0x1720, addmod(mload(0x15e0), mload(0x16e0), f_q))
mstore(0x1740, addmod(mload(0x1600), mload(0x1700), f_q))
mstore(0x1760, mulmod(1, mload(0x5e0), f_q))
mstore(0x1780, mulmod(1, mload(0x1760), f_q))
mstore(0x17a0, mulmod(39033254847818212395286706435128746857159659164139250548781411570340225835782, mload(0x5e0), f_q))
mstore(0x17c0, mulmod(mload(0x1700), mload(0x17a0), f_q))

        {
            mstore(0x17e0, 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
            mstore(0x1800, 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
            mstore(0x1820, 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(0x1840, 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
        }
{
                    mstore(0x1860, mload(0x17e0))
mstore(0x1880, mload(0x1800))
mstore(0x18a0, mload(0x1820))
mstore(0x18c0, mload(0x1840))
                }
mstore(0x18e0, mload(0x1720))
success := and(eq(staticcall(gas(), 0xc, 0x1860, 0xa0, 0x1860, 0x80), 1), success)
{
                    mstore(0x1900, mload(0x1860))
mstore(0x1920, mload(0x1880))
mstore(0x1940, mload(0x18a0))
mstore(0x1960, mload(0x18c0))
                }
{
                    mstore(0x1980, mload(0x1c0))
mstore(0x19a0, mload(0x1e0))
mstore(0x19c0, mload(0x200))
mstore(0x19e0, mload(0x220))
                }
success := and(eq(staticcall(gas(), 0xb, 0x1900, 0x100, 0x1900, 0x80), 1), success)
{
                    mstore(0x1a00, mload(0x360))
mstore(0x1a20, mload(0x380))
mstore(0x1a40, mload(0x3a0))
mstore(0x1a60, mload(0x3c0))
                }
mstore(0x1a80, mload(0x1740))
success := and(eq(staticcall(gas(), 0xc, 0x1a00, 0xa0, 0x1a00, 0x80), 1), success)
{
                    mstore(0x1aa0, mload(0x1900))
mstore(0x1ac0, mload(0x1920))
mstore(0x1ae0, mload(0x1940))
mstore(0x1b00, mload(0x1960))
                }
{
                    mstore(0x1b20, mload(0x1a00))
mstore(0x1b40, mload(0x1a20))
mstore(0x1b60, mload(0x1a40))
mstore(0x1b80, mload(0x1a60))
                }
success := and(eq(staticcall(gas(), 0xb, 0x1aa0, 0x100, 0x1aa0, 0x80), 1), success)
{
                    mstore(0x1ba0, mload(0x80))
mstore(0x1bc0, mload(0xa0))
mstore(0x1be0, mload(0xc0))
mstore(0x1c00, mload(0xe0))
                }
mstore(0x1c20, mload(0x1620))
success := and(eq(staticcall(gas(), 0xc, 0x1ba0, 0xa0, 0x1ba0, 0x80), 1), success)
{
                    mstore(0x1c40, mload(0x1aa0))
mstore(0x1c60, mload(0x1ac0))
mstore(0x1c80, mload(0x1ae0))
mstore(0x1ca0, mload(0x1b00))
                }
{
                    mstore(0x1cc0, mload(0x1ba0))
mstore(0x1ce0, mload(0x1bc0))
mstore(0x1d00, mload(0x1be0))
mstore(0x1d20, mload(0x1c00))
                }
success := and(eq(staticcall(gas(), 0xb, 0x1c40, 0x100, 0x1c40, 0x80), 1), success)
{
                    mstore(0x1d40, mload(0x100))
mstore(0x1d60, mload(0x120))
mstore(0x1d80, mload(0x140))
mstore(0x1da0, mload(0x160))
                }
mstore(0x1dc0, mload(0x1640))
success := and(eq(staticcall(gas(), 0xc, 0x1d40, 0xa0, 0x1d40, 0x80), 1), success)
{
                    mstore(0x1de0, mload(0x1c40))
mstore(0x1e00, mload(0x1c60))
mstore(0x1e20, mload(0x1c80))
mstore(0x1e40, mload(0x1ca0))
                }
{
                    mstore(0x1e60, mload(0x1d40))
mstore(0x1e80, mload(0x1d60))
mstore(0x1ea0, mload(0x1d80))
mstore(0x1ec0, mload(0x1da0))
                }
success := and(eq(staticcall(gas(), 0xb, 0x1de0, 0x100, 0x1de0, 0x80), 1), success)
{
                    mstore(0x1ee0, mload(0x4c0))
mstore(0x1f00, mload(0x4e0))
mstore(0x1f20, mload(0x500))
mstore(0x1f40, mload(0x520))
                }
mstore(0x1f60, mload(0x1660))
success := and(eq(staticcall(gas(), 0xc, 0x1ee0, 0xa0, 0x1ee0, 0x80), 1), success)
{
                    mstore(0x1f80, mload(0x1de0))
mstore(0x1fa0, mload(0x1e00))
mstore(0x1fc0, mload(0x1e20))
mstore(0x1fe0, mload(0x1e40))
                }
{
                    mstore(0x2000, mload(0x1ee0))
mstore(0x2020, mload(0x1f00))
mstore(0x2040, mload(0x1f20))
mstore(0x2060, mload(0x1f40))
                }
success := and(eq(staticcall(gas(), 0xb, 0x1f80, 0x100, 0x1f80, 0x80), 1), success)
{
                    mstore(0x2080, mload(0x540))
mstore(0x20a0, mload(0x560))
mstore(0x20c0, mload(0x580))
mstore(0x20e0, mload(0x5a0))
                }
mstore(0x2100, mload(0x1680))
success := and(eq(staticcall(gas(), 0xc, 0x2080, 0xa0, 0x2080, 0x80), 1), success)
{
                    mstore(0x2120, mload(0x1f80))
mstore(0x2140, mload(0x1fa0))
mstore(0x2160, mload(0x1fc0))
mstore(0x2180, mload(0x1fe0))
                }
{
                    mstore(0x21a0, mload(0x2080))
mstore(0x21c0, mload(0x20a0))
mstore(0x21e0, mload(0x20c0))
mstore(0x2200, mload(0x20e0))
                }
success := and(eq(staticcall(gas(), 0xb, 0x2120, 0x100, 0x2120, 0x80), 1), success)
{
                    mstore(0x2220, mload(0x3e0))
mstore(0x2240, mload(0x400))
mstore(0x2260, mload(0x420))
mstore(0x2280, mload(0x440))
                }
mstore(0x22a0, mload(0x16a0))
success := and(eq(staticcall(gas(), 0xc, 0x2220, 0xa0, 0x2220, 0x80), 1), success)
{
                    mstore(0x22c0, mload(0x2120))
mstore(0x22e0, mload(0x2140))
mstore(0x2300, mload(0x2160))
mstore(0x2320, mload(0x2180))
                }
{
                    mstore(0x2340, mload(0x2220))
mstore(0x2360, mload(0x2240))
mstore(0x2380, mload(0x2260))
mstore(0x23a0, mload(0x2280))
                }
success := and(eq(staticcall(gas(), 0xb, 0x22c0, 0x100, 0x22c0, 0x80), 1), success)
{
                    mstore(0x23c0, mload(0x740))
mstore(0x23e0, mload(0x760))
mstore(0x2400, mload(0x780))
mstore(0x2420, mload(0x7a0))
                }
mstore(0x2440, mload(0x1780))
success := and(eq(staticcall(gas(), 0xc, 0x23c0, 0xa0, 0x23c0, 0x80), 1), success)
{
                    mstore(0x2460, mload(0x22c0))
mstore(0x2480, mload(0x22e0))
mstore(0x24a0, mload(0x2300))
mstore(0x24c0, mload(0x2320))
                }
{
                    mstore(0x24e0, mload(0x23c0))
mstore(0x2500, mload(0x23e0))
mstore(0x2520, mload(0x2400))
mstore(0x2540, mload(0x2420))
                }
success := and(eq(staticcall(gas(), 0xb, 0x2460, 0x100, 0x2460, 0x80), 1), success)
{
                    mstore(0x2560, mload(0x7c0))
mstore(0x2580, mload(0x7e0))
mstore(0x25a0, mload(0x800))
mstore(0x25c0, mload(0x820))
                }
mstore(0x25e0, mload(0x17c0))
success := and(eq(staticcall(gas(), 0xc, 0x2560, 0xa0, 0x2560, 0x80), 1), success)
{
                    mstore(0x2600, mload(0x2460))
mstore(0x2620, mload(0x2480))
mstore(0x2640, mload(0x24a0))
mstore(0x2660, mload(0x24c0))
                }
{
                    mstore(0x2680, mload(0x2560))
mstore(0x26a0, mload(0x2580))
mstore(0x26c0, mload(0x25a0))
mstore(0x26e0, mload(0x25c0))
                }
success := and(eq(staticcall(gas(), 0xb, 0x2600, 0x100, 0x2600, 0x80), 1), success)

        {
            mstore(0x2700, 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
            mstore(0x2720, 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
            mstore(0x2740, 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(0x2760, 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
        }
{
                    mstore(0x2780, mload(0x7c0))
mstore(0x27a0, mload(0x7e0))
mstore(0x27c0, mload(0x800))
mstore(0x27e0, mload(0x820))
                }
mstore(0x2800, mload(0x1700))
success := and(eq(staticcall(gas(), 0xc, 0x2780, 0xa0, 0x2780, 0x80), 1), success)
{
                    mstore(0x2820, mload(0x740))
mstore(0x2840, mload(0x760))
mstore(0x2860, mload(0x780))
mstore(0x2880, mload(0x7a0))
                }
{
                    mstore(0x28a0, mload(0x2780))
mstore(0x28c0, mload(0x27a0))
mstore(0x28e0, mload(0x27c0))
mstore(0x2900, mload(0x27e0))
                }
success := and(eq(staticcall(gas(), 0xb, 0x2820, 0x100, 0x2820, 0x80), 1), success)
{
                    mstore(0x2920, mload(0x2600))
mstore(0x2940, mload(0x2620))
mstore(0x2960, mload(0x2640))
mstore(0x2980, mload(0x2660))
                }
mstore(0x29a0, 0x00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051)
mstore(0x29c0, 0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8)
mstore(0x29e0, 0x0000000000000000000000000000000013e02b6052719f607dacd3a088274f65)
mstore(0x2a00, 0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
mstore(0x2a20, 0x000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351a)
mstore(0x2a40, 0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801)
mstore(0x2a60, 0x000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99)
mstore(0x2a80, 0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)
{
                    mstore(0x2aa0, mload(0x2820))
mstore(0x2ac0, mload(0x2840))
mstore(0x2ae0, mload(0x2860))
mstore(0x2b00, mload(0x2880))
                }
mstore(0x2b20, 0x0000000000000000000000000000000019e6014e57135c126f03087170a51a8a)
mstore(0x2b40, 0xe60a5e339a1448aac900ce41b51e66bac0324686e3128bbbc0b309a1b6d413fc)
mstore(0x2b60, 0x000000000000000000000000000000000f7aec1791ffeb04b9eb32622f910bd5)
mstore(0x2b80, 0xb1ee90c549d25aab9f8a0b57f4c700a20216fb6f86f4506e9dc96d649b360189)
mstore(0x2ba0, 0x0000000000000000000000000000000002b9846367f4e259953f18b13c14b1b8)
mstore(0x2bc0, 0x22d77214e8ff6c1c58d0a868e6d78138efd7a4f72a6913490af10317f5bc7496)
mstore(0x2be0, 0x0000000000000000000000000000000011c920b401d5a2f33cc10f86a26af617)
mstore(0x2c00, 0x1425bde32e91126dcb1b3767156299e1730dc472c672ad74985287184e8841e7)
success := and(eq(staticcall(gas(), 0xf, 0x2920, 0x300, 0x2920, 0x20), 1), success)
success := and(eq(mload(0x2920), 1), success)

            // Revert if anything fails
            if iszero(success) { revert(0, 0) }

            // Return empty bytes on success
            return(0, 0)

        }
    }
}
        