
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
            mstore(0x220, 0x000000000000000000000000000000001170cad86e5afb1d4cdd8a6251d46cbb)
            mstore(0x240, 0x85f3261e6b1954a77492241599016e7293029133bed3f0b90f560c0ebe69606e)
            mstore(0x260, 0x0000000000000000000000000000000013099a7835073646b79a0e9c60650132)
            mstore(0x280, 0x247b22413b3a8674d081e73623ebaf398638b87771d9f2cda7f152b249e645c3)
        }

        {
            mstore(0x2a0, 0x000000000000000000000000000000000b282d617a91f4d1ff00a6243771931a)
            mstore(0x2c0, 0xe5a512f21813fc3c2d8724a093ce5df71ca2eb14ac60b2acacab27d9ffe9fd1e)
            mstore(0x2e0, 0x000000000000000000000000000000000d83c7f6a5c77064ad92bda194d35224)
            mstore(0x300, 0x976fcdbf14687aecd071c20ffe00e2465d42835d8fcbfa84e4238002614e0ab4)
        }

        {
            mstore(0x320, 0x000000000000000000000000000000000e4febceb0c75e74bb4a82858851388b)
            mstore(0x340, 0x7dfc6ab427eb3efca57fb33f8061ad19151067e197b7b80cf133048d05906780)
            mstore(0x360, 0x000000000000000000000000000000000f94878a2f29befce1d34c2c6cacd7b7)
            mstore(0x380, 0xf974e1aeebc66250b22b40483ac0aef0fd63f81ecdc5ec77e86b0baf47ee4161)
        }

        {
            mstore(0x3a0, 0x0000000000000000000000000000000010410d2f52f549d810c0b20762b3d23f)
            mstore(0x3c0, 0x492faf9c0412566918320fa1bd1a2f866de371c682ce58291298da7054c15e37)
            mstore(0x3e0, 0x0000000000000000000000000000000005bb60e740941076894a635a8b68b2ad)
            mstore(0x400, 0x0cafe4dfb5b26b266e3d7f90648df3316eeac10a8552daa2e10139e558e89c8b)
        }

        {
            mstore(0x420, 0x000000000000000000000000000000001732e93c22240fc9b25ada31c744ec43)
            mstore(0x440, 0x81c24342543e1d9207d676cab7b4748bd0f3bd207c0e0f58b01cdfaf06bf398a)
            mstore(0x460, 0x000000000000000000000000000000000888fdf5fb7001185488816bf214db93)
            mstore(0x480, 0x91fc843d2e6e2122b16c6cb2db555e5462c37d5c33f7618db3fc2c282be965b3)
        }

        {
            mstore(0x4a0, 0x000000000000000000000000000000001312bdc240cd2373467c0335ef191197)
            mstore(0x4c0, 0xf8128d4d4025c77c934160e876b41236cd5104c8b234fea21db0fa4aaebf2de3)
            mstore(0x4e0, 0x0000000000000000000000000000000008a756827bc26e82b27713959e4f0fd4)
            mstore(0x500, 0x024d331264b2d9d864b723eeebdcb9037ce00efaae2d8692b843fdffb9fe0be7)
        }

        {
            mstore(0x520, 0x000000000000000000000000000000000fa4a6b7754886e78dd0e9068ee9049a)
            mstore(0x540, 0x6175fee991b60a8a7fbf1bf731d90b3160c7f2fc49c8d743236961dd105254d6)
            mstore(0x560, 0x0000000000000000000000000000000019b9ae84f878111bd3b7d04fdd1f9b4c)
            mstore(0x580, 0x4610f2b7e9f9e5c8fda9a0c7bbc45fb4ed59209693fffc3fa8d1232bd86d18ea)
        }

        {
            mstore(0x5a0, 0x000000000000000000000000000000000e8076d8e749c7bfe5af53cb7b41f713)
            mstore(0x5c0, 0xa3c91571447d7e154d609b92fd23b751dac284102cd1c819e5450651b381ba07)
            mstore(0x5e0, 0x00000000000000000000000000000000010fd8233696eb2b819137499e8cf259)
            mstore(0x600, 0x538dc547287695ab7c92407048f8cfc0e2dcf62915af2a0025a400337fecfcf3)
        }

        {
            mstore(0x620, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x640, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x660, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x680, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x6a0, 0x000000000000000000000000000000001124166c5b5a37887b5bbe342f8ac8b9)
            mstore(0x6c0, 0x3954dd3896331fee30e23578b069fafdf287b3d2f722d56627e112b870355668)
            mstore(0x6e0, 0x00000000000000000000000000000000075c264eefdba228713189d50699f41a)
            mstore(0x700, 0xc7d530221425801ccab07a64e636ff31dc04928d4ada7d7069b105b88f179b4f)
        }

        {
            mstore(0x720, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x740, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x760, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x780, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x7a0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x7c0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x7e0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x800, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x820, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x840, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x860, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x880, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x8a0, 0x0000000000000000000000000000000004406ed3f7dd1a67cfd8826477766644)
            mstore(0x8c0, 0x6ebf00fbad53877f5fd6d1a2038b5d8df988079e1564589446724a5ed5f3e6ee)
            mstore(0x8e0, 0x000000000000000000000000000000001501329004b8a8f367268386cdfcf31a)
            mstore(0x900, 0xcde2feee42a0b6a896f5d39df5c6058d4f52e3f757fb5c80f8b5c17ca657f100)
        }

        {
            mstore(0x920, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x940, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x960, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x980, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x9a0, 0x000000000000000000000000000000000144f9dfdcc72389bf9a825edb32d7a4)
            mstore(0x9c0, 0x904eafce4112dae3fc92be52ff83fafbe5ad9867507ec615588df15d5e9a0633)
            mstore(0x9e0, 0x0000000000000000000000000000000010f4bbdbfed0d96a62f950f7a988c3a2)
            mstore(0xa00, 0xeb7b8154f8e9ca0a1b147830f3f4dd121926a3a64eb4dcc905f3e516ad497c50)
        }

        {
            mstore(0xa20, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0xa40, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0xa60, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0xa80, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0xaa0, 0x000000000000000000000000000000000f4f2f406c3962d61843db8bc1559573)
            mstore(0xac0, 0x973da3cc13073becc1ff670c2b256f5331d14b95c51bc52ea4605be1c889884e)
            mstore(0xae0, 0x0000000000000000000000000000000018b6cf86bd879fbe05412ca1d900cfbb)
            mstore(0xb00, 0xba180f1b0439e77500ab19a03431abdceb676dbfec8b52416afa4babf876cf75)
        }

        {
            mstore(0xb20, 0x000000000000000000000000000000000080fbcf63e3fb6c7acbe235e784e8a6)
            mstore(0xb40, 0x44437be5f54b2fb04d80e95ce7db6bcbb3d909cf63d67337d5c631c5ab7410d3)
            mstore(0xb60, 0x000000000000000000000000000000000831a0cfa3f0a4adb5e246db4d037831)
            mstore(0xb80, 0x8b978488f0891c4a40ce1aa050c990fb50adbb0b3c29a7aae5d88c93a20bf6ca)
        }

        {
            mstore(0xba0, 0x00000000000000000000000000000000186cb8140666759f42c0c1782a42c860)
            mstore(0xbc0, 0x9bba633d9d947fa918647fb631e8d657c7068f2a2e8654d49052b88311593f24)
            mstore(0xbe0, 0x0000000000000000000000000000000017871082b594ec733486a7885afecf37)
            mstore(0xc00, 0x9d80478256ebb7c90b49078382b8fbb032df65d9b4c79fe8634a85aa490b7137)
        }

        {
            mstore(0xc20, 0x00000000000000000000000000000000166547db70fb617b12b6e23da0a43fbc)
            mstore(0xc40, 0x84e2ee7a0c11367fa660281c402efbfbd3a3aa3f8c18a803095cd5f982aa4c7e)
            mstore(0xc60, 0x000000000000000000000000000000000d3f94f097b7cf2ae913039e6d28eb9a)
            mstore(0xc80, 0xf8ebb581e0ca6d876ee33a62fb241618bce02ad27104e731c248f8a96809fda2)
        }

        {
            mstore(0xca0, 0x0000000000000000000000000000000010e49bac65ece98d1d6262b819bc95cc)
            mstore(0xcc0, 0x12daaccb14f1bc77801d1e6be99e904c767128e69d9e22212777d2c7b8926ca1)
            mstore(0xce0, 0x0000000000000000000000000000000015827ef34173b456481b6fbb898a4734)
            mstore(0xd00, 0x0f77ce253fb452e162700c411d90f02756cf5f63625660b9d672205b7a8af36b)
        }

        {
            mstore(0xd20, 0x00000000000000000000000000000000092c5fcecf93fca32c4b25f16893a0a4)
            mstore(0xd40, 0x08232d283d8fe5a60aaf667f95a0b5fa1c97b02402d75bc2565cdc188234ecb6)
            mstore(0xd60, 0x000000000000000000000000000000000946f9122b38db27ba559527d941a159)
            mstore(0xd80, 0x5a0f86769bda59fca94944c944e897a54268958fe22e42d88e638e037826fa79)
        }

        {
            mstore(0xda0, 0x0000000000000000000000000000000009d8e400415f21f4d08aeebcddac018f)
            mstore(0xdc0, 0x38c207ec396fa2248a74171ce11b50f1262d5b3130910e6aa8312225a128de8d)
            mstore(0xde0, 0x000000000000000000000000000000001542095c996cf3369d4d6f88d893bae5)
            mstore(0xe00, 0x02094511259e4e4ebab04ddd67734c50bf045dec3740d30d656a2c144b765179)
        }

        {
            mstore(0xe20, 0x0000000000000000000000000000000008f4d51fb39849ae50e1c0db9cd179fc)
            mstore(0xe40, 0x5ef96a736a4ef378515789a9ea86d830217d82751480a3dcc049cf0d4969e627)
            mstore(0xe60, 0x00000000000000000000000000000000090e52a50a2b6b9b38d47c26946649a0)
            mstore(0xe80, 0x3ba16a6224830c3a165575ed836ba6284df33c457bcadb616c4a057e27a99bbe)
        }

        {
            mstore(0xea0, 0x000000000000000000000000000000000644efebda38cae6c5ad6786e0319bd5)
            mstore(0xec0, 0x760b894d26980802774573f9b4205bb9f93cde2549eb6dd127a073c87181afaf)
            mstore(0xee0, 0x0000000000000000000000000000000009bcd759d0b85c8658be2dfa7e0cc467)
            mstore(0xf00, 0x30b399b8e3637260d49d71444f98cf9ca5490ccc8b1f161a86e4235120cfc289)
        }

        {
            mstore(0xf20, 0x000000000000000000000000000000000a15bb85f22d1e245aef851c305b5492)
            mstore(0xf40, 0xaab756d2c6fef19d416e1392812cfc063413be7c72b017c17f28384f995704af)
            mstore(0xf60, 0x0000000000000000000000000000000015f3f5a42d569f4f2077101283983e3f)
            mstore(0xf80, 0xa544756951718a6ed54e4ef6c7129547099976298cc6da7c9dd73734e02216cf)
        }

        {
            mstore(0xfc0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0xfe0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x1000, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x1020, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }
mstore(0x1040, mod(calldataload(0x0), f_q))
mstore(0x1060, 23028419784151240539403500789343164848746138653814563173188701058439593665262)
{
                    mstore(0x1080, mload(0xfc0))
mstore(0x10a0, mload(0xfe0))
mstore(0x10c0, mload(0x1000))
mstore(0x10e0, mload(0x1020))
                }
mstore(0x1100, 1)
mstore(0x1120, mload(0x1040))

        {
            let flag := byte(0, calldataload(0x20))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1140, 0)
            mstore(0x1160, 0)
            mstore(0x1180, 0)
            mstore(0x11a0, 0)
            calldatacopy(0x1150, 0x21, 0x30)

            let x_hi := mload(0x1140)
            let x_lo := mload(0x1160)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1180, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1180))
                mstore(0x100, mload(0x11a0))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x11a0)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1180)), borrow)
                    mstore(0x1180, neg_y_hi)
                    mstore(0x11a0, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x51))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x11c0, 0)
            mstore(0x11e0, 0)
            mstore(0x1200, 0)
            mstore(0x1220, 0)
            calldatacopy(0x11d0, 0x52, 0x30)

            let x_hi := mload(0x11c0)
            let x_lo := mload(0x11e0)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1200, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1200))
                mstore(0x100, mload(0x1220))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1220)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1200)), borrow)
                    mstore(0x1200, neg_y_hi)
                    mstore(0x1220, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x82))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1240, 0)
            mstore(0x1260, 0)
            mstore(0x1280, 0)
            mstore(0x12a0, 0)
            calldatacopy(0x1250, 0x83, 0x30)

            let x_hi := mload(0x1240)
            let x_lo := mload(0x1260)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1280, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1280))
                mstore(0x100, mload(0x12a0))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x12a0)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1280)), borrow)
                    mstore(0x1280, neg_y_hi)
                    mstore(0x12a0, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0xb3))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x12c0, 0)
            mstore(0x12e0, 0)
            mstore(0x1300, 0)
            mstore(0x1320, 0)
            calldatacopy(0x12d0, 0xb4, 0x30)

            let x_hi := mload(0x12c0)
            let x_lo := mload(0x12e0)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1300, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1300))
                mstore(0x100, mload(0x1320))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1320)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1300)), borrow)
                    mstore(0x1300, neg_y_hi)
                    mstore(0x1320, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0xe4))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1340, 0)
            mstore(0x1360, 0)
            mstore(0x1380, 0)
            mstore(0x13a0, 0)
            calldatacopy(0x1350, 0xe5, 0x30)

            let x_hi := mload(0x1340)
            let x_lo := mload(0x1360)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1380, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1380))
                mstore(0x100, mload(0x13a0))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x13a0)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1380)), borrow)
                    mstore(0x1380, neg_y_hi)
                    mstore(0x13a0, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x115))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x13c0, 0)
            mstore(0x13e0, 0)
            mstore(0x1400, 0)
            mstore(0x1420, 0)
            calldatacopy(0x13d0, 0x116, 0x30)

            let x_hi := mload(0x13c0)
            let x_lo := mload(0x13e0)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1400, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1400))
                mstore(0x100, mload(0x1420))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1420)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1400)), borrow)
                    mstore(0x1400, neg_y_hi)
                    mstore(0x1420, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x146))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1440, 0)
            mstore(0x1460, 0)
            mstore(0x1480, 0)
            mstore(0x14a0, 0)
            calldatacopy(0x1450, 0x147, 0x30)

            let x_hi := mload(0x1440)
            let x_lo := mload(0x1460)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1480, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1480))
                mstore(0x100, mload(0x14a0))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x14a0)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1480)), borrow)
                    mstore(0x1480, neg_y_hi)
                    mstore(0x14a0, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x177))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x14c0, 0)
            mstore(0x14e0, 0)
            mstore(0x1500, 0)
            mstore(0x1520, 0)
            calldatacopy(0x14d0, 0x178, 0x30)

            let x_hi := mload(0x14c0)
            let x_lo := mload(0x14e0)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1500, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1500))
                mstore(0x100, mload(0x1520))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1520)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1500)), borrow)
                    mstore(0x1500, neg_y_hi)
                    mstore(0x1520, neg_y_lo)
                }
            }
        }
mstore(0x1540, keccak256(0x1060, 1248))
{
            let hash := mload(0x1540)
            mstore(0x1560, mod(hash, f_q))
            mstore(0x1580, hash)
        }

        {
            let flag := byte(0, calldataload(0x1a8))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x15a0, 0)
            mstore(0x15c0, 0)
            mstore(0x15e0, 0)
            mstore(0x1600, 0)
            calldatacopy(0x15b0, 0x1a9, 0x30)

            let x_hi := mload(0x15a0)
            let x_lo := mload(0x15c0)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x15e0, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x15e0))
                mstore(0x100, mload(0x1600))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1600)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x15e0)), borrow)
                    mstore(0x15e0, neg_y_hi)
                    mstore(0x1600, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x1d9))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1620, 0)
            mstore(0x1640, 0)
            mstore(0x1660, 0)
            mstore(0x1680, 0)
            calldatacopy(0x1630, 0x1da, 0x30)

            let x_hi := mload(0x1620)
            let x_lo := mload(0x1640)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1660, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1660))
                mstore(0x100, mload(0x1680))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1680)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1660)), borrow)
                    mstore(0x1660, neg_y_hi)
                    mstore(0x1680, neg_y_lo)
                }
            }
        }
mstore(0x16a0, keccak256(0x1580, 288))
{
            let hash := mload(0x16a0)
            mstore(0x16c0, mod(hash, f_q))
            mstore(0x16e0, hash)
        }
mstore8(5888, 1)
mstore(0x1700, keccak256(0x16e0, 33))
{
            let hash := mload(0x1700)
            mstore(0x1720, mod(hash, f_q))
            mstore(0x1740, hash)
        }

        {
            let flag := byte(0, calldataload(0x20a))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1760, 0)
            mstore(0x1780, 0)
            mstore(0x17a0, 0)
            mstore(0x17c0, 0)
            calldatacopy(0x1770, 0x20b, 0x30)

            let x_hi := mload(0x1760)
            let x_lo := mload(0x1780)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x17a0, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x17a0))
                mstore(0x100, mload(0x17c0))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x17c0)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x17a0)), borrow)
                    mstore(0x17a0, neg_y_hi)
                    mstore(0x17c0, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x23b))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x17e0, 0)
            mstore(0x1800, 0)
            mstore(0x1820, 0)
            mstore(0x1840, 0)
            calldatacopy(0x17f0, 0x23c, 0x30)

            let x_hi := mload(0x17e0)
            let x_lo := mload(0x1800)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1820, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1820))
                mstore(0x100, mload(0x1840))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1840)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1820)), borrow)
                    mstore(0x1820, neg_y_hi)
                    mstore(0x1840, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x26c))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1860, 0)
            mstore(0x1880, 0)
            mstore(0x18a0, 0)
            mstore(0x18c0, 0)
            calldatacopy(0x1870, 0x26d, 0x30)

            let x_hi := mload(0x1860)
            let x_lo := mload(0x1880)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x18a0, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x18a0))
                mstore(0x100, mload(0x18c0))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x18c0)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x18a0)), borrow)
                    mstore(0x18a0, neg_y_hi)
                    mstore(0x18c0, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x29d))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x18e0, 0)
            mstore(0x1900, 0)
            mstore(0x1920, 0)
            mstore(0x1940, 0)
            calldatacopy(0x18f0, 0x29e, 0x30)

            let x_hi := mload(0x18e0)
            let x_lo := mload(0x1900)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1920, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1920))
                mstore(0x100, mload(0x1940))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1940)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1920)), borrow)
                    mstore(0x1920, neg_y_hi)
                    mstore(0x1940, neg_y_lo)
                }
            }
        }
mstore(0x1960, keccak256(0x1740, 544))
{
            let hash := mload(0x1960)
            mstore(0x1980, mod(hash, f_q))
            mstore(0x19a0, hash)
        }

        {
            let flag := byte(0, calldataload(0x2ce))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x19c0, 0)
            mstore(0x19e0, 0)
            mstore(0x1a00, 0)
            mstore(0x1a20, 0)
            calldatacopy(0x19d0, 0x2cf, 0x30)

            let x_hi := mload(0x19c0)
            let x_lo := mload(0x19e0)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a00, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1a00))
                mstore(0x100, mload(0x1a20))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1a20)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1a00)), borrow)
                    mstore(0x1a00, neg_y_hi)
                    mstore(0x1a20, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x2ff))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1a40, 0)
            mstore(0x1a60, 0)
            mstore(0x1a80, 0)
            mstore(0x1aa0, 0)
            calldatacopy(0x1a50, 0x300, 0x30)

            let x_hi := mload(0x1a40)
            let x_lo := mload(0x1a60)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a80, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1a80))
                mstore(0x100, mload(0x1aa0))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1aa0)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1a80)), borrow)
                    mstore(0x1a80, neg_y_hi)
                    mstore(0x1aa0, neg_y_lo)
                }
            }
        }
mstore(0x1ac0, keccak256(0x19a0, 288))
{
            let hash := mload(0x1ac0)
            mstore(0x1ae0, mod(hash, f_q))
            mstore(0x1b00, hash)
        }

        {
            let flag := byte(0, calldataload(0x330))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1b20, 0)
            mstore(0x1b40, 0)
            mstore(0x1b60, 0)
            mstore(0x1b80, 0)
            calldatacopy(0x1b30, 0x331, 0x30)

            let x_hi := mload(0x1b20)
            let x_lo := mload(0x1b40)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1b60, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1b60))
                mstore(0x100, mload(0x1b80))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1b80)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1b60)), borrow)
                    mstore(0x1b60, neg_y_hi)
                    mstore(0x1b80, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x361))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1ba0, 0)
            mstore(0x1bc0, 0)
            mstore(0x1be0, 0)
            mstore(0x1c00, 0)
            calldatacopy(0x1bb0, 0x362, 0x30)

            let x_hi := mload(0x1ba0)
            let x_lo := mload(0x1bc0)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1be0, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1be0))
                mstore(0x100, mload(0x1c00))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1c00)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1be0)), borrow)
                    mstore(0x1be0, neg_y_hi)
                    mstore(0x1c00, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x392))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1c20, 0)
            mstore(0x1c40, 0)
            mstore(0x1c60, 0)
            mstore(0x1c80, 0)
            calldatacopy(0x1c30, 0x393, 0x30)

            let x_hi := mload(0x1c20)
            let x_lo := mload(0x1c40)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1c60, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1c60))
                mstore(0x100, mload(0x1c80))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1c80)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1c60)), borrow)
                    mstore(0x1c60, neg_y_hi)
                    mstore(0x1c80, neg_y_lo)
                }
            }
        }

        {
            let flag := byte(0, calldataload(0x3c3))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x1ca0, 0)
            mstore(0x1cc0, 0)
            mstore(0x1ce0, 0)
            mstore(0x1d00, 0)
            calldatacopy(0x1cb0, 0x3c4, 0x30)

            let x_hi := mload(0x1ca0)
            let x_lo := mload(0x1cc0)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1ce0, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x1ce0))
                mstore(0x100, mload(0x1d00))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x1d00)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x1ce0)), borrow)
                    mstore(0x1ce0, neg_y_hi)
                    mstore(0x1d00, neg_y_lo)
                }
            }
        }
mstore(0x1d20, keccak256(0x1b00, 544))
{
            let hash := mload(0x1d20)
            mstore(0x1d40, mod(hash, f_q))
            mstore(0x1d60, hash)
        }
mstore(0x1d80, mod(calldataload(0x3f4), f_q))
mstore(0x1da0, mod(calldataload(0x414), f_q))
mstore(0x1dc0, mod(calldataload(0x434), f_q))
mstore(0x1de0, mod(calldataload(0x454), f_q))
mstore(0x1e00, mod(calldataload(0x474), f_q))
mstore(0x1e20, mod(calldataload(0x494), f_q))
mstore(0x1e40, mod(calldataload(0x4b4), f_q))
mstore(0x1e60, mod(calldataload(0x4d4), f_q))
mstore(0x1e80, mod(calldataload(0x4f4), f_q))
mstore(0x1ea0, mod(calldataload(0x514), f_q))
mstore(0x1ec0, mod(calldataload(0x534), f_q))
mstore(0x1ee0, mod(calldataload(0x554), f_q))
mstore(0x1f00, mod(calldataload(0x574), f_q))
mstore(0x1f20, mod(calldataload(0x594), f_q))
mstore(0x1f40, mod(calldataload(0x5b4), f_q))
mstore(0x1f60, mod(calldataload(0x5d4), f_q))
mstore(0x1f80, mod(calldataload(0x5f4), f_q))
mstore(0x1fa0, mod(calldataload(0x614), f_q))
mstore(0x1fc0, mod(calldataload(0x634), f_q))
mstore(0x1fe0, mod(calldataload(0x654), f_q))
mstore(0x2000, mod(calldataload(0x674), f_q))
mstore(0x2020, mod(calldataload(0x694), f_q))
mstore(0x2040, mod(calldataload(0x6b4), f_q))
mstore(0x2060, mod(calldataload(0x6d4), f_q))
mstore(0x2080, mod(calldataload(0x6f4), f_q))
mstore(0x20a0, mod(calldataload(0x714), f_q))
mstore(0x20c0, mod(calldataload(0x734), f_q))
mstore(0x20e0, mod(calldataload(0x754), f_q))
mstore(0x2100, mod(calldataload(0x774), f_q))
mstore(0x2120, mod(calldataload(0x794), f_q))
mstore(0x2140, mod(calldataload(0x7b4), f_q))
mstore(0x2160, mod(calldataload(0x7d4), f_q))
mstore(0x2180, mod(calldataload(0x7f4), f_q))
mstore(0x21a0, mod(calldataload(0x814), f_q))
mstore(0x21c0, mod(calldataload(0x834), f_q))
mstore(0x21e0, mod(calldataload(0x854), f_q))
mstore(0x2200, mod(calldataload(0x874), f_q))
mstore(0x2220, mod(calldataload(0x894), f_q))
mstore(0x2240, mod(calldataload(0x8b4), f_q))
mstore(0x2260, mod(calldataload(0x8d4), f_q))
mstore(0x2280, mod(calldataload(0x8f4), f_q))
mstore(0x22a0, mod(calldataload(0x914), f_q))
mstore(0x22c0, mod(calldataload(0x934), f_q))
mstore(0x22e0, mod(calldataload(0x954), f_q))
mstore(0x2300, mod(calldataload(0x974), f_q))
mstore(0x2320, mod(calldataload(0x994), f_q))
mstore(0x2340, mod(calldataload(0x9b4), f_q))
mstore(0x2360, mod(calldataload(0x9d4), f_q))
mstore(0x2380, mod(calldataload(0x9f4), f_q))
mstore(0x23a0, mod(calldataload(0xa14), f_q))
mstore(0x23c0, mod(calldataload(0xa34), f_q))
mstore(0x23e0, mod(calldataload(0xa54), f_q))
mstore(0x2400, mod(calldataload(0xa74), f_q))
mstore(0x2420, mod(calldataload(0xa94), f_q))
mstore(0x2440, keccak256(0x1d60, 1760))
{
            let hash := mload(0x2440)
            mstore(0x2460, mod(hash, f_q))
            mstore(0x2480, hash)
        }
mstore8(9376, 1)
mstore(0x24a0, keccak256(0x2480, 33))
{
            let hash := mload(0x24a0)
            mstore(0x24c0, mod(hash, f_q))
            mstore(0x24e0, hash)
        }

        {
            let flag := byte(0, calldataload(0xab4))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x2500, 0)
            mstore(0x2520, 0)
            mstore(0x2540, 0)
            mstore(0x2560, 0)
            calldatacopy(0x2510, 0xab5, 0x30)

            let x_hi := mload(0x2500)
            let x_lo := mload(0x2520)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x2540, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x2540))
                mstore(0x100, mload(0x2560))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x2560)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x2540)), borrow)
                    mstore(0x2540, neg_y_hi)
                    mstore(0x2560, neg_y_lo)
                }
            }
        }
mstore(0x2580, keccak256(0x24e0, 160))
{
            let hash := mload(0x2580)
            mstore(0x25a0, mod(hash, f_q))
            mstore(0x25c0, hash)
        }
mstore(0x25e0, mod(calldataload(0xae5), f_q))
mstore(0x2600, mod(calldataload(0xb05), f_q))
mstore(0x2620, mod(calldataload(0xb25), f_q))
mstore(0x2640, mod(calldataload(0xb45), f_q))
mstore(0x2660, keccak256(0x25c0, 160))
{
            let hash := mload(0x2660)
            mstore(0x2680, mod(hash, f_q))
            mstore(0x26a0, hash)
        }

        {
            let flag := byte(0, calldataload(0xb65))
            let y_odd := and(flag, 1)
            let is_inf := and(shr(1, flag), 1)
            // Reject unsupported flag bits.
            success := and(iszero(and(flag, 0xfc)), success)

            // Zero-initialize x/y limbs then copy compact x.
            mstore(0x26c0, 0)
            mstore(0x26e0, 0)
            mstore(0x2700, 0)
            mstore(0x2720, 0)
            calldatacopy(0x26d0, 0xb66, 0x30)

            let x_hi := mload(0x26c0)
            let x_lo := mload(0x26e0)

            if is_inf {
                // Infinity must carry zero x and odd-flag unset.
                success := and(eq(y_odd, 0), success)
                success := and(eq(x_hi, 0), success)
                success := and(eq(x_lo, 0), success)
            }

            if iszero(is_inf) {
                // Enforce x < p.
                success := and(
                    or(lt(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(x_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), lt(x_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))),
                    success
                )

                // rhs <- x^3 mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, x_hi)
                mstore(0x100, x_lo)
                mstore(0x120, 0)
                mstore(0x140, 3)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1a0, 0x40), 1),
                    success
                )

                // rhs <- (x^3 + 4) mod p.
                let rhs_hi := mload(0x1a0)
                let rhs_lo0 := mload(0x1c0)
                let rhs_lo := add(rhs_lo0, 4)
                let carry := lt(rhs_lo, rhs_lo0)
                rhs_hi := add(rhs_hi, carry)
                if or(gt(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), and(eq(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7), iszero(lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)))) {
                    rhs_hi := sub(rhs_hi, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                    let borrow := lt(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_lo := sub(rhs_lo, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                    rhs_hi := sub(rhs_hi, borrow)
                }
                mstore(0x1a0, rhs_hi)
                mstore(0x1c0, rhs_lo)

                // y <- rhs^((p+1)/4) mod p.
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, rhs_hi)
                mstore(0x100, rhs_lo)
                mstore(0x120, 0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35)
                mstore(0x140, 0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x2700, 0x40), 1),
                    success
                )

                // Validate square root: y^2 == rhs (mod p).
                mstore(0x80, 0x40)
                mstore(0xa0, 0x40)
                mstore(0xc0, 0x40)
                mstore(0xe0, mload(0x2700))
                mstore(0x100, mload(0x2720))
                mstore(0x120, 0)
                mstore(0x140, 2)
                mstore(0x160, 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7)
                mstore(0x180, 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
                success := and(
                    eq(staticcall(gas(), 0x5, 0x80, 0x120, 0x1e0, 0x40), 1),
                    success
                )
                success := and(eq(mload(0x1e0), mload(0x1a0)), success)
                success := and(eq(mload(0x200), mload(0x1c0)), success)

                // Select y root by oddness bit.
                let y_lo := mload(0x2720)
                let is_odd_y := and(y_lo, 1)
                if xor(is_odd_y, y_odd) {
                    let neg_y_lo := sub(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let borrow := lt(0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab, y_lo)
                    let neg_y_hi := sub(sub(0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7, mload(0x2700)), borrow)
                    mstore(0x2700, neg_y_hi)
                    mstore(0x2720, neg_y_lo)
                }
            }
        }

        {
            mstore(0x2740, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x2760, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x2780, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x27a0, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }
mstore(0x27c0, mulmod(mload(0x1d40), mload(0x1d40), f_q))
mstore(0x27e0, mulmod(mload(0x27c0), mload(0x27c0), f_q))
mstore(0x2800, mulmod(mload(0x27e0), mload(0x27e0), f_q))
mstore(0x2820, mulmod(mload(0x2800), mload(0x2800), f_q))
mstore(0x2840, mulmod(mload(0x2820), mload(0x2820), f_q))
mstore(0x2860, mulmod(mload(0x2840), mload(0x2840), f_q))
mstore(0x2880, addmod(mload(0x2860), 52435875175126190479447740508185965837690552500527637822603658699938581184512, f_q))
mstore(0x28a0, mulmod(mload(0x2880), 51616564625514843753206369562745560121476637617706893481625476532752040853505, f_q))
mstore(0x28c0, mulmod(mload(0x28a0), 21259823323969146045885553965890482219221908228759787200404479960115227367690, f_q))
mstore(0x28e0, addmod(mload(0x1d40), 31176051851157044433562186542295483618468644271767850622199178739823353816823, f_q))
mstore(0x2900, mulmod(mload(0x28a0), 14887102955893838413024403264664292195708703256831905665143363416435654328648, f_q))
mstore(0x2920, addmod(mload(0x1d40), 37548772219232352066423337243521673641981849243695732157460295283502926855865, f_q))
mstore(0x2940, mulmod(mload(0x28a0), 2527721918302134385520002926840515195543678449692795676238296383251703745807, f_q))
mstore(0x2960, addmod(mload(0x1d40), 49908153256824056093927737581345450642146874050834842146365362316686877438706, f_q))
mstore(0x2980, mulmod(mload(0x28a0), 26753076894533791554649012143113393549300550745003194222677083919072199473480, f_q))
mstore(0x29a0, addmod(mload(0x1d40), 25682798280592398924798728365072572288390001755524443599926574780866381711033, f_q))
mstore(0x29c0, mulmod(mload(0x28a0), 7500590202698556019030633716209352927214297656990813043538655792743940636058, f_q))
mstore(0x29e0, addmod(mload(0x1d40), 44935284972427634460417106791976612910476254843536824779065002907194640548455, f_q))
mstore(0x2a00, mulmod(mload(0x28a0), 42722234674624019897108426302713230860602919991722520098540931937949837992684, f_q))
mstore(0x2a20, addmod(mload(0x1d40), 9713640500502170582339314205472734977087632508805117724062726761988743191829, f_q))
mstore(0x2a40, mulmod(mload(0x28a0), 45254319123522011116259460062854627366454101350769349111320208945036885998124, f_q))
mstore(0x2a60, addmod(mload(0x1d40), 7181556051604179363188280445331338471236451149758288711283449754901695186389, f_q))
mstore(0x2a80, mulmod(mload(0x28a0), 1, f_q))
mstore(0x2aa0, addmod(mload(0x1d40), 52435875175126190479447740508185965837690552500527637822603658699938581184512, f_q))
{
            let prod := mload(0x28e0)

                prod := mulmod(mload(0x2920), prod, f_q)
                mstore(0x2ac0, prod)
            
                prod := mulmod(mload(0x2960), prod, f_q)
                mstore(0x2ae0, prod)
            
                prod := mulmod(mload(0x29a0), prod, f_q)
                mstore(0x2b00, prod)
            
                prod := mulmod(mload(0x29e0), prod, f_q)
                mstore(0x2b20, prod)
            
                prod := mulmod(mload(0x2a20), prod, f_q)
                mstore(0x2b40, prod)
            
                prod := mulmod(mload(0x2a60), prod, f_q)
                mstore(0x2b60, prod)
            
                prod := mulmod(mload(0x2aa0), prod, f_q)
                mstore(0x2b80, prod)
            
                prod := mulmod(mload(0x2880), prod, f_q)
                mstore(0x2ba0, prod)
            
        }
mstore(0x2be0, 32)
mstore(0x2c00, 32)
mstore(0x2c20, 32)
mstore(0x2c40, mload(0x2ba0))
mstore(0x2c60, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x2c80, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x2be0, 0xc0, 0x2bc0, 0x20), 1), success)
{
            
            let inv := mload(0x2bc0)
            let v
        
                    v := mload(0x2880)
                    mstore(10368, mulmod(mload(0x2b80), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x2aa0)
                    mstore(10912, mulmod(mload(0x2b60), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x2a60)
                    mstore(10848, mulmod(mload(0x2b40), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x2a20)
                    mstore(10784, mulmod(mload(0x2b20), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x29e0)
                    mstore(10720, mulmod(mload(0x2b00), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x29a0)
                    mstore(10656, mulmod(mload(0x2ae0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x2960)
                    mstore(10592, mulmod(mload(0x2ac0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x2920)
                    mstore(10528, mulmod(mload(0x28e0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                mstore(0x28e0, inv)

        }
mstore(0x2ca0, mulmod(mload(0x28c0), mload(0x28e0), f_q))
mstore(0x2cc0, mulmod(mload(0x2900), mload(0x2920), f_q))
mstore(0x2ce0, mulmod(mload(0x2940), mload(0x2960), f_q))
mstore(0x2d00, mulmod(mload(0x2980), mload(0x29a0), f_q))
mstore(0x2d20, mulmod(mload(0x29c0), mload(0x29e0), f_q))
mstore(0x2d40, mulmod(mload(0x2a00), mload(0x2a20), f_q))
mstore(0x2d60, mulmod(mload(0x2a40), mload(0x2a60), f_q))
mstore(0x2d80, mulmod(mload(0x2a80), mload(0x2aa0), f_q))
{
            let result := mulmod(mload(0x2d80), mload(0x1040), f_q)
mstore(11680, result)
        }
mstore(0x2dc0, mulmod(mload(0x1da0), mload(0x1f20), f_q))
mstore(0x2de0, addmod(mload(0x2020), mload(0x2dc0), f_q))
mstore(0x2e00, mulmod(mload(0x1dc0), mload(0x1f40), f_q))
mstore(0x2e20, addmod(mload(0x2de0), mload(0x2e00), f_q))
mstore(0x2e40, mulmod(mload(0x1de0), mload(0x1f60), f_q))
mstore(0x2e60, addmod(mload(0x2e20), mload(0x2e40), f_q))
mstore(0x2e80, mulmod(mload(0x1e00), mload(0x1f80), f_q))
mstore(0x2ea0, addmod(mload(0x2e60), mload(0x2e80), f_q))
mstore(0x2ec0, mulmod(mload(0x1e20), mload(0x1fa0), f_q))
mstore(0x2ee0, addmod(mload(0x2ea0), mload(0x2ec0), f_q))
mstore(0x2f00, mulmod(mload(0x1e40), mload(0x1fc0), f_q))
mstore(0x2f20, addmod(mload(0x2ee0), mload(0x2f00), f_q))
mstore(0x2f40, mulmod(mload(0x1da0), mload(0x1fe0), f_q))
mstore(0x2f60, mulmod(mload(0x1dc0), mload(0x2f40), f_q))
mstore(0x2f80, addmod(mload(0x2f20), mload(0x2f60), f_q))
mstore(0x2fa0, mulmod(mload(0x1da0), mload(0x2000), f_q))
mstore(0x2fc0, mulmod(mload(0x1de0), mload(0x2fa0), f_q))
mstore(0x2fe0, addmod(mload(0x2f80), mload(0x2fc0), f_q))
mstore(0x3000, mulmod(mload(0x2fe0), mload(0x20a0), f_q))
mstore(0x3020, mulmod(mload(0x1ae0), mload(0x3000), f_q))
mstore(0x3040, addmod(mload(0x1dc0), mload(0x1de0), f_q))
mstore(0x3060, addmod(mload(0x3040), sub(f_q, mload(0x1e00)), f_q))
mstore(0x3080, addmod(mload(0x3060), sub(f_q, mload(0x1e20)), f_q))
mstore(0x30a0, mulmod(mload(0x3080), mload(0x20c0), f_q))
mstore(0x30c0, addmod(mload(0x3020), mload(0x30a0), f_q))
mstore(0x30e0, mulmod(mload(0x1ae0), mload(0x30c0), f_q))
mstore(0x3100, addmod(mload(0x1da0), mload(0x1f20), f_q))
mstore(0x3120, addmod(mload(0x3100), sub(f_q, mload(0x1e40)), f_q))
mstore(0x3140, mulmod(mload(0x3120), mload(0x20e0), f_q))
mstore(0x3160, addmod(mload(0x30e0), mload(0x3140), f_q))
mstore(0x3180, mulmod(mload(0x1ae0), mload(0x3160), f_q))
mstore(0x31a0, addmod(mload(0x1dc0), mload(0x1f40), f_q))
mstore(0x31c0, addmod(mload(0x31a0), sub(f_q, mload(0x1e60)), f_q))
mstore(0x31e0, mulmod(mload(0x31c0), mload(0x20e0), f_q))
mstore(0x3200, addmod(mload(0x3180), mload(0x31e0), f_q))
mstore(0x3220, mulmod(mload(0x1ae0), mload(0x3200), f_q))
mstore(0x3240, addmod(mload(0x1de0), mload(0x1f60), f_q))
mstore(0x3260, addmod(mload(0x3240), sub(f_q, mload(0x1e80)), f_q))
mstore(0x3280, mulmod(mload(0x3260), mload(0x20e0), f_q))
mstore(0x32a0, addmod(mload(0x3220), mload(0x3280), f_q))
mstore(0x32c0, mulmod(mload(0x1ae0), mload(0x32a0), f_q))
mstore(0x32e0, mulmod(mload(0x1da0), mload(0x1da0), f_q))
mstore(0x3300, mulmod(mload(0x32e0), mload(0x1da0), f_q))
mstore(0x3320, addmod(mload(0x3300), sub(f_q, mload(0x1e00)), f_q))
mstore(0x3340, mulmod(mload(0x3320), mload(0x2120), f_q))
mstore(0x3360, addmod(mload(0x32c0), mload(0x3340), f_q))
mstore(0x3380, mulmod(mload(0x1ae0), mload(0x3360), f_q))
mstore(0x33a0, mulmod(mload(0x1dc0), mload(0x1dc0), f_q))
mstore(0x33c0, mulmod(mload(0x33a0), mload(0x1dc0), f_q))
mstore(0x33e0, addmod(mload(0x33c0), sub(f_q, mload(0x1e20)), f_q))
mstore(0x3400, mulmod(mload(0x33e0), mload(0x2120), f_q))
mstore(0x3420, addmod(mload(0x3380), mload(0x3400), f_q))
mstore(0x3440, mulmod(mload(0x1ae0), mload(0x3420), f_q))
mstore(0x3460, mulmod(mload(0x1de0), mload(0x1de0), f_q))
mstore(0x3480, mulmod(mload(0x3460), mload(0x1de0), f_q))
mstore(0x34a0, addmod(mload(0x3480), sub(f_q, mload(0x1ea0)), f_q))
mstore(0x34c0, mulmod(mload(0x34a0), mload(0x2120), f_q))
mstore(0x34e0, addmod(mload(0x3440), mload(0x34c0), f_q))
mstore(0x3500, mulmod(mload(0x1ae0), mload(0x34e0), f_q))
mstore(0x3520, addmod(mload(0x1fc0), sub(f_q, mload(0x1e40)), f_q))
mstore(0x3540, mulmod(mload(0x1e00), mload(0x32e0), f_q))
mstore(0x3560, mulmod(mload(0x3540), 12440513488882586407557540066179884648646530011544707182889396930153310132942, f_q))
mstore(0x3580, addmod(mload(0x3520), mload(0x3560), f_q))
mstore(0x35a0, mulmod(mload(0x1e20), mload(0x33a0), f_q))
mstore(0x35c0, mulmod(mload(0x35a0), 28020747150333089913259220781304558809551608596314918030152947066915898054499, f_q))
mstore(0x35e0, addmod(mload(0x3580), mload(0x35c0), f_q))
mstore(0x3600, mulmod(mload(0x1ea0), mload(0x3460), f_q))
mstore(0x3620, mulmod(mload(0x3600), 28505902463311974130913002774524928623644005505993681602486681565155683331521, f_q))
mstore(0x3640, addmod(mload(0x35e0), mload(0x3620), f_q))
mstore(0x3660, mulmod(mload(0x3640), mload(0x2120), f_q))
mstore(0x3680, addmod(mload(0x3500), mload(0x3660), f_q))
mstore(0x36a0, mulmod(mload(0x1ae0), mload(0x3680), f_q))
mstore(0x36c0, addmod(mload(0x1fe0), sub(f_q, mload(0x1e60)), f_q))
mstore(0x36e0, mulmod(mload(0x3540), 29084297485723905200880885323289986130569887053242706304266829364413965316980, f_q))
mstore(0x3700, addmod(mload(0x36c0), mload(0x36e0), f_q))
mstore(0x3720, mulmod(mload(0x35a0), 5054565981041632243581284853746902850980503096245579875276544410572564089329, f_q))
mstore(0x3740, addmod(mload(0x3700), mload(0x3720), f_q))
mstore(0x3760, mulmod(mload(0x3600), 7179405695647424344643177657798954274869382720335107962712222495241823787551, f_q))
mstore(0x3780, addmod(mload(0x3740), mload(0x3760), f_q))
mstore(0x37a0, mulmod(mload(0x3780), mload(0x2120), f_q))
mstore(0x37c0, addmod(mload(0x36a0), mload(0x37a0), f_q))
mstore(0x37e0, mulmod(mload(0x1ae0), mload(0x37c0), f_q))
mstore(0x3800, addmod(mload(0x2000), sub(f_q, mload(0x1e80)), f_q))
mstore(0x3820, mulmod(mload(0x3540), 42569072482279996318031820844820583094661593761988851871644829917446303682880, f_q))
mstore(0x3840, addmod(mload(0x3800), mload(0x3820), f_q))
mstore(0x3860, mulmod(mload(0x35a0), 48777675531739959342114240072267441286903816384223937749440830379544192657290, f_q))
mstore(0x3880, addmod(mload(0x3840), mload(0x3860), f_q))
mstore(0x38a0, mulmod(mload(0x3600), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x38c0, addmod(mload(0x3880), mload(0x38a0), f_q))
mstore(0x38e0, mulmod(mload(0x38c0), mload(0x2120), f_q))
mstore(0x3900, addmod(mload(0x37e0), mload(0x38e0), f_q))
mstore(0x3920, mulmod(mload(0x1ae0), mload(0x3900), f_q))
mstore(0x3940, addmod(1, sub(f_q, mload(0x2280)), f_q))
mstore(0x3960, mulmod(mload(0x3940), mload(0x2d80), f_q))
mstore(0x3980, addmod(mload(0x3920), mload(0x3960), f_q))
mstore(0x39a0, mulmod(mload(0x1ae0), mload(0x3980), f_q))
mstore(0x39c0, mulmod(mload(0x2340), mload(0x2340), f_q))
mstore(0x39e0, addmod(mload(0x39c0), sub(f_q, mload(0x2340)), f_q))
mstore(0x3a00, mulmod(mload(0x39e0), mload(0x2ca0), f_q))
mstore(0x3a20, addmod(mload(0x39a0), mload(0x3a00), f_q))
mstore(0x3a40, mulmod(mload(0x1ae0), mload(0x3a20), f_q))
mstore(0x3a60, addmod(mload(0x22e0), sub(f_q, mload(0x22c0)), f_q))
mstore(0x3a80, mulmod(mload(0x3a60), mload(0x2d80), f_q))
mstore(0x3aa0, addmod(mload(0x3a40), mload(0x3a80), f_q))
mstore(0x3ac0, mulmod(mload(0x1ae0), mload(0x3aa0), f_q))
mstore(0x3ae0, addmod(mload(0x2340), sub(f_q, mload(0x2320)), f_q))
mstore(0x3b00, mulmod(mload(0x3ae0), mload(0x2d80), f_q))
mstore(0x3b20, addmod(mload(0x3ac0), mload(0x3b00), f_q))
mstore(0x3b40, mulmod(mload(0x1ae0), mload(0x3b20), f_q))
mstore(0x3b60, addmod(1, sub(f_q, mload(0x2ca0)), f_q))
mstore(0x3b80, addmod(mload(0x2cc0), mload(0x2ce0), f_q))
mstore(0x3ba0, addmod(mload(0x3b80), mload(0x2d00), f_q))
mstore(0x3bc0, addmod(mload(0x3ba0), mload(0x2d20), f_q))
mstore(0x3be0, addmod(mload(0x3bc0), mload(0x2d40), f_q))
mstore(0x3c00, addmod(mload(0x3be0), mload(0x2d60), f_q))
mstore(0x3c20, addmod(mload(0x3b60), sub(f_q, mload(0x3c00)), f_q))
mstore(0x3c40, mulmod(mload(0x2180), mload(0x16c0), f_q))
mstore(0x3c60, addmod(mload(0x1f00), mload(0x3c40), f_q))
mstore(0x3c80, addmod(mload(0x3c60), mload(0x1720), f_q))
mstore(0x3ca0, mulmod(mload(0x21a0), mload(0x16c0), f_q))
mstore(0x3cc0, addmod(mload(0x1da0), mload(0x3ca0), f_q))
mstore(0x3ce0, addmod(mload(0x3cc0), mload(0x1720), f_q))
mstore(0x3d00, mulmod(mload(0x3ce0), mload(0x3c80), f_q))
mstore(0x3d20, mulmod(mload(0x21c0), mload(0x16c0), f_q))
mstore(0x3d40, addmod(mload(0x1dc0), mload(0x3d20), f_q))
mstore(0x3d60, addmod(mload(0x3d40), mload(0x1720), f_q))
mstore(0x3d80, mulmod(mload(0x3d60), mload(0x3d00), f_q))
mstore(0x3da0, mulmod(mload(0x3d80), mload(0x22a0), f_q))
mstore(0x3dc0, mulmod(1, mload(0x16c0), f_q))
mstore(0x3de0, mulmod(mload(0x1d40), mload(0x3dc0), f_q))
mstore(0x3e00, addmod(mload(0x1f00), mload(0x3de0), f_q))
mstore(0x3e20, addmod(mload(0x3e00), mload(0x1720), f_q))
mstore(0x3e40, mulmod(3793952369011177517951424454785176000433849974408744014172535497121832470999, mload(0x16c0), f_q))
mstore(0x3e60, mulmod(mload(0x1d40), mload(0x3e40), f_q))
mstore(0x3e80, addmod(mload(0x1da0), mload(0x3e60), f_q))
mstore(0x3ea0, addmod(mload(0x3e80), mload(0x1720), f_q))
mstore(0x3ec0, mulmod(mload(0x3ea0), mload(0x3e20), f_q))
mstore(0x3ee0, mulmod(29260201042546974833203213796440688721049425934417030432187341694347311461130, mload(0x16c0), f_q))
mstore(0x3f00, mulmod(mload(0x1d40), mload(0x3ee0), f_q))
mstore(0x3f20, addmod(mload(0x1dc0), mload(0x3f00), f_q))
mstore(0x3f40, addmod(mload(0x3f20), mload(0x1720), f_q))
mstore(0x3f60, mulmod(mload(0x3f40), mload(0x3ec0), f_q))
mstore(0x3f80, mulmod(mload(0x3f60), mload(0x2280), f_q))
mstore(0x3fa0, addmod(mload(0x3da0), sub(f_q, mload(0x3f80)), f_q))
mstore(0x3fc0, mulmod(mload(0x3fa0), mload(0x3c20), f_q))
mstore(0x3fe0, addmod(mload(0x3b40), mload(0x3fc0), f_q))
mstore(0x4000, mulmod(mload(0x1ae0), mload(0x3fe0), f_q))
mstore(0x4020, mulmod(mload(0x21e0), mload(0x16c0), f_q))
mstore(0x4040, addmod(mload(0x1de0), mload(0x4020), f_q))
mstore(0x4060, addmod(mload(0x4040), mload(0x1720), f_q))
mstore(0x4080, mulmod(mload(0x2200), mload(0x16c0), f_q))
mstore(0x40a0, addmod(mload(0x1e00), mload(0x4080), f_q))
mstore(0x40c0, addmod(mload(0x40a0), mload(0x1720), f_q))
mstore(0x40e0, mulmod(mload(0x40c0), mload(0x4060), f_q))
mstore(0x4100, mulmod(mload(0x2220), mload(0x16c0), f_q))
mstore(0x4120, addmod(mload(0x1e20), mload(0x4100), f_q))
mstore(0x4140, addmod(mload(0x4120), mload(0x1720), f_q))
mstore(0x4160, mulmod(mload(0x4140), mload(0x40e0), f_q))
mstore(0x4180, mulmod(mload(0x4160), mload(0x2300), f_q))
mstore(0x41a0, mulmod(30087697416233164107364529847082617342382024227044140347550467692890124986659, mload(0x16c0), f_q))
mstore(0x41c0, mulmod(mload(0x1d40), mload(0x41a0), f_q))
mstore(0x41e0, addmod(mload(0x1de0), mload(0x41c0), f_q))
mstore(0x4200, addmod(mload(0x41e0), mload(0x1720), f_q))
mstore(0x4220, mulmod(50007016967099397293092916471763530035790684642821601195394169310725916110291, mload(0x16c0), f_q))
mstore(0x4240, mulmod(mload(0x1d40), mload(0x4220), f_q))
mstore(0x4260, addmod(mload(0x1e00), mload(0x4240), f_q))
mstore(0x4280, addmod(mload(0x4260), mload(0x1720), f_q))
mstore(0x42a0, mulmod(mload(0x4280), mload(0x4200), f_q))
mstore(0x42c0, mulmod(27153057483211730484975145092142082049750746716056827598870820011140481502624, mload(0x16c0), f_q))
mstore(0x42e0, mulmod(mload(0x1d40), mload(0x42c0), f_q))
mstore(0x4300, addmod(mload(0x1e20), mload(0x42e0), f_q))
mstore(0x4320, addmod(mload(0x4300), mload(0x1720), f_q))
mstore(0x4340, mulmod(mload(0x4320), mload(0x42a0), f_q))
mstore(0x4360, mulmod(mload(0x4340), mload(0x22e0), f_q))
mstore(0x4380, addmod(mload(0x4180), sub(f_q, mload(0x4360)), f_q))
mstore(0x43a0, mulmod(mload(0x4380), mload(0x3c20), f_q))
mstore(0x43c0, addmod(mload(0x4000), mload(0x43a0), f_q))
mstore(0x43e0, mulmod(mload(0x1ae0), mload(0x43c0), f_q))
mstore(0x4400, mulmod(mload(0x2240), mload(0x16c0), f_q))
mstore(0x4420, addmod(mload(0x1d80), mload(0x4400), f_q))
mstore(0x4440, addmod(mload(0x4420), mload(0x1720), f_q))
mstore(0x4460, mulmod(mload(0x2260), mload(0x16c0), f_q))
mstore(0x4480, addmod(mload(0x2da0), mload(0x4460), f_q))
mstore(0x44a0, addmod(mload(0x4480), mload(0x1720), f_q))
mstore(0x44c0, mulmod(mload(0x44a0), mload(0x4440), f_q))
mstore(0x44e0, mulmod(mload(0x44c0), mload(0x2360), f_q))
mstore(0x4500, mulmod(10702539897433481834547003544093270805576009760020429658622430844384109348913, mload(0x16c0), f_q))
mstore(0x4520, mulmod(mload(0x1d40), mload(0x4500), f_q))
mstore(0x4540, addmod(mload(0x1d80), mload(0x4520), f_q))
mstore(0x4560, addmod(mload(0x4540), mload(0x1720), f_q))
mstore(0x4580, mulmod(12176195809781855613695208773552147130199916160023471917144658464292859735274, mload(0x16c0), f_q))
mstore(0x45a0, mulmod(mload(0x1d40), mload(0x4580), f_q))
mstore(0x45c0, addmod(mload(0x2da0), mload(0x45a0), f_q))
mstore(0x45e0, addmod(mload(0x45c0), mload(0x1720), f_q))
mstore(0x4600, mulmod(mload(0x45e0), mload(0x4560), f_q))
mstore(0x4620, mulmod(mload(0x4600), mload(0x2340), f_q))
mstore(0x4640, addmod(mload(0x44e0), sub(f_q, mload(0x4620)), f_q))
mstore(0x4660, mulmod(mload(0x4640), mload(0x3c20), f_q))
mstore(0x4680, addmod(mload(0x43e0), mload(0x4660), f_q))
mstore(0x46a0, mulmod(mload(0x1ae0), mload(0x4680), f_q))
mstore(0x46c0, addmod(1, sub(f_q, mload(0x2380)), f_q))
mstore(0x46e0, mulmod(mload(0x46c0), mload(0x2d80), f_q))
mstore(0x4700, addmod(mload(0x46a0), mload(0x46e0), f_q))
mstore(0x4720, mulmod(mload(0x1ae0), mload(0x4700), f_q))
mstore(0x4740, mulmod(mload(0x2380), mload(0x2380), f_q))
mstore(0x4760, addmod(mload(0x4740), sub(f_q, mload(0x2380)), f_q))
mstore(0x4780, mulmod(mload(0x4760), mload(0x2ca0), f_q))
mstore(0x47a0, addmod(mload(0x4720), mload(0x4780), f_q))
mstore(0x47c0, mulmod(mload(0x1ae0), mload(0x47a0), f_q))
mstore(0x47e0, addmod(mload(0x23c0), mload(0x16c0), f_q))
mstore(0x4800, mulmod(mload(0x47e0), mload(0x23a0), f_q))
mstore(0x4820, addmod(mload(0x2400), mload(0x1720), f_q))
mstore(0x4840, mulmod(mload(0x4820), mload(0x4800), f_q))
mstore(0x4860, mulmod(mload(0x1560), mload(0x2040), f_q))
mstore(0x4880, mulmod(mload(0x1dc0), mload(0x2100), f_q))
mstore(0x48a0, addmod(mload(0x4860), mload(0x4880), f_q))
mstore(0x48c0, addmod(mload(0x48a0), mload(0x16c0), f_q))
mstore(0x48e0, mulmod(mload(0x48c0), mload(0x2380), f_q))
mstore(0x4900, mulmod(mload(0x1560), mload(0x2060), f_q))
mstore(0x4920, addmod(mload(0x4900), mload(0x2080), f_q))
mstore(0x4940, addmod(mload(0x4920), mload(0x1720), f_q))
mstore(0x4960, mulmod(mload(0x4940), mload(0x48e0), f_q))
mstore(0x4980, addmod(mload(0x4840), sub(f_q, mload(0x4960)), f_q))
mstore(0x49a0, mulmod(mload(0x4980), mload(0x3c20), f_q))
mstore(0x49c0, addmod(mload(0x47c0), mload(0x49a0), f_q))
mstore(0x49e0, mulmod(mload(0x1ae0), mload(0x49c0), f_q))
mstore(0x4a00, addmod(mload(0x23c0), sub(f_q, mload(0x2400)), f_q))
mstore(0x4a20, mulmod(mload(0x4a00), mload(0x2d80), f_q))
mstore(0x4a40, addmod(mload(0x49e0), mload(0x4a20), f_q))
mstore(0x4a60, mulmod(mload(0x1ae0), mload(0x4a40), f_q))
mstore(0x4a80, mulmod(mload(0x4a00), mload(0x3c20), f_q))
mstore(0x4aa0, addmod(mload(0x23c0), sub(f_q, mload(0x23e0)), f_q))
mstore(0x4ac0, mulmod(mload(0x4aa0), mload(0x4a80), f_q))
mstore(0x4ae0, addmod(mload(0x4a60), mload(0x4ac0), f_q))
mstore(0x4b00, mulmod(mload(0x1ae0), mload(0x4ae0), f_q))
mstore(0x4b20, mulmod(mload(0x1da0), 40276410782279108334863105369904789343040261455045516584779277825615697839985, f_q))
mstore(0x4b40, mulmod(mload(0x1dc0), 37527016513455530468277088833539226510789135770417315120855317098742889359215, f_q))
mstore(0x4b60, addmod(mload(0x4b20), mload(0x4b40), f_q))
mstore(0x4b80, mulmod(mload(0x3460), mload(0x3460), f_q))
mstore(0x4ba0, mulmod(mload(0x4b80), mload(0x1de0), f_q))
mstore(0x4bc0, mulmod(mload(0x4ba0), 23990009175532390848383686641478884818239121606019298540653394434675622011304, f_q))
mstore(0x4be0, addmod(mload(0x4b60), mload(0x4bc0), f_q))
mstore(0x4c00, mulmod(mload(0x1e00), mload(0x1e00), f_q))
mstore(0x4c20, mulmod(mload(0x4c00), mload(0x4c00), f_q))
mstore(0x4c40, mulmod(mload(0x4c20), mload(0x1e00), f_q))
mstore(0x4c60, mulmod(mload(0x4c40), 23180151978504326669680984036118508621180775988903922469131210268215350444530, f_q))
mstore(0x4c80, addmod(mload(0x4be0), mload(0x4c60), f_q))
mstore(0x4ca0, mulmod(mload(0x1e20), mload(0x1e20), f_q))
mstore(0x4cc0, mulmod(mload(0x4ca0), mload(0x4ca0), f_q))
mstore(0x4ce0, mulmod(mload(0x4cc0), mload(0x1e20), f_q))
mstore(0x4d00, mulmod(mload(0x4ce0), 29479126442377740792305085857437384138015409209423896273007595542837761281189, f_q))
mstore(0x4d20, addmod(mload(0x4c80), mload(0x4d00), f_q))
mstore(0x4d40, mulmod(mload(0x1ea0), mload(0x1ea0), f_q))
mstore(0x4d60, mulmod(mload(0x4d40), mload(0x4d40), f_q))
mstore(0x4d80, mulmod(mload(0x4d60), mload(0x1ea0), f_q))
mstore(0x4da0, mulmod(mload(0x4d80), 37990615931907094420184937091556956528876595328335061740913699785965517240590, f_q))
mstore(0x4dc0, addmod(mload(0x4d20), mload(0x4da0), f_q))
mstore(0x4de0, mulmod(mload(0x1ec0), mload(0x1ec0), f_q))
mstore(0x4e00, mulmod(mload(0x4de0), mload(0x4de0), f_q))
mstore(0x4e20, mulmod(mload(0x4e00), mload(0x1ec0), f_q))
mstore(0x4e40, mulmod(mload(0x4e20), 3075540889646953729606836824147910283102396481803053667698778232583469493556, f_q))
mstore(0x4e60, addmod(mload(0x4dc0), mload(0x4e40), f_q))
mstore(0x4e80, mulmod(mload(0x1ee0), mload(0x1ee0), f_q))
mstore(0x4ea0, mulmod(mload(0x4e80), mload(0x4e80), f_q))
mstore(0x4ec0, mulmod(mload(0x4ea0), mload(0x1ee0), f_q))
mstore(0x4ee0, mulmod(mload(0x4ec0), 28505902463311974130913002774524928623644005505993681602486681565155683331521, f_q))
mstore(0x4f00, addmod(mload(0x4e60), mload(0x4ee0), f_q))
mstore(0x4f20, addmod(mload(0x3520), mload(0x4f00), f_q))
mstore(0x4f40, mulmod(mload(0x1980), mload(0x4f20), f_q))
mstore(0x4f60, mulmod(mload(0x1da0), 41216583078069907292136355165153270142521178992429414226155254333730607536733, f_q))
mstore(0x4f80, mulmod(mload(0x1dc0), 34853984525125276266590937240908152702715112008598809217765432339048892301352, f_q))
mstore(0x4fa0, addmod(mload(0x4f60), mload(0x4f80), f_q))
mstore(0x4fc0, mulmod(mload(0x4ba0), 17548561380688843065348281029305916198268522889382278651903462232179510668048, f_q))
mstore(0x4fe0, addmod(mload(0x4fa0), mload(0x4fc0), f_q))
mstore(0x5000, mulmod(mload(0x4c40), 22573484092096950280151461091492173066588738155952808584348937425179801521445, f_q))
mstore(0x5020, addmod(mload(0x4fe0), mload(0x5000), f_q))
mstore(0x5040, mulmod(mload(0x4ce0), 17799439645526593468527852005527707639891232191326421130080209212181800663685, f_q))
mstore(0x5060, addmod(mload(0x5020), mload(0x5040), f_q))
mstore(0x5080, mulmod(mload(0x4d80), 43072347715431875659722495403924484570295794297555905065846140476197612812033, f_q))
mstore(0x50a0, addmod(mload(0x5060), mload(0x5080), f_q))
mstore(0x50c0, mulmod(mload(0x4e20), 21762182386571606640672645248729054582240844218141454043565005480082460585677, f_q))
mstore(0x50e0, addmod(mload(0x50a0), mload(0x50c0), f_q))
mstore(0x5100, mulmod(mload(0x4ec0), 7179405695647424344643177657798954274869382720335107962712222495241823787551, f_q))
mstore(0x5120, addmod(mload(0x50e0), mload(0x5100), f_q))
mstore(0x5140, addmod(mload(0x36c0), mload(0x5120), f_q))
mstore(0x5160, addmod(mload(0x4f40), mload(0x5140), f_q))
mstore(0x5180, mulmod(mload(0x1980), mload(0x5160), f_q))
mstore(0x51a0, addmod(mload(0x2000), sub(f_q, mload(0x1e00)), f_q))
mstore(0x51c0, mulmod(mload(0x1da0), 42569072482279996318031820844820583094661593761988851871644829917446303682880, f_q))
mstore(0x51e0, mulmod(mload(0x1dc0), 48777675531739959342114240072267441286903816384223937749440830379544192657290, f_q))
mstore(0x5200, addmod(mload(0x51c0), mload(0x51e0), f_q))
mstore(0x5220, mulmod(mload(0x4ba0), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x5240, addmod(mload(0x5200), mload(0x5220), f_q))
mstore(0x5260, addmod(mload(0x51a0), mload(0x5240), f_q))
mstore(0x5280, addmod(mload(0x5180), mload(0x5260), f_q))
mstore(0x52a0, mulmod(mload(0x1980), mload(0x5280), f_q))
mstore(0x52c0, addmod(mload(0x2020), sub(f_q, mload(0x1e20)), f_q))
mstore(0x52e0, mulmod(mload(0x1da0), 15460822173785725787510766083057066620988948322919030231014542645107533362369, f_q))
mstore(0x5300, mulmod(mload(0x1dc0), 17532068198837287192548063441235938928456800450058734482970684092419295703441, f_q))
mstore(0x5320, addmod(mload(0x52e0), mload(0x5300), f_q))
mstore(0x5340, mulmod(mload(0x4ba0), 30536090514433970940206888994283604712174418989908022047600262784049007297138, f_q))
mstore(0x5360, addmod(mload(0x5320), mload(0x5340), f_q))
mstore(0x5380, mulmod(mload(0x4c40), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x53a0, addmod(mload(0x5360), mload(0x5380), f_q))
mstore(0x53c0, addmod(mload(0x52c0), mload(0x53a0), f_q))
mstore(0x53e0, addmod(mload(0x52a0), mload(0x53c0), f_q))
mstore(0x5400, mulmod(mload(0x1980), mload(0x53e0), f_q))
mstore(0x5420, addmod(mload(0x1f20), sub(f_q, mload(0x1ea0)), f_q))
mstore(0x5440, mulmod(mload(0x1da0), 51757916557095931492101637894700153753738985202877927051595743124655465049675, f_q))
mstore(0x5460, mulmod(mload(0x1dc0), 16513270875002105355154055214392863859886533828870466617169669632972895048992, f_q))
mstore(0x5480, addmod(mload(0x5440), mload(0x5460), f_q))
mstore(0x54a0, mulmod(mload(0x4ba0), 35426167520291240455001880880580845749581081201345737315527923196315309304361, f_q))
mstore(0x54c0, addmod(mload(0x5480), mload(0x54a0), f_q))
mstore(0x54e0, mulmod(mload(0x4c40), 30536090514433970940206888994283604712174418989908022047600262784049007297138, f_q))
mstore(0x5500, addmod(mload(0x54c0), mload(0x54e0), f_q))
mstore(0x5520, mulmod(mload(0x4ce0), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x5540, addmod(mload(0x5500), mload(0x5520), f_q))
mstore(0x5560, addmod(mload(0x5420), mload(0x5540), f_q))
mstore(0x5580, addmod(mload(0x5400), mload(0x5560), f_q))
mstore(0x55a0, mulmod(mload(0x1980), mload(0x5580), f_q))
mstore(0x55c0, addmod(mload(0x1f40), sub(f_q, mload(0x1ec0)), f_q))
mstore(0x55e0, mulmod(mload(0x1da0), 21416013269199706780655207523311618433421828314385182423308221541654338163111, f_q))
mstore(0x5600, mulmod(mload(0x1dc0), 16124966132388516597090803080166171234527932877010453966457664182846667286567, f_q))
mstore(0x5620, addmod(mload(0x55e0), mload(0x5600), f_q))
mstore(0x5640, mulmod(mload(0x4ba0), 11536991632578856038169226946888068627873692153441762213164802460898458963278, f_q))
mstore(0x5660, addmod(mload(0x5620), mload(0x5640), f_q))
mstore(0x5680, mulmod(mload(0x4c40), 35426167520291240455001880880580845749581081201345737315527923196315309304361, f_q))
mstore(0x56a0, addmod(mload(0x5660), mload(0x5680), f_q))
mstore(0x56c0, mulmod(mload(0x4ce0), 30536090514433970940206888994283604712174418989908022047600262784049007297138, f_q))
mstore(0x56e0, addmod(mload(0x56a0), mload(0x56c0), f_q))
mstore(0x5700, mulmod(mload(0x4d80), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x5720, addmod(mload(0x56e0), mload(0x5700), f_q))
mstore(0x5740, addmod(mload(0x55c0), mload(0x5720), f_q))
mstore(0x5760, addmod(mload(0x55a0), mload(0x5740), f_q))
mstore(0x5780, mulmod(mload(0x1980), mload(0x5760), f_q))
mstore(0x57a0, addmod(mload(0x1f60), sub(f_q, mload(0x1ee0)), f_q))
mstore(0x57c0, mulmod(mload(0x1da0), 49312067300773142348143637644007756944161175278464826357343119536320139437898, f_q))
mstore(0x57e0, mulmod(mload(0x1dc0), 18048464036633869753218556016152804134446546727997311594407968562256775743561, f_q))
mstore(0x5800, addmod(mload(0x57c0), mload(0x57e0), f_q))
mstore(0x5820, mulmod(mload(0x4ba0), 383932250696541742607310001569714138555014361290971921083431601725621863731, f_q))
mstore(0x5840, addmod(mload(0x5800), mload(0x5820), f_q))
mstore(0x5860, mulmod(mload(0x4c40), 11536991632578856038169226946888068627873692153441762213164802460898458963278, f_q))
mstore(0x5880, addmod(mload(0x5840), mload(0x5860), f_q))
mstore(0x58a0, mulmod(mload(0x4ce0), 35426167520291240455001880880580845749581081201345737315527923196315309304361, f_q))
mstore(0x58c0, addmod(mload(0x5880), mload(0x58a0), f_q))
mstore(0x58e0, mulmod(mload(0x4d80), 30536090514433970940206888994283604712174418989908022047600262784049007297138, f_q))
mstore(0x5900, addmod(mload(0x58c0), mload(0x58e0), f_q))
mstore(0x5920, mulmod(mload(0x4e20), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x5940, addmod(mload(0x5900), mload(0x5920), f_q))
mstore(0x5960, addmod(mload(0x57a0), mload(0x5940), f_q))
mstore(0x5980, addmod(mload(0x5780), mload(0x5960), f_q))
mstore(0x59a0, mulmod(mload(0x1980), mload(0x5980), f_q))
mstore(0x59c0, addmod(mload(0x1f80), sub(f_q, mload(0x1e80)), f_q))
mstore(0x59e0, mulmod(mload(0x1da0), 51042352737684322926421982719448027244098131173912330356286361328735472870963, f_q))
mstore(0x5a00, mulmod(mload(0x1dc0), 29390124884714250559401457937586375728515143848012653816777731013221302010465, f_q))
mstore(0x5a20, addmod(mload(0x59e0), mload(0x5a00), f_q))
mstore(0x5a40, mulmod(mload(0x4ba0), 14193443826180214291995136727309819104154361382389237431794542473275951615294, f_q))
mstore(0x5a60, addmod(mload(0x5a20), mload(0x5a40), f_q))
mstore(0x5a80, mulmod(mload(0x4c40), 383932250696541742607310001569714138555014361290971921083431601725621863731, f_q))
mstore(0x5aa0, addmod(mload(0x5a60), mload(0x5a80), f_q))
mstore(0x5ac0, mulmod(mload(0x4ce0), 11536991632578856038169226946888068627873692153441762213164802460898458963278, f_q))
mstore(0x5ae0, addmod(mload(0x5aa0), mload(0x5ac0), f_q))
mstore(0x5b00, mulmod(mload(0x4d80), 35426167520291240455001880880580845749581081201345737315527923196315309304361, f_q))
mstore(0x5b20, addmod(mload(0x5ae0), mload(0x5b00), f_q))
mstore(0x5b40, mulmod(mload(0x4e20), 30536090514433970940206888994283604712174418989908022047600262784049007297138, f_q))
mstore(0x5b60, addmod(mload(0x5b20), mload(0x5b40), f_q))
mstore(0x5b80, mulmod(mload(0x4ec0), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x5ba0, addmod(mload(0x5b60), mload(0x5b80), f_q))
mstore(0x5bc0, addmod(mload(0x59c0), mload(0x5ba0), f_q))
mstore(0x5be0, addmod(mload(0x59a0), mload(0x5bc0), f_q))
mstore(0x5c00, addmod(1, sub(f_q, mload(0x2140)), f_q))
mstore(0x5c20, mulmod(mload(0x2420), mload(0x5c00), f_q))
mstore(0x5c40, addmod(mload(0x5be0), sub(f_q, mload(0x5c20)), f_q))
mstore(0x5c60, addmod(mload(0x4b00), mload(0x5c40), f_q))
mstore(0x5ca0, 32)
mstore(0x5cc0, 32)
mstore(0x5ce0, 32)
mstore(0x5d00, mload(0x1d40))
mstore(0x5d20, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x5d40, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x5ca0, 0xc0, 0x5c80, 0x20), 1), success)
mstore(0x5d60, mulmod(mload(0x2860), mload(0x5c80), f_q))
mstore(0x5d80, mulmod(mload(0x5d60), mload(0x5d60), f_q))
mstore(0x5da0, mulmod(mload(0x5d80), mload(0x5d60), f_q))
mstore(0x5dc0, mulmod(mload(0x5da0), mload(0x5d60), f_q))
mstore(0x5de0, mulmod(1, mload(0x5d60), f_q))
mstore(0x5e00, mulmod(1, mload(0x5d80), f_q))
mstore(0x5e20, mulmod(1, mload(0x5da0), f_q))
mstore(0x5e40, mulmod(mload(0x5c60), mload(0x2880), f_q))
mstore(0x5e60, mulmod(mload(0x1d40), 1, f_q))
mstore(0x5e80, mulmod(mload(0x1d40), 31519469946562159605140591558550197856588417350474800936898404023113662197331, f_q))
mstore(0x5ea0, mulmod(mload(0x1d40), 21259823323969146045885553965890482219221908228759787200404479960115227367690, f_q))
mstore(0x5ec0, mulmod(mload(0x1d40), 45254319123522011116259460062854627366454101350769349111320208945036885998124, f_q))
mstore(0x5ee0, mulmod(mload(0x2460), mload(0x2460), f_q))
mstore(0x5f00, mulmod(mload(0x5ee0), mload(0x2460), f_q))
mstore(0x5f20, mulmod(mload(0x5f00), mload(0x2460), f_q))
mstore(0x5f40, mulmod(mload(0x5f20), mload(0x2460), f_q))
mstore(0x5f60, mulmod(mload(0x5f40), mload(0x2460), f_q))
mstore(0x5f80, mulmod(mload(0x5f60), mload(0x2460), f_q))
mstore(0x5fa0, mulmod(mload(0x5f80), mload(0x2460), f_q))
mstore(0x5fc0, mulmod(mload(0x5fa0), mload(0x2460), f_q))
mstore(0x5fe0, mulmod(mload(0x5fc0), mload(0x2460), f_q))
mstore(0x6000, mulmod(mload(0x5fe0), mload(0x2460), f_q))
mstore(0x6020, mulmod(mload(0x6000), mload(0x2460), f_q))
mstore(0x6040, mulmod(mload(0x6020), mload(0x2460), f_q))
mstore(0x6060, mulmod(mload(0x6040), mload(0x2460), f_q))
mstore(0x6080, mulmod(mload(0x6060), mload(0x2460), f_q))
mstore(0x60a0, mulmod(mload(0x6080), mload(0x2460), f_q))
mstore(0x60c0, mulmod(mload(0x60a0), mload(0x2460), f_q))
mstore(0x60e0, mulmod(mload(0x60c0), mload(0x2460), f_q))
mstore(0x6100, mulmod(mload(0x60e0), mload(0x2460), f_q))
mstore(0x6120, mulmod(mload(0x6100), mload(0x2460), f_q))
mstore(0x6140, mulmod(mload(0x6120), mload(0x2460), f_q))
mstore(0x6160, mulmod(mload(0x6140), mload(0x2460), f_q))
mstore(0x6180, mulmod(mload(0x6160), mload(0x2460), f_q))
mstore(0x61a0, mulmod(mload(0x6180), mload(0x2460), f_q))
mstore(0x61c0, mulmod(mload(0x61a0), mload(0x2460), f_q))
mstore(0x61e0, mulmod(mload(0x61c0), mload(0x2460), f_q))
mstore(0x6200, mulmod(mload(0x61e0), mload(0x2460), f_q))
mstore(0x6220, mulmod(mload(0x6200), mload(0x2460), f_q))
mstore(0x6240, mulmod(mload(0x6220), mload(0x2460), f_q))
mstore(0x6260, mulmod(mload(0x6240), mload(0x2460), f_q))
mstore(0x6280, mulmod(mload(0x6260), mload(0x2460), f_q))
mstore(0x62a0, mulmod(mload(0x6280), mload(0x2460), f_q))
mstore(0x62c0, mulmod(mload(0x62a0), mload(0x2460), f_q))
mstore(0x62e0, mulmod(mload(0x62c0), mload(0x2460), f_q))
mstore(0x6300, mulmod(mload(0x62e0), mload(0x2460), f_q))
mstore(0x6320, mulmod(mload(0x6300), mload(0x2460), f_q))
mstore(0x6340, mulmod(mload(0x6320), mload(0x2460), f_q))
mstore(0x6360, mulmod(1, mload(0x2460), f_q))
mstore(0x6380, mulmod(1, mload(0x5ee0), f_q))
mstore(0x63a0, mulmod(1, mload(0x5f00), f_q))
mstore(0x63c0, mulmod(1, mload(0x5f20), f_q))
mstore(0x63e0, mulmod(1, mload(0x5f40), f_q))
mstore(0x6400, mulmod(1, mload(0x5f60), f_q))
mstore(0x6420, mulmod(1, mload(0x5f80), f_q))
mstore(0x6440, mulmod(1, mload(0x5fa0), f_q))
mstore(0x6460, mulmod(1, mload(0x5fc0), f_q))
mstore(0x6480, mulmod(1, mload(0x5fe0), f_q))
mstore(0x64a0, mulmod(1, mload(0x6000), f_q))
mstore(0x64c0, mulmod(1, mload(0x6020), f_q))
mstore(0x64e0, mulmod(1, mload(0x6040), f_q))
mstore(0x6500, mulmod(1, mload(0x6060), f_q))
mstore(0x6520, mulmod(1, mload(0x6080), f_q))
mstore(0x6540, mulmod(1, mload(0x60a0), f_q))
mstore(0x6560, mulmod(1, mload(0x60c0), f_q))
mstore(0x6580, mulmod(1, mload(0x60e0), f_q))
mstore(0x65a0, mulmod(1, mload(0x6100), f_q))
mstore(0x65c0, mulmod(1, mload(0x6120), f_q))
mstore(0x65e0, mulmod(1, mload(0x6140), f_q))
mstore(0x6600, mulmod(1, mload(0x6160), f_q))
mstore(0x6620, mulmod(1, mload(0x6180), f_q))
mstore(0x6640, mulmod(1, mload(0x61a0), f_q))
mstore(0x6660, mulmod(1, mload(0x61c0), f_q))
mstore(0x6680, mulmod(1, mload(0x61e0), f_q))
mstore(0x66a0, mulmod(1, mload(0x6200), f_q))
mstore(0x66c0, mulmod(1, mload(0x6220), f_q))
mstore(0x66e0, mulmod(1, mload(0x6240), f_q))
mstore(0x6700, mulmod(1, mload(0x6260), f_q))
mstore(0x6720, mulmod(1, mload(0x6280), f_q))
mstore(0x6740, mulmod(1, mload(0x62a0), f_q))
mstore(0x6760, mulmod(1, mload(0x62c0), f_q))
mstore(0x6780, mulmod(1, mload(0x62e0), f_q))
mstore(0x67a0, mulmod(1, mload(0x6300), f_q))
mstore(0x67c0, mulmod(mload(0x5de0), mload(0x6300), f_q))
mstore(0x67e0, mulmod(mload(0x5e00), mload(0x6300), f_q))
mstore(0x6800, mulmod(mload(0x5e20), mload(0x6300), f_q))
mstore(0x6820, mulmod(1, mload(0x6320), f_q))
mstore(0x6840, mulmod(mload(0x1d80), 1, f_q))
mstore(0x6860, addmod(0, mload(0x6840), f_q))
mstore(0x6880, mulmod(mload(0x1e00), mload(0x2460), f_q))
mstore(0x68a0, addmod(mload(0x6860), mload(0x6880), f_q))
mstore(0x68c0, mulmod(mload(0x1e20), mload(0x5ee0), f_q))
mstore(0x68e0, addmod(mload(0x68a0), mload(0x68c0), f_q))
mstore(0x6900, mulmod(mload(0x1ea0), mload(0x5f00), f_q))
mstore(0x6920, addmod(mload(0x68e0), mload(0x6900), f_q))
mstore(0x6940, mulmod(mload(0x1ec0), mload(0x5f20), f_q))
mstore(0x6960, addmod(mload(0x6920), mload(0x6940), f_q))
mstore(0x6980, mulmod(mload(0x1ee0), mload(0x5f40), f_q))
mstore(0x69a0, addmod(mload(0x6960), mload(0x6980), f_q))
mstore(0x69c0, mulmod(mload(0x2400), mload(0x5f60), f_q))
mstore(0x69e0, addmod(mload(0x69a0), mload(0x69c0), f_q))
mstore(0x6a00, mulmod(mload(0x2420), mload(0x5f80), f_q))
mstore(0x6a20, addmod(mload(0x69e0), mload(0x6a00), f_q))
mstore(0x6a40, mulmod(mload(0x1f00), mload(0x5fa0), f_q))
mstore(0x6a60, addmod(mload(0x6a20), mload(0x6a40), f_q))
mstore(0x6a80, mulmod(mload(0x1f20), mload(0x5fc0), f_q))
mstore(0x6aa0, addmod(mload(0x6a60), mload(0x6a80), f_q))
mstore(0x6ac0, mulmod(mload(0x1f40), mload(0x5fe0), f_q))
mstore(0x6ae0, addmod(mload(0x6aa0), mload(0x6ac0), f_q))
mstore(0x6b00, mulmod(mload(0x1f60), mload(0x6000), f_q))
mstore(0x6b20, addmod(mload(0x6ae0), mload(0x6b00), f_q))
mstore(0x6b40, mulmod(mload(0x1f80), mload(0x6020), f_q))
mstore(0x6b60, addmod(mload(0x6b20), mload(0x6b40), f_q))
mstore(0x6b80, mulmod(mload(0x1fa0), mload(0x6040), f_q))
mstore(0x6ba0, addmod(mload(0x6b60), mload(0x6b80), f_q))
mstore(0x6bc0, mulmod(mload(0x1fc0), mload(0x6060), f_q))
mstore(0x6be0, addmod(mload(0x6ba0), mload(0x6bc0), f_q))
mstore(0x6c00, mulmod(mload(0x1fe0), mload(0x6080), f_q))
mstore(0x6c20, addmod(mload(0x6be0), mload(0x6c00), f_q))
mstore(0x6c40, mulmod(mload(0x2000), mload(0x60a0), f_q))
mstore(0x6c60, addmod(mload(0x6c20), mload(0x6c40), f_q))
mstore(0x6c80, mulmod(mload(0x2020), mload(0x60c0), f_q))
mstore(0x6ca0, addmod(mload(0x6c60), mload(0x6c80), f_q))
mstore(0x6cc0, mulmod(mload(0x2040), mload(0x60e0), f_q))
mstore(0x6ce0, addmod(mload(0x6ca0), mload(0x6cc0), f_q))
mstore(0x6d00, mulmod(mload(0x2060), mload(0x6100), f_q))
mstore(0x6d20, addmod(mload(0x6ce0), mload(0x6d00), f_q))
mstore(0x6d40, mulmod(mload(0x2080), mload(0x6120), f_q))
mstore(0x6d60, addmod(mload(0x6d20), mload(0x6d40), f_q))
mstore(0x6d80, mulmod(mload(0x20a0), mload(0x6140), f_q))
mstore(0x6da0, addmod(mload(0x6d60), mload(0x6d80), f_q))
mstore(0x6dc0, mulmod(mload(0x20c0), mload(0x6160), f_q))
mstore(0x6de0, addmod(mload(0x6da0), mload(0x6dc0), f_q))
mstore(0x6e00, mulmod(mload(0x20e0), mload(0x6180), f_q))
mstore(0x6e20, addmod(mload(0x6de0), mload(0x6e00), f_q))
mstore(0x6e40, mulmod(mload(0x2100), mload(0x61a0), f_q))
mstore(0x6e60, addmod(mload(0x6e20), mload(0x6e40), f_q))
mstore(0x6e80, mulmod(mload(0x2120), mload(0x61c0), f_q))
mstore(0x6ea0, addmod(mload(0x6e60), mload(0x6e80), f_q))
mstore(0x6ec0, mulmod(mload(0x2140), mload(0x61e0), f_q))
mstore(0x6ee0, addmod(mload(0x6ea0), mload(0x6ec0), f_q))
mstore(0x6f00, mulmod(mload(0x2180), mload(0x6200), f_q))
mstore(0x6f20, addmod(mload(0x6ee0), mload(0x6f00), f_q))
mstore(0x6f40, mulmod(mload(0x21a0), mload(0x6220), f_q))
mstore(0x6f60, addmod(mload(0x6f20), mload(0x6f40), f_q))
mstore(0x6f80, mulmod(mload(0x21c0), mload(0x6240), f_q))
mstore(0x6fa0, addmod(mload(0x6f60), mload(0x6f80), f_q))
mstore(0x6fc0, mulmod(mload(0x21e0), mload(0x6260), f_q))
mstore(0x6fe0, addmod(mload(0x6fa0), mload(0x6fc0), f_q))
mstore(0x7000, mulmod(mload(0x2200), mload(0x6280), f_q))
mstore(0x7020, addmod(mload(0x6fe0), mload(0x7000), f_q))
mstore(0x7040, mulmod(mload(0x2220), mload(0x62a0), f_q))
mstore(0x7060, addmod(mload(0x7020), mload(0x7040), f_q))
mstore(0x7080, mulmod(mload(0x2240), mload(0x62c0), f_q))
mstore(0x70a0, addmod(mload(0x7060), mload(0x7080), f_q))
mstore(0x70c0, mulmod(mload(0x2260), mload(0x62e0), f_q))
mstore(0x70e0, addmod(mload(0x70a0), mload(0x70c0), f_q))
mstore(0x7100, mulmod(mload(0x5e40), mload(0x6300), f_q))
mstore(0x7120, addmod(mload(0x70e0), mload(0x7100), f_q))
mstore(0x7140, mulmod(mload(0x2160), mload(0x6320), f_q))
mstore(0x7160, addmod(mload(0x7120), mload(0x7140), f_q))
mstore(0x7180, mulmod(mload(0x1da0), 1, f_q))
mstore(0x71a0, addmod(0, mload(0x7180), f_q))
mstore(0x71c0, mulmod(mload(0x1e40), 1, f_q))
mstore(0x71e0, addmod(0, mload(0x71c0), f_q))
mstore(0x7200, mulmod(mload(0x1dc0), mload(0x2460), f_q))
mstore(0x7220, addmod(mload(0x71a0), mload(0x7200), f_q))
mstore(0x7240, mulmod(mload(0x1e60), mload(0x2460), f_q))
mstore(0x7260, addmod(mload(0x71e0), mload(0x7240), f_q))
mstore(0x7280, mulmod(mload(0x1de0), mload(0x5ee0), f_q))
mstore(0x72a0, addmod(mload(0x7220), mload(0x7280), f_q))
mstore(0x72c0, mulmod(mload(0x1e80), mload(0x5ee0), f_q))
mstore(0x72e0, addmod(mload(0x7260), mload(0x72c0), f_q))
mstore(0x7300, mulmod(mload(0x2340), mload(0x5f00), f_q))
mstore(0x7320, addmod(mload(0x72a0), mload(0x7300), f_q))
mstore(0x7340, mulmod(mload(0x2360), mload(0x5f00), f_q))
mstore(0x7360, addmod(mload(0x72e0), mload(0x7340), f_q))
mstore(0x7380, mulmod(mload(0x2380), mload(0x5f20), f_q))
mstore(0x73a0, addmod(mload(0x7320), mload(0x7380), f_q))
mstore(0x73c0, mulmod(mload(0x23a0), mload(0x5f20), f_q))
mstore(0x73e0, addmod(mload(0x7360), mload(0x73c0), f_q))
mstore(0x7400, mulmod(mload(0x2280), 1, f_q))
mstore(0x7420, addmod(0, mload(0x7400), f_q))
mstore(0x7440, mulmod(mload(0x22a0), 1, f_q))
mstore(0x7460, addmod(0, mload(0x7440), f_q))
mstore(0x7480, mulmod(mload(0x22c0), 1, f_q))
mstore(0x74a0, addmod(0, mload(0x7480), f_q))
mstore(0x74c0, mulmod(mload(0x22e0), mload(0x2460), f_q))
mstore(0x74e0, addmod(mload(0x7420), mload(0x74c0), f_q))
mstore(0x7500, mulmod(mload(0x2300), mload(0x2460), f_q))
mstore(0x7520, addmod(mload(0x7460), mload(0x7500), f_q))
mstore(0x7540, mulmod(mload(0x2320), mload(0x2460), f_q))
mstore(0x7560, addmod(mload(0x74a0), mload(0x7540), f_q))
mstore(0x7580, mulmod(mload(0x23c0), 1, f_q))
mstore(0x75a0, addmod(0, mload(0x7580), f_q))
mstore(0x75c0, mulmod(mload(0x23e0), 1, f_q))
mstore(0x75e0, addmod(0, mload(0x75c0), f_q))
mstore(0x7600, addmod(mload(0x5e60), sub(f_q, mload(0x5ec0)), f_q))
mstore(0x7620, mulmod(1, mload(0x7600), f_q))
mstore(0x7640, addmod(mload(0x5ec0), sub(f_q, mload(0x5e60)), f_q))
mstore(0x7660, mulmod(1, mload(0x7640), f_q))
{
            let prod := mload(0x7620)

                prod := mulmod(mload(0x7660), prod, f_q)
                mstore(0x7680, prod)
            
        }
mstore(0x76c0, 32)
mstore(0x76e0, 32)
mstore(0x7700, 32)
mstore(0x7720, mload(0x7680))
mstore(0x7740, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x7760, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x76c0, 0xc0, 0x76a0, 0x20), 1), success)
{
            
            let inv := mload(0x76a0)
            let v
        
                    v := mload(0x7660)
                    mstore(30304, mulmod(mload(0x7620), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                mstore(0x7620, inv)

        }
mstore(0x7780, addmod(mload(0x25a0), sub(f_q, mload(0x5ec0)), f_q))
mstore(0x77a0, mulmod(1, mload(0x7780), f_q))
mstore(0x77c0, mulmod(mload(0x75a0), mload(0x77a0), f_q))
mstore(0x77e0, mulmod(mload(0x77c0), mload(0x7620), f_q))
mstore(0x7800, addmod(0, mload(0x77e0), f_q))
mstore(0x7820, addmod(mload(0x25a0), sub(f_q, mload(0x5e60)), f_q))
mstore(0x7840, mulmod(1, mload(0x7820), f_q))
mstore(0x7860, mulmod(mload(0x75e0), mload(0x7840), f_q))
mstore(0x7880, mulmod(mload(0x7860), mload(0x7660), f_q))
mstore(0x78a0, addmod(mload(0x7800), mload(0x7880), f_q))
mstore(0x78c0, mulmod(mload(0x7840), mload(0x7780), f_q))
mstore(0x7900, 32)
mstore(0x7920, 32)
mstore(0x7940, 32)
mstore(0x7960, mload(0x78c0))
mstore(0x7980, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x79a0, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x7900, 0xc0, 0x78e0, 0x20), 1), success)
mstore(0x79c0, addmod(mload(0x2640), sub(f_q, mload(0x78a0)), f_q))
mstore(0x79e0, mulmod(mload(0x79c0), mload(0x78e0), f_q))
mstore(0x7a00, mulmod(0, mload(0x24c0), f_q))
mstore(0x7a20, addmod(mload(0x7a00), mload(0x79e0), f_q))
mstore(0x7a40, addmod(mload(0x5e60), sub(f_q, mload(0x5e80)), f_q))
mstore(0x7a60, mulmod(1, mload(0x7a40), f_q))
mstore(0x7a80, addmod(mload(0x5e60), sub(f_q, mload(0x5ea0)), f_q))
mstore(0x7aa0, mulmod(mload(0x7a60), mload(0x7a80), f_q))
mstore(0x7ac0, addmod(mload(0x5e80), sub(f_q, mload(0x5e60)), f_q))
mstore(0x7ae0, mulmod(1, mload(0x7ac0), f_q))
mstore(0x7b00, addmod(mload(0x5e80), sub(f_q, mload(0x5ea0)), f_q))
mstore(0x7b20, mulmod(mload(0x7ae0), mload(0x7b00), f_q))
mstore(0x7b40, addmod(mload(0x5ea0), sub(f_q, mload(0x5e60)), f_q))
mstore(0x7b60, mulmod(1, mload(0x7b40), f_q))
mstore(0x7b80, addmod(mload(0x5ea0), sub(f_q, mload(0x5e80)), f_q))
mstore(0x7ba0, mulmod(mload(0x7b60), mload(0x7b80), f_q))
{
            let prod := mload(0x7aa0)

                prod := mulmod(mload(0x7b20), prod, f_q)
                mstore(0x7bc0, prod)
            
                prod := mulmod(mload(0x7ba0), prod, f_q)
                mstore(0x7be0, prod)
            
        }
mstore(0x7c20, 32)
mstore(0x7c40, 32)
mstore(0x7c60, 32)
mstore(0x7c80, mload(0x7be0))
mstore(0x7ca0, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x7cc0, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x7c20, 0xc0, 0x7c00, 0x20), 1), success)
{
            
            let inv := mload(0x7c00)
            let v
        
                    v := mload(0x7ba0)
                    mstore(31648, mulmod(mload(0x7bc0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x7b20)
                    mstore(31520, mulmod(mload(0x7aa0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                mstore(0x7aa0, inv)

        }
mstore(0x7ce0, addmod(mload(0x25a0), sub(f_q, mload(0x5e80)), f_q))
mstore(0x7d00, mulmod(1, mload(0x7ce0), f_q))
mstore(0x7d20, addmod(mload(0x25a0), sub(f_q, mload(0x5ea0)), f_q))
mstore(0x7d40, mulmod(mload(0x7d00), mload(0x7d20), f_q))
mstore(0x7d60, mulmod(mload(0x74e0), mload(0x7d40), f_q))
mstore(0x7d80, mulmod(mload(0x7d60), mload(0x7aa0), f_q))
mstore(0x7da0, addmod(0, mload(0x7d80), f_q))
mstore(0x7dc0, mulmod(mload(0x7840), mload(0x7d20), f_q))
mstore(0x7de0, mulmod(mload(0x7520), mload(0x7dc0), f_q))
mstore(0x7e00, mulmod(mload(0x7de0), mload(0x7b20), f_q))
mstore(0x7e20, addmod(mload(0x7da0), mload(0x7e00), f_q))
mstore(0x7e40, mulmod(mload(0x7840), mload(0x7ce0), f_q))
mstore(0x7e60, mulmod(mload(0x7560), mload(0x7e40), f_q))
mstore(0x7e80, mulmod(mload(0x7e60), mload(0x7ba0), f_q))
mstore(0x7ea0, addmod(mload(0x7e20), mload(0x7e80), f_q))
mstore(0x7ec0, mulmod(mload(0x7e40), mload(0x7d20), f_q))
mstore(0x7f00, 32)
mstore(0x7f20, 32)
mstore(0x7f40, 32)
mstore(0x7f60, mload(0x7ec0))
mstore(0x7f80, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x7fa0, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x7f00, 0xc0, 0x7ee0, 0x20), 1), success)
mstore(0x7fc0, addmod(mload(0x2620), sub(f_q, mload(0x7ea0)), f_q))
mstore(0x7fe0, mulmod(mload(0x7fc0), mload(0x7ee0), f_q))
mstore(0x8000, mulmod(mload(0x7a20), mload(0x24c0), f_q))
mstore(0x8020, addmod(mload(0x8000), mload(0x7fe0), f_q))
{
            let prod := mload(0x7a60)

                prod := mulmod(mload(0x7ae0), prod, f_q)
                mstore(0x8040, prod)
            
        }
mstore(0x8080, 32)
mstore(0x80a0, 32)
mstore(0x80c0, 32)
mstore(0x80e0, mload(0x8040))
mstore(0x8100, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x8120, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x8080, 0xc0, 0x8060, 0x20), 1), success)
{
            
            let inv := mload(0x8060)
            let v
        
                    v := mload(0x7ae0)
                    mstore(31456, mulmod(mload(0x7a60), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                mstore(0x7a60, inv)

        }
mstore(0x8140, mulmod(mload(0x73a0), mload(0x7d00), f_q))
mstore(0x8160, mulmod(mload(0x8140), mload(0x7a60), f_q))
mstore(0x8180, addmod(0, mload(0x8160), f_q))
mstore(0x81a0, mulmod(mload(0x73e0), mload(0x7840), f_q))
mstore(0x81c0, mulmod(mload(0x81a0), mload(0x7ae0), f_q))
mstore(0x81e0, addmod(mload(0x8180), mload(0x81c0), f_q))
mstore(0x8220, 32)
mstore(0x8240, 32)
mstore(0x8260, 32)
mstore(0x8280, mload(0x7e40))
mstore(0x82a0, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x82c0, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x8220, 0xc0, 0x8200, 0x20), 1), success)
mstore(0x82e0, addmod(mload(0x2600), sub(f_q, mload(0x81e0)), f_q))
mstore(0x8300, mulmod(mload(0x82e0), mload(0x8200), f_q))
mstore(0x8320, mulmod(mload(0x8020), mload(0x24c0), f_q))
mstore(0x8340, addmod(mload(0x8320), mload(0x8300), f_q))
mstore(0x8380, 32)
mstore(0x83a0, 32)
mstore(0x83c0, 32)
mstore(0x83e0, mload(0x7840))
mstore(0x8400, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x8420, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x8380, 0xc0, 0x8360, 0x20), 1), success)
mstore(0x8440, addmod(mload(0x25e0), sub(f_q, mload(0x7160)), f_q))
mstore(0x8460, mulmod(mload(0x8440), mload(0x8360), f_q))
mstore(0x8480, mulmod(mload(0x8340), mload(0x24c0), f_q))
mstore(0x84a0, addmod(mload(0x8480), mload(0x8460), f_q))
mstore(0x84c0, mulmod(mload(0x2680), mload(0x2680), f_q))
mstore(0x84e0, mulmod(mload(0x84c0), mload(0x2680), f_q))
mstore(0x8500, mulmod(mload(0x84e0), mload(0x2680), f_q))
mstore(0x8520, mulmod(mload(0x8500), mload(0x2680), f_q))
mstore(0x8540, mulmod(mload(0x6360), 1, f_q))
mstore(0x8560, mulmod(mload(0x6380), 1, f_q))
mstore(0x8580, mulmod(mload(0x63a0), 1, f_q))
mstore(0x85a0, mulmod(mload(0x63c0), 1, f_q))
mstore(0x85c0, mulmod(mload(0x63e0), 1, f_q))
mstore(0x85e0, mulmod(mload(0x6400), 1, f_q))
mstore(0x8600, mulmod(mload(0x6420), 1, f_q))
mstore(0x8620, mulmod(mload(0x6440), 1, f_q))
mstore(0x8640, mulmod(mload(0x6460), 1, f_q))
mstore(0x8660, mulmod(mload(0x6480), 1, f_q))
mstore(0x8680, mulmod(mload(0x64a0), 1, f_q))
mstore(0x86a0, mulmod(mload(0x64c0), 1, f_q))
mstore(0x86c0, mulmod(mload(0x64e0), 1, f_q))
mstore(0x86e0, mulmod(mload(0x6500), 1, f_q))
mstore(0x8700, mulmod(mload(0x6520), 1, f_q))
mstore(0x8720, mulmod(mload(0x6540), 1, f_q))
mstore(0x8740, mulmod(mload(0x6560), 1, f_q))
mstore(0x8760, mulmod(mload(0x6580), 1, f_q))
mstore(0x8780, mulmod(mload(0x65a0), 1, f_q))
mstore(0x87a0, mulmod(mload(0x65c0), 1, f_q))
mstore(0x87c0, mulmod(mload(0x65e0), 1, f_q))
mstore(0x87e0, mulmod(mload(0x6600), 1, f_q))
mstore(0x8800, mulmod(mload(0x6620), 1, f_q))
mstore(0x8820, mulmod(mload(0x6640), 1, f_q))
mstore(0x8840, mulmod(mload(0x6660), 1, f_q))
mstore(0x8860, mulmod(mload(0x6680), 1, f_q))
mstore(0x8880, mulmod(mload(0x66a0), 1, f_q))
mstore(0x88a0, mulmod(mload(0x66c0), 1, f_q))
mstore(0x88c0, mulmod(mload(0x66e0), 1, f_q))
mstore(0x88e0, mulmod(mload(0x6700), 1, f_q))
mstore(0x8900, mulmod(mload(0x6720), 1, f_q))
mstore(0x8920, mulmod(mload(0x6740), 1, f_q))
mstore(0x8940, mulmod(mload(0x6760), 1, f_q))
mstore(0x8960, mulmod(mload(0x6780), 1, f_q))
mstore(0x8980, mulmod(mload(0x67a0), 1, f_q))
mstore(0x89a0, mulmod(mload(0x67c0), 1, f_q))
mstore(0x89c0, mulmod(mload(0x67e0), 1, f_q))
mstore(0x89e0, mulmod(mload(0x6800), 1, f_q))
mstore(0x8a00, mulmod(mload(0x6820), 1, f_q))
mstore(0x8a20, mulmod(1, mload(0x2680), f_q))
mstore(0x8a40, mulmod(mload(0x6360), mload(0x2680), f_q))
mstore(0x8a60, mulmod(mload(0x6380), mload(0x2680), f_q))
mstore(0x8a80, mulmod(mload(0x63a0), mload(0x2680), f_q))
mstore(0x8aa0, mulmod(mload(0x63c0), mload(0x2680), f_q))
mstore(0x8ac0, mulmod(1, mload(0x84c0), f_q))
mstore(0x8ae0, mulmod(mload(0x6360), mload(0x84c0), f_q))
mstore(0x8b00, mulmod(1, mload(0x84e0), f_q))
mstore(0x8b20, mulmod(1, mload(0x8500), f_q))
mstore(0x8b40, mulmod(mload(0x25e0), 1, f_q))
mstore(0x8b60, addmod(0, mload(0x8b40), f_q))
mstore(0x8b80, mulmod(mload(0x2600), mload(0x2680), f_q))
mstore(0x8ba0, addmod(mload(0x8b60), mload(0x8b80), f_q))
mstore(0x8bc0, mulmod(mload(0x2620), mload(0x84c0), f_q))
mstore(0x8be0, addmod(mload(0x8ba0), mload(0x8bc0), f_q))
mstore(0x8c00, mulmod(mload(0x2640), mload(0x84e0), f_q))
mstore(0x8c20, addmod(mload(0x8be0), mload(0x8c00), f_q))
mstore(0x8c40, mulmod(mload(0x84a0), mload(0x8500), f_q))
mstore(0x8c60, addmod(mload(0x8c20), mload(0x8c40), f_q))
mstore(0x8c80, mulmod(1, mload(0x25a0), f_q))

        {
            mstore(0x8ca0, 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
            mstore(0x8cc0, 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
            mstore(0x8ce0, 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(0x8d00, 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
        }
{
                    mstore(0x8d20, mload(0x8ca0))
mstore(0x8d40, mload(0x8cc0))
mstore(0x8d60, mload(0x8ce0))
mstore(0x8d80, mload(0x8d00))
                }
mstore(0x8da0, sub(f_q, mload(0x8c60)))

        {
            let scalar := mload(0x8da0)
            let is_inf := and(
                and(eq(mload(0x8d20), 0), eq(mload(0x8d40), 0)),
                and(eq(mload(0x8d60), 0), eq(mload(0x8d80), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x8d20, 0)
                mstore(0x8d40, 0)
                mstore(0x8d60, 0)
                mstore(0x8d80, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x8d20, 0xa0, 0x8d20, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x8dc0, mload(0x8d20))
mstore(0x8de0, mload(0x8d40))
mstore(0x8e00, mload(0x8d60))
mstore(0x8e20, mload(0x8d80))
                }
{
                    mstore(0x8e40, mload(0xfc0))
mstore(0x8e60, mload(0xfe0))
mstore(0x8e80, mload(0x1000))
mstore(0x8ea0, mload(0x1020))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x8dc0), 0), eq(mload(0x8de0), 0)),
                and(eq(mload(0x8e00), 0), eq(mload(0x8e20), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x8e40), 0), eq(mload(0x8e60), 0)),
                and(eq(mload(0x8e80), 0), eq(mload(0x8ea0), 0))
            )
            if lhs_inf {
                mstore(0x8dc0, mload(0x8e40))
                mstore(0x8de0, mload(0x8e60))
                mstore(0x8e00, mload(0x8e80))
                mstore(0x8e20, mload(0x8ea0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x8dc0, 0x100, 0x8dc0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x8ec0, mload(0x12c0))
mstore(0x8ee0, mload(0x12e0))
mstore(0x8f00, mload(0x1300))
mstore(0x8f20, mload(0x1320))
                }
mstore(0x8f40, mload(0x8540))

        {
            let scalar := mload(0x8f40)
            let is_inf := and(
                and(eq(mload(0x8ec0), 0), eq(mload(0x8ee0), 0)),
                and(eq(mload(0x8f00), 0), eq(mload(0x8f20), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x8ec0, 0)
                mstore(0x8ee0, 0)
                mstore(0x8f00, 0)
                mstore(0x8f20, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x8ec0, 0xa0, 0x8ec0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x8f60, mload(0x8dc0))
mstore(0x8f80, mload(0x8de0))
mstore(0x8fa0, mload(0x8e00))
mstore(0x8fc0, mload(0x8e20))
                }
{
                    mstore(0x8fe0, mload(0x8ec0))
mstore(0x9000, mload(0x8ee0))
mstore(0x9020, mload(0x8f00))
mstore(0x9040, mload(0x8f20))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x8f60), 0), eq(mload(0x8f80), 0)),
                and(eq(mload(0x8fa0), 0), eq(mload(0x8fc0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x8fe0), 0), eq(mload(0x9000), 0)),
                and(eq(mload(0x9020), 0), eq(mload(0x9040), 0))
            )
            if lhs_inf {
                mstore(0x8f60, mload(0x8fe0))
                mstore(0x8f80, mload(0x9000))
                mstore(0x8fa0, mload(0x9020))
                mstore(0x8fc0, mload(0x9040))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x8f60, 0x100, 0x8f60, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9060, mload(0x1340))
mstore(0x9080, mload(0x1360))
mstore(0x90a0, mload(0x1380))
mstore(0x90c0, mload(0x13a0))
                }
mstore(0x90e0, mload(0x8560))

        {
            let scalar := mload(0x90e0)
            let is_inf := and(
                and(eq(mload(0x9060), 0), eq(mload(0x9080), 0)),
                and(eq(mload(0x90a0), 0), eq(mload(0x90c0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x9060, 0)
                mstore(0x9080, 0)
                mstore(0x90a0, 0)
                mstore(0x90c0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x9060, 0xa0, 0x9060, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9100, mload(0x8f60))
mstore(0x9120, mload(0x8f80))
mstore(0x9140, mload(0x8fa0))
mstore(0x9160, mload(0x8fc0))
                }
{
                    mstore(0x9180, mload(0x9060))
mstore(0x91a0, mload(0x9080))
mstore(0x91c0, mload(0x90a0))
mstore(0x91e0, mload(0x90c0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x9100), 0), eq(mload(0x9120), 0)),
                and(eq(mload(0x9140), 0), eq(mload(0x9160), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x9180), 0), eq(mload(0x91a0), 0)),
                and(eq(mload(0x91c0), 0), eq(mload(0x91e0), 0))
            )
            if lhs_inf {
                mstore(0x9100, mload(0x9180))
                mstore(0x9120, mload(0x91a0))
                mstore(0x9140, mload(0x91c0))
                mstore(0x9160, mload(0x91e0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x9100, 0x100, 0x9100, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9200, mload(0x13c0))
mstore(0x9220, mload(0x13e0))
mstore(0x9240, mload(0x1400))
mstore(0x9260, mload(0x1420))
                }
mstore(0x9280, mload(0x8580))

        {
            let scalar := mload(0x9280)
            let is_inf := and(
                and(eq(mload(0x9200), 0), eq(mload(0x9220), 0)),
                and(eq(mload(0x9240), 0), eq(mload(0x9260), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x9200, 0)
                mstore(0x9220, 0)
                mstore(0x9240, 0)
                mstore(0x9260, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x9200, 0xa0, 0x9200, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x92a0, mload(0x9100))
mstore(0x92c0, mload(0x9120))
mstore(0x92e0, mload(0x9140))
mstore(0x9300, mload(0x9160))
                }
{
                    mstore(0x9320, mload(0x9200))
mstore(0x9340, mload(0x9220))
mstore(0x9360, mload(0x9240))
mstore(0x9380, mload(0x9260))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x92a0), 0), eq(mload(0x92c0), 0)),
                and(eq(mload(0x92e0), 0), eq(mload(0x9300), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x9320), 0), eq(mload(0x9340), 0)),
                and(eq(mload(0x9360), 0), eq(mload(0x9380), 0))
            )
            if lhs_inf {
                mstore(0x92a0, mload(0x9320))
                mstore(0x92c0, mload(0x9340))
                mstore(0x92e0, mload(0x9360))
                mstore(0x9300, mload(0x9380))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x92a0, 0x100, 0x92a0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x93a0, mload(0x1440))
mstore(0x93c0, mload(0x1460))
mstore(0x93e0, mload(0x1480))
mstore(0x9400, mload(0x14a0))
                }
mstore(0x9420, mload(0x85a0))

        {
            let scalar := mload(0x9420)
            let is_inf := and(
                and(eq(mload(0x93a0), 0), eq(mload(0x93c0), 0)),
                and(eq(mload(0x93e0), 0), eq(mload(0x9400), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x93a0, 0)
                mstore(0x93c0, 0)
                mstore(0x93e0, 0)
                mstore(0x9400, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x93a0, 0xa0, 0x93a0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9440, mload(0x92a0))
mstore(0x9460, mload(0x92c0))
mstore(0x9480, mload(0x92e0))
mstore(0x94a0, mload(0x9300))
                }
{
                    mstore(0x94c0, mload(0x93a0))
mstore(0x94e0, mload(0x93c0))
mstore(0x9500, mload(0x93e0))
mstore(0x9520, mload(0x9400))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x9440), 0), eq(mload(0x9460), 0)),
                and(eq(mload(0x9480), 0), eq(mload(0x94a0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x94c0), 0), eq(mload(0x94e0), 0)),
                and(eq(mload(0x9500), 0), eq(mload(0x9520), 0))
            )
            if lhs_inf {
                mstore(0x9440, mload(0x94c0))
                mstore(0x9460, mload(0x94e0))
                mstore(0x9480, mload(0x9500))
                mstore(0x94a0, mload(0x9520))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x9440, 0x100, 0x9440, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9540, mload(0x14c0))
mstore(0x9560, mload(0x14e0))
mstore(0x9580, mload(0x1500))
mstore(0x95a0, mload(0x1520))
                }
mstore(0x95c0, mload(0x85c0))

        {
            let scalar := mload(0x95c0)
            let is_inf := and(
                and(eq(mload(0x9540), 0), eq(mload(0x9560), 0)),
                and(eq(mload(0x9580), 0), eq(mload(0x95a0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x9540, 0)
                mstore(0x9560, 0)
                mstore(0x9580, 0)
                mstore(0x95a0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x9540, 0xa0, 0x9540, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x95e0, mload(0x9440))
mstore(0x9600, mload(0x9460))
mstore(0x9620, mload(0x9480))
mstore(0x9640, mload(0x94a0))
                }
{
                    mstore(0x9660, mload(0x9540))
mstore(0x9680, mload(0x9560))
mstore(0x96a0, mload(0x9580))
mstore(0x96c0, mload(0x95a0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x95e0), 0), eq(mload(0x9600), 0)),
                and(eq(mload(0x9620), 0), eq(mload(0x9640), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x9660), 0), eq(mload(0x9680), 0)),
                and(eq(mload(0x96a0), 0), eq(mload(0x96c0), 0))
            )
            if lhs_inf {
                mstore(0x95e0, mload(0x9660))
                mstore(0x9600, mload(0x9680))
                mstore(0x9620, mload(0x96a0))
                mstore(0x9640, mload(0x96c0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x95e0, 0x100, 0x95e0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x96e0, mload(0x1620))
mstore(0x9700, mload(0x1640))
mstore(0x9720, mload(0x1660))
mstore(0x9740, mload(0x1680))
                }
mstore(0x9760, mload(0x85e0))

        {
            let scalar := mload(0x9760)
            let is_inf := and(
                and(eq(mload(0x96e0), 0), eq(mload(0x9700), 0)),
                and(eq(mload(0x9720), 0), eq(mload(0x9740), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x96e0, 0)
                mstore(0x9700, 0)
                mstore(0x9720, 0)
                mstore(0x9740, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x96e0, 0xa0, 0x96e0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9780, mload(0x95e0))
mstore(0x97a0, mload(0x9600))
mstore(0x97c0, mload(0x9620))
mstore(0x97e0, mload(0x9640))
                }
{
                    mstore(0x9800, mload(0x96e0))
mstore(0x9820, mload(0x9700))
mstore(0x9840, mload(0x9720))
mstore(0x9860, mload(0x9740))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x9780), 0), eq(mload(0x97a0), 0)),
                and(eq(mload(0x97c0), 0), eq(mload(0x97e0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x9800), 0), eq(mload(0x9820), 0)),
                and(eq(mload(0x9840), 0), eq(mload(0x9860), 0))
            )
            if lhs_inf {
                mstore(0x9780, mload(0x9800))
                mstore(0x97a0, mload(0x9820))
                mstore(0x97c0, mload(0x9840))
                mstore(0x97e0, mload(0x9860))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x9780, 0x100, 0x9780, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9880, mload(0x19c0))
mstore(0x98a0, mload(0x19e0))
mstore(0x98c0, mload(0x1a00))
mstore(0x98e0, mload(0x1a20))
                }
mstore(0x9900, mload(0x8600))

        {
            let scalar := mload(0x9900)
            let is_inf := and(
                and(eq(mload(0x9880), 0), eq(mload(0x98a0), 0)),
                and(eq(mload(0x98c0), 0), eq(mload(0x98e0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x9880, 0)
                mstore(0x98a0, 0)
                mstore(0x98c0, 0)
                mstore(0x98e0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x9880, 0xa0, 0x9880, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9920, mload(0x9780))
mstore(0x9940, mload(0x97a0))
mstore(0x9960, mload(0x97c0))
mstore(0x9980, mload(0x97e0))
                }
{
                    mstore(0x99a0, mload(0x9880))
mstore(0x99c0, mload(0x98a0))
mstore(0x99e0, mload(0x98c0))
mstore(0x9a00, mload(0x98e0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x9920), 0), eq(mload(0x9940), 0)),
                and(eq(mload(0x9960), 0), eq(mload(0x9980), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x99a0), 0), eq(mload(0x99c0), 0)),
                and(eq(mload(0x99e0), 0), eq(mload(0x9a00), 0))
            )
            if lhs_inf {
                mstore(0x9920, mload(0x99a0))
                mstore(0x9940, mload(0x99c0))
                mstore(0x9960, mload(0x99e0))
                mstore(0x9980, mload(0x9a00))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x9920, 0x100, 0x9920, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9a20, mload(0x6a0))
mstore(0x9a40, mload(0x6c0))
mstore(0x9a60, mload(0x6e0))
mstore(0x9a80, mload(0x700))
                }
mstore(0x9aa0, mload(0x8620))

        {
            let scalar := mload(0x9aa0)
            let is_inf := and(
                and(eq(mload(0x9a20), 0), eq(mload(0x9a40), 0)),
                and(eq(mload(0x9a60), 0), eq(mload(0x9a80), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x9a20, 0)
                mstore(0x9a40, 0)
                mstore(0x9a60, 0)
                mstore(0x9a80, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x9a20, 0xa0, 0x9a20, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9ac0, mload(0x9920))
mstore(0x9ae0, mload(0x9940))
mstore(0x9b00, mload(0x9960))
mstore(0x9b20, mload(0x9980))
                }
{
                    mstore(0x9b40, mload(0x9a20))
mstore(0x9b60, mload(0x9a40))
mstore(0x9b80, mload(0x9a60))
mstore(0x9ba0, mload(0x9a80))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x9ac0), 0), eq(mload(0x9ae0), 0)),
                and(eq(mload(0x9b00), 0), eq(mload(0x9b20), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x9b40), 0), eq(mload(0x9b60), 0)),
                and(eq(mload(0x9b80), 0), eq(mload(0x9ba0), 0))
            )
            if lhs_inf {
                mstore(0x9ac0, mload(0x9b40))
                mstore(0x9ae0, mload(0x9b60))
                mstore(0x9b00, mload(0x9b80))
                mstore(0x9b20, mload(0x9ba0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x9ac0, 0x100, 0x9ac0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9bc0, mload(0x420))
mstore(0x9be0, mload(0x440))
mstore(0x9c00, mload(0x460))
mstore(0x9c20, mload(0x480))
                }
mstore(0x9c40, mload(0x8640))

        {
            let scalar := mload(0x9c40)
            let is_inf := and(
                and(eq(mload(0x9bc0), 0), eq(mload(0x9be0), 0)),
                and(eq(mload(0x9c00), 0), eq(mload(0x9c20), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x9bc0, 0)
                mstore(0x9be0, 0)
                mstore(0x9c00, 0)
                mstore(0x9c20, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x9bc0, 0xa0, 0x9bc0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9c60, mload(0x9ac0))
mstore(0x9c80, mload(0x9ae0))
mstore(0x9ca0, mload(0x9b00))
mstore(0x9cc0, mload(0x9b20))
                }
{
                    mstore(0x9ce0, mload(0x9bc0))
mstore(0x9d00, mload(0x9be0))
mstore(0x9d20, mload(0x9c00))
mstore(0x9d40, mload(0x9c20))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x9c60), 0), eq(mload(0x9c80), 0)),
                and(eq(mload(0x9ca0), 0), eq(mload(0x9cc0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x9ce0), 0), eq(mload(0x9d00), 0)),
                and(eq(mload(0x9d20), 0), eq(mload(0x9d40), 0))
            )
            if lhs_inf {
                mstore(0x9c60, mload(0x9ce0))
                mstore(0x9c80, mload(0x9d00))
                mstore(0x9ca0, mload(0x9d20))
                mstore(0x9cc0, mload(0x9d40))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x9c60, 0x100, 0x9c60, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9d60, mload(0x4a0))
mstore(0x9d80, mload(0x4c0))
mstore(0x9da0, mload(0x4e0))
mstore(0x9dc0, mload(0x500))
                }
mstore(0x9de0, mload(0x8660))

        {
            let scalar := mload(0x9de0)
            let is_inf := and(
                and(eq(mload(0x9d60), 0), eq(mload(0x9d80), 0)),
                and(eq(mload(0x9da0), 0), eq(mload(0x9dc0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x9d60, 0)
                mstore(0x9d80, 0)
                mstore(0x9da0, 0)
                mstore(0x9dc0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x9d60, 0xa0, 0x9d60, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9e00, mload(0x9c60))
mstore(0x9e20, mload(0x9c80))
mstore(0x9e40, mload(0x9ca0))
mstore(0x9e60, mload(0x9cc0))
                }
{
                    mstore(0x9e80, mload(0x9d60))
mstore(0x9ea0, mload(0x9d80))
mstore(0x9ec0, mload(0x9da0))
mstore(0x9ee0, mload(0x9dc0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x9e00), 0), eq(mload(0x9e20), 0)),
                and(eq(mload(0x9e40), 0), eq(mload(0x9e60), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0x9e80), 0), eq(mload(0x9ea0), 0)),
                and(eq(mload(0x9ec0), 0), eq(mload(0x9ee0), 0))
            )
            if lhs_inf {
                mstore(0x9e00, mload(0x9e80))
                mstore(0x9e20, mload(0x9ea0))
                mstore(0x9e40, mload(0x9ec0))
                mstore(0x9e60, mload(0x9ee0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x9e00, 0x100, 0x9e00, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9f00, mload(0x520))
mstore(0x9f20, mload(0x540))
mstore(0x9f40, mload(0x560))
mstore(0x9f60, mload(0x580))
                }
mstore(0x9f80, mload(0x8680))

        {
            let scalar := mload(0x9f80)
            let is_inf := and(
                and(eq(mload(0x9f00), 0), eq(mload(0x9f20), 0)),
                and(eq(mload(0x9f40), 0), eq(mload(0x9f60), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0x9f00, 0)
                mstore(0x9f20, 0)
                mstore(0x9f40, 0)
                mstore(0x9f60, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0x9f00, 0xa0, 0x9f00, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0x9fa0, mload(0x9e00))
mstore(0x9fc0, mload(0x9e20))
mstore(0x9fe0, mload(0x9e40))
mstore(0xa000, mload(0x9e60))
                }
{
                    mstore(0xa020, mload(0x9f00))
mstore(0xa040, mload(0x9f20))
mstore(0xa060, mload(0x9f40))
mstore(0xa080, mload(0x9f60))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0x9fa0), 0), eq(mload(0x9fc0), 0)),
                and(eq(mload(0x9fe0), 0), eq(mload(0xa000), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xa020), 0), eq(mload(0xa040), 0)),
                and(eq(mload(0xa060), 0), eq(mload(0xa080), 0))
            )
            if lhs_inf {
                mstore(0x9fa0, mload(0xa020))
                mstore(0x9fc0, mload(0xa040))
                mstore(0x9fe0, mload(0xa060))
                mstore(0xa000, mload(0xa080))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0x9fa0, 0x100, 0x9fa0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa0a0, mload(0x5a0))
mstore(0xa0c0, mload(0x5c0))
mstore(0xa0e0, mload(0x5e0))
mstore(0xa100, mload(0x600))
                }
mstore(0xa120, mload(0x86a0))

        {
            let scalar := mload(0xa120)
            let is_inf := and(
                and(eq(mload(0xa0a0), 0), eq(mload(0xa0c0), 0)),
                and(eq(mload(0xa0e0), 0), eq(mload(0xa100), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xa0a0, 0)
                mstore(0xa0c0, 0)
                mstore(0xa0e0, 0)
                mstore(0xa100, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xa0a0, 0xa0, 0xa0a0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa140, mload(0x9fa0))
mstore(0xa160, mload(0x9fc0))
mstore(0xa180, mload(0x9fe0))
mstore(0xa1a0, mload(0xa000))
                }
{
                    mstore(0xa1c0, mload(0xa0a0))
mstore(0xa1e0, mload(0xa0c0))
mstore(0xa200, mload(0xa0e0))
mstore(0xa220, mload(0xa100))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xa140), 0), eq(mload(0xa160), 0)),
                and(eq(mload(0xa180), 0), eq(mload(0xa1a0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xa1c0), 0), eq(mload(0xa1e0), 0)),
                and(eq(mload(0xa200), 0), eq(mload(0xa220), 0))
            )
            if lhs_inf {
                mstore(0xa140, mload(0xa1c0))
                mstore(0xa160, mload(0xa1e0))
                mstore(0xa180, mload(0xa200))
                mstore(0xa1a0, mload(0xa220))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xa140, 0x100, 0xa140, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa240, mload(0x620))
mstore(0xa260, mload(0x640))
mstore(0xa280, mload(0x660))
mstore(0xa2a0, mload(0x680))
                }
mstore(0xa2c0, mload(0x86c0))

        {
            let scalar := mload(0xa2c0)
            let is_inf := and(
                and(eq(mload(0xa240), 0), eq(mload(0xa260), 0)),
                and(eq(mload(0xa280), 0), eq(mload(0xa2a0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xa240, 0)
                mstore(0xa260, 0)
                mstore(0xa280, 0)
                mstore(0xa2a0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xa240, 0xa0, 0xa240, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa2e0, mload(0xa140))
mstore(0xa300, mload(0xa160))
mstore(0xa320, mload(0xa180))
mstore(0xa340, mload(0xa1a0))
                }
{
                    mstore(0xa360, mload(0xa240))
mstore(0xa380, mload(0xa260))
mstore(0xa3a0, mload(0xa280))
mstore(0xa3c0, mload(0xa2a0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xa2e0), 0), eq(mload(0xa300), 0)),
                and(eq(mload(0xa320), 0), eq(mload(0xa340), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xa360), 0), eq(mload(0xa380), 0)),
                and(eq(mload(0xa3a0), 0), eq(mload(0xa3c0), 0))
            )
            if lhs_inf {
                mstore(0xa2e0, mload(0xa360))
                mstore(0xa300, mload(0xa380))
                mstore(0xa320, mload(0xa3a0))
                mstore(0xa340, mload(0xa3c0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xa2e0, 0x100, 0xa2e0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa3e0, mload(0x220))
mstore(0xa400, mload(0x240))
mstore(0xa420, mload(0x260))
mstore(0xa440, mload(0x280))
                }
mstore(0xa460, mload(0x86e0))

        {
            let scalar := mload(0xa460)
            let is_inf := and(
                and(eq(mload(0xa3e0), 0), eq(mload(0xa400), 0)),
                and(eq(mload(0xa420), 0), eq(mload(0xa440), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xa3e0, 0)
                mstore(0xa400, 0)
                mstore(0xa420, 0)
                mstore(0xa440, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xa3e0, 0xa0, 0xa3e0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa480, mload(0xa2e0))
mstore(0xa4a0, mload(0xa300))
mstore(0xa4c0, mload(0xa320))
mstore(0xa4e0, mload(0xa340))
                }
{
                    mstore(0xa500, mload(0xa3e0))
mstore(0xa520, mload(0xa400))
mstore(0xa540, mload(0xa420))
mstore(0xa560, mload(0xa440))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xa480), 0), eq(mload(0xa4a0), 0)),
                and(eq(mload(0xa4c0), 0), eq(mload(0xa4e0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xa500), 0), eq(mload(0xa520), 0)),
                and(eq(mload(0xa540), 0), eq(mload(0xa560), 0))
            )
            if lhs_inf {
                mstore(0xa480, mload(0xa500))
                mstore(0xa4a0, mload(0xa520))
                mstore(0xa4c0, mload(0xa540))
                mstore(0xa4e0, mload(0xa560))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xa480, 0x100, 0xa480, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa580, mload(0x2a0))
mstore(0xa5a0, mload(0x2c0))
mstore(0xa5c0, mload(0x2e0))
mstore(0xa5e0, mload(0x300))
                }
mstore(0xa600, mload(0x8700))

        {
            let scalar := mload(0xa600)
            let is_inf := and(
                and(eq(mload(0xa580), 0), eq(mload(0xa5a0), 0)),
                and(eq(mload(0xa5c0), 0), eq(mload(0xa5e0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xa580, 0)
                mstore(0xa5a0, 0)
                mstore(0xa5c0, 0)
                mstore(0xa5e0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xa580, 0xa0, 0xa580, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa620, mload(0xa480))
mstore(0xa640, mload(0xa4a0))
mstore(0xa660, mload(0xa4c0))
mstore(0xa680, mload(0xa4e0))
                }
{
                    mstore(0xa6a0, mload(0xa580))
mstore(0xa6c0, mload(0xa5a0))
mstore(0xa6e0, mload(0xa5c0))
mstore(0xa700, mload(0xa5e0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xa620), 0), eq(mload(0xa640), 0)),
                and(eq(mload(0xa660), 0), eq(mload(0xa680), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xa6a0), 0), eq(mload(0xa6c0), 0)),
                and(eq(mload(0xa6e0), 0), eq(mload(0xa700), 0))
            )
            if lhs_inf {
                mstore(0xa620, mload(0xa6a0))
                mstore(0xa640, mload(0xa6c0))
                mstore(0xa660, mload(0xa6e0))
                mstore(0xa680, mload(0xa700))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xa620, 0x100, 0xa620, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa720, mload(0x320))
mstore(0xa740, mload(0x340))
mstore(0xa760, mload(0x360))
mstore(0xa780, mload(0x380))
                }
mstore(0xa7a0, mload(0x8720))

        {
            let scalar := mload(0xa7a0)
            let is_inf := and(
                and(eq(mload(0xa720), 0), eq(mload(0xa740), 0)),
                and(eq(mload(0xa760), 0), eq(mload(0xa780), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xa720, 0)
                mstore(0xa740, 0)
                mstore(0xa760, 0)
                mstore(0xa780, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xa720, 0xa0, 0xa720, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa7c0, mload(0xa620))
mstore(0xa7e0, mload(0xa640))
mstore(0xa800, mload(0xa660))
mstore(0xa820, mload(0xa680))
                }
{
                    mstore(0xa840, mload(0xa720))
mstore(0xa860, mload(0xa740))
mstore(0xa880, mload(0xa760))
mstore(0xa8a0, mload(0xa780))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xa7c0), 0), eq(mload(0xa7e0), 0)),
                and(eq(mload(0xa800), 0), eq(mload(0xa820), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xa840), 0), eq(mload(0xa860), 0)),
                and(eq(mload(0xa880), 0), eq(mload(0xa8a0), 0))
            )
            if lhs_inf {
                mstore(0xa7c0, mload(0xa840))
                mstore(0xa7e0, mload(0xa860))
                mstore(0xa800, mload(0xa880))
                mstore(0xa820, mload(0xa8a0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xa7c0, 0x100, 0xa7c0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa8c0, mload(0x3a0))
mstore(0xa8e0, mload(0x3c0))
mstore(0xa900, mload(0x3e0))
mstore(0xa920, mload(0x400))
                }
mstore(0xa940, mload(0x8740))

        {
            let scalar := mload(0xa940)
            let is_inf := and(
                and(eq(mload(0xa8c0), 0), eq(mload(0xa8e0), 0)),
                and(eq(mload(0xa900), 0), eq(mload(0xa920), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xa8c0, 0)
                mstore(0xa8e0, 0)
                mstore(0xa900, 0)
                mstore(0xa920, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xa8c0, 0xa0, 0xa8c0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xa960, mload(0xa7c0))
mstore(0xa980, mload(0xa7e0))
mstore(0xa9a0, mload(0xa800))
mstore(0xa9c0, mload(0xa820))
                }
{
                    mstore(0xa9e0, mload(0xa8c0))
mstore(0xaa00, mload(0xa8e0))
mstore(0xaa20, mload(0xa900))
mstore(0xaa40, mload(0xa920))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xa960), 0), eq(mload(0xa980), 0)),
                and(eq(mload(0xa9a0), 0), eq(mload(0xa9c0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xa9e0), 0), eq(mload(0xaa00), 0)),
                and(eq(mload(0xaa20), 0), eq(mload(0xaa40), 0))
            )
            if lhs_inf {
                mstore(0xa960, mload(0xa9e0))
                mstore(0xa980, mload(0xaa00))
                mstore(0xa9a0, mload(0xaa20))
                mstore(0xa9c0, mload(0xaa40))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xa960, 0x100, 0xa960, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xaa60, mload(0x720))
mstore(0xaa80, mload(0x740))
mstore(0xaaa0, mload(0x760))
mstore(0xaac0, mload(0x780))
                }
mstore(0xaae0, mload(0x8760))

        {
            let scalar := mload(0xaae0)
            let is_inf := and(
                and(eq(mload(0xaa60), 0), eq(mload(0xaa80), 0)),
                and(eq(mload(0xaaa0), 0), eq(mload(0xaac0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xaa60, 0)
                mstore(0xaa80, 0)
                mstore(0xaaa0, 0)
                mstore(0xaac0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xaa60, 0xa0, 0xaa60, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xab00, mload(0xa960))
mstore(0xab20, mload(0xa980))
mstore(0xab40, mload(0xa9a0))
mstore(0xab60, mload(0xa9c0))
                }
{
                    mstore(0xab80, mload(0xaa60))
mstore(0xaba0, mload(0xaa80))
mstore(0xabc0, mload(0xaaa0))
mstore(0xabe0, mload(0xaac0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xab00), 0), eq(mload(0xab20), 0)),
                and(eq(mload(0xab40), 0), eq(mload(0xab60), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xab80), 0), eq(mload(0xaba0), 0)),
                and(eq(mload(0xabc0), 0), eq(mload(0xabe0), 0))
            )
            if lhs_inf {
                mstore(0xab00, mload(0xab80))
                mstore(0xab20, mload(0xaba0))
                mstore(0xab40, mload(0xabc0))
                mstore(0xab60, mload(0xabe0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xab00, 0x100, 0xab00, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xac00, mload(0x7a0))
mstore(0xac20, mload(0x7c0))
mstore(0xac40, mload(0x7e0))
mstore(0xac60, mload(0x800))
                }
mstore(0xac80, mload(0x8780))

        {
            let scalar := mload(0xac80)
            let is_inf := and(
                and(eq(mload(0xac00), 0), eq(mload(0xac20), 0)),
                and(eq(mload(0xac40), 0), eq(mload(0xac60), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xac00, 0)
                mstore(0xac20, 0)
                mstore(0xac40, 0)
                mstore(0xac60, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xac00, 0xa0, 0xac00, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xaca0, mload(0xab00))
mstore(0xacc0, mload(0xab20))
mstore(0xace0, mload(0xab40))
mstore(0xad00, mload(0xab60))
                }
{
                    mstore(0xad20, mload(0xac00))
mstore(0xad40, mload(0xac20))
mstore(0xad60, mload(0xac40))
mstore(0xad80, mload(0xac60))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xaca0), 0), eq(mload(0xacc0), 0)),
                and(eq(mload(0xace0), 0), eq(mload(0xad00), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xad20), 0), eq(mload(0xad40), 0)),
                and(eq(mload(0xad60), 0), eq(mload(0xad80), 0))
            )
            if lhs_inf {
                mstore(0xaca0, mload(0xad20))
                mstore(0xacc0, mload(0xad40))
                mstore(0xace0, mload(0xad60))
                mstore(0xad00, mload(0xad80))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xaca0, 0x100, 0xaca0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xada0, mload(0x820))
mstore(0xadc0, mload(0x840))
mstore(0xade0, mload(0x860))
mstore(0xae00, mload(0x880))
                }
mstore(0xae20, mload(0x87a0))

        {
            let scalar := mload(0xae20)
            let is_inf := and(
                and(eq(mload(0xada0), 0), eq(mload(0xadc0), 0)),
                and(eq(mload(0xade0), 0), eq(mload(0xae00), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xada0, 0)
                mstore(0xadc0, 0)
                mstore(0xade0, 0)
                mstore(0xae00, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xada0, 0xa0, 0xada0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xae40, mload(0xaca0))
mstore(0xae60, mload(0xacc0))
mstore(0xae80, mload(0xace0))
mstore(0xaea0, mload(0xad00))
                }
{
                    mstore(0xaec0, mload(0xada0))
mstore(0xaee0, mload(0xadc0))
mstore(0xaf00, mload(0xade0))
mstore(0xaf20, mload(0xae00))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xae40), 0), eq(mload(0xae60), 0)),
                and(eq(mload(0xae80), 0), eq(mload(0xaea0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xaec0), 0), eq(mload(0xaee0), 0)),
                and(eq(mload(0xaf00), 0), eq(mload(0xaf20), 0))
            )
            if lhs_inf {
                mstore(0xae40, mload(0xaec0))
                mstore(0xae60, mload(0xaee0))
                mstore(0xae80, mload(0xaf00))
                mstore(0xaea0, mload(0xaf20))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xae40, 0x100, 0xae40, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xaf40, mload(0x8a0))
mstore(0xaf60, mload(0x8c0))
mstore(0xaf80, mload(0x8e0))
mstore(0xafa0, mload(0x900))
                }
mstore(0xafc0, mload(0x87c0))

        {
            let scalar := mload(0xafc0)
            let is_inf := and(
                and(eq(mload(0xaf40), 0), eq(mload(0xaf60), 0)),
                and(eq(mload(0xaf80), 0), eq(mload(0xafa0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xaf40, 0)
                mstore(0xaf60, 0)
                mstore(0xaf80, 0)
                mstore(0xafa0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xaf40, 0xa0, 0xaf40, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xafe0, mload(0xae40))
mstore(0xb000, mload(0xae60))
mstore(0xb020, mload(0xae80))
mstore(0xb040, mload(0xaea0))
                }
{
                    mstore(0xb060, mload(0xaf40))
mstore(0xb080, mload(0xaf60))
mstore(0xb0a0, mload(0xaf80))
mstore(0xb0c0, mload(0xafa0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xafe0), 0), eq(mload(0xb000), 0)),
                and(eq(mload(0xb020), 0), eq(mload(0xb040), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xb060), 0), eq(mload(0xb080), 0)),
                and(eq(mload(0xb0a0), 0), eq(mload(0xb0c0), 0))
            )
            if lhs_inf {
                mstore(0xafe0, mload(0xb060))
                mstore(0xb000, mload(0xb080))
                mstore(0xb020, mload(0xb0a0))
                mstore(0xb040, mload(0xb0c0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xafe0, 0x100, 0xafe0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb0e0, mload(0x920))
mstore(0xb100, mload(0x940))
mstore(0xb120, mload(0x960))
mstore(0xb140, mload(0x980))
                }
mstore(0xb160, mload(0x87e0))

        {
            let scalar := mload(0xb160)
            let is_inf := and(
                and(eq(mload(0xb0e0), 0), eq(mload(0xb100), 0)),
                and(eq(mload(0xb120), 0), eq(mload(0xb140), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xb0e0, 0)
                mstore(0xb100, 0)
                mstore(0xb120, 0)
                mstore(0xb140, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xb0e0, 0xa0, 0xb0e0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb180, mload(0xafe0))
mstore(0xb1a0, mload(0xb000))
mstore(0xb1c0, mload(0xb020))
mstore(0xb1e0, mload(0xb040))
                }
{
                    mstore(0xb200, mload(0xb0e0))
mstore(0xb220, mload(0xb100))
mstore(0xb240, mload(0xb120))
mstore(0xb260, mload(0xb140))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xb180), 0), eq(mload(0xb1a0), 0)),
                and(eq(mload(0xb1c0), 0), eq(mload(0xb1e0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xb200), 0), eq(mload(0xb220), 0)),
                and(eq(mload(0xb240), 0), eq(mload(0xb260), 0))
            )
            if lhs_inf {
                mstore(0xb180, mload(0xb200))
                mstore(0xb1a0, mload(0xb220))
                mstore(0xb1c0, mload(0xb240))
                mstore(0xb1e0, mload(0xb260))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xb180, 0x100, 0xb180, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb280, mload(0x9a0))
mstore(0xb2a0, mload(0x9c0))
mstore(0xb2c0, mload(0x9e0))
mstore(0xb2e0, mload(0xa00))
                }
mstore(0xb300, mload(0x8800))

        {
            let scalar := mload(0xb300)
            let is_inf := and(
                and(eq(mload(0xb280), 0), eq(mload(0xb2a0), 0)),
                and(eq(mload(0xb2c0), 0), eq(mload(0xb2e0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xb280, 0)
                mstore(0xb2a0, 0)
                mstore(0xb2c0, 0)
                mstore(0xb2e0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xb280, 0xa0, 0xb280, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb320, mload(0xb180))
mstore(0xb340, mload(0xb1a0))
mstore(0xb360, mload(0xb1c0))
mstore(0xb380, mload(0xb1e0))
                }
{
                    mstore(0xb3a0, mload(0xb280))
mstore(0xb3c0, mload(0xb2a0))
mstore(0xb3e0, mload(0xb2c0))
mstore(0xb400, mload(0xb2e0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xb320), 0), eq(mload(0xb340), 0)),
                and(eq(mload(0xb360), 0), eq(mload(0xb380), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xb3a0), 0), eq(mload(0xb3c0), 0)),
                and(eq(mload(0xb3e0), 0), eq(mload(0xb400), 0))
            )
            if lhs_inf {
                mstore(0xb320, mload(0xb3a0))
                mstore(0xb340, mload(0xb3c0))
                mstore(0xb360, mload(0xb3e0))
                mstore(0xb380, mload(0xb400))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xb320, 0x100, 0xb320, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb420, mload(0xa20))
mstore(0xb440, mload(0xa40))
mstore(0xb460, mload(0xa60))
mstore(0xb480, mload(0xa80))
                }
mstore(0xb4a0, mload(0x8820))

        {
            let scalar := mload(0xb4a0)
            let is_inf := and(
                and(eq(mload(0xb420), 0), eq(mload(0xb440), 0)),
                and(eq(mload(0xb460), 0), eq(mload(0xb480), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xb420, 0)
                mstore(0xb440, 0)
                mstore(0xb460, 0)
                mstore(0xb480, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xb420, 0xa0, 0xb420, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb4c0, mload(0xb320))
mstore(0xb4e0, mload(0xb340))
mstore(0xb500, mload(0xb360))
mstore(0xb520, mload(0xb380))
                }
{
                    mstore(0xb540, mload(0xb420))
mstore(0xb560, mload(0xb440))
mstore(0xb580, mload(0xb460))
mstore(0xb5a0, mload(0xb480))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xb4c0), 0), eq(mload(0xb4e0), 0)),
                and(eq(mload(0xb500), 0), eq(mload(0xb520), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xb540), 0), eq(mload(0xb560), 0)),
                and(eq(mload(0xb580), 0), eq(mload(0xb5a0), 0))
            )
            if lhs_inf {
                mstore(0xb4c0, mload(0xb540))
                mstore(0xb4e0, mload(0xb560))
                mstore(0xb500, mload(0xb580))
                mstore(0xb520, mload(0xb5a0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xb4c0, 0x100, 0xb4c0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb5c0, mload(0xaa0))
mstore(0xb5e0, mload(0xac0))
mstore(0xb600, mload(0xae0))
mstore(0xb620, mload(0xb00))
                }
mstore(0xb640, mload(0x8840))

        {
            let scalar := mload(0xb640)
            let is_inf := and(
                and(eq(mload(0xb5c0), 0), eq(mload(0xb5e0), 0)),
                and(eq(mload(0xb600), 0), eq(mload(0xb620), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xb5c0, 0)
                mstore(0xb5e0, 0)
                mstore(0xb600, 0)
                mstore(0xb620, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xb5c0, 0xa0, 0xb5c0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb660, mload(0xb4c0))
mstore(0xb680, mload(0xb4e0))
mstore(0xb6a0, mload(0xb500))
mstore(0xb6c0, mload(0xb520))
                }
{
                    mstore(0xb6e0, mload(0xb5c0))
mstore(0xb700, mload(0xb5e0))
mstore(0xb720, mload(0xb600))
mstore(0xb740, mload(0xb620))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xb660), 0), eq(mload(0xb680), 0)),
                and(eq(mload(0xb6a0), 0), eq(mload(0xb6c0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xb6e0), 0), eq(mload(0xb700), 0)),
                and(eq(mload(0xb720), 0), eq(mload(0xb740), 0))
            )
            if lhs_inf {
                mstore(0xb660, mload(0xb6e0))
                mstore(0xb680, mload(0xb700))
                mstore(0xb6a0, mload(0xb720))
                mstore(0xb6c0, mload(0xb740))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xb660, 0x100, 0xb660, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb760, mload(0xb20))
mstore(0xb780, mload(0xb40))
mstore(0xb7a0, mload(0xb60))
mstore(0xb7c0, mload(0xb80))
                }
mstore(0xb7e0, mload(0x8860))

        {
            let scalar := mload(0xb7e0)
            let is_inf := and(
                and(eq(mload(0xb760), 0), eq(mload(0xb780), 0)),
                and(eq(mload(0xb7a0), 0), eq(mload(0xb7c0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xb760, 0)
                mstore(0xb780, 0)
                mstore(0xb7a0, 0)
                mstore(0xb7c0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xb760, 0xa0, 0xb760, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb800, mload(0xb660))
mstore(0xb820, mload(0xb680))
mstore(0xb840, mload(0xb6a0))
mstore(0xb860, mload(0xb6c0))
                }
{
                    mstore(0xb880, mload(0xb760))
mstore(0xb8a0, mload(0xb780))
mstore(0xb8c0, mload(0xb7a0))
mstore(0xb8e0, mload(0xb7c0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xb800), 0), eq(mload(0xb820), 0)),
                and(eq(mload(0xb840), 0), eq(mload(0xb860), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xb880), 0), eq(mload(0xb8a0), 0)),
                and(eq(mload(0xb8c0), 0), eq(mload(0xb8e0), 0))
            )
            if lhs_inf {
                mstore(0xb800, mload(0xb880))
                mstore(0xb820, mload(0xb8a0))
                mstore(0xb840, mload(0xb8c0))
                mstore(0xb860, mload(0xb8e0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xb800, 0x100, 0xb800, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb900, mload(0xba0))
mstore(0xb920, mload(0xbc0))
mstore(0xb940, mload(0xbe0))
mstore(0xb960, mload(0xc00))
                }
mstore(0xb980, mload(0x8880))

        {
            let scalar := mload(0xb980)
            let is_inf := and(
                and(eq(mload(0xb900), 0), eq(mload(0xb920), 0)),
                and(eq(mload(0xb940), 0), eq(mload(0xb960), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xb900, 0)
                mstore(0xb920, 0)
                mstore(0xb940, 0)
                mstore(0xb960, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xb900, 0xa0, 0xb900, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xb9a0, mload(0xb800))
mstore(0xb9c0, mload(0xb820))
mstore(0xb9e0, mload(0xb840))
mstore(0xba00, mload(0xb860))
                }
{
                    mstore(0xba20, mload(0xb900))
mstore(0xba40, mload(0xb920))
mstore(0xba60, mload(0xb940))
mstore(0xba80, mload(0xb960))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xb9a0), 0), eq(mload(0xb9c0), 0)),
                and(eq(mload(0xb9e0), 0), eq(mload(0xba00), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xba20), 0), eq(mload(0xba40), 0)),
                and(eq(mload(0xba60), 0), eq(mload(0xba80), 0))
            )
            if lhs_inf {
                mstore(0xb9a0, mload(0xba20))
                mstore(0xb9c0, mload(0xba40))
                mstore(0xb9e0, mload(0xba60))
                mstore(0xba00, mload(0xba80))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xb9a0, 0x100, 0xb9a0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xbaa0, mload(0xc20))
mstore(0xbac0, mload(0xc40))
mstore(0xbae0, mload(0xc60))
mstore(0xbb00, mload(0xc80))
                }
mstore(0xbb20, mload(0x88a0))

        {
            let scalar := mload(0xbb20)
            let is_inf := and(
                and(eq(mload(0xbaa0), 0), eq(mload(0xbac0), 0)),
                and(eq(mload(0xbae0), 0), eq(mload(0xbb00), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xbaa0, 0)
                mstore(0xbac0, 0)
                mstore(0xbae0, 0)
                mstore(0xbb00, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xbaa0, 0xa0, 0xbaa0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xbb40, mload(0xb9a0))
mstore(0xbb60, mload(0xb9c0))
mstore(0xbb80, mload(0xb9e0))
mstore(0xbba0, mload(0xba00))
                }
{
                    mstore(0xbbc0, mload(0xbaa0))
mstore(0xbbe0, mload(0xbac0))
mstore(0xbc00, mload(0xbae0))
mstore(0xbc20, mload(0xbb00))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xbb40), 0), eq(mload(0xbb60), 0)),
                and(eq(mload(0xbb80), 0), eq(mload(0xbba0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xbbc0), 0), eq(mload(0xbbe0), 0)),
                and(eq(mload(0xbc00), 0), eq(mload(0xbc20), 0))
            )
            if lhs_inf {
                mstore(0xbb40, mload(0xbbc0))
                mstore(0xbb60, mload(0xbbe0))
                mstore(0xbb80, mload(0xbc00))
                mstore(0xbba0, mload(0xbc20))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xbb40, 0x100, 0xbb40, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xbc40, mload(0xca0))
mstore(0xbc60, mload(0xcc0))
mstore(0xbc80, mload(0xce0))
mstore(0xbca0, mload(0xd00))
                }
mstore(0xbcc0, mload(0x88c0))

        {
            let scalar := mload(0xbcc0)
            let is_inf := and(
                and(eq(mload(0xbc40), 0), eq(mload(0xbc60), 0)),
                and(eq(mload(0xbc80), 0), eq(mload(0xbca0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xbc40, 0)
                mstore(0xbc60, 0)
                mstore(0xbc80, 0)
                mstore(0xbca0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xbc40, 0xa0, 0xbc40, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xbce0, mload(0xbb40))
mstore(0xbd00, mload(0xbb60))
mstore(0xbd20, mload(0xbb80))
mstore(0xbd40, mload(0xbba0))
                }
{
                    mstore(0xbd60, mload(0xbc40))
mstore(0xbd80, mload(0xbc60))
mstore(0xbda0, mload(0xbc80))
mstore(0xbdc0, mload(0xbca0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xbce0), 0), eq(mload(0xbd00), 0)),
                and(eq(mload(0xbd20), 0), eq(mload(0xbd40), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xbd60), 0), eq(mload(0xbd80), 0)),
                and(eq(mload(0xbda0), 0), eq(mload(0xbdc0), 0))
            )
            if lhs_inf {
                mstore(0xbce0, mload(0xbd60))
                mstore(0xbd00, mload(0xbd80))
                mstore(0xbd20, mload(0xbda0))
                mstore(0xbd40, mload(0xbdc0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xbce0, 0x100, 0xbce0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xbde0, mload(0xd20))
mstore(0xbe00, mload(0xd40))
mstore(0xbe20, mload(0xd60))
mstore(0xbe40, mload(0xd80))
                }
mstore(0xbe60, mload(0x88e0))

        {
            let scalar := mload(0xbe60)
            let is_inf := and(
                and(eq(mload(0xbde0), 0), eq(mload(0xbe00), 0)),
                and(eq(mload(0xbe20), 0), eq(mload(0xbe40), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xbde0, 0)
                mstore(0xbe00, 0)
                mstore(0xbe20, 0)
                mstore(0xbe40, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xbde0, 0xa0, 0xbde0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xbe80, mload(0xbce0))
mstore(0xbea0, mload(0xbd00))
mstore(0xbec0, mload(0xbd20))
mstore(0xbee0, mload(0xbd40))
                }
{
                    mstore(0xbf00, mload(0xbde0))
mstore(0xbf20, mload(0xbe00))
mstore(0xbf40, mload(0xbe20))
mstore(0xbf60, mload(0xbe40))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xbe80), 0), eq(mload(0xbea0), 0)),
                and(eq(mload(0xbec0), 0), eq(mload(0xbee0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xbf00), 0), eq(mload(0xbf20), 0)),
                and(eq(mload(0xbf40), 0), eq(mload(0xbf60), 0))
            )
            if lhs_inf {
                mstore(0xbe80, mload(0xbf00))
                mstore(0xbea0, mload(0xbf20))
                mstore(0xbec0, mload(0xbf40))
                mstore(0xbee0, mload(0xbf60))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xbe80, 0x100, 0xbe80, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xbf80, mload(0xda0))
mstore(0xbfa0, mload(0xdc0))
mstore(0xbfc0, mload(0xde0))
mstore(0xbfe0, mload(0xe00))
                }
mstore(0xc000, mload(0x8900))

        {
            let scalar := mload(0xc000)
            let is_inf := and(
                and(eq(mload(0xbf80), 0), eq(mload(0xbfa0), 0)),
                and(eq(mload(0xbfc0), 0), eq(mload(0xbfe0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xbf80, 0)
                mstore(0xbfa0, 0)
                mstore(0xbfc0, 0)
                mstore(0xbfe0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xbf80, 0xa0, 0xbf80, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc020, mload(0xbe80))
mstore(0xc040, mload(0xbea0))
mstore(0xc060, mload(0xbec0))
mstore(0xc080, mload(0xbee0))
                }
{
                    mstore(0xc0a0, mload(0xbf80))
mstore(0xc0c0, mload(0xbfa0))
mstore(0xc0e0, mload(0xbfc0))
mstore(0xc100, mload(0xbfe0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xc020), 0), eq(mload(0xc040), 0)),
                and(eq(mload(0xc060), 0), eq(mload(0xc080), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xc0a0), 0), eq(mload(0xc0c0), 0)),
                and(eq(mload(0xc0e0), 0), eq(mload(0xc100), 0))
            )
            if lhs_inf {
                mstore(0xc020, mload(0xc0a0))
                mstore(0xc040, mload(0xc0c0))
                mstore(0xc060, mload(0xc0e0))
                mstore(0xc080, mload(0xc100))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xc020, 0x100, 0xc020, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc120, mload(0xe20))
mstore(0xc140, mload(0xe40))
mstore(0xc160, mload(0xe60))
mstore(0xc180, mload(0xe80))
                }
mstore(0xc1a0, mload(0x8920))

        {
            let scalar := mload(0xc1a0)
            let is_inf := and(
                and(eq(mload(0xc120), 0), eq(mload(0xc140), 0)),
                and(eq(mload(0xc160), 0), eq(mload(0xc180), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xc120, 0)
                mstore(0xc140, 0)
                mstore(0xc160, 0)
                mstore(0xc180, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xc120, 0xa0, 0xc120, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc1c0, mload(0xc020))
mstore(0xc1e0, mload(0xc040))
mstore(0xc200, mload(0xc060))
mstore(0xc220, mload(0xc080))
                }
{
                    mstore(0xc240, mload(0xc120))
mstore(0xc260, mload(0xc140))
mstore(0xc280, mload(0xc160))
mstore(0xc2a0, mload(0xc180))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xc1c0), 0), eq(mload(0xc1e0), 0)),
                and(eq(mload(0xc200), 0), eq(mload(0xc220), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xc240), 0), eq(mload(0xc260), 0)),
                and(eq(mload(0xc280), 0), eq(mload(0xc2a0), 0))
            )
            if lhs_inf {
                mstore(0xc1c0, mload(0xc240))
                mstore(0xc1e0, mload(0xc260))
                mstore(0xc200, mload(0xc280))
                mstore(0xc220, mload(0xc2a0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xc1c0, 0x100, 0xc1c0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc2c0, mload(0xea0))
mstore(0xc2e0, mload(0xec0))
mstore(0xc300, mload(0xee0))
mstore(0xc320, mload(0xf00))
                }
mstore(0xc340, mload(0x8940))

        {
            let scalar := mload(0xc340)
            let is_inf := and(
                and(eq(mload(0xc2c0), 0), eq(mload(0xc2e0), 0)),
                and(eq(mload(0xc300), 0), eq(mload(0xc320), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xc2c0, 0)
                mstore(0xc2e0, 0)
                mstore(0xc300, 0)
                mstore(0xc320, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xc2c0, 0xa0, 0xc2c0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc360, mload(0xc1c0))
mstore(0xc380, mload(0xc1e0))
mstore(0xc3a0, mload(0xc200))
mstore(0xc3c0, mload(0xc220))
                }
{
                    mstore(0xc3e0, mload(0xc2c0))
mstore(0xc400, mload(0xc2e0))
mstore(0xc420, mload(0xc300))
mstore(0xc440, mload(0xc320))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xc360), 0), eq(mload(0xc380), 0)),
                and(eq(mload(0xc3a0), 0), eq(mload(0xc3c0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xc3e0), 0), eq(mload(0xc400), 0)),
                and(eq(mload(0xc420), 0), eq(mload(0xc440), 0))
            )
            if lhs_inf {
                mstore(0xc360, mload(0xc3e0))
                mstore(0xc380, mload(0xc400))
                mstore(0xc3a0, mload(0xc420))
                mstore(0xc3c0, mload(0xc440))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xc360, 0x100, 0xc360, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc460, mload(0xf20))
mstore(0xc480, mload(0xf40))
mstore(0xc4a0, mload(0xf60))
mstore(0xc4c0, mload(0xf80))
                }
mstore(0xc4e0, mload(0x8960))

        {
            let scalar := mload(0xc4e0)
            let is_inf := and(
                and(eq(mload(0xc460), 0), eq(mload(0xc480), 0)),
                and(eq(mload(0xc4a0), 0), eq(mload(0xc4c0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xc460, 0)
                mstore(0xc480, 0)
                mstore(0xc4a0, 0)
                mstore(0xc4c0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xc460, 0xa0, 0xc460, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc500, mload(0xc360))
mstore(0xc520, mload(0xc380))
mstore(0xc540, mload(0xc3a0))
mstore(0xc560, mload(0xc3c0))
                }
{
                    mstore(0xc580, mload(0xc460))
mstore(0xc5a0, mload(0xc480))
mstore(0xc5c0, mload(0xc4a0))
mstore(0xc5e0, mload(0xc4c0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xc500), 0), eq(mload(0xc520), 0)),
                and(eq(mload(0xc540), 0), eq(mload(0xc560), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xc580), 0), eq(mload(0xc5a0), 0)),
                and(eq(mload(0xc5c0), 0), eq(mload(0xc5e0), 0))
            )
            if lhs_inf {
                mstore(0xc500, mload(0xc580))
                mstore(0xc520, mload(0xc5a0))
                mstore(0xc540, mload(0xc5c0))
                mstore(0xc560, mload(0xc5e0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xc500, 0x100, 0xc500, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc600, mload(0x1b20))
mstore(0xc620, mload(0x1b40))
mstore(0xc640, mload(0x1b60))
mstore(0xc660, mload(0x1b80))
                }
mstore(0xc680, mload(0x8980))

        {
            let scalar := mload(0xc680)
            let is_inf := and(
                and(eq(mload(0xc600), 0), eq(mload(0xc620), 0)),
                and(eq(mload(0xc640), 0), eq(mload(0xc660), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xc600, 0)
                mstore(0xc620, 0)
                mstore(0xc640, 0)
                mstore(0xc660, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xc600, 0xa0, 0xc600, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc6a0, mload(0xc500))
mstore(0xc6c0, mload(0xc520))
mstore(0xc6e0, mload(0xc540))
mstore(0xc700, mload(0xc560))
                }
{
                    mstore(0xc720, mload(0xc600))
mstore(0xc740, mload(0xc620))
mstore(0xc760, mload(0xc640))
mstore(0xc780, mload(0xc660))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xc6a0), 0), eq(mload(0xc6c0), 0)),
                and(eq(mload(0xc6e0), 0), eq(mload(0xc700), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xc720), 0), eq(mload(0xc740), 0)),
                and(eq(mload(0xc760), 0), eq(mload(0xc780), 0))
            )
            if lhs_inf {
                mstore(0xc6a0, mload(0xc720))
                mstore(0xc6c0, mload(0xc740))
                mstore(0xc6e0, mload(0xc760))
                mstore(0xc700, mload(0xc780))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xc6a0, 0x100, 0xc6a0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc7a0, mload(0x1ba0))
mstore(0xc7c0, mload(0x1bc0))
mstore(0xc7e0, mload(0x1be0))
mstore(0xc800, mload(0x1c00))
                }
mstore(0xc820, mload(0x89a0))

        {
            let scalar := mload(0xc820)
            let is_inf := and(
                and(eq(mload(0xc7a0), 0), eq(mload(0xc7c0), 0)),
                and(eq(mload(0xc7e0), 0), eq(mload(0xc800), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xc7a0, 0)
                mstore(0xc7c0, 0)
                mstore(0xc7e0, 0)
                mstore(0xc800, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xc7a0, 0xa0, 0xc7a0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc840, mload(0xc6a0))
mstore(0xc860, mload(0xc6c0))
mstore(0xc880, mload(0xc6e0))
mstore(0xc8a0, mload(0xc700))
                }
{
                    mstore(0xc8c0, mload(0xc7a0))
mstore(0xc8e0, mload(0xc7c0))
mstore(0xc900, mload(0xc7e0))
mstore(0xc920, mload(0xc800))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xc840), 0), eq(mload(0xc860), 0)),
                and(eq(mload(0xc880), 0), eq(mload(0xc8a0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xc8c0), 0), eq(mload(0xc8e0), 0)),
                and(eq(mload(0xc900), 0), eq(mload(0xc920), 0))
            )
            if lhs_inf {
                mstore(0xc840, mload(0xc8c0))
                mstore(0xc860, mload(0xc8e0))
                mstore(0xc880, mload(0xc900))
                mstore(0xc8a0, mload(0xc920))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xc840, 0x100, 0xc840, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc940, mload(0x1c20))
mstore(0xc960, mload(0x1c40))
mstore(0xc980, mload(0x1c60))
mstore(0xc9a0, mload(0x1c80))
                }
mstore(0xc9c0, mload(0x89c0))

        {
            let scalar := mload(0xc9c0)
            let is_inf := and(
                and(eq(mload(0xc940), 0), eq(mload(0xc960), 0)),
                and(eq(mload(0xc980), 0), eq(mload(0xc9a0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xc940, 0)
                mstore(0xc960, 0)
                mstore(0xc980, 0)
                mstore(0xc9a0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xc940, 0xa0, 0xc940, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xc9e0, mload(0xc840))
mstore(0xca00, mload(0xc860))
mstore(0xca20, mload(0xc880))
mstore(0xca40, mload(0xc8a0))
                }
{
                    mstore(0xca60, mload(0xc940))
mstore(0xca80, mload(0xc960))
mstore(0xcaa0, mload(0xc980))
mstore(0xcac0, mload(0xc9a0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xc9e0), 0), eq(mload(0xca00), 0)),
                and(eq(mload(0xca20), 0), eq(mload(0xca40), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xca60), 0), eq(mload(0xca80), 0)),
                and(eq(mload(0xcaa0), 0), eq(mload(0xcac0), 0))
            )
            if lhs_inf {
                mstore(0xc9e0, mload(0xca60))
                mstore(0xca00, mload(0xca80))
                mstore(0xca20, mload(0xcaa0))
                mstore(0xca40, mload(0xcac0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xc9e0, 0x100, 0xc9e0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xcae0, mload(0x1ca0))
mstore(0xcb00, mload(0x1cc0))
mstore(0xcb20, mload(0x1ce0))
mstore(0xcb40, mload(0x1d00))
                }
mstore(0xcb60, mload(0x89e0))

        {
            let scalar := mload(0xcb60)
            let is_inf := and(
                and(eq(mload(0xcae0), 0), eq(mload(0xcb00), 0)),
                and(eq(mload(0xcb20), 0), eq(mload(0xcb40), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xcae0, 0)
                mstore(0xcb00, 0)
                mstore(0xcb20, 0)
                mstore(0xcb40, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xcae0, 0xa0, 0xcae0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xcb80, mload(0xc9e0))
mstore(0xcba0, mload(0xca00))
mstore(0xcbc0, mload(0xca20))
mstore(0xcbe0, mload(0xca40))
                }
{
                    mstore(0xcc00, mload(0xcae0))
mstore(0xcc20, mload(0xcb00))
mstore(0xcc40, mload(0xcb20))
mstore(0xcc60, mload(0xcb40))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xcb80), 0), eq(mload(0xcba0), 0)),
                and(eq(mload(0xcbc0), 0), eq(mload(0xcbe0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xcc00), 0), eq(mload(0xcc20), 0)),
                and(eq(mload(0xcc40), 0), eq(mload(0xcc60), 0))
            )
            if lhs_inf {
                mstore(0xcb80, mload(0xcc00))
                mstore(0xcba0, mload(0xcc20))
                mstore(0xcbc0, mload(0xcc40))
                mstore(0xcbe0, mload(0xcc60))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xcb80, 0x100, 0xcb80, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xcc80, mload(0x1a40))
mstore(0xcca0, mload(0x1a60))
mstore(0xccc0, mload(0x1a80))
mstore(0xcce0, mload(0x1aa0))
                }
mstore(0xcd00, mload(0x8a00))

        {
            let scalar := mload(0xcd00)
            let is_inf := and(
                and(eq(mload(0xcc80), 0), eq(mload(0xcca0), 0)),
                and(eq(mload(0xccc0), 0), eq(mload(0xcce0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xcc80, 0)
                mstore(0xcca0, 0)
                mstore(0xccc0, 0)
                mstore(0xcce0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xcc80, 0xa0, 0xcc80, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xcd20, mload(0xcb80))
mstore(0xcd40, mload(0xcba0))
mstore(0xcd60, mload(0xcbc0))
mstore(0xcd80, mload(0xcbe0))
                }
{
                    mstore(0xcda0, mload(0xcc80))
mstore(0xcdc0, mload(0xcca0))
mstore(0xcde0, mload(0xccc0))
mstore(0xce00, mload(0xcce0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xcd20), 0), eq(mload(0xcd40), 0)),
                and(eq(mload(0xcd60), 0), eq(mload(0xcd80), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xcda0), 0), eq(mload(0xcdc0), 0)),
                and(eq(mload(0xcde0), 0), eq(mload(0xce00), 0))
            )
            if lhs_inf {
                mstore(0xcd20, mload(0xcda0))
                mstore(0xcd40, mload(0xcdc0))
                mstore(0xcd60, mload(0xcde0))
                mstore(0xcd80, mload(0xce00))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xcd20, 0x100, 0xcd20, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xce20, mload(0x1140))
mstore(0xce40, mload(0x1160))
mstore(0xce60, mload(0x1180))
mstore(0xce80, mload(0x11a0))
                }
mstore(0xcea0, mload(0x8a20))

        {
            let scalar := mload(0xcea0)
            let is_inf := and(
                and(eq(mload(0xce20), 0), eq(mload(0xce40), 0)),
                and(eq(mload(0xce60), 0), eq(mload(0xce80), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xce20, 0)
                mstore(0xce40, 0)
                mstore(0xce60, 0)
                mstore(0xce80, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xce20, 0xa0, 0xce20, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xcec0, mload(0xcd20))
mstore(0xcee0, mload(0xcd40))
mstore(0xcf00, mload(0xcd60))
mstore(0xcf20, mload(0xcd80))
                }
{
                    mstore(0xcf40, mload(0xce20))
mstore(0xcf60, mload(0xce40))
mstore(0xcf80, mload(0xce60))
mstore(0xcfa0, mload(0xce80))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xcec0), 0), eq(mload(0xcee0), 0)),
                and(eq(mload(0xcf00), 0), eq(mload(0xcf20), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xcf40), 0), eq(mload(0xcf60), 0)),
                and(eq(mload(0xcf80), 0), eq(mload(0xcfa0), 0))
            )
            if lhs_inf {
                mstore(0xcec0, mload(0xcf40))
                mstore(0xcee0, mload(0xcf60))
                mstore(0xcf00, mload(0xcf80))
                mstore(0xcf20, mload(0xcfa0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xcec0, 0x100, 0xcec0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xcfc0, mload(0x11c0))
mstore(0xcfe0, mload(0x11e0))
mstore(0xd000, mload(0x1200))
mstore(0xd020, mload(0x1220))
                }
mstore(0xd040, mload(0x8a40))

        {
            let scalar := mload(0xd040)
            let is_inf := and(
                and(eq(mload(0xcfc0), 0), eq(mload(0xcfe0), 0)),
                and(eq(mload(0xd000), 0), eq(mload(0xd020), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xcfc0, 0)
                mstore(0xcfe0, 0)
                mstore(0xd000, 0)
                mstore(0xd020, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xcfc0, 0xa0, 0xcfc0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd060, mload(0xcec0))
mstore(0xd080, mload(0xcee0))
mstore(0xd0a0, mload(0xcf00))
mstore(0xd0c0, mload(0xcf20))
                }
{
                    mstore(0xd0e0, mload(0xcfc0))
mstore(0xd100, mload(0xcfe0))
mstore(0xd120, mload(0xd000))
mstore(0xd140, mload(0xd020))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xd060), 0), eq(mload(0xd080), 0)),
                and(eq(mload(0xd0a0), 0), eq(mload(0xd0c0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xd0e0), 0), eq(mload(0xd100), 0)),
                and(eq(mload(0xd120), 0), eq(mload(0xd140), 0))
            )
            if lhs_inf {
                mstore(0xd060, mload(0xd0e0))
                mstore(0xd080, mload(0xd100))
                mstore(0xd0a0, mload(0xd120))
                mstore(0xd0c0, mload(0xd140))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xd060, 0x100, 0xd060, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd160, mload(0x1240))
mstore(0xd180, mload(0x1260))
mstore(0xd1a0, mload(0x1280))
mstore(0xd1c0, mload(0x12a0))
                }
mstore(0xd1e0, mload(0x8a60))

        {
            let scalar := mload(0xd1e0)
            let is_inf := and(
                and(eq(mload(0xd160), 0), eq(mload(0xd180), 0)),
                and(eq(mload(0xd1a0), 0), eq(mload(0xd1c0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xd160, 0)
                mstore(0xd180, 0)
                mstore(0xd1a0, 0)
                mstore(0xd1c0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xd160, 0xa0, 0xd160, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd200, mload(0xd060))
mstore(0xd220, mload(0xd080))
mstore(0xd240, mload(0xd0a0))
mstore(0xd260, mload(0xd0c0))
                }
{
                    mstore(0xd280, mload(0xd160))
mstore(0xd2a0, mload(0xd180))
mstore(0xd2c0, mload(0xd1a0))
mstore(0xd2e0, mload(0xd1c0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xd200), 0), eq(mload(0xd220), 0)),
                and(eq(mload(0xd240), 0), eq(mload(0xd260), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xd280), 0), eq(mload(0xd2a0), 0)),
                and(eq(mload(0xd2c0), 0), eq(mload(0xd2e0), 0))
            )
            if lhs_inf {
                mstore(0xd200, mload(0xd280))
                mstore(0xd220, mload(0xd2a0))
                mstore(0xd240, mload(0xd2c0))
                mstore(0xd260, mload(0xd2e0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xd200, 0x100, 0xd200, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd300, mload(0x1860))
mstore(0xd320, mload(0x1880))
mstore(0xd340, mload(0x18a0))
mstore(0xd360, mload(0x18c0))
                }
mstore(0xd380, mload(0x8a80))

        {
            let scalar := mload(0xd380)
            let is_inf := and(
                and(eq(mload(0xd300), 0), eq(mload(0xd320), 0)),
                and(eq(mload(0xd340), 0), eq(mload(0xd360), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xd300, 0)
                mstore(0xd320, 0)
                mstore(0xd340, 0)
                mstore(0xd360, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xd300, 0xa0, 0xd300, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd3a0, mload(0xd200))
mstore(0xd3c0, mload(0xd220))
mstore(0xd3e0, mload(0xd240))
mstore(0xd400, mload(0xd260))
                }
{
                    mstore(0xd420, mload(0xd300))
mstore(0xd440, mload(0xd320))
mstore(0xd460, mload(0xd340))
mstore(0xd480, mload(0xd360))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xd3a0), 0), eq(mload(0xd3c0), 0)),
                and(eq(mload(0xd3e0), 0), eq(mload(0xd400), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xd420), 0), eq(mload(0xd440), 0)),
                and(eq(mload(0xd460), 0), eq(mload(0xd480), 0))
            )
            if lhs_inf {
                mstore(0xd3a0, mload(0xd420))
                mstore(0xd3c0, mload(0xd440))
                mstore(0xd3e0, mload(0xd460))
                mstore(0xd400, mload(0xd480))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xd3a0, 0x100, 0xd3a0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd4a0, mload(0x18e0))
mstore(0xd4c0, mload(0x1900))
mstore(0xd4e0, mload(0x1920))
mstore(0xd500, mload(0x1940))
                }
mstore(0xd520, mload(0x8aa0))

        {
            let scalar := mload(0xd520)
            let is_inf := and(
                and(eq(mload(0xd4a0), 0), eq(mload(0xd4c0), 0)),
                and(eq(mload(0xd4e0), 0), eq(mload(0xd500), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xd4a0, 0)
                mstore(0xd4c0, 0)
                mstore(0xd4e0, 0)
                mstore(0xd500, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xd4a0, 0xa0, 0xd4a0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd540, mload(0xd3a0))
mstore(0xd560, mload(0xd3c0))
mstore(0xd580, mload(0xd3e0))
mstore(0xd5a0, mload(0xd400))
                }
{
                    mstore(0xd5c0, mload(0xd4a0))
mstore(0xd5e0, mload(0xd4c0))
mstore(0xd600, mload(0xd4e0))
mstore(0xd620, mload(0xd500))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xd540), 0), eq(mload(0xd560), 0)),
                and(eq(mload(0xd580), 0), eq(mload(0xd5a0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xd5c0), 0), eq(mload(0xd5e0), 0)),
                and(eq(mload(0xd600), 0), eq(mload(0xd620), 0))
            )
            if lhs_inf {
                mstore(0xd540, mload(0xd5c0))
                mstore(0xd560, mload(0xd5e0))
                mstore(0xd580, mload(0xd600))
                mstore(0xd5a0, mload(0xd620))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xd540, 0x100, 0xd540, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd640, mload(0x1760))
mstore(0xd660, mload(0x1780))
mstore(0xd680, mload(0x17a0))
mstore(0xd6a0, mload(0x17c0))
                }
mstore(0xd6c0, mload(0x8ac0))

        {
            let scalar := mload(0xd6c0)
            let is_inf := and(
                and(eq(mload(0xd640), 0), eq(mload(0xd660), 0)),
                and(eq(mload(0xd680), 0), eq(mload(0xd6a0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xd640, 0)
                mstore(0xd660, 0)
                mstore(0xd680, 0)
                mstore(0xd6a0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xd640, 0xa0, 0xd640, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd6e0, mload(0xd540))
mstore(0xd700, mload(0xd560))
mstore(0xd720, mload(0xd580))
mstore(0xd740, mload(0xd5a0))
                }
{
                    mstore(0xd760, mload(0xd640))
mstore(0xd780, mload(0xd660))
mstore(0xd7a0, mload(0xd680))
mstore(0xd7c0, mload(0xd6a0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xd6e0), 0), eq(mload(0xd700), 0)),
                and(eq(mload(0xd720), 0), eq(mload(0xd740), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xd760), 0), eq(mload(0xd780), 0)),
                and(eq(mload(0xd7a0), 0), eq(mload(0xd7c0), 0))
            )
            if lhs_inf {
                mstore(0xd6e0, mload(0xd760))
                mstore(0xd700, mload(0xd780))
                mstore(0xd720, mload(0xd7a0))
                mstore(0xd740, mload(0xd7c0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xd6e0, 0x100, 0xd6e0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd7e0, mload(0x17e0))
mstore(0xd800, mload(0x1800))
mstore(0xd820, mload(0x1820))
mstore(0xd840, mload(0x1840))
                }
mstore(0xd860, mload(0x8ae0))

        {
            let scalar := mload(0xd860)
            let is_inf := and(
                and(eq(mload(0xd7e0), 0), eq(mload(0xd800), 0)),
                and(eq(mload(0xd820), 0), eq(mload(0xd840), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xd7e0, 0)
                mstore(0xd800, 0)
                mstore(0xd820, 0)
                mstore(0xd840, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xd7e0, 0xa0, 0xd7e0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd880, mload(0xd6e0))
mstore(0xd8a0, mload(0xd700))
mstore(0xd8c0, mload(0xd720))
mstore(0xd8e0, mload(0xd740))
                }
{
                    mstore(0xd900, mload(0xd7e0))
mstore(0xd920, mload(0xd800))
mstore(0xd940, mload(0xd820))
mstore(0xd960, mload(0xd840))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xd880), 0), eq(mload(0xd8a0), 0)),
                and(eq(mload(0xd8c0), 0), eq(mload(0xd8e0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xd900), 0), eq(mload(0xd920), 0)),
                and(eq(mload(0xd940), 0), eq(mload(0xd960), 0))
            )
            if lhs_inf {
                mstore(0xd880, mload(0xd900))
                mstore(0xd8a0, mload(0xd920))
                mstore(0xd8c0, mload(0xd940))
                mstore(0xd8e0, mload(0xd960))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xd880, 0x100, 0xd880, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xd980, mload(0x15a0))
mstore(0xd9a0, mload(0x15c0))
mstore(0xd9c0, mload(0x15e0))
mstore(0xd9e0, mload(0x1600))
                }
mstore(0xda00, mload(0x8b00))

        {
            let scalar := mload(0xda00)
            let is_inf := and(
                and(eq(mload(0xd980), 0), eq(mload(0xd9a0), 0)),
                and(eq(mload(0xd9c0), 0), eq(mload(0xd9e0), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xd980, 0)
                mstore(0xd9a0, 0)
                mstore(0xd9c0, 0)
                mstore(0xd9e0, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xd980, 0xa0, 0xd980, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xda20, mload(0xd880))
mstore(0xda40, mload(0xd8a0))
mstore(0xda60, mload(0xd8c0))
mstore(0xda80, mload(0xd8e0))
                }
{
                    mstore(0xdaa0, mload(0xd980))
mstore(0xdac0, mload(0xd9a0))
mstore(0xdae0, mload(0xd9c0))
mstore(0xdb00, mload(0xd9e0))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xda20), 0), eq(mload(0xda40), 0)),
                and(eq(mload(0xda60), 0), eq(mload(0xda80), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xdaa0), 0), eq(mload(0xdac0), 0)),
                and(eq(mload(0xdae0), 0), eq(mload(0xdb00), 0))
            )
            if lhs_inf {
                mstore(0xda20, mload(0xdaa0))
                mstore(0xda40, mload(0xdac0))
                mstore(0xda60, mload(0xdae0))
                mstore(0xda80, mload(0xdb00))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xda20, 0x100, 0xda20, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xdb20, mload(0x2500))
mstore(0xdb40, mload(0x2520))
mstore(0xdb60, mload(0x2540))
mstore(0xdb80, mload(0x2560))
                }
mstore(0xdba0, mload(0x8b20))

        {
            let scalar := mload(0xdba0)
            let is_inf := and(
                and(eq(mload(0xdb20), 0), eq(mload(0xdb40), 0)),
                and(eq(mload(0xdb60), 0), eq(mload(0xdb80), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xdb20, 0)
                mstore(0xdb40, 0)
                mstore(0xdb60, 0)
                mstore(0xdb80, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xdb20, 0xa0, 0xdb20, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xdbc0, mload(0xda20))
mstore(0xdbe0, mload(0xda40))
mstore(0xdc00, mload(0xda60))
mstore(0xdc20, mload(0xda80))
                }
{
                    mstore(0xdc40, mload(0xdb20))
mstore(0xdc60, mload(0xdb40))
mstore(0xdc80, mload(0xdb60))
mstore(0xdca0, mload(0xdb80))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xdbc0), 0), eq(mload(0xdbe0), 0)),
                and(eq(mload(0xdc00), 0), eq(mload(0xdc20), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xdc40), 0), eq(mload(0xdc60), 0)),
                and(eq(mload(0xdc80), 0), eq(mload(0xdca0), 0))
            )
            if lhs_inf {
                mstore(0xdbc0, mload(0xdc40))
                mstore(0xdbe0, mload(0xdc60))
                mstore(0xdc00, mload(0xdc80))
                mstore(0xdc20, mload(0xdca0))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xdbc0, 0x100, 0xdbc0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xdcc0, mload(0x26c0))
mstore(0xdce0, mload(0x26e0))
mstore(0xdd00, mload(0x2700))
mstore(0xdd20, mload(0x2720))
                }
mstore(0xdd40, mload(0x8c80))

        {
            let scalar := mload(0xdd40)
            let is_inf := and(
                and(eq(mload(0xdcc0), 0), eq(mload(0xdce0), 0)),
                and(eq(mload(0xdd00), 0), eq(mload(0xdd20), 0))
            )
            let should_skip := or(is_inf, eq(scalar, 0))
            if should_skip {
                mstore(0xdcc0, 0)
                mstore(0xdce0, 0)
                mstore(0xdd00, 0)
                mstore(0xdd20, 0)
            }
            if iszero(should_skip) {
                success := and(
                    eq(staticcall(gas(), 0x0c, 0xdcc0, 0xa0, 0xdcc0, 0x80), 1),
                    success
                )
            }
        }
{
                    mstore(0xdd60, mload(0xdbc0))
mstore(0xdd80, mload(0xdbe0))
mstore(0xdda0, mload(0xdc00))
mstore(0xddc0, mload(0xdc20))
                }
{
                    mstore(0xdde0, mload(0xdcc0))
mstore(0xde00, mload(0xdce0))
mstore(0xde20, mload(0xdd00))
mstore(0xde40, mload(0xdd20))
                }

        {
            let lhs_inf := and(
                and(eq(mload(0xdd60), 0), eq(mload(0xdd80), 0)),
                and(eq(mload(0xdda0), 0), eq(mload(0xddc0), 0))
            )
            let rhs_inf := and(
                and(eq(mload(0xdde0), 0), eq(mload(0xde00), 0)),
                and(eq(mload(0xde20), 0), eq(mload(0xde40), 0))
            )
            if lhs_inf {
                mstore(0xdd60, mload(0xdde0))
                mstore(0xdd80, mload(0xde00))
                mstore(0xdda0, mload(0xde20))
                mstore(0xddc0, mload(0xde40))
            }
            if iszero(or(lhs_inf, rhs_inf)) {
                success := and(
                    eq(staticcall(gas(), 0x0b, 0xdd60, 0x100, 0xdd60, 0x80), 1),
                    success
                )
            }
        }

        {
            mstore(0xde60, 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
            mstore(0xde80, 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
            mstore(0xdea0, 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(0xdec0, 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
        }
{
                    mstore(0xdee0, mload(0xdd60))
mstore(0xdf00, mload(0xdd80))
mstore(0xdf20, mload(0xdda0))
mstore(0xdf40, mload(0xddc0))
                }
mstore(0xdf60, 0x00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051)
mstore(0xdf80, 0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8)
mstore(0xdfa0, 0x0000000000000000000000000000000013e02b6052719f607dacd3a088274f65)
mstore(0xdfc0, 0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
mstore(0xdfe0, 0x000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351a)
mstore(0xe000, 0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801)
mstore(0xe020, 0x000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99)
mstore(0xe040, 0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)
{
                    mstore(0xe060, mload(0x26c0))
mstore(0xe080, mload(0x26e0))
mstore(0xe0a0, mload(0x2700))
mstore(0xe0c0, mload(0x2720))
                }
mstore(0xe0e0, 0x0000000000000000000000000000000005e37bfd4b51756e634a544d46fb18f0)
mstore(0xe100, 0x75dc77b3be46e909d4772dd7e95e06802ae2586e08007df9b04fb49038d7c244)
mstore(0xe120, 0x00000000000000000000000000000000055795deea11d5c801728b834307c2e3)
mstore(0xe140, 0x2c8d43443d92d768c897728e7e64c108d546c7324090962dfbd438b32d34e1f7)
mstore(0xe160, 0x00000000000000000000000000000000114f72536c8b3597f17d187275332c06)
mstore(0xe180, 0x91c365591c7caf13653cb9e24e3320135a2483c53689e0e1efbfacbd262a8a81)
mstore(0xe1a0, 0x0000000000000000000000000000000002e900424c3584facb138d93920c1be0)
mstore(0xe1c0, 0xc23adce4a30acc13e87a92a37c814c065f18fd4540619e79b6a61aa41d32a602)
success := and(eq(staticcall(gas(), 0xf, 0xdee0, 0x300, 0xdee0, 0x20), 1), success)
success := and(eq(mload(0xdee0), 1), success)

            // Revert if anything fails
            if iszero(success) { revert(0, 0) }

            // Return empty bytes on success
            return(0, 0)

        }
    }
}
        