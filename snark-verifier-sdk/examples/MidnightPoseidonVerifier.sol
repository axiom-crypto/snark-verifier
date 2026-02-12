
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
            mstore(0x80, 0x0000000000000000000000000000000000ce7a71d780546182fd981bf270c973)
            mstore(0xa0, 0x01045a79650ebb1c4d5023b89d964bb1c0907b6809548b8e43233dbea445cf2c)
            mstore(0xc0, 0x0000000000000000000000000000000010bf3ef7afe726ba6ba16a2d2df5d92d)
            mstore(0xe0, 0x0f4719afc9c6d7b3b003aba23f97b32a1f72847354e1d6b51d62e8799e5027f2)
        }

        {
            mstore(0x100, 0x0000000000000000000000000000000018fb7942645b0dd6afe47e5e8b6f990c)
            mstore(0x120, 0xb84173d720f7eb37077de65dbd97c0d747c547d20df9448a72507e52e2159a50)
            mstore(0x140, 0x0000000000000000000000000000000000c97dc8d52577ffafa942550986775a)
            mstore(0x160, 0x79749498044357d00d1675af4a410639fd3d12cf980a4fafa084187b4d698369)
        }

        {
            mstore(0x180, 0x0000000000000000000000000000000016fbfb3b183d2fd87e34eab335eb8c71)
            mstore(0x1a0, 0x034e666be0a09f64ad4e9daa72cc02c80f61dd026f04eaf2fc41caeeccba83fd)
            mstore(0x1c0, 0x000000000000000000000000000000001268f5cfa13e99c7b58fca9e1a981912)
            mstore(0x1e0, 0x9cc10a1bf612e87a0714271e0fdb30f444027240f791667591520d4c1336f50e)
        }

        {
            mstore(0x200, 0x00000000000000000000000000000000025673455716291e51ab07890604b0d8)
            mstore(0x220, 0x9b41735c17eb62000ebdff7c4fa813d17ff4e0758ccd194e48d4229a332a7c64)
            mstore(0x240, 0x000000000000000000000000000000000b4ba64471fadba16c689d5178d38400)
            mstore(0x260, 0x015eb6f57cf45b6130fedf3880a8c2323164e30d7e0d634486379eba167d6c71)
        }

        {
            mstore(0x280, 0x00000000000000000000000000000000163a374ba62694a19dcc296478a2b530)
            mstore(0x2a0, 0x92adda414c714596445f633e4a7dba27afced83abeaee2fd38e487e5f63388af)
            mstore(0x2c0, 0x000000000000000000000000000000000faa8f9a599d7ca60c7dab6b0f891194)
            mstore(0x2e0, 0x1d720fcd7b30c72eed5a4d7e40ea2c5efd0d777b9ac20acfeeb65f535f26800b)
        }

        {
            mstore(0x300, 0x000000000000000000000000000000000f1d105a0b309b1e059c0cf5c53128b0)
            mstore(0x320, 0xbdfc51fc61df8d4a4e691faa918b18e4e06b6003c982c00906ac8cc9dc5ecf08)
            mstore(0x340, 0x0000000000000000000000000000000015cb05a2c328940a9f68c9631d4c5026)
            mstore(0x360, 0x595b1ecaeb523a910bdab7f7b6bf99565b1f8cb97a57e039b0b20b8d0f5abb4c)
        }

        {
            mstore(0x380, 0x00000000000000000000000000000000152c26c487eba81a71b297fb9f5752dd)
            mstore(0x3a0, 0x02ab23b89801bb29357808be9f6dceee418e5b922cc5146722f3adc561b63cea)
            mstore(0x3c0, 0x0000000000000000000000000000000010e8e3f0929000f496fe103ae2d72c5b)
            mstore(0x3e0, 0xc39f1db40fdbe948ba2c1a0ed7ba19730ec4318267a7b2e47575e92e11698d90)
        }

        {
            mstore(0x400, 0x0000000000000000000000000000000017b227e196019cc78d1889ef9f2c842c)
            mstore(0x420, 0xa193407c7c7af9daf887ba75c056f6d695adc2bac958c1b9bc41ef705be66b9d)
            mstore(0x440, 0x0000000000000000000000000000000007c64ad15c2d171ae189c9582a45bd01)
            mstore(0x460, 0xaa6c149a1d8ce9751e32ad685b0394f6206dba40c3e6b5917d77929596d60895)
        }

        {
            mstore(0x480, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x4a0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x4c0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x4e0, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x500, 0x000000000000000000000000000000000ebf16a84a48a46f8fdb5fd42296af27)
            mstore(0x520, 0x5e721a126b8ca93f6a7b7f212668bfcc9c556f3f772d637619e6bf2c28097a25)
            mstore(0x540, 0x000000000000000000000000000000000b5263e7f0631e3a1758d6906108ce38)
            mstore(0x560, 0x1ea6d13f1012b64e6c3f361831f4d6f1be651791ecfa1ededfa396ff50101879)
        }

        {
            mstore(0x580, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x5a0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x5c0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x5e0, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x600, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x620, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x640, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x660, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x680, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x6a0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x6c0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x6e0, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x700, 0x0000000000000000000000000000000000b2745cd59e1aabdf9548f063a7adae)
            mstore(0x720, 0x80564526eb5bdcb4653a4144f1aabbe30a0002ba6721925951761b0c4583f406)
            mstore(0x740, 0x0000000000000000000000000000000001387e3b0e3a59ce98ddb5e816a0403f)
            mstore(0x760, 0xef60d478b98bfd6cfc1635e5bcb7161ff53abff11ed9ceb9def1267700f42758)
        }

        {
            mstore(0x780, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x7a0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x7c0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x7e0, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x800, 0x00000000000000000000000000000000189f59e453c68d18cf31d2c845bc701b)
            mstore(0x820, 0xf0f36813928c5eab67c26f6dc830704de1ed567c2ecb9e8eac6d1b0a5ab47ab3)
            mstore(0x840, 0x00000000000000000000000000000000091601b206dea62ae527fa5015d9cc00)
            mstore(0x860, 0x392e2b8a6a03b4379856e609eebc239f663c256c61776f7e2c6aa8e89faa601e)
        }

        {
            mstore(0x880, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x8a0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x8c0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x8e0, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }

        {
            mstore(0x900, 0x00000000000000000000000000000000006f0c5ff76f57b682b58f32d9ff5d6f)
            mstore(0x920, 0xfd47593bb4e7b011de63374c0e1b058b1f21d8e1f6ff5e215d88841755a1bd96)
            mstore(0x940, 0x0000000000000000000000000000000019b00b6b151e0707f4935959c53d7ce7)
            mstore(0x960, 0x8f16bc9e8545f9ded55ca6cd5d34f78afa1ebc8715cfc2878b4b7822a2ab904c)
        }

        {
            mstore(0x980, 0x0000000000000000000000000000000011a8b2890a24c6501af494a025830c62)
            mstore(0x9a0, 0x5a77ad1fbbe75b10f5674b2a32b57751b46425fc114f807b11de79778a38b6b7)
            mstore(0x9c0, 0x000000000000000000000000000000000c3aa4b1d86b1e134e9a191ab2040168)
            mstore(0x9e0, 0x4d5b15fb793577253626c68c44c4f2b6eaa30c539635be1cb079f8d6a739d67d)
        }

        {
            mstore(0xa00, 0x00000000000000000000000000000000055c50ac8e0bd6394d502e8dbabc672d)
            mstore(0xa20, 0xd51ebcecd768c262bf857915b21ef9fb9200a1732d541b4516521f2a41eede68)
            mstore(0xa40, 0x00000000000000000000000000000000166965c36271ae35708f39e66a356ddb)
            mstore(0xa60, 0x29d83eb54b747d73b3d86a5b602d07e9ac97d190e89a8a73fd042ef1c1c4465b)
        }

        {
            mstore(0xa80, 0x000000000000000000000000000000000a3b7a65f0447897dd80c26d05285fc5)
            mstore(0xaa0, 0x318f6446fba89fb17fca79e71fa1b12d8f3fa2546caac62d5978014891d76ffe)
            mstore(0xac0, 0x0000000000000000000000000000000009b56de3c36d2e4ca290eddfb697dd9b)
            mstore(0xae0, 0xfd4ca94962386022a845c8164f0c3b57605cd0ba4841ef27901911bfd92f370f)
        }

        {
            mstore(0xb00, 0x00000000000000000000000000000000056a06d87b64fe24e77f6228cdbf89f4)
            mstore(0xb20, 0x02973b0a06c21e2e8d1aeec75c64ff0025b241d9c6205ec75ea14596d9adf5f9)
            mstore(0xb40, 0x0000000000000000000000000000000017abd81af5a25470b3e491c943d2f9e3)
            mstore(0xb60, 0x349c5f8df0844597b3c0208598a7f6f0621f3c73d2d5eafed77c38f090819c3d)
        }

        {
            mstore(0xb80, 0x0000000000000000000000000000000011cdfecd7b77dd45ff2a680e39acbf77)
            mstore(0xba0, 0xadb1a9aae181344da7f9fe7acdf8f6ebd84d3722ec660ccd976d216874b5d725)
            mstore(0xbc0, 0x00000000000000000000000000000000165b2ed3e05f11230d0a6ed889287a09)
            mstore(0xbe0, 0xe8aa8c9fc4ea9022207ed0c596712a0efdf315d8ba9399ccf1f8159981add6d5)
        }

        {
            mstore(0xc00, 0x000000000000000000000000000000000dc09e1b913d822cb6794463b3d5d3fc)
            mstore(0xc20, 0xb3b882c826f32201b6559cd71a2e3b0576ea44d81593ba462fa43721b0c6cd54)
            mstore(0xc40, 0x000000000000000000000000000000000d3e97fcb51c2ae841f66e7c5a13be40)
            mstore(0xc60, 0x72c865f9cb8f2c70ed8431a7a96b39b581ddf38618d6e61081aecabe0700da44)
        }

        {
            mstore(0xc80, 0x000000000000000000000000000000000b7d937296d04bf31aa47faa6cc5f1e3)
            mstore(0xca0, 0xa468272dd0d7321c8ef21b05e47a99408fcb284d63b038573bc3e5618f13215e)
            mstore(0xcc0, 0x000000000000000000000000000000000f72bb03935c205d150ba9687d4e6dc8)
            mstore(0xce0, 0x64ee0e078c7c66a630724d27eacc8cfa75f8a2cc876cf4c98a49caed98aad026)
        }

        {
            mstore(0xd00, 0x0000000000000000000000000000000009a9fc3c5d87c7fca848ae0ef5294188)
            mstore(0xd20, 0xf6eb807f4d4abf4ce351d8ee8b0a849f1f245be2dea6f933f53cbc78c7a8f95a)
            mstore(0xd40, 0x00000000000000000000000000000000141d46894acd70ebc38f9abc0165fa5c)
            mstore(0xd60, 0xad426d42ff80d15da75083f629d1bcf17ae8c36614691c74d86e176ccba55d7f)
        }

        {
            mstore(0xd80, 0x0000000000000000000000000000000015a283c8ea4d194938cc69f9cef3f08f)
            mstore(0xda0, 0xe0cf839b4e99f7519b793a1ea45c5ec6f4d2e92dcd38e18123033c31b9931aa0)
            mstore(0xdc0, 0x00000000000000000000000000000000105a573c240e604040314f82b102aade)
            mstore(0xde0, 0x660d31d238934f8f742798fcf15a8e626e59ede83fa0cd0b85292c198b0ff5cf)
        }

        {
            mstore(0xe20, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0xe40, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0xe60, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0xe80, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }
mstore(0xea0, mod(calldataload(0x0), f_q))
mstore(0xec0, 1179168404063990578546446962809701368832197505566437192077829781686544810249)
{
                    mstore(0xee0, mload(0xe20))
mstore(0xf00, mload(0xe40))
mstore(0xf20, mload(0xe60))
mstore(0xf40, mload(0xe80))
                }
mstore(0xf60, 1)
mstore(0xf80, mload(0xea0))

        {
            mstore(0xfa0, 0)
            mstore(0xfc0, 0)
            mstore(0xfe0, 0)
            mstore(0x1000, 0)
            calldatacopy(0xfb0, 0x20, 0x30)
            calldatacopy(0xff0, 0x50, 0x30)
        }

        {
            mstore(0x1020, 0)
            mstore(0x1040, 0)
            mstore(0x1060, 0)
            mstore(0x1080, 0)
            calldatacopy(0x1030, 0x80, 0x30)
            calldatacopy(0x1070, 0xb0, 0x30)
        }

        {
            mstore(0x10a0, 0)
            mstore(0x10c0, 0)
            mstore(0x10e0, 0)
            mstore(0x1100, 0)
            calldatacopy(0x10b0, 0xe0, 0x30)
            calldatacopy(0x10f0, 0x110, 0x30)
        }

        {
            mstore(0x1120, 0)
            mstore(0x1140, 0)
            mstore(0x1160, 0)
            mstore(0x1180, 0)
            calldatacopy(0x1130, 0x140, 0x30)
            calldatacopy(0x1170, 0x170, 0x30)
        }

        {
            mstore(0x11a0, 0)
            mstore(0x11c0, 0)
            mstore(0x11e0, 0)
            mstore(0x1200, 0)
            calldatacopy(0x11b0, 0x1a0, 0x30)
            calldatacopy(0x11f0, 0x1d0, 0x30)
        }

        {
            mstore(0x1220, 0)
            mstore(0x1240, 0)
            mstore(0x1260, 0)
            mstore(0x1280, 0)
            calldatacopy(0x1230, 0x200, 0x30)
            calldatacopy(0x1270, 0x230, 0x30)
        }

        {
            mstore(0x12a0, 0)
            mstore(0x12c0, 0)
            mstore(0x12e0, 0)
            mstore(0x1300, 0)
            calldatacopy(0x12b0, 0x260, 0x30)
            calldatacopy(0x12f0, 0x290, 0x30)
        }

        {
            mstore(0x1320, 0)
            mstore(0x1340, 0)
            mstore(0x1360, 0)
            mstore(0x1380, 0)
            calldatacopy(0x1330, 0x2c0, 0x30)
            calldatacopy(0x1370, 0x2f0, 0x30)
        }
mstore(0x13a0, keccak256(0xec0, 1248))
{
            let hash := mload(0x13a0)
            mstore(0x13c0, mod(hash, f_q))
            mstore(0x13e0, hash)
        }

        {
            mstore(0x1400, 0)
            mstore(0x1420, 0)
            mstore(0x1440, 0)
            mstore(0x1460, 0)
            calldatacopy(0x1410, 0x320, 0x30)
            calldatacopy(0x1450, 0x350, 0x30)
        }

        {
            mstore(0x1480, 0)
            mstore(0x14a0, 0)
            mstore(0x14c0, 0)
            mstore(0x14e0, 0)
            calldatacopy(0x1490, 0x380, 0x30)
            calldatacopy(0x14d0, 0x3b0, 0x30)
        }
mstore(0x1500, keccak256(0x13e0, 288))
{
            let hash := mload(0x1500)
            mstore(0x1520, mod(hash, f_q))
            mstore(0x1540, hash)
        }
mstore8(5472, 1)
mstore(0x1560, keccak256(0x1540, 33))
{
            let hash := mload(0x1560)
            mstore(0x1580, mod(hash, f_q))
            mstore(0x15a0, hash)
        }

        {
            mstore(0x15c0, 0)
            mstore(0x15e0, 0)
            mstore(0x1600, 0)
            mstore(0x1620, 0)
            calldatacopy(0x15d0, 0x3e0, 0x30)
            calldatacopy(0x1610, 0x410, 0x30)
        }

        {
            mstore(0x1640, 0)
            mstore(0x1660, 0)
            mstore(0x1680, 0)
            mstore(0x16a0, 0)
            calldatacopy(0x1650, 0x440, 0x30)
            calldatacopy(0x1690, 0x470, 0x30)
        }

        {
            mstore(0x16c0, 0)
            mstore(0x16e0, 0)
            mstore(0x1700, 0)
            mstore(0x1720, 0)
            calldatacopy(0x16d0, 0x4a0, 0x30)
            calldatacopy(0x1710, 0x4d0, 0x30)
        }

        {
            mstore(0x1740, 0)
            mstore(0x1760, 0)
            mstore(0x1780, 0)
            mstore(0x17a0, 0)
            calldatacopy(0x1750, 0x500, 0x30)
            calldatacopy(0x1790, 0x530, 0x30)
        }
mstore(0x17c0, keccak256(0x15a0, 544))
{
            let hash := mload(0x17c0)
            mstore(0x17e0, mod(hash, f_q))
            mstore(0x1800, hash)
        }

        {
            mstore(0x1820, 0)
            mstore(0x1840, 0)
            mstore(0x1860, 0)
            mstore(0x1880, 0)
            calldatacopy(0x1830, 0x560, 0x30)
            calldatacopy(0x1870, 0x590, 0x30)
        }

        {
            mstore(0x18a0, 0)
            mstore(0x18c0, 0)
            mstore(0x18e0, 0)
            mstore(0x1900, 0)
            calldatacopy(0x18b0, 0x5c0, 0x30)
            calldatacopy(0x18f0, 0x5f0, 0x30)
        }
mstore(0x1920, keccak256(0x1800, 288))
{
            let hash := mload(0x1920)
            mstore(0x1940, mod(hash, f_q))
            mstore(0x1960, hash)
        }

        {
            mstore(0x1980, 0)
            mstore(0x19a0, 0)
            mstore(0x19c0, 0)
            mstore(0x19e0, 0)
            calldatacopy(0x1990, 0x620, 0x30)
            calldatacopy(0x19d0, 0x650, 0x30)
        }

        {
            mstore(0x1a00, 0)
            mstore(0x1a20, 0)
            mstore(0x1a40, 0)
            mstore(0x1a60, 0)
            calldatacopy(0x1a10, 0x680, 0x30)
            calldatacopy(0x1a50, 0x6b0, 0x30)
        }

        {
            mstore(0x1a80, 0)
            mstore(0x1aa0, 0)
            mstore(0x1ac0, 0)
            mstore(0x1ae0, 0)
            calldatacopy(0x1a90, 0x6e0, 0x30)
            calldatacopy(0x1ad0, 0x710, 0x30)
        }

        {
            mstore(0x1b00, 0)
            mstore(0x1b20, 0)
            mstore(0x1b40, 0)
            mstore(0x1b60, 0)
            calldatacopy(0x1b10, 0x740, 0x30)
            calldatacopy(0x1b50, 0x770, 0x30)
        }
mstore(0x1b80, keccak256(0x1960, 544))
{
            let hash := mload(0x1b80)
            mstore(0x1ba0, mod(hash, f_q))
            mstore(0x1bc0, hash)
        }
mstore(0x1be0, mod(calldataload(0x7a0), f_q))
mstore(0x1c00, mod(calldataload(0x7c0), f_q))
mstore(0x1c20, mod(calldataload(0x7e0), f_q))
mstore(0x1c40, mod(calldataload(0x800), f_q))
mstore(0x1c60, mod(calldataload(0x820), f_q))
mstore(0x1c80, mod(calldataload(0x840), f_q))
mstore(0x1ca0, mod(calldataload(0x860), f_q))
mstore(0x1cc0, mod(calldataload(0x880), f_q))
mstore(0x1ce0, mod(calldataload(0x8a0), f_q))
mstore(0x1d00, mod(calldataload(0x8c0), f_q))
mstore(0x1d20, mod(calldataload(0x8e0), f_q))
mstore(0x1d40, mod(calldataload(0x900), f_q))
mstore(0x1d60, mod(calldataload(0x920), f_q))
mstore(0x1d80, mod(calldataload(0x940), f_q))
mstore(0x1da0, mod(calldataload(0x960), f_q))
mstore(0x1dc0, mod(calldataload(0x980), f_q))
mstore(0x1de0, mod(calldataload(0x9a0), f_q))
mstore(0x1e00, mod(calldataload(0x9c0), f_q))
mstore(0x1e20, mod(calldataload(0x9e0), f_q))
mstore(0x1e40, mod(calldataload(0xa00), f_q))
mstore(0x1e60, mod(calldataload(0xa20), f_q))
mstore(0x1e80, mod(calldataload(0xa40), f_q))
mstore(0x1ea0, mod(calldataload(0xa60), f_q))
mstore(0x1ec0, mod(calldataload(0xa80), f_q))
mstore(0x1ee0, mod(calldataload(0xaa0), f_q))
mstore(0x1f00, mod(calldataload(0xac0), f_q))
mstore(0x1f20, mod(calldataload(0xae0), f_q))
mstore(0x1f40, mod(calldataload(0xb00), f_q))
mstore(0x1f60, mod(calldataload(0xb20), f_q))
mstore(0x1f80, mod(calldataload(0xb40), f_q))
mstore(0x1fa0, mod(calldataload(0xb60), f_q))
mstore(0x1fc0, mod(calldataload(0xb80), f_q))
mstore(0x1fe0, mod(calldataload(0xba0), f_q))
mstore(0x2000, mod(calldataload(0xbc0), f_q))
mstore(0x2020, mod(calldataload(0xbe0), f_q))
mstore(0x2040, mod(calldataload(0xc00), f_q))
mstore(0x2060, mod(calldataload(0xc20), f_q))
mstore(0x2080, mod(calldataload(0xc40), f_q))
mstore(0x20a0, mod(calldataload(0xc60), f_q))
mstore(0x20c0, mod(calldataload(0xc80), f_q))
mstore(0x20e0, mod(calldataload(0xca0), f_q))
mstore(0x2100, mod(calldataload(0xcc0), f_q))
mstore(0x2120, mod(calldataload(0xce0), f_q))
mstore(0x2140, mod(calldataload(0xd00), f_q))
mstore(0x2160, mod(calldataload(0xd20), f_q))
mstore(0x2180, mod(calldataload(0xd40), f_q))
mstore(0x21a0, mod(calldataload(0xd60), f_q))
mstore(0x21c0, mod(calldataload(0xd80), f_q))
mstore(0x21e0, mod(calldataload(0xda0), f_q))
mstore(0x2200, mod(calldataload(0xdc0), f_q))
mstore(0x2220, mod(calldataload(0xde0), f_q))
mstore(0x2240, mod(calldataload(0xe00), f_q))
mstore(0x2260, mod(calldataload(0xe20), f_q))
mstore(0x2280, mod(calldataload(0xe40), f_q))
mstore(0x22a0, keccak256(0x1bc0, 1760))
{
            let hash := mload(0x22a0)
            mstore(0x22c0, mod(hash, f_q))
            mstore(0x22e0, hash)
        }
mstore8(8960, 1)
mstore(0x2300, keccak256(0x22e0, 33))
{
            let hash := mload(0x2300)
            mstore(0x2320, mod(hash, f_q))
            mstore(0x2340, hash)
        }

        {
            mstore(0x2360, 0)
            mstore(0x2380, 0)
            mstore(0x23a0, 0)
            mstore(0x23c0, 0)
            calldatacopy(0x2370, 0xe60, 0x30)
            calldatacopy(0x23b0, 0xe90, 0x30)
        }
mstore(0x23e0, keccak256(0x2340, 160))
{
            let hash := mload(0x23e0)
            mstore(0x2400, mod(hash, f_q))
            mstore(0x2420, hash)
        }
mstore(0x2440, mod(calldataload(0xec0), f_q))
mstore(0x2460, mod(calldataload(0xee0), f_q))
mstore(0x2480, mod(calldataload(0xf00), f_q))
mstore(0x24a0, mod(calldataload(0xf20), f_q))
mstore(0x24c0, keccak256(0x2420, 160))
{
            let hash := mload(0x24c0)
            mstore(0x24e0, mod(hash, f_q))
            mstore(0x2500, hash)
        }

        {
            mstore(0x2520, 0)
            mstore(0x2540, 0)
            mstore(0x2560, 0)
            mstore(0x2580, 0)
            calldatacopy(0x2530, 0xf40, 0x30)
            calldatacopy(0x2570, 0xf70, 0x30)
        }

        {
            mstore(0x25a0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x25c0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x25e0, 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(0x2600, 0x0000000000000000000000000000000000000000000000000000000000000000)
        }
mstore(0x2620, mulmod(mload(0x1ba0), mload(0x1ba0), f_q))
mstore(0x2640, mulmod(mload(0x2620), mload(0x2620), f_q))
mstore(0x2660, mulmod(mload(0x2640), mload(0x2640), f_q))
mstore(0x2680, mulmod(mload(0x2660), mload(0x2660), f_q))
mstore(0x26a0, mulmod(mload(0x2680), mload(0x2680), f_q))
mstore(0x26c0, mulmod(mload(0x26a0), mload(0x26a0), f_q))
mstore(0x26e0, addmod(mload(0x26c0), 52435875175126190479447740508185965837690552500527637822603658699938581184512, f_q))
mstore(0x2700, mulmod(mload(0x26e0), 51616564625514843753206369562745560121476637617706893481625476532752040853505, f_q))
mstore(0x2720, mulmod(mload(0x2700), 21259823323969146045885553965890482219221908228759787200404479960115227367690, f_q))
mstore(0x2740, addmod(mload(0x1ba0), 31176051851157044433562186542295483618468644271767850622199178739823353816823, f_q))
mstore(0x2760, mulmod(mload(0x2700), 14887102955893838413024403264664292195708703256831905665143363416435654328648, f_q))
mstore(0x2780, addmod(mload(0x1ba0), 37548772219232352066423337243521673641981849243695732157460295283502926855865, f_q))
mstore(0x27a0, mulmod(mload(0x2700), 2527721918302134385520002926840515195543678449692795676238296383251703745807, f_q))
mstore(0x27c0, addmod(mload(0x1ba0), 49908153256824056093927737581345450642146874050834842146365362316686877438706, f_q))
mstore(0x27e0, mulmod(mload(0x2700), 26753076894533791554649012143113393549300550745003194222677083919072199473480, f_q))
mstore(0x2800, addmod(mload(0x1ba0), 25682798280592398924798728365072572288390001755524443599926574780866381711033, f_q))
mstore(0x2820, mulmod(mload(0x2700), 7500590202698556019030633716209352927214297656990813043538655792743940636058, f_q))
mstore(0x2840, addmod(mload(0x1ba0), 44935284972427634460417106791976612910476254843536824779065002907194640548455, f_q))
mstore(0x2860, mulmod(mload(0x2700), 42722234674624019897108426302713230860602919991722520098540931937949837992684, f_q))
mstore(0x2880, addmod(mload(0x1ba0), 9713640500502170582339314205472734977087632508805117724062726761988743191829, f_q))
mstore(0x28a0, mulmod(mload(0x2700), 45254319123522011116259460062854627366454101350769349111320208945036885998124, f_q))
mstore(0x28c0, addmod(mload(0x1ba0), 7181556051604179363188280445331338471236451149758288711283449754901695186389, f_q))
mstore(0x28e0, mulmod(mload(0x2700), 1, f_q))
mstore(0x2900, addmod(mload(0x1ba0), 52435875175126190479447740508185965837690552500527637822603658699938581184512, f_q))
{
            let prod := mload(0x2740)

                prod := mulmod(mload(0x2780), prod, f_q)
                mstore(0x2920, prod)
            
                prod := mulmod(mload(0x27c0), prod, f_q)
                mstore(0x2940, prod)
            
                prod := mulmod(mload(0x2800), prod, f_q)
                mstore(0x2960, prod)
            
                prod := mulmod(mload(0x2840), prod, f_q)
                mstore(0x2980, prod)
            
                prod := mulmod(mload(0x2880), prod, f_q)
                mstore(0x29a0, prod)
            
                prod := mulmod(mload(0x28c0), prod, f_q)
                mstore(0x29c0, prod)
            
                prod := mulmod(mload(0x2900), prod, f_q)
                mstore(0x29e0, prod)
            
                prod := mulmod(mload(0x26e0), prod, f_q)
                mstore(0x2a00, prod)
            
        }
mstore(0x2a40, 32)
mstore(0x2a60, 32)
mstore(0x2a80, 32)
mstore(0x2aa0, mload(0x2a00))
mstore(0x2ac0, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x2ae0, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x2a40, 0xc0, 0x2a20, 0x20), 1), success)
{
            
            let inv := mload(0x2a20)
            let v
        
                    v := mload(0x26e0)
                    mstore(9952, mulmod(mload(0x29e0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x2900)
                    mstore(10496, mulmod(mload(0x29c0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x28c0)
                    mstore(10432, mulmod(mload(0x29a0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x2880)
                    mstore(10368, mulmod(mload(0x2980), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x2840)
                    mstore(10304, mulmod(mload(0x2960), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x2800)
                    mstore(10240, mulmod(mload(0x2940), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x27c0)
                    mstore(10176, mulmod(mload(0x2920), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x2780)
                    mstore(10112, mulmod(mload(0x2740), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                mstore(0x2740, inv)

        }
mstore(0x2b00, mulmod(mload(0x2720), mload(0x2740), f_q))
mstore(0x2b20, mulmod(mload(0x2760), mload(0x2780), f_q))
mstore(0x2b40, mulmod(mload(0x27a0), mload(0x27c0), f_q))
mstore(0x2b60, mulmod(mload(0x27e0), mload(0x2800), f_q))
mstore(0x2b80, mulmod(mload(0x2820), mload(0x2840), f_q))
mstore(0x2ba0, mulmod(mload(0x2860), mload(0x2880), f_q))
mstore(0x2bc0, mulmod(mload(0x28a0), mload(0x28c0), f_q))
mstore(0x2be0, mulmod(mload(0x28e0), mload(0x2900), f_q))
{
            let result := mulmod(mload(0x2be0), mload(0xea0), f_q)
mstore(11264, result)
        }
mstore(0x2c20, mulmod(mload(0x1c00), mload(0x1d80), f_q))
mstore(0x2c40, addmod(mload(0x1e80), mload(0x2c20), f_q))
mstore(0x2c60, mulmod(mload(0x1c20), mload(0x1da0), f_q))
mstore(0x2c80, addmod(mload(0x2c40), mload(0x2c60), f_q))
mstore(0x2ca0, mulmod(mload(0x1c40), mload(0x1dc0), f_q))
mstore(0x2cc0, addmod(mload(0x2c80), mload(0x2ca0), f_q))
mstore(0x2ce0, mulmod(mload(0x1c60), mload(0x1de0), f_q))
mstore(0x2d00, addmod(mload(0x2cc0), mload(0x2ce0), f_q))
mstore(0x2d20, mulmod(mload(0x1c80), mload(0x1e00), f_q))
mstore(0x2d40, addmod(mload(0x2d00), mload(0x2d20), f_q))
mstore(0x2d60, mulmod(mload(0x1ca0), mload(0x1e20), f_q))
mstore(0x2d80, addmod(mload(0x2d40), mload(0x2d60), f_q))
mstore(0x2da0, mulmod(mload(0x1c00), mload(0x1e40), f_q))
mstore(0x2dc0, mulmod(mload(0x1c20), mload(0x2da0), f_q))
mstore(0x2de0, addmod(mload(0x2d80), mload(0x2dc0), f_q))
mstore(0x2e00, mulmod(mload(0x1c00), mload(0x1e60), f_q))
mstore(0x2e20, mulmod(mload(0x1c40), mload(0x2e00), f_q))
mstore(0x2e40, addmod(mload(0x2de0), mload(0x2e20), f_q))
mstore(0x2e60, mulmod(mload(0x2e40), mload(0x1f00), f_q))
mstore(0x2e80, mulmod(mload(0x1940), mload(0x2e60), f_q))
mstore(0x2ea0, addmod(mload(0x1c20), mload(0x1c40), f_q))
mstore(0x2ec0, addmod(mload(0x2ea0), sub(f_q, mload(0x1c60)), f_q))
mstore(0x2ee0, addmod(mload(0x2ec0), sub(f_q, mload(0x1c80)), f_q))
mstore(0x2f00, mulmod(mload(0x2ee0), mload(0x1f20), f_q))
mstore(0x2f20, addmod(mload(0x2e80), mload(0x2f00), f_q))
mstore(0x2f40, mulmod(mload(0x1940), mload(0x2f20), f_q))
mstore(0x2f60, addmod(mload(0x1c00), mload(0x1d80), f_q))
mstore(0x2f80, addmod(mload(0x2f60), sub(f_q, mload(0x1ca0)), f_q))
mstore(0x2fa0, mulmod(mload(0x2f80), mload(0x1f40), f_q))
mstore(0x2fc0, addmod(mload(0x2f40), mload(0x2fa0), f_q))
mstore(0x2fe0, mulmod(mload(0x1940), mload(0x2fc0), f_q))
mstore(0x3000, addmod(mload(0x1c20), mload(0x1da0), f_q))
mstore(0x3020, addmod(mload(0x3000), sub(f_q, mload(0x1cc0)), f_q))
mstore(0x3040, mulmod(mload(0x3020), mload(0x1f40), f_q))
mstore(0x3060, addmod(mload(0x2fe0), mload(0x3040), f_q))
mstore(0x3080, mulmod(mload(0x1940), mload(0x3060), f_q))
mstore(0x30a0, addmod(mload(0x1c40), mload(0x1dc0), f_q))
mstore(0x30c0, addmod(mload(0x30a0), sub(f_q, mload(0x1ce0)), f_q))
mstore(0x30e0, mulmod(mload(0x30c0), mload(0x1f40), f_q))
mstore(0x3100, addmod(mload(0x3080), mload(0x30e0), f_q))
mstore(0x3120, mulmod(mload(0x1940), mload(0x3100), f_q))
mstore(0x3140, mulmod(mload(0x1c00), mload(0x1c00), f_q))
mstore(0x3160, mulmod(mload(0x3140), mload(0x1c00), f_q))
mstore(0x3180, addmod(mload(0x3160), sub(f_q, mload(0x1c60)), f_q))
mstore(0x31a0, mulmod(mload(0x3180), mload(0x1f80), f_q))
mstore(0x31c0, addmod(mload(0x3120), mload(0x31a0), f_q))
mstore(0x31e0, mulmod(mload(0x1940), mload(0x31c0), f_q))
mstore(0x3200, mulmod(mload(0x1c20), mload(0x1c20), f_q))
mstore(0x3220, mulmod(mload(0x3200), mload(0x1c20), f_q))
mstore(0x3240, addmod(mload(0x3220), sub(f_q, mload(0x1c80)), f_q))
mstore(0x3260, mulmod(mload(0x3240), mload(0x1f80), f_q))
mstore(0x3280, addmod(mload(0x31e0), mload(0x3260), f_q))
mstore(0x32a0, mulmod(mload(0x1940), mload(0x3280), f_q))
mstore(0x32c0, mulmod(mload(0x1c40), mload(0x1c40), f_q))
mstore(0x32e0, mulmod(mload(0x32c0), mload(0x1c40), f_q))
mstore(0x3300, addmod(mload(0x32e0), sub(f_q, mload(0x1d00)), f_q))
mstore(0x3320, mulmod(mload(0x3300), mload(0x1f80), f_q))
mstore(0x3340, addmod(mload(0x32a0), mload(0x3320), f_q))
mstore(0x3360, mulmod(mload(0x1940), mload(0x3340), f_q))
mstore(0x3380, addmod(mload(0x1e20), sub(f_q, mload(0x1ca0)), f_q))
mstore(0x33a0, mulmod(mload(0x1c60), mload(0x3140), f_q))
mstore(0x33c0, mulmod(mload(0x33a0), 12440513488882586407557540066179884648646530011544707182889396930153310132942, f_q))
mstore(0x33e0, addmod(mload(0x3380), mload(0x33c0), f_q))
mstore(0x3400, mulmod(mload(0x1c80), mload(0x3200), f_q))
mstore(0x3420, mulmod(mload(0x3400), 28020747150333089913259220781304558809551608596314918030152947066915898054499, f_q))
mstore(0x3440, addmod(mload(0x33e0), mload(0x3420), f_q))
mstore(0x3460, mulmod(mload(0x1d00), mload(0x32c0), f_q))
mstore(0x3480, mulmod(mload(0x3460), 28505902463311974130913002774524928623644005505993681602486681565155683331521, f_q))
mstore(0x34a0, addmod(mload(0x3440), mload(0x3480), f_q))
mstore(0x34c0, mulmod(mload(0x34a0), mload(0x1f80), f_q))
mstore(0x34e0, addmod(mload(0x3360), mload(0x34c0), f_q))
mstore(0x3500, mulmod(mload(0x1940), mload(0x34e0), f_q))
mstore(0x3520, addmod(mload(0x1e40), sub(f_q, mload(0x1cc0)), f_q))
mstore(0x3540, mulmod(mload(0x33a0), 29084297485723905200880885323289986130569887053242706304266829364413965316980, f_q))
mstore(0x3560, addmod(mload(0x3520), mload(0x3540), f_q))
mstore(0x3580, mulmod(mload(0x3400), 5054565981041632243581284853746902850980503096245579875276544410572564089329, f_q))
mstore(0x35a0, addmod(mload(0x3560), mload(0x3580), f_q))
mstore(0x35c0, mulmod(mload(0x3460), 7179405695647424344643177657798954274869382720335107962712222495241823787551, f_q))
mstore(0x35e0, addmod(mload(0x35a0), mload(0x35c0), f_q))
mstore(0x3600, mulmod(mload(0x35e0), mload(0x1f80), f_q))
mstore(0x3620, addmod(mload(0x3500), mload(0x3600), f_q))
mstore(0x3640, mulmod(mload(0x1940), mload(0x3620), f_q))
mstore(0x3660, addmod(mload(0x1e60), sub(f_q, mload(0x1ce0)), f_q))
mstore(0x3680, mulmod(mload(0x33a0), 42569072482279996318031820844820583094661593761988851871644829917446303682880, f_q))
mstore(0x36a0, addmod(mload(0x3660), mload(0x3680), f_q))
mstore(0x36c0, mulmod(mload(0x3400), 48777675531739959342114240072267441286903816384223937749440830379544192657290, f_q))
mstore(0x36e0, addmod(mload(0x36a0), mload(0x36c0), f_q))
mstore(0x3700, mulmod(mload(0x3460), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x3720, addmod(mload(0x36e0), mload(0x3700), f_q))
mstore(0x3740, mulmod(mload(0x3720), mload(0x1f80), f_q))
mstore(0x3760, addmod(mload(0x3640), mload(0x3740), f_q))
mstore(0x3780, mulmod(mload(0x1940), mload(0x3760), f_q))
mstore(0x37a0, addmod(1, sub(f_q, mload(0x20e0)), f_q))
mstore(0x37c0, mulmod(mload(0x37a0), mload(0x2be0), f_q))
mstore(0x37e0, addmod(mload(0x3780), mload(0x37c0), f_q))
mstore(0x3800, mulmod(mload(0x1940), mload(0x37e0), f_q))
mstore(0x3820, mulmod(mload(0x21a0), mload(0x21a0), f_q))
mstore(0x3840, addmod(mload(0x3820), sub(f_q, mload(0x21a0)), f_q))
mstore(0x3860, mulmod(mload(0x3840), mload(0x2b00), f_q))
mstore(0x3880, addmod(mload(0x3800), mload(0x3860), f_q))
mstore(0x38a0, mulmod(mload(0x1940), mload(0x3880), f_q))
mstore(0x38c0, addmod(mload(0x2140), sub(f_q, mload(0x2120)), f_q))
mstore(0x38e0, mulmod(mload(0x38c0), mload(0x2be0), f_q))
mstore(0x3900, addmod(mload(0x38a0), mload(0x38e0), f_q))
mstore(0x3920, mulmod(mload(0x1940), mload(0x3900), f_q))
mstore(0x3940, addmod(mload(0x21a0), sub(f_q, mload(0x2180)), f_q))
mstore(0x3960, mulmod(mload(0x3940), mload(0x2be0), f_q))
mstore(0x3980, addmod(mload(0x3920), mload(0x3960), f_q))
mstore(0x39a0, mulmod(mload(0x1940), mload(0x3980), f_q))
mstore(0x39c0, addmod(1, sub(f_q, mload(0x2b00)), f_q))
mstore(0x39e0, addmod(mload(0x2b20), mload(0x2b40), f_q))
mstore(0x3a00, addmod(mload(0x39e0), mload(0x2b60), f_q))
mstore(0x3a20, addmod(mload(0x3a00), mload(0x2b80), f_q))
mstore(0x3a40, addmod(mload(0x3a20), mload(0x2ba0), f_q))
mstore(0x3a60, addmod(mload(0x3a40), mload(0x2bc0), f_q))
mstore(0x3a80, addmod(mload(0x39c0), sub(f_q, mload(0x3a60)), f_q))
mstore(0x3aa0, mulmod(mload(0x1fe0), mload(0x1520), f_q))
mstore(0x3ac0, addmod(mload(0x1d60), mload(0x3aa0), f_q))
mstore(0x3ae0, addmod(mload(0x3ac0), mload(0x1580), f_q))
mstore(0x3b00, mulmod(mload(0x2000), mload(0x1520), f_q))
mstore(0x3b20, addmod(mload(0x1c00), mload(0x3b00), f_q))
mstore(0x3b40, addmod(mload(0x3b20), mload(0x1580), f_q))
mstore(0x3b60, mulmod(mload(0x3b40), mload(0x3ae0), f_q))
mstore(0x3b80, mulmod(mload(0x2020), mload(0x1520), f_q))
mstore(0x3ba0, addmod(mload(0x1c20), mload(0x3b80), f_q))
mstore(0x3bc0, addmod(mload(0x3ba0), mload(0x1580), f_q))
mstore(0x3be0, mulmod(mload(0x3bc0), mload(0x3b60), f_q))
mstore(0x3c00, mulmod(mload(0x3be0), mload(0x2100), f_q))
mstore(0x3c20, mulmod(1, mload(0x1520), f_q))
mstore(0x3c40, mulmod(mload(0x1ba0), mload(0x3c20), f_q))
mstore(0x3c60, addmod(mload(0x1d60), mload(0x3c40), f_q))
mstore(0x3c80, addmod(mload(0x3c60), mload(0x1580), f_q))
mstore(0x3ca0, mulmod(3793952369011177517951424454785176000433849974408744014172535497121832470999, mload(0x1520), f_q))
mstore(0x3cc0, mulmod(mload(0x1ba0), mload(0x3ca0), f_q))
mstore(0x3ce0, addmod(mload(0x1c00), mload(0x3cc0), f_q))
mstore(0x3d00, addmod(mload(0x3ce0), mload(0x1580), f_q))
mstore(0x3d20, mulmod(mload(0x3d00), mload(0x3c80), f_q))
mstore(0x3d40, mulmod(29260201042546974833203213796440688721049425934417030432187341694347311461130, mload(0x1520), f_q))
mstore(0x3d60, mulmod(mload(0x1ba0), mload(0x3d40), f_q))
mstore(0x3d80, addmod(mload(0x1c20), mload(0x3d60), f_q))
mstore(0x3da0, addmod(mload(0x3d80), mload(0x1580), f_q))
mstore(0x3dc0, mulmod(mload(0x3da0), mload(0x3d20), f_q))
mstore(0x3de0, mulmod(mload(0x3dc0), mload(0x20e0), f_q))
mstore(0x3e00, addmod(mload(0x3c00), sub(f_q, mload(0x3de0)), f_q))
mstore(0x3e20, mulmod(mload(0x3e00), mload(0x3a80), f_q))
mstore(0x3e40, addmod(mload(0x39a0), mload(0x3e20), f_q))
mstore(0x3e60, mulmod(mload(0x1940), mload(0x3e40), f_q))
mstore(0x3e80, mulmod(mload(0x2040), mload(0x1520), f_q))
mstore(0x3ea0, addmod(mload(0x1c40), mload(0x3e80), f_q))
mstore(0x3ec0, addmod(mload(0x3ea0), mload(0x1580), f_q))
mstore(0x3ee0, mulmod(mload(0x2060), mload(0x1520), f_q))
mstore(0x3f00, addmod(mload(0x1c60), mload(0x3ee0), f_q))
mstore(0x3f20, addmod(mload(0x3f00), mload(0x1580), f_q))
mstore(0x3f40, mulmod(mload(0x3f20), mload(0x3ec0), f_q))
mstore(0x3f60, mulmod(mload(0x2080), mload(0x1520), f_q))
mstore(0x3f80, addmod(mload(0x1c80), mload(0x3f60), f_q))
mstore(0x3fa0, addmod(mload(0x3f80), mload(0x1580), f_q))
mstore(0x3fc0, mulmod(mload(0x3fa0), mload(0x3f40), f_q))
mstore(0x3fe0, mulmod(mload(0x3fc0), mload(0x2160), f_q))
mstore(0x4000, mulmod(30087697416233164107364529847082617342382024227044140347550467692890124986659, mload(0x1520), f_q))
mstore(0x4020, mulmod(mload(0x1ba0), mload(0x4000), f_q))
mstore(0x4040, addmod(mload(0x1c40), mload(0x4020), f_q))
mstore(0x4060, addmod(mload(0x4040), mload(0x1580), f_q))
mstore(0x4080, mulmod(50007016967099397293092916471763530035790684642821601195394169310725916110291, mload(0x1520), f_q))
mstore(0x40a0, mulmod(mload(0x1ba0), mload(0x4080), f_q))
mstore(0x40c0, addmod(mload(0x1c60), mload(0x40a0), f_q))
mstore(0x40e0, addmod(mload(0x40c0), mload(0x1580), f_q))
mstore(0x4100, mulmod(mload(0x40e0), mload(0x4060), f_q))
mstore(0x4120, mulmod(27153057483211730484975145092142082049750746716056827598870820011140481502624, mload(0x1520), f_q))
mstore(0x4140, mulmod(mload(0x1ba0), mload(0x4120), f_q))
mstore(0x4160, addmod(mload(0x1c80), mload(0x4140), f_q))
mstore(0x4180, addmod(mload(0x4160), mload(0x1580), f_q))
mstore(0x41a0, mulmod(mload(0x4180), mload(0x4100), f_q))
mstore(0x41c0, mulmod(mload(0x41a0), mload(0x2140), f_q))
mstore(0x41e0, addmod(mload(0x3fe0), sub(f_q, mload(0x41c0)), f_q))
mstore(0x4200, mulmod(mload(0x41e0), mload(0x3a80), f_q))
mstore(0x4220, addmod(mload(0x3e60), mload(0x4200), f_q))
mstore(0x4240, mulmod(mload(0x1940), mload(0x4220), f_q))
mstore(0x4260, mulmod(mload(0x20a0), mload(0x1520), f_q))
mstore(0x4280, addmod(mload(0x1be0), mload(0x4260), f_q))
mstore(0x42a0, addmod(mload(0x4280), mload(0x1580), f_q))
mstore(0x42c0, mulmod(mload(0x20c0), mload(0x1520), f_q))
mstore(0x42e0, addmod(mload(0x2c00), mload(0x42c0), f_q))
mstore(0x4300, addmod(mload(0x42e0), mload(0x1580), f_q))
mstore(0x4320, mulmod(mload(0x4300), mload(0x42a0), f_q))
mstore(0x4340, mulmod(mload(0x4320), mload(0x21c0), f_q))
mstore(0x4360, mulmod(10702539897433481834547003544093270805576009760020429658622430844384109348913, mload(0x1520), f_q))
mstore(0x4380, mulmod(mload(0x1ba0), mload(0x4360), f_q))
mstore(0x43a0, addmod(mload(0x1be0), mload(0x4380), f_q))
mstore(0x43c0, addmod(mload(0x43a0), mload(0x1580), f_q))
mstore(0x43e0, mulmod(12176195809781855613695208773552147130199916160023471917144658464292859735274, mload(0x1520), f_q))
mstore(0x4400, mulmod(mload(0x1ba0), mload(0x43e0), f_q))
mstore(0x4420, addmod(mload(0x2c00), mload(0x4400), f_q))
mstore(0x4440, addmod(mload(0x4420), mload(0x1580), f_q))
mstore(0x4460, mulmod(mload(0x4440), mload(0x43c0), f_q))
mstore(0x4480, mulmod(mload(0x4460), mload(0x21a0), f_q))
mstore(0x44a0, addmod(mload(0x4340), sub(f_q, mload(0x4480)), f_q))
mstore(0x44c0, mulmod(mload(0x44a0), mload(0x3a80), f_q))
mstore(0x44e0, addmod(mload(0x4240), mload(0x44c0), f_q))
mstore(0x4500, mulmod(mload(0x1940), mload(0x44e0), f_q))
mstore(0x4520, addmod(1, sub(f_q, mload(0x21e0)), f_q))
mstore(0x4540, mulmod(mload(0x4520), mload(0x2be0), f_q))
mstore(0x4560, addmod(mload(0x4500), mload(0x4540), f_q))
mstore(0x4580, mulmod(mload(0x1940), mload(0x4560), f_q))
mstore(0x45a0, mulmod(mload(0x21e0), mload(0x21e0), f_q))
mstore(0x45c0, addmod(mload(0x45a0), sub(f_q, mload(0x21e0)), f_q))
mstore(0x45e0, mulmod(mload(0x45c0), mload(0x2b00), f_q))
mstore(0x4600, addmod(mload(0x4580), mload(0x45e0), f_q))
mstore(0x4620, mulmod(mload(0x1940), mload(0x4600), f_q))
mstore(0x4640, addmod(mload(0x2220), mload(0x1520), f_q))
mstore(0x4660, mulmod(mload(0x4640), mload(0x2200), f_q))
mstore(0x4680, addmod(mload(0x2260), mload(0x1580), f_q))
mstore(0x46a0, mulmod(mload(0x4680), mload(0x4660), f_q))
mstore(0x46c0, mulmod(mload(0x13c0), mload(0x1ea0), f_q))
mstore(0x46e0, mulmod(mload(0x1c20), mload(0x1f60), f_q))
mstore(0x4700, addmod(mload(0x46c0), mload(0x46e0), f_q))
mstore(0x4720, addmod(mload(0x4700), mload(0x1520), f_q))
mstore(0x4740, mulmod(mload(0x4720), mload(0x21e0), f_q))
mstore(0x4760, mulmod(mload(0x13c0), mload(0x1ec0), f_q))
mstore(0x4780, addmod(mload(0x4760), mload(0x1ee0), f_q))
mstore(0x47a0, addmod(mload(0x4780), mload(0x1580), f_q))
mstore(0x47c0, mulmod(mload(0x47a0), mload(0x4740), f_q))
mstore(0x47e0, addmod(mload(0x46a0), sub(f_q, mload(0x47c0)), f_q))
mstore(0x4800, mulmod(mload(0x47e0), mload(0x3a80), f_q))
mstore(0x4820, addmod(mload(0x4620), mload(0x4800), f_q))
mstore(0x4840, mulmod(mload(0x1940), mload(0x4820), f_q))
mstore(0x4860, addmod(mload(0x2220), sub(f_q, mload(0x2260)), f_q))
mstore(0x4880, mulmod(mload(0x4860), mload(0x2be0), f_q))
mstore(0x48a0, addmod(mload(0x4840), mload(0x4880), f_q))
mstore(0x48c0, mulmod(mload(0x1940), mload(0x48a0), f_q))
mstore(0x48e0, mulmod(mload(0x4860), mload(0x3a80), f_q))
mstore(0x4900, addmod(mload(0x2220), sub(f_q, mload(0x2240)), f_q))
mstore(0x4920, mulmod(mload(0x4900), mload(0x48e0), f_q))
mstore(0x4940, addmod(mload(0x48c0), mload(0x4920), f_q))
mstore(0x4960, mulmod(mload(0x1940), mload(0x4940), f_q))
mstore(0x4980, mulmod(mload(0x1c00), 40276410782279108334863105369904789343040261455045516584779277825615697839985, f_q))
mstore(0x49a0, mulmod(mload(0x1c20), 37527016513455530468277088833539226510789135770417315120855317098742889359215, f_q))
mstore(0x49c0, addmod(mload(0x4980), mload(0x49a0), f_q))
mstore(0x49e0, mulmod(mload(0x32c0), mload(0x32c0), f_q))
mstore(0x4a00, mulmod(mload(0x49e0), mload(0x1c40), f_q))
mstore(0x4a20, mulmod(mload(0x4a00), 23990009175532390848383686641478884818239121606019298540653394434675622011304, f_q))
mstore(0x4a40, addmod(mload(0x49c0), mload(0x4a20), f_q))
mstore(0x4a60, mulmod(mload(0x1c60), mload(0x1c60), f_q))
mstore(0x4a80, mulmod(mload(0x4a60), mload(0x4a60), f_q))
mstore(0x4aa0, mulmod(mload(0x4a80), mload(0x1c60), f_q))
mstore(0x4ac0, mulmod(mload(0x4aa0), 23180151978504326669680984036118508621180775988903922469131210268215350444530, f_q))
mstore(0x4ae0, addmod(mload(0x4a40), mload(0x4ac0), f_q))
mstore(0x4b00, mulmod(mload(0x1c80), mload(0x1c80), f_q))
mstore(0x4b20, mulmod(mload(0x4b00), mload(0x4b00), f_q))
mstore(0x4b40, mulmod(mload(0x4b20), mload(0x1c80), f_q))
mstore(0x4b60, mulmod(mload(0x4b40), 29479126442377740792305085857437384138015409209423896273007595542837761281189, f_q))
mstore(0x4b80, addmod(mload(0x4ae0), mload(0x4b60), f_q))
mstore(0x4ba0, mulmod(mload(0x1d00), mload(0x1d00), f_q))
mstore(0x4bc0, mulmod(mload(0x4ba0), mload(0x4ba0), f_q))
mstore(0x4be0, mulmod(mload(0x4bc0), mload(0x1d00), f_q))
mstore(0x4c00, mulmod(mload(0x4be0), 37990615931907094420184937091556956528876595328335061740913699785965517240590, f_q))
mstore(0x4c20, addmod(mload(0x4b80), mload(0x4c00), f_q))
mstore(0x4c40, mulmod(mload(0x1d20), mload(0x1d20), f_q))
mstore(0x4c60, mulmod(mload(0x4c40), mload(0x4c40), f_q))
mstore(0x4c80, mulmod(mload(0x4c60), mload(0x1d20), f_q))
mstore(0x4ca0, mulmod(mload(0x4c80), 3075540889646953729606836824147910283102396481803053667698778232583469493556, f_q))
mstore(0x4cc0, addmod(mload(0x4c20), mload(0x4ca0), f_q))
mstore(0x4ce0, mulmod(mload(0x1d40), mload(0x1d40), f_q))
mstore(0x4d00, mulmod(mload(0x4ce0), mload(0x4ce0), f_q))
mstore(0x4d20, mulmod(mload(0x4d00), mload(0x1d40), f_q))
mstore(0x4d40, mulmod(mload(0x4d20), 28505902463311974130913002774524928623644005505993681602486681565155683331521, f_q))
mstore(0x4d60, addmod(mload(0x4cc0), mload(0x4d40), f_q))
mstore(0x4d80, addmod(mload(0x3380), mload(0x4d60), f_q))
mstore(0x4da0, mulmod(mload(0x17e0), mload(0x4d80), f_q))
mstore(0x4dc0, mulmod(mload(0x1c00), 41216583078069907292136355165153270142521178992429414226155254333730607536733, f_q))
mstore(0x4de0, mulmod(mload(0x1c20), 34853984525125276266590937240908152702715112008598809217765432339048892301352, f_q))
mstore(0x4e00, addmod(mload(0x4dc0), mload(0x4de0), f_q))
mstore(0x4e20, mulmod(mload(0x4a00), 17548561380688843065348281029305916198268522889382278651903462232179510668048, f_q))
mstore(0x4e40, addmod(mload(0x4e00), mload(0x4e20), f_q))
mstore(0x4e60, mulmod(mload(0x4aa0), 22573484092096950280151461091492173066588738155952808584348937425179801521445, f_q))
mstore(0x4e80, addmod(mload(0x4e40), mload(0x4e60), f_q))
mstore(0x4ea0, mulmod(mload(0x4b40), 17799439645526593468527852005527707639891232191326421130080209212181800663685, f_q))
mstore(0x4ec0, addmod(mload(0x4e80), mload(0x4ea0), f_q))
mstore(0x4ee0, mulmod(mload(0x4be0), 43072347715431875659722495403924484570295794297555905065846140476197612812033, f_q))
mstore(0x4f00, addmod(mload(0x4ec0), mload(0x4ee0), f_q))
mstore(0x4f20, mulmod(mload(0x4c80), 21762182386571606640672645248729054582240844218141454043565005480082460585677, f_q))
mstore(0x4f40, addmod(mload(0x4f00), mload(0x4f20), f_q))
mstore(0x4f60, mulmod(mload(0x4d20), 7179405695647424344643177657798954274869382720335107962712222495241823787551, f_q))
mstore(0x4f80, addmod(mload(0x4f40), mload(0x4f60), f_q))
mstore(0x4fa0, addmod(mload(0x3520), mload(0x4f80), f_q))
mstore(0x4fc0, addmod(mload(0x4da0), mload(0x4fa0), f_q))
mstore(0x4fe0, mulmod(mload(0x17e0), mload(0x4fc0), f_q))
mstore(0x5000, addmod(mload(0x1e60), sub(f_q, mload(0x1c60)), f_q))
mstore(0x5020, mulmod(mload(0x1c00), 42569072482279996318031820844820583094661593761988851871644829917446303682880, f_q))
mstore(0x5040, mulmod(mload(0x1c20), 48777675531739959342114240072267441286903816384223937749440830379544192657290, f_q))
mstore(0x5060, addmod(mload(0x5020), mload(0x5040), f_q))
mstore(0x5080, mulmod(mload(0x4a00), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x50a0, addmod(mload(0x5060), mload(0x5080), f_q))
mstore(0x50c0, addmod(mload(0x5000), mload(0x50a0), f_q))
mstore(0x50e0, addmod(mload(0x4fe0), mload(0x50c0), f_q))
mstore(0x5100, mulmod(mload(0x17e0), mload(0x50e0), f_q))
mstore(0x5120, addmod(mload(0x1e80), sub(f_q, mload(0x1c80)), f_q))
mstore(0x5140, mulmod(mload(0x1c00), 15460822173785725787510766083057066620988948322919030231014542645107533362369, f_q))
mstore(0x5160, mulmod(mload(0x1c20), 17532068198837287192548063441235938928456800450058734482970684092419295703441, f_q))
mstore(0x5180, addmod(mload(0x5140), mload(0x5160), f_q))
mstore(0x51a0, mulmod(mload(0x4a00), 30536090514433970940206888994283604712174418989908022047600262784049007297138, f_q))
mstore(0x51c0, addmod(mload(0x5180), mload(0x51a0), f_q))
mstore(0x51e0, mulmod(mload(0x4aa0), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x5200, addmod(mload(0x51c0), mload(0x51e0), f_q))
mstore(0x5220, addmod(mload(0x5120), mload(0x5200), f_q))
mstore(0x5240, addmod(mload(0x5100), mload(0x5220), f_q))
mstore(0x5260, mulmod(mload(0x17e0), mload(0x5240), f_q))
mstore(0x5280, addmod(mload(0x1d80), sub(f_q, mload(0x1d00)), f_q))
mstore(0x52a0, mulmod(mload(0x1c00), 51757916557095931492101637894700153753738985202877927051595743124655465049675, f_q))
mstore(0x52c0, mulmod(mload(0x1c20), 16513270875002105355154055214392863859886533828870466617169669632972895048992, f_q))
mstore(0x52e0, addmod(mload(0x52a0), mload(0x52c0), f_q))
mstore(0x5300, mulmod(mload(0x4a00), 35426167520291240455001880880580845749581081201345737315527923196315309304361, f_q))
mstore(0x5320, addmod(mload(0x52e0), mload(0x5300), f_q))
mstore(0x5340, mulmod(mload(0x4aa0), 30536090514433970940206888994283604712174418989908022047600262784049007297138, f_q))
mstore(0x5360, addmod(mload(0x5320), mload(0x5340), f_q))
mstore(0x5380, mulmod(mload(0x4b40), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x53a0, addmod(mload(0x5360), mload(0x5380), f_q))
mstore(0x53c0, addmod(mload(0x5280), mload(0x53a0), f_q))
mstore(0x53e0, addmod(mload(0x5260), mload(0x53c0), f_q))
mstore(0x5400, mulmod(mload(0x17e0), mload(0x53e0), f_q))
mstore(0x5420, addmod(mload(0x1da0), sub(f_q, mload(0x1d20)), f_q))
mstore(0x5440, mulmod(mload(0x1c00), 21416013269199706780655207523311618433421828314385182423308221541654338163111, f_q))
mstore(0x5460, mulmod(mload(0x1c20), 16124966132388516597090803080166171234527932877010453966457664182846667286567, f_q))
mstore(0x5480, addmod(mload(0x5440), mload(0x5460), f_q))
mstore(0x54a0, mulmod(mload(0x4a00), 11536991632578856038169226946888068627873692153441762213164802460898458963278, f_q))
mstore(0x54c0, addmod(mload(0x5480), mload(0x54a0), f_q))
mstore(0x54e0, mulmod(mload(0x4aa0), 35426167520291240455001880880580845749581081201345737315527923196315309304361, f_q))
mstore(0x5500, addmod(mload(0x54c0), mload(0x54e0), f_q))
mstore(0x5520, mulmod(mload(0x4b40), 30536090514433970940206888994283604712174418989908022047600262784049007297138, f_q))
mstore(0x5540, addmod(mload(0x5500), mload(0x5520), f_q))
mstore(0x5560, mulmod(mload(0x4be0), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x5580, addmod(mload(0x5540), mload(0x5560), f_q))
mstore(0x55a0, addmod(mload(0x5420), mload(0x5580), f_q))
mstore(0x55c0, addmod(mload(0x5400), mload(0x55a0), f_q))
mstore(0x55e0, mulmod(mload(0x17e0), mload(0x55c0), f_q))
mstore(0x5600, addmod(mload(0x1dc0), sub(f_q, mload(0x1d40)), f_q))
mstore(0x5620, mulmod(mload(0x1c00), 49312067300773142348143637644007756944161175278464826357343119536320139437898, f_q))
mstore(0x5640, mulmod(mload(0x1c20), 18048464036633869753218556016152804134446546727997311594407968562256775743561, f_q))
mstore(0x5660, addmod(mload(0x5620), mload(0x5640), f_q))
mstore(0x5680, mulmod(mload(0x4a00), 383932250696541742607310001569714138555014361290971921083431601725621863731, f_q))
mstore(0x56a0, addmod(mload(0x5660), mload(0x5680), f_q))
mstore(0x56c0, mulmod(mload(0x4aa0), 11536991632578856038169226946888068627873692153441762213164802460898458963278, f_q))
mstore(0x56e0, addmod(mload(0x56a0), mload(0x56c0), f_q))
mstore(0x5700, mulmod(mload(0x4b40), 35426167520291240455001880880580845749581081201345737315527923196315309304361, f_q))
mstore(0x5720, addmod(mload(0x56e0), mload(0x5700), f_q))
mstore(0x5740, mulmod(mload(0x4be0), 30536090514433970940206888994283604712174418989908022047600262784049007297138, f_q))
mstore(0x5760, addmod(mload(0x5720), mload(0x5740), f_q))
mstore(0x5780, mulmod(mload(0x4c80), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x57a0, addmod(mload(0x5760), mload(0x5780), f_q))
mstore(0x57c0, addmod(mload(0x5600), mload(0x57a0), f_q))
mstore(0x57e0, addmod(mload(0x55e0), mload(0x57c0), f_q))
mstore(0x5800, mulmod(mload(0x17e0), mload(0x57e0), f_q))
mstore(0x5820, addmod(mload(0x1de0), sub(f_q, mload(0x1ce0)), f_q))
mstore(0x5840, mulmod(mload(0x1c00), 51042352737684322926421982719448027244098131173912330356286361328735472870963, f_q))
mstore(0x5860, mulmod(mload(0x1c20), 29390124884714250559401457937586375728515143848012653816777731013221302010465, f_q))
mstore(0x5880, addmod(mload(0x5840), mload(0x5860), f_q))
mstore(0x58a0, mulmod(mload(0x4a00), 14193443826180214291995136727309819104154361382389237431794542473275951615294, f_q))
mstore(0x58c0, addmod(mload(0x5880), mload(0x58a0), f_q))
mstore(0x58e0, mulmod(mload(0x4aa0), 383932250696541742607310001569714138555014361290971921083431601725621863731, f_q))
mstore(0x5900, addmod(mload(0x58c0), mload(0x58e0), f_q))
mstore(0x5920, mulmod(mload(0x4b40), 11536991632578856038169226946888068627873692153441762213164802460898458963278, f_q))
mstore(0x5940, addmod(mload(0x5900), mload(0x5920), f_q))
mstore(0x5960, mulmod(mload(0x4be0), 35426167520291240455001880880580845749581081201345737315527923196315309304361, f_q))
mstore(0x5980, addmod(mload(0x5940), mload(0x5960), f_q))
mstore(0x59a0, mulmod(mload(0x4c80), 30536090514433970940206888994283604712174418989908022047600262784049007297138, f_q))
mstore(0x59c0, addmod(mload(0x5980), mload(0x59a0), f_q))
mstore(0x59e0, mulmod(mload(0x4d20), 33286996086728685078854749126251163286167502628080690207063928367301359689947, f_q))
mstore(0x5a00, addmod(mload(0x59c0), mload(0x59e0), f_q))
mstore(0x5a20, addmod(mload(0x5820), mload(0x5a00), f_q))
mstore(0x5a40, addmod(mload(0x5800), mload(0x5a20), f_q))
mstore(0x5a60, addmod(1, sub(f_q, mload(0x1fa0)), f_q))
mstore(0x5a80, mulmod(mload(0x2280), mload(0x5a60), f_q))
mstore(0x5aa0, addmod(mload(0x5a40), sub(f_q, mload(0x5a80)), f_q))
mstore(0x5ac0, addmod(mload(0x4960), mload(0x5aa0), f_q))
mstore(0x5b00, 32)
mstore(0x5b20, 32)
mstore(0x5b40, 32)
mstore(0x5b60, mload(0x1ba0))
mstore(0x5b80, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x5ba0, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x5b00, 0xc0, 0x5ae0, 0x20), 1), success)
mstore(0x5bc0, mulmod(mload(0x26c0), mload(0x5ae0), f_q))
mstore(0x5be0, mulmod(mload(0x5bc0), mload(0x5bc0), f_q))
mstore(0x5c00, mulmod(mload(0x5be0), mload(0x5bc0), f_q))
mstore(0x5c20, mulmod(mload(0x5c00), mload(0x5bc0), f_q))
mstore(0x5c40, mulmod(1, mload(0x5bc0), f_q))
mstore(0x5c60, mulmod(1, mload(0x5be0), f_q))
mstore(0x5c80, mulmod(1, mload(0x5c00), f_q))
mstore(0x5ca0, mulmod(mload(0x5ac0), mload(0x26e0), f_q))
mstore(0x5cc0, mulmod(mload(0x1ba0), 1, f_q))
mstore(0x5ce0, mulmod(mload(0x1ba0), 31519469946562159605140591558550197856588417350474800936898404023113662197331, f_q))
mstore(0x5d00, mulmod(mload(0x1ba0), 21259823323969146045885553965890482219221908228759787200404479960115227367690, f_q))
mstore(0x5d20, mulmod(mload(0x1ba0), 45254319123522011116259460062854627366454101350769349111320208945036885998124, f_q))
mstore(0x5d40, mulmod(mload(0x22c0), mload(0x22c0), f_q))
mstore(0x5d60, mulmod(mload(0x5d40), mload(0x22c0), f_q))
mstore(0x5d80, mulmod(mload(0x5d60), mload(0x22c0), f_q))
mstore(0x5da0, mulmod(mload(0x5d80), mload(0x22c0), f_q))
mstore(0x5dc0, mulmod(mload(0x5da0), mload(0x22c0), f_q))
mstore(0x5de0, mulmod(mload(0x5dc0), mload(0x22c0), f_q))
mstore(0x5e00, mulmod(mload(0x5de0), mload(0x22c0), f_q))
mstore(0x5e20, mulmod(mload(0x5e00), mload(0x22c0), f_q))
mstore(0x5e40, mulmod(mload(0x5e20), mload(0x22c0), f_q))
mstore(0x5e60, mulmod(mload(0x5e40), mload(0x22c0), f_q))
mstore(0x5e80, mulmod(mload(0x5e60), mload(0x22c0), f_q))
mstore(0x5ea0, mulmod(mload(0x5e80), mload(0x22c0), f_q))
mstore(0x5ec0, mulmod(mload(0x5ea0), mload(0x22c0), f_q))
mstore(0x5ee0, mulmod(mload(0x5ec0), mload(0x22c0), f_q))
mstore(0x5f00, mulmod(mload(0x5ee0), mload(0x22c0), f_q))
mstore(0x5f20, mulmod(mload(0x5f00), mload(0x22c0), f_q))
mstore(0x5f40, mulmod(mload(0x5f20), mload(0x22c0), f_q))
mstore(0x5f60, mulmod(mload(0x5f40), mload(0x22c0), f_q))
mstore(0x5f80, mulmod(mload(0x5f60), mload(0x22c0), f_q))
mstore(0x5fa0, mulmod(mload(0x5f80), mload(0x22c0), f_q))
mstore(0x5fc0, mulmod(mload(0x5fa0), mload(0x22c0), f_q))
mstore(0x5fe0, mulmod(mload(0x5fc0), mload(0x22c0), f_q))
mstore(0x6000, mulmod(mload(0x5fe0), mload(0x22c0), f_q))
mstore(0x6020, mulmod(mload(0x6000), mload(0x22c0), f_q))
mstore(0x6040, mulmod(mload(0x6020), mload(0x22c0), f_q))
mstore(0x6060, mulmod(mload(0x6040), mload(0x22c0), f_q))
mstore(0x6080, mulmod(mload(0x6060), mload(0x22c0), f_q))
mstore(0x60a0, mulmod(mload(0x6080), mload(0x22c0), f_q))
mstore(0x60c0, mulmod(mload(0x60a0), mload(0x22c0), f_q))
mstore(0x60e0, mulmod(mload(0x60c0), mload(0x22c0), f_q))
mstore(0x6100, mulmod(mload(0x60e0), mload(0x22c0), f_q))
mstore(0x6120, mulmod(mload(0x6100), mload(0x22c0), f_q))
mstore(0x6140, mulmod(mload(0x6120), mload(0x22c0), f_q))
mstore(0x6160, mulmod(mload(0x6140), mload(0x22c0), f_q))
mstore(0x6180, mulmod(mload(0x6160), mload(0x22c0), f_q))
mstore(0x61a0, mulmod(mload(0x6180), mload(0x22c0), f_q))
mstore(0x61c0, mulmod(1, mload(0x22c0), f_q))
mstore(0x61e0, mulmod(1, mload(0x5d40), f_q))
mstore(0x6200, mulmod(1, mload(0x5d60), f_q))
mstore(0x6220, mulmod(1, mload(0x5d80), f_q))
mstore(0x6240, mulmod(1, mload(0x5da0), f_q))
mstore(0x6260, mulmod(1, mload(0x5dc0), f_q))
mstore(0x6280, mulmod(1, mload(0x5de0), f_q))
mstore(0x62a0, mulmod(1, mload(0x5e00), f_q))
mstore(0x62c0, mulmod(1, mload(0x5e20), f_q))
mstore(0x62e0, mulmod(1, mload(0x5e40), f_q))
mstore(0x6300, mulmod(1, mload(0x5e60), f_q))
mstore(0x6320, mulmod(1, mload(0x5e80), f_q))
mstore(0x6340, mulmod(1, mload(0x5ea0), f_q))
mstore(0x6360, mulmod(1, mload(0x5ec0), f_q))
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
mstore(0x6620, mulmod(mload(0x5c40), mload(0x6160), f_q))
mstore(0x6640, mulmod(mload(0x5c60), mload(0x6160), f_q))
mstore(0x6660, mulmod(mload(0x5c80), mload(0x6160), f_q))
mstore(0x6680, mulmod(1, mload(0x6180), f_q))
mstore(0x66a0, mulmod(mload(0x1be0), 1, f_q))
mstore(0x66c0, addmod(0, mload(0x66a0), f_q))
mstore(0x66e0, mulmod(mload(0x1c60), mload(0x22c0), f_q))
mstore(0x6700, addmod(mload(0x66c0), mload(0x66e0), f_q))
mstore(0x6720, mulmod(mload(0x1c80), mload(0x5d40), f_q))
mstore(0x6740, addmod(mload(0x6700), mload(0x6720), f_q))
mstore(0x6760, mulmod(mload(0x1d00), mload(0x5d60), f_q))
mstore(0x6780, addmod(mload(0x6740), mload(0x6760), f_q))
mstore(0x67a0, mulmod(mload(0x1d20), mload(0x5d80), f_q))
mstore(0x67c0, addmod(mload(0x6780), mload(0x67a0), f_q))
mstore(0x67e0, mulmod(mload(0x1d40), mload(0x5da0), f_q))
mstore(0x6800, addmod(mload(0x67c0), mload(0x67e0), f_q))
mstore(0x6820, mulmod(mload(0x2260), mload(0x5dc0), f_q))
mstore(0x6840, addmod(mload(0x6800), mload(0x6820), f_q))
mstore(0x6860, mulmod(mload(0x2280), mload(0x5de0), f_q))
mstore(0x6880, addmod(mload(0x6840), mload(0x6860), f_q))
mstore(0x68a0, mulmod(mload(0x1d60), mload(0x5e00), f_q))
mstore(0x68c0, addmod(mload(0x6880), mload(0x68a0), f_q))
mstore(0x68e0, mulmod(mload(0x1d80), mload(0x5e20), f_q))
mstore(0x6900, addmod(mload(0x68c0), mload(0x68e0), f_q))
mstore(0x6920, mulmod(mload(0x1da0), mload(0x5e40), f_q))
mstore(0x6940, addmod(mload(0x6900), mload(0x6920), f_q))
mstore(0x6960, mulmod(mload(0x1dc0), mload(0x5e60), f_q))
mstore(0x6980, addmod(mload(0x6940), mload(0x6960), f_q))
mstore(0x69a0, mulmod(mload(0x1de0), mload(0x5e80), f_q))
mstore(0x69c0, addmod(mload(0x6980), mload(0x69a0), f_q))
mstore(0x69e0, mulmod(mload(0x1e00), mload(0x5ea0), f_q))
mstore(0x6a00, addmod(mload(0x69c0), mload(0x69e0), f_q))
mstore(0x6a20, mulmod(mload(0x1e20), mload(0x5ec0), f_q))
mstore(0x6a40, addmod(mload(0x6a00), mload(0x6a20), f_q))
mstore(0x6a60, mulmod(mload(0x1e40), mload(0x5ee0), f_q))
mstore(0x6a80, addmod(mload(0x6a40), mload(0x6a60), f_q))
mstore(0x6aa0, mulmod(mload(0x1e60), mload(0x5f00), f_q))
mstore(0x6ac0, addmod(mload(0x6a80), mload(0x6aa0), f_q))
mstore(0x6ae0, mulmod(mload(0x1e80), mload(0x5f20), f_q))
mstore(0x6b00, addmod(mload(0x6ac0), mload(0x6ae0), f_q))
mstore(0x6b20, mulmod(mload(0x1ea0), mload(0x5f40), f_q))
mstore(0x6b40, addmod(mload(0x6b00), mload(0x6b20), f_q))
mstore(0x6b60, mulmod(mload(0x1ec0), mload(0x5f60), f_q))
mstore(0x6b80, addmod(mload(0x6b40), mload(0x6b60), f_q))
mstore(0x6ba0, mulmod(mload(0x1ee0), mload(0x5f80), f_q))
mstore(0x6bc0, addmod(mload(0x6b80), mload(0x6ba0), f_q))
mstore(0x6be0, mulmod(mload(0x1f00), mload(0x5fa0), f_q))
mstore(0x6c00, addmod(mload(0x6bc0), mload(0x6be0), f_q))
mstore(0x6c20, mulmod(mload(0x1f20), mload(0x5fc0), f_q))
mstore(0x6c40, addmod(mload(0x6c00), mload(0x6c20), f_q))
mstore(0x6c60, mulmod(mload(0x1f40), mload(0x5fe0), f_q))
mstore(0x6c80, addmod(mload(0x6c40), mload(0x6c60), f_q))
mstore(0x6ca0, mulmod(mload(0x1f60), mload(0x6000), f_q))
mstore(0x6cc0, addmod(mload(0x6c80), mload(0x6ca0), f_q))
mstore(0x6ce0, mulmod(mload(0x1f80), mload(0x6020), f_q))
mstore(0x6d00, addmod(mload(0x6cc0), mload(0x6ce0), f_q))
mstore(0x6d20, mulmod(mload(0x1fa0), mload(0x6040), f_q))
mstore(0x6d40, addmod(mload(0x6d00), mload(0x6d20), f_q))
mstore(0x6d60, mulmod(mload(0x1fe0), mload(0x6060), f_q))
mstore(0x6d80, addmod(mload(0x6d40), mload(0x6d60), f_q))
mstore(0x6da0, mulmod(mload(0x2000), mload(0x6080), f_q))
mstore(0x6dc0, addmod(mload(0x6d80), mload(0x6da0), f_q))
mstore(0x6de0, mulmod(mload(0x2020), mload(0x60a0), f_q))
mstore(0x6e00, addmod(mload(0x6dc0), mload(0x6de0), f_q))
mstore(0x6e20, mulmod(mload(0x2040), mload(0x60c0), f_q))
mstore(0x6e40, addmod(mload(0x6e00), mload(0x6e20), f_q))
mstore(0x6e60, mulmod(mload(0x2060), mload(0x60e0), f_q))
mstore(0x6e80, addmod(mload(0x6e40), mload(0x6e60), f_q))
mstore(0x6ea0, mulmod(mload(0x2080), mload(0x6100), f_q))
mstore(0x6ec0, addmod(mload(0x6e80), mload(0x6ea0), f_q))
mstore(0x6ee0, mulmod(mload(0x20a0), mload(0x6120), f_q))
mstore(0x6f00, addmod(mload(0x6ec0), mload(0x6ee0), f_q))
mstore(0x6f20, mulmod(mload(0x20c0), mload(0x6140), f_q))
mstore(0x6f40, addmod(mload(0x6f00), mload(0x6f20), f_q))
mstore(0x6f60, mulmod(mload(0x5ca0), mload(0x6160), f_q))
mstore(0x6f80, addmod(mload(0x6f40), mload(0x6f60), f_q))
mstore(0x6fa0, mulmod(mload(0x1fc0), mload(0x6180), f_q))
mstore(0x6fc0, addmod(mload(0x6f80), mload(0x6fa0), f_q))
mstore(0x6fe0, mulmod(mload(0x1c00), 1, f_q))
mstore(0x7000, addmod(0, mload(0x6fe0), f_q))
mstore(0x7020, mulmod(mload(0x1ca0), 1, f_q))
mstore(0x7040, addmod(0, mload(0x7020), f_q))
mstore(0x7060, mulmod(mload(0x1c20), mload(0x22c0), f_q))
mstore(0x7080, addmod(mload(0x7000), mload(0x7060), f_q))
mstore(0x70a0, mulmod(mload(0x1cc0), mload(0x22c0), f_q))
mstore(0x70c0, addmod(mload(0x7040), mload(0x70a0), f_q))
mstore(0x70e0, mulmod(mload(0x1c40), mload(0x5d40), f_q))
mstore(0x7100, addmod(mload(0x7080), mload(0x70e0), f_q))
mstore(0x7120, mulmod(mload(0x1ce0), mload(0x5d40), f_q))
mstore(0x7140, addmod(mload(0x70c0), mload(0x7120), f_q))
mstore(0x7160, mulmod(mload(0x21a0), mload(0x5d60), f_q))
mstore(0x7180, addmod(mload(0x7100), mload(0x7160), f_q))
mstore(0x71a0, mulmod(mload(0x21c0), mload(0x5d60), f_q))
mstore(0x71c0, addmod(mload(0x7140), mload(0x71a0), f_q))
mstore(0x71e0, mulmod(mload(0x21e0), mload(0x5d80), f_q))
mstore(0x7200, addmod(mload(0x7180), mload(0x71e0), f_q))
mstore(0x7220, mulmod(mload(0x2200), mload(0x5d80), f_q))
mstore(0x7240, addmod(mload(0x71c0), mload(0x7220), f_q))
mstore(0x7260, mulmod(mload(0x20e0), 1, f_q))
mstore(0x7280, addmod(0, mload(0x7260), f_q))
mstore(0x72a0, mulmod(mload(0x2100), 1, f_q))
mstore(0x72c0, addmod(0, mload(0x72a0), f_q))
mstore(0x72e0, mulmod(mload(0x2120), 1, f_q))
mstore(0x7300, addmod(0, mload(0x72e0), f_q))
mstore(0x7320, mulmod(mload(0x2140), mload(0x22c0), f_q))
mstore(0x7340, addmod(mload(0x7280), mload(0x7320), f_q))
mstore(0x7360, mulmod(mload(0x2160), mload(0x22c0), f_q))
mstore(0x7380, addmod(mload(0x72c0), mload(0x7360), f_q))
mstore(0x73a0, mulmod(mload(0x2180), mload(0x22c0), f_q))
mstore(0x73c0, addmod(mload(0x7300), mload(0x73a0), f_q))
mstore(0x73e0, mulmod(mload(0x2220), 1, f_q))
mstore(0x7400, addmod(0, mload(0x73e0), f_q))
mstore(0x7420, mulmod(mload(0x2240), 1, f_q))
mstore(0x7440, addmod(0, mload(0x7420), f_q))
mstore(0x7460, addmod(mload(0x5cc0), sub(f_q, mload(0x5d20)), f_q))
mstore(0x7480, mulmod(1, mload(0x7460), f_q))
mstore(0x74a0, addmod(mload(0x5d20), sub(f_q, mload(0x5cc0)), f_q))
mstore(0x74c0, mulmod(1, mload(0x74a0), f_q))
{
            let prod := mload(0x7480)

                prod := mulmod(mload(0x74c0), prod, f_q)
                mstore(0x74e0, prod)
            
        }
mstore(0x7520, 32)
mstore(0x7540, 32)
mstore(0x7560, 32)
mstore(0x7580, mload(0x74e0))
mstore(0x75a0, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x75c0, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x7520, 0xc0, 0x7500, 0x20), 1), success)
{
            
            let inv := mload(0x7500)
            let v
        
                    v := mload(0x74c0)
                    mstore(29888, mulmod(mload(0x7480), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                mstore(0x7480, inv)

        }
mstore(0x75e0, addmod(mload(0x2400), sub(f_q, mload(0x5d20)), f_q))
mstore(0x7600, mulmod(1, mload(0x75e0), f_q))
mstore(0x7620, mulmod(mload(0x7400), mload(0x7600), f_q))
mstore(0x7640, mulmod(mload(0x7620), mload(0x7480), f_q))
mstore(0x7660, addmod(0, mload(0x7640), f_q))
mstore(0x7680, addmod(mload(0x2400), sub(f_q, mload(0x5cc0)), f_q))
mstore(0x76a0, mulmod(1, mload(0x7680), f_q))
mstore(0x76c0, mulmod(mload(0x7440), mload(0x76a0), f_q))
mstore(0x76e0, mulmod(mload(0x76c0), mload(0x74c0), f_q))
mstore(0x7700, addmod(mload(0x7660), mload(0x76e0), f_q))
mstore(0x7720, mulmod(mload(0x76a0), mload(0x75e0), f_q))
mstore(0x7760, 32)
mstore(0x7780, 32)
mstore(0x77a0, 32)
mstore(0x77c0, mload(0x7720))
mstore(0x77e0, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x7800, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x7760, 0xc0, 0x7740, 0x20), 1), success)
mstore(0x7820, addmod(mload(0x24a0), sub(f_q, mload(0x7700)), f_q))
mstore(0x7840, mulmod(mload(0x7820), mload(0x7740), f_q))
mstore(0x7860, mulmod(0, mload(0x2320), f_q))
mstore(0x7880, addmod(mload(0x7860), mload(0x7840), f_q))
mstore(0x78a0, addmod(mload(0x5cc0), sub(f_q, mload(0x5ce0)), f_q))
mstore(0x78c0, mulmod(1, mload(0x78a0), f_q))
mstore(0x78e0, addmod(mload(0x5cc0), sub(f_q, mload(0x5d00)), f_q))
mstore(0x7900, mulmod(mload(0x78c0), mload(0x78e0), f_q))
mstore(0x7920, addmod(mload(0x5ce0), sub(f_q, mload(0x5cc0)), f_q))
mstore(0x7940, mulmod(1, mload(0x7920), f_q))
mstore(0x7960, addmod(mload(0x5ce0), sub(f_q, mload(0x5d00)), f_q))
mstore(0x7980, mulmod(mload(0x7940), mload(0x7960), f_q))
mstore(0x79a0, addmod(mload(0x5d00), sub(f_q, mload(0x5cc0)), f_q))
mstore(0x79c0, mulmod(1, mload(0x79a0), f_q))
mstore(0x79e0, addmod(mload(0x5d00), sub(f_q, mload(0x5ce0)), f_q))
mstore(0x7a00, mulmod(mload(0x79c0), mload(0x79e0), f_q))
{
            let prod := mload(0x7900)

                prod := mulmod(mload(0x7980), prod, f_q)
                mstore(0x7a20, prod)
            
                prod := mulmod(mload(0x7a00), prod, f_q)
                mstore(0x7a40, prod)
            
        }
mstore(0x7a80, 32)
mstore(0x7aa0, 32)
mstore(0x7ac0, 32)
mstore(0x7ae0, mload(0x7a40))
mstore(0x7b00, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x7b20, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x7a80, 0xc0, 0x7a60, 0x20), 1), success)
{
            
            let inv := mload(0x7a60)
            let v
        
                    v := mload(0x7a00)
                    mstore(31232, mulmod(mload(0x7a20), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                
                    v := mload(0x7980)
                    mstore(31104, mulmod(mload(0x7900), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                mstore(0x7900, inv)

        }
mstore(0x7b40, addmod(mload(0x2400), sub(f_q, mload(0x5ce0)), f_q))
mstore(0x7b60, mulmod(1, mload(0x7b40), f_q))
mstore(0x7b80, addmod(mload(0x2400), sub(f_q, mload(0x5d00)), f_q))
mstore(0x7ba0, mulmod(mload(0x7b60), mload(0x7b80), f_q))
mstore(0x7bc0, mulmod(mload(0x7340), mload(0x7ba0), f_q))
mstore(0x7be0, mulmod(mload(0x7bc0), mload(0x7900), f_q))
mstore(0x7c00, addmod(0, mload(0x7be0), f_q))
mstore(0x7c20, mulmod(mload(0x76a0), mload(0x7b80), f_q))
mstore(0x7c40, mulmod(mload(0x7380), mload(0x7c20), f_q))
mstore(0x7c60, mulmod(mload(0x7c40), mload(0x7980), f_q))
mstore(0x7c80, addmod(mload(0x7c00), mload(0x7c60), f_q))
mstore(0x7ca0, mulmod(mload(0x76a0), mload(0x7b40), f_q))
mstore(0x7cc0, mulmod(mload(0x73c0), mload(0x7ca0), f_q))
mstore(0x7ce0, mulmod(mload(0x7cc0), mload(0x7a00), f_q))
mstore(0x7d00, addmod(mload(0x7c80), mload(0x7ce0), f_q))
mstore(0x7d20, mulmod(mload(0x7ca0), mload(0x7b80), f_q))
mstore(0x7d60, 32)
mstore(0x7d80, 32)
mstore(0x7da0, 32)
mstore(0x7dc0, mload(0x7d20))
mstore(0x7de0, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x7e00, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x7d60, 0xc0, 0x7d40, 0x20), 1), success)
mstore(0x7e20, addmod(mload(0x2480), sub(f_q, mload(0x7d00)), f_q))
mstore(0x7e40, mulmod(mload(0x7e20), mload(0x7d40), f_q))
mstore(0x7e60, mulmod(mload(0x7880), mload(0x2320), f_q))
mstore(0x7e80, addmod(mload(0x7e60), mload(0x7e40), f_q))
{
            let prod := mload(0x78c0)

                prod := mulmod(mload(0x7940), prod, f_q)
                mstore(0x7ea0, prod)
            
        }
mstore(0x7ee0, 32)
mstore(0x7f00, 32)
mstore(0x7f20, 32)
mstore(0x7f40, mload(0x7ea0))
mstore(0x7f60, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x7f80, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x7ee0, 0xc0, 0x7ec0, 0x20), 1), success)
{
            
            let inv := mload(0x7ec0)
            let v
        
                    v := mload(0x7940)
                    mstore(31040, mulmod(mload(0x78c0), inv, f_q))
                    inv := mulmod(v, inv, f_q)
                mstore(0x78c0, inv)

        }
mstore(0x7fa0, mulmod(mload(0x7200), mload(0x7b60), f_q))
mstore(0x7fc0, mulmod(mload(0x7fa0), mload(0x78c0), f_q))
mstore(0x7fe0, addmod(0, mload(0x7fc0), f_q))
mstore(0x8000, mulmod(mload(0x7240), mload(0x76a0), f_q))
mstore(0x8020, mulmod(mload(0x8000), mload(0x7940), f_q))
mstore(0x8040, addmod(mload(0x7fe0), mload(0x8020), f_q))
mstore(0x8080, 32)
mstore(0x80a0, 32)
mstore(0x80c0, 32)
mstore(0x80e0, mload(0x7ca0))
mstore(0x8100, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x8120, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x8080, 0xc0, 0x8060, 0x20), 1), success)
mstore(0x8140, addmod(mload(0x2460), sub(f_q, mload(0x8040)), f_q))
mstore(0x8160, mulmod(mload(0x8140), mload(0x8060), f_q))
mstore(0x8180, mulmod(mload(0x7e80), mload(0x2320), f_q))
mstore(0x81a0, addmod(mload(0x8180), mload(0x8160), f_q))
mstore(0x81e0, 32)
mstore(0x8200, 32)
mstore(0x8220, 32)
mstore(0x8240, mload(0x76a0))
mstore(0x8260, 52435875175126190479447740508185965837690552500527637822603658699938581184511)
mstore(0x8280, 52435875175126190479447740508185965837690552500527637822603658699938581184513)
success := and(eq(staticcall(gas(), 0x5, 0x81e0, 0xc0, 0x81c0, 0x20), 1), success)
mstore(0x82a0, addmod(mload(0x2440), sub(f_q, mload(0x6fc0)), f_q))
mstore(0x82c0, mulmod(mload(0x82a0), mload(0x81c0), f_q))
mstore(0x82e0, mulmod(mload(0x81a0), mload(0x2320), f_q))
mstore(0x8300, addmod(mload(0x82e0), mload(0x82c0), f_q))
mstore(0x8320, mulmod(mload(0x24e0), mload(0x24e0), f_q))
mstore(0x8340, mulmod(mload(0x8320), mload(0x24e0), f_q))
mstore(0x8360, mulmod(mload(0x8340), mload(0x24e0), f_q))
mstore(0x8380, mulmod(mload(0x8360), mload(0x24e0), f_q))
mstore(0x83a0, mulmod(mload(0x61c0), 1, f_q))
mstore(0x83c0, mulmod(mload(0x61e0), 1, f_q))
mstore(0x83e0, mulmod(mload(0x6200), 1, f_q))
mstore(0x8400, mulmod(mload(0x6220), 1, f_q))
mstore(0x8420, mulmod(mload(0x6240), 1, f_q))
mstore(0x8440, mulmod(mload(0x6260), 1, f_q))
mstore(0x8460, mulmod(mload(0x6280), 1, f_q))
mstore(0x8480, mulmod(mload(0x62a0), 1, f_q))
mstore(0x84a0, mulmod(mload(0x62c0), 1, f_q))
mstore(0x84c0, mulmod(mload(0x62e0), 1, f_q))
mstore(0x84e0, mulmod(mload(0x6300), 1, f_q))
mstore(0x8500, mulmod(mload(0x6320), 1, f_q))
mstore(0x8520, mulmod(mload(0x6340), 1, f_q))
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
mstore(0x8880, mulmod(1, mload(0x24e0), f_q))
mstore(0x88a0, mulmod(mload(0x61c0), mload(0x24e0), f_q))
mstore(0x88c0, mulmod(mload(0x61e0), mload(0x24e0), f_q))
mstore(0x88e0, mulmod(mload(0x6200), mload(0x24e0), f_q))
mstore(0x8900, mulmod(mload(0x6220), mload(0x24e0), f_q))
mstore(0x8920, mulmod(1, mload(0x8320), f_q))
mstore(0x8940, mulmod(mload(0x61c0), mload(0x8320), f_q))
mstore(0x8960, mulmod(1, mload(0x8340), f_q))
mstore(0x8980, mulmod(1, mload(0x8360), f_q))
mstore(0x89a0, mulmod(mload(0x2440), 1, f_q))
mstore(0x89c0, addmod(0, mload(0x89a0), f_q))
mstore(0x89e0, mulmod(mload(0x2460), mload(0x24e0), f_q))
mstore(0x8a00, addmod(mload(0x89c0), mload(0x89e0), f_q))
mstore(0x8a20, mulmod(mload(0x2480), mload(0x8320), f_q))
mstore(0x8a40, addmod(mload(0x8a00), mload(0x8a20), f_q))
mstore(0x8a60, mulmod(mload(0x24a0), mload(0x8340), f_q))
mstore(0x8a80, addmod(mload(0x8a40), mload(0x8a60), f_q))
mstore(0x8aa0, mulmod(mload(0x8300), mload(0x8360), f_q))
mstore(0x8ac0, addmod(mload(0x8a80), mload(0x8aa0), f_q))
mstore(0x8ae0, mulmod(1, mload(0x2400), f_q))

        {
            mstore(0x8b00, 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
            mstore(0x8b20, 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
            mstore(0x8b40, 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(0x8b60, 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
        }
{
                    mstore(0x8b80, mload(0x8b00))
mstore(0x8ba0, mload(0x8b20))
mstore(0x8bc0, mload(0x8b40))
mstore(0x8be0, mload(0x8b60))
                }
mstore(0x8c00, sub(f_q, mload(0x8ac0)))
success := and(eq(staticcall(gas(), 0xc, 0x8b80, 0xa0, 0x8b80, 0x80), 1), success)
{
                    mstore(0x8c20, mload(0x8b80))
mstore(0x8c40, mload(0x8ba0))
mstore(0x8c60, mload(0x8bc0))
mstore(0x8c80, mload(0x8be0))
                }
{
                    mstore(0x8ca0, mload(0xe20))
mstore(0x8cc0, mload(0xe40))
mstore(0x8ce0, mload(0xe60))
mstore(0x8d00, mload(0xe80))
                }
success := and(eq(staticcall(gas(), 0xb, 0x8c20, 0x100, 0x8c20, 0x80), 1), success)
{
                    mstore(0x8d20, mload(0x1120))
mstore(0x8d40, mload(0x1140))
mstore(0x8d60, mload(0x1160))
mstore(0x8d80, mload(0x1180))
                }
mstore(0x8da0, mload(0x83a0))
success := and(eq(staticcall(gas(), 0xc, 0x8d20, 0xa0, 0x8d20, 0x80), 1), success)
{
                    mstore(0x8dc0, mload(0x8c20))
mstore(0x8de0, mload(0x8c40))
mstore(0x8e00, mload(0x8c60))
mstore(0x8e20, mload(0x8c80))
                }
{
                    mstore(0x8e40, mload(0x8d20))
mstore(0x8e60, mload(0x8d40))
mstore(0x8e80, mload(0x8d60))
mstore(0x8ea0, mload(0x8d80))
                }
success := and(eq(staticcall(gas(), 0xb, 0x8dc0, 0x100, 0x8dc0, 0x80), 1), success)
{
                    mstore(0x8ec0, mload(0x11a0))
mstore(0x8ee0, mload(0x11c0))
mstore(0x8f00, mload(0x11e0))
mstore(0x8f20, mload(0x1200))
                }
mstore(0x8f40, mload(0x83c0))
success := and(eq(staticcall(gas(), 0xc, 0x8ec0, 0xa0, 0x8ec0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x8f60, 0x100, 0x8f60, 0x80), 1), success)
{
                    mstore(0x9060, mload(0x1220))
mstore(0x9080, mload(0x1240))
mstore(0x90a0, mload(0x1260))
mstore(0x90c0, mload(0x1280))
                }
mstore(0x90e0, mload(0x83e0))
success := and(eq(staticcall(gas(), 0xc, 0x9060, 0xa0, 0x9060, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x9100, 0x100, 0x9100, 0x80), 1), success)
{
                    mstore(0x9200, mload(0x12a0))
mstore(0x9220, mload(0x12c0))
mstore(0x9240, mload(0x12e0))
mstore(0x9260, mload(0x1300))
                }
mstore(0x9280, mload(0x8400))
success := and(eq(staticcall(gas(), 0xc, 0x9200, 0xa0, 0x9200, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x92a0, 0x100, 0x92a0, 0x80), 1), success)
{
                    mstore(0x93a0, mload(0x1320))
mstore(0x93c0, mload(0x1340))
mstore(0x93e0, mload(0x1360))
mstore(0x9400, mload(0x1380))
                }
mstore(0x9420, mload(0x8420))
success := and(eq(staticcall(gas(), 0xc, 0x93a0, 0xa0, 0x93a0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x9440, 0x100, 0x9440, 0x80), 1), success)
{
                    mstore(0x9540, mload(0x1480))
mstore(0x9560, mload(0x14a0))
mstore(0x9580, mload(0x14c0))
mstore(0x95a0, mload(0x14e0))
                }
mstore(0x95c0, mload(0x8440))
success := and(eq(staticcall(gas(), 0xc, 0x9540, 0xa0, 0x9540, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x95e0, 0x100, 0x95e0, 0x80), 1), success)
{
                    mstore(0x96e0, mload(0x1820))
mstore(0x9700, mload(0x1840))
mstore(0x9720, mload(0x1860))
mstore(0x9740, mload(0x1880))
                }
mstore(0x9760, mload(0x8460))
success := and(eq(staticcall(gas(), 0xc, 0x96e0, 0xa0, 0x96e0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x9780, 0x100, 0x9780, 0x80), 1), success)
{
                    mstore(0x9880, mload(0x500))
mstore(0x98a0, mload(0x520))
mstore(0x98c0, mload(0x540))
mstore(0x98e0, mload(0x560))
                }
mstore(0x9900, mload(0x8480))
success := and(eq(staticcall(gas(), 0xc, 0x9880, 0xa0, 0x9880, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x9920, 0x100, 0x9920, 0x80), 1), success)
{
                    mstore(0x9a20, mload(0x280))
mstore(0x9a40, mload(0x2a0))
mstore(0x9a60, mload(0x2c0))
mstore(0x9a80, mload(0x2e0))
                }
mstore(0x9aa0, mload(0x84a0))
success := and(eq(staticcall(gas(), 0xc, 0x9a20, 0xa0, 0x9a20, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x9ac0, 0x100, 0x9ac0, 0x80), 1), success)
{
                    mstore(0x9bc0, mload(0x300))
mstore(0x9be0, mload(0x320))
mstore(0x9c00, mload(0x340))
mstore(0x9c20, mload(0x360))
                }
mstore(0x9c40, mload(0x84c0))
success := and(eq(staticcall(gas(), 0xc, 0x9bc0, 0xa0, 0x9bc0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x9c60, 0x100, 0x9c60, 0x80), 1), success)
{
                    mstore(0x9d60, mload(0x380))
mstore(0x9d80, mload(0x3a0))
mstore(0x9da0, mload(0x3c0))
mstore(0x9dc0, mload(0x3e0))
                }
mstore(0x9de0, mload(0x84e0))
success := and(eq(staticcall(gas(), 0xc, 0x9d60, 0xa0, 0x9d60, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x9e00, 0x100, 0x9e00, 0x80), 1), success)
{
                    mstore(0x9f00, mload(0x400))
mstore(0x9f20, mload(0x420))
mstore(0x9f40, mload(0x440))
mstore(0x9f60, mload(0x460))
                }
mstore(0x9f80, mload(0x8500))
success := and(eq(staticcall(gas(), 0xc, 0x9f00, 0xa0, 0x9f00, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0x9fa0, 0x100, 0x9fa0, 0x80), 1), success)
{
                    mstore(0xa0a0, mload(0x480))
mstore(0xa0c0, mload(0x4a0))
mstore(0xa0e0, mload(0x4c0))
mstore(0xa100, mload(0x4e0))
                }
mstore(0xa120, mload(0x8520))
success := and(eq(staticcall(gas(), 0xc, 0xa0a0, 0xa0, 0xa0a0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xa140, 0x100, 0xa140, 0x80), 1), success)
{
                    mstore(0xa240, mload(0x80))
mstore(0xa260, mload(0xa0))
mstore(0xa280, mload(0xc0))
mstore(0xa2a0, mload(0xe0))
                }
mstore(0xa2c0, mload(0x8540))
success := and(eq(staticcall(gas(), 0xc, 0xa240, 0xa0, 0xa240, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xa2e0, 0x100, 0xa2e0, 0x80), 1), success)
{
                    mstore(0xa3e0, mload(0x100))
mstore(0xa400, mload(0x120))
mstore(0xa420, mload(0x140))
mstore(0xa440, mload(0x160))
                }
mstore(0xa460, mload(0x8560))
success := and(eq(staticcall(gas(), 0xc, 0xa3e0, 0xa0, 0xa3e0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xa480, 0x100, 0xa480, 0x80), 1), success)
{
                    mstore(0xa580, mload(0x180))
mstore(0xa5a0, mload(0x1a0))
mstore(0xa5c0, mload(0x1c0))
mstore(0xa5e0, mload(0x1e0))
                }
mstore(0xa600, mload(0x8580))
success := and(eq(staticcall(gas(), 0xc, 0xa580, 0xa0, 0xa580, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xa620, 0x100, 0xa620, 0x80), 1), success)
{
                    mstore(0xa720, mload(0x200))
mstore(0xa740, mload(0x220))
mstore(0xa760, mload(0x240))
mstore(0xa780, mload(0x260))
                }
mstore(0xa7a0, mload(0x85a0))
success := and(eq(staticcall(gas(), 0xc, 0xa720, 0xa0, 0xa720, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xa7c0, 0x100, 0xa7c0, 0x80), 1), success)
{
                    mstore(0xa8c0, mload(0x580))
mstore(0xa8e0, mload(0x5a0))
mstore(0xa900, mload(0x5c0))
mstore(0xa920, mload(0x5e0))
                }
mstore(0xa940, mload(0x85c0))
success := and(eq(staticcall(gas(), 0xc, 0xa8c0, 0xa0, 0xa8c0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xa960, 0x100, 0xa960, 0x80), 1), success)
{
                    mstore(0xaa60, mload(0x600))
mstore(0xaa80, mload(0x620))
mstore(0xaaa0, mload(0x640))
mstore(0xaac0, mload(0x660))
                }
mstore(0xaae0, mload(0x85e0))
success := and(eq(staticcall(gas(), 0xc, 0xaa60, 0xa0, 0xaa60, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xab00, 0x100, 0xab00, 0x80), 1), success)
{
                    mstore(0xac00, mload(0x680))
mstore(0xac20, mload(0x6a0))
mstore(0xac40, mload(0x6c0))
mstore(0xac60, mload(0x6e0))
                }
mstore(0xac80, mload(0x8600))
success := and(eq(staticcall(gas(), 0xc, 0xac00, 0xa0, 0xac00, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xaca0, 0x100, 0xaca0, 0x80), 1), success)
{
                    mstore(0xada0, mload(0x700))
mstore(0xadc0, mload(0x720))
mstore(0xade0, mload(0x740))
mstore(0xae00, mload(0x760))
                }
mstore(0xae20, mload(0x8620))
success := and(eq(staticcall(gas(), 0xc, 0xada0, 0xa0, 0xada0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xae40, 0x100, 0xae40, 0x80), 1), success)
{
                    mstore(0xaf40, mload(0x780))
mstore(0xaf60, mload(0x7a0))
mstore(0xaf80, mload(0x7c0))
mstore(0xafa0, mload(0x7e0))
                }
mstore(0xafc0, mload(0x8640))
success := and(eq(staticcall(gas(), 0xc, 0xaf40, 0xa0, 0xaf40, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xafe0, 0x100, 0xafe0, 0x80), 1), success)
{
                    mstore(0xb0e0, mload(0x800))
mstore(0xb100, mload(0x820))
mstore(0xb120, mload(0x840))
mstore(0xb140, mload(0x860))
                }
mstore(0xb160, mload(0x8660))
success := and(eq(staticcall(gas(), 0xc, 0xb0e0, 0xa0, 0xb0e0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xb180, 0x100, 0xb180, 0x80), 1), success)
{
                    mstore(0xb280, mload(0x880))
mstore(0xb2a0, mload(0x8a0))
mstore(0xb2c0, mload(0x8c0))
mstore(0xb2e0, mload(0x8e0))
                }
mstore(0xb300, mload(0x8680))
success := and(eq(staticcall(gas(), 0xc, 0xb280, 0xa0, 0xb280, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xb320, 0x100, 0xb320, 0x80), 1), success)
{
                    mstore(0xb420, mload(0x900))
mstore(0xb440, mload(0x920))
mstore(0xb460, mload(0x940))
mstore(0xb480, mload(0x960))
                }
mstore(0xb4a0, mload(0x86a0))
success := and(eq(staticcall(gas(), 0xc, 0xb420, 0xa0, 0xb420, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xb4c0, 0x100, 0xb4c0, 0x80), 1), success)
{
                    mstore(0xb5c0, mload(0x980))
mstore(0xb5e0, mload(0x9a0))
mstore(0xb600, mload(0x9c0))
mstore(0xb620, mload(0x9e0))
                }
mstore(0xb640, mload(0x86c0))
success := and(eq(staticcall(gas(), 0xc, 0xb5c0, 0xa0, 0xb5c0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xb660, 0x100, 0xb660, 0x80), 1), success)
{
                    mstore(0xb760, mload(0xa00))
mstore(0xb780, mload(0xa20))
mstore(0xb7a0, mload(0xa40))
mstore(0xb7c0, mload(0xa60))
                }
mstore(0xb7e0, mload(0x86e0))
success := and(eq(staticcall(gas(), 0xc, 0xb760, 0xa0, 0xb760, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xb800, 0x100, 0xb800, 0x80), 1), success)
{
                    mstore(0xb900, mload(0xa80))
mstore(0xb920, mload(0xaa0))
mstore(0xb940, mload(0xac0))
mstore(0xb960, mload(0xae0))
                }
mstore(0xb980, mload(0x8700))
success := and(eq(staticcall(gas(), 0xc, 0xb900, 0xa0, 0xb900, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xb9a0, 0x100, 0xb9a0, 0x80), 1), success)
{
                    mstore(0xbaa0, mload(0xb00))
mstore(0xbac0, mload(0xb20))
mstore(0xbae0, mload(0xb40))
mstore(0xbb00, mload(0xb60))
                }
mstore(0xbb20, mload(0x8720))
success := and(eq(staticcall(gas(), 0xc, 0xbaa0, 0xa0, 0xbaa0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xbb40, 0x100, 0xbb40, 0x80), 1), success)
{
                    mstore(0xbc40, mload(0xb80))
mstore(0xbc60, mload(0xba0))
mstore(0xbc80, mload(0xbc0))
mstore(0xbca0, mload(0xbe0))
                }
mstore(0xbcc0, mload(0x8740))
success := and(eq(staticcall(gas(), 0xc, 0xbc40, 0xa0, 0xbc40, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xbce0, 0x100, 0xbce0, 0x80), 1), success)
{
                    mstore(0xbde0, mload(0xc00))
mstore(0xbe00, mload(0xc20))
mstore(0xbe20, mload(0xc40))
mstore(0xbe40, mload(0xc60))
                }
mstore(0xbe60, mload(0x8760))
success := and(eq(staticcall(gas(), 0xc, 0xbde0, 0xa0, 0xbde0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xbe80, 0x100, 0xbe80, 0x80), 1), success)
{
                    mstore(0xbf80, mload(0xc80))
mstore(0xbfa0, mload(0xca0))
mstore(0xbfc0, mload(0xcc0))
mstore(0xbfe0, mload(0xce0))
                }
mstore(0xc000, mload(0x8780))
success := and(eq(staticcall(gas(), 0xc, 0xbf80, 0xa0, 0xbf80, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xc020, 0x100, 0xc020, 0x80), 1), success)
{
                    mstore(0xc120, mload(0xd00))
mstore(0xc140, mload(0xd20))
mstore(0xc160, mload(0xd40))
mstore(0xc180, mload(0xd60))
                }
mstore(0xc1a0, mload(0x87a0))
success := and(eq(staticcall(gas(), 0xc, 0xc120, 0xa0, 0xc120, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xc1c0, 0x100, 0xc1c0, 0x80), 1), success)
{
                    mstore(0xc2c0, mload(0xd80))
mstore(0xc2e0, mload(0xda0))
mstore(0xc300, mload(0xdc0))
mstore(0xc320, mload(0xde0))
                }
mstore(0xc340, mload(0x87c0))
success := and(eq(staticcall(gas(), 0xc, 0xc2c0, 0xa0, 0xc2c0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xc360, 0x100, 0xc360, 0x80), 1), success)
{
                    mstore(0xc460, mload(0x1980))
mstore(0xc480, mload(0x19a0))
mstore(0xc4a0, mload(0x19c0))
mstore(0xc4c0, mload(0x19e0))
                }
mstore(0xc4e0, mload(0x87e0))
success := and(eq(staticcall(gas(), 0xc, 0xc460, 0xa0, 0xc460, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xc500, 0x100, 0xc500, 0x80), 1), success)
{
                    mstore(0xc600, mload(0x1a00))
mstore(0xc620, mload(0x1a20))
mstore(0xc640, mload(0x1a40))
mstore(0xc660, mload(0x1a60))
                }
mstore(0xc680, mload(0x8800))
success := and(eq(staticcall(gas(), 0xc, 0xc600, 0xa0, 0xc600, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xc6a0, 0x100, 0xc6a0, 0x80), 1), success)
{
                    mstore(0xc7a0, mload(0x1a80))
mstore(0xc7c0, mload(0x1aa0))
mstore(0xc7e0, mload(0x1ac0))
mstore(0xc800, mload(0x1ae0))
                }
mstore(0xc820, mload(0x8820))
success := and(eq(staticcall(gas(), 0xc, 0xc7a0, 0xa0, 0xc7a0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xc840, 0x100, 0xc840, 0x80), 1), success)
{
                    mstore(0xc940, mload(0x1b00))
mstore(0xc960, mload(0x1b20))
mstore(0xc980, mload(0x1b40))
mstore(0xc9a0, mload(0x1b60))
                }
mstore(0xc9c0, mload(0x8840))
success := and(eq(staticcall(gas(), 0xc, 0xc940, 0xa0, 0xc940, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xc9e0, 0x100, 0xc9e0, 0x80), 1), success)
{
                    mstore(0xcae0, mload(0x18a0))
mstore(0xcb00, mload(0x18c0))
mstore(0xcb20, mload(0x18e0))
mstore(0xcb40, mload(0x1900))
                }
mstore(0xcb60, mload(0x8860))
success := and(eq(staticcall(gas(), 0xc, 0xcae0, 0xa0, 0xcae0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xcb80, 0x100, 0xcb80, 0x80), 1), success)
{
                    mstore(0xcc80, mload(0xfa0))
mstore(0xcca0, mload(0xfc0))
mstore(0xccc0, mload(0xfe0))
mstore(0xcce0, mload(0x1000))
                }
mstore(0xcd00, mload(0x8880))
success := and(eq(staticcall(gas(), 0xc, 0xcc80, 0xa0, 0xcc80, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xcd20, 0x100, 0xcd20, 0x80), 1), success)
{
                    mstore(0xce20, mload(0x1020))
mstore(0xce40, mload(0x1040))
mstore(0xce60, mload(0x1060))
mstore(0xce80, mload(0x1080))
                }
mstore(0xcea0, mload(0x88a0))
success := and(eq(staticcall(gas(), 0xc, 0xce20, 0xa0, 0xce20, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xcec0, 0x100, 0xcec0, 0x80), 1), success)
{
                    mstore(0xcfc0, mload(0x10a0))
mstore(0xcfe0, mload(0x10c0))
mstore(0xd000, mload(0x10e0))
mstore(0xd020, mload(0x1100))
                }
mstore(0xd040, mload(0x88c0))
success := and(eq(staticcall(gas(), 0xc, 0xcfc0, 0xa0, 0xcfc0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xd060, 0x100, 0xd060, 0x80), 1), success)
{
                    mstore(0xd160, mload(0x16c0))
mstore(0xd180, mload(0x16e0))
mstore(0xd1a0, mload(0x1700))
mstore(0xd1c0, mload(0x1720))
                }
mstore(0xd1e0, mload(0x88e0))
success := and(eq(staticcall(gas(), 0xc, 0xd160, 0xa0, 0xd160, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xd200, 0x100, 0xd200, 0x80), 1), success)
{
                    mstore(0xd300, mload(0x1740))
mstore(0xd320, mload(0x1760))
mstore(0xd340, mload(0x1780))
mstore(0xd360, mload(0x17a0))
                }
mstore(0xd380, mload(0x8900))
success := and(eq(staticcall(gas(), 0xc, 0xd300, 0xa0, 0xd300, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xd3a0, 0x100, 0xd3a0, 0x80), 1), success)
{
                    mstore(0xd4a0, mload(0x15c0))
mstore(0xd4c0, mload(0x15e0))
mstore(0xd4e0, mload(0x1600))
mstore(0xd500, mload(0x1620))
                }
mstore(0xd520, mload(0x8920))
success := and(eq(staticcall(gas(), 0xc, 0xd4a0, 0xa0, 0xd4a0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xd540, 0x100, 0xd540, 0x80), 1), success)
{
                    mstore(0xd640, mload(0x1640))
mstore(0xd660, mload(0x1660))
mstore(0xd680, mload(0x1680))
mstore(0xd6a0, mload(0x16a0))
                }
mstore(0xd6c0, mload(0x8940))
success := and(eq(staticcall(gas(), 0xc, 0xd640, 0xa0, 0xd640, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xd6e0, 0x100, 0xd6e0, 0x80), 1), success)
{
                    mstore(0xd7e0, mload(0x1400))
mstore(0xd800, mload(0x1420))
mstore(0xd820, mload(0x1440))
mstore(0xd840, mload(0x1460))
                }
mstore(0xd860, mload(0x8960))
success := and(eq(staticcall(gas(), 0xc, 0xd7e0, 0xa0, 0xd7e0, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xd880, 0x100, 0xd880, 0x80), 1), success)
{
                    mstore(0xd980, mload(0x2360))
mstore(0xd9a0, mload(0x2380))
mstore(0xd9c0, mload(0x23a0))
mstore(0xd9e0, mload(0x23c0))
                }
mstore(0xda00, mload(0x8980))
success := and(eq(staticcall(gas(), 0xc, 0xd980, 0xa0, 0xd980, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xda20, 0x100, 0xda20, 0x80), 1), success)
{
                    mstore(0xdb20, mload(0x2520))
mstore(0xdb40, mload(0x2540))
mstore(0xdb60, mload(0x2560))
mstore(0xdb80, mload(0x2580))
                }
mstore(0xdba0, mload(0x8ae0))
success := and(eq(staticcall(gas(), 0xc, 0xdb20, 0xa0, 0xdb20, 0x80), 1), success)
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
success := and(eq(staticcall(gas(), 0xb, 0xdbc0, 0x100, 0xdbc0, 0x80), 1), success)

        {
            mstore(0xdcc0, 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
            mstore(0xdce0, 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
            mstore(0xdd00, 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(0xdd20, 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
        }
{
                    mstore(0xdd40, mload(0xdbc0))
mstore(0xdd60, mload(0xdbe0))
mstore(0xdd80, mload(0xdc00))
mstore(0xdda0, mload(0xdc20))
                }
mstore(0xddc0, 0x00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051)
mstore(0xdde0, 0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8)
mstore(0xde00, 0x0000000000000000000000000000000013e02b6052719f607dacd3a088274f65)
mstore(0xde20, 0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
mstore(0xde40, 0x000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351a)
mstore(0xde60, 0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801)
mstore(0xde80, 0x000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99)
mstore(0xdea0, 0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)
{
                    mstore(0xdec0, mload(0x2520))
mstore(0xdee0, mload(0x2540))
mstore(0xdf00, mload(0x2560))
mstore(0xdf20, mload(0x2580))
                }
mstore(0xdf40, 0x000000000000000000000000000000000c411098b41af7474a870e96b24b98d9)
mstore(0xdf60, 0x07ed7b733737bd0dc06423044b7f88dd19e5d450cdbffa14a8011f8b7e3cd8e2)
mstore(0xdf80, 0x0000000000000000000000000000000014a9ff2c514cf1a9ea7058e88e34d5b7)
mstore(0xdfa0, 0x8478c9600c726d6a72f5edb7af4f8c2bc51d4ae51e5d0c49e6ef7ba7a79d893b)
mstore(0xdfc0, 0x000000000000000000000000000000000b42f4add12e04fcfe2e8f4648cf7f2a)
mstore(0xdfe0, 0x7a7e27b3addabe0e43f6ca5b9a27964e0aa9bcf68b135266610bd6dd9b1d789d)
mstore(0xe000, 0x0000000000000000000000000000000006c9cbda81a8f3d8af85b7b9c5b3c887)
mstore(0xe020, 0xdd612a8b0d5e218dedb2b689e608aab15f4360351fefffef033a6beaeec203d4)
success := and(eq(staticcall(gas(), 0xf, 0xdd40, 0x300, 0xdd40, 0x20), 1), success)
success := and(eq(mload(0xdd40), 1), success)

            // Revert if anything fails
            if iszero(success) { revert(0, 0) }

            // Return empty bytes on success
            return(0, 0)

        }
    }
}
        