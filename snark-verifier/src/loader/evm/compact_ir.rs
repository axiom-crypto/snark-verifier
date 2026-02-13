#![allow(missing_docs)]

use super::U256;

pub const COMPACT_OPCODE_VERSION: u32 = 1;
pub const COMPACT_PAGE_BYTES: usize = 24_576;

const OP_MSTORE_CONST: u8 = 1;
const OP_MSTORE_MEM: u8 = 2;
const OP_MSTORE8: u8 = 3;
const OP_SCALAR_NEG: u8 = 4;
const OP_SCALAR_ADD: u8 = 5;
const OP_SCALAR_MUL: u8 = 6;
const OP_CALLDATA_SCALAR: u8 = 7;
const OP_CALLDATA_POINT_UNCOMPRESSED: u8 = 8;
const OP_COPY_POINT: u8 = 9;
const OP_KECCAK: u8 = 10;
const OP_STATICCALL: u8 = 11;
const OP_ASSERT_ONE: u8 = 12;
const OP_POINT_FROM_LIMBS: u8 = 13;
const OP_MOD_FROM_MEM: u8 = 14;
const OP_SCALAR_NEG_MEM: u8 = 15;
const OP_SCALAR_ADD_MEM_MEM: u8 = 16;
const OP_SCALAR_MUL_MEM_MEM: u8 = 17;

const OPERAND_TAG_MEM: u8 = 0;
const OPERAND_TAG_CONST: u8 = 1;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompactOperand {
    Memory(usize),
    Constant(U256),
}

#[derive(Clone, Debug)]
pub enum CompactInstruction {
    MstoreConst {
        dst: usize,
        value: U256,
    },
    MstoreMem {
        dst: usize,
        src: usize,
    },
    Mstore8 {
        dst: usize,
        value: u8,
    },
    ScalarNeg {
        dst: usize,
        operand: CompactOperand,
    },
    ScalarAdd {
        dst: usize,
        lhs: CompactOperand,
        rhs: CompactOperand,
    },
    ScalarMul {
        dst: usize,
        lhs: CompactOperand,
        rhs: CompactOperand,
    },
    CalldataScalar {
        dst: usize,
        offset: usize,
    },
    CalldataPointUncompressed {
        dst: usize,
        offset: usize,
        coord_bytes: usize,
    },
    CopyPoint {
        dst: usize,
        src: usize,
    },
    Keccak {
        dst: usize,
        ptr: usize,
        len: usize,
    },
    StaticCall {
        precompile: usize,
        cd_ptr: usize,
        rd_ptr: usize,
    },
    AssertOne {
        ptr: usize,
    },
    PointFromLimbs {
        dst: usize,
        bits: usize,
        x_limbs: Vec<CompactOperand>,
        y_limbs: Vec<CompactOperand>,
    },
    ModFromMem {
        dst: usize,
        src: usize,
    },
    ScalarNegMem {
        dst: usize,
        src: usize,
    },
    ScalarAddMemMem {
        dst: usize,
        lhs: usize,
        rhs: usize,
    },
    ScalarMulMemMem {
        dst: usize,
        lhs: usize,
        rhs: usize,
    },
}

#[derive(Clone, Debug, Default)]
pub struct CompactProgramBuilder {
    instructions: Vec<CompactInstruction>,
}

impl CompactProgramBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, instruction: CompactInstruction) {
        self.instructions.push(instruction);
    }

    pub fn instructions(&self) -> &[CompactInstruction] {
        &self.instructions
    }

    pub fn encode(&self) -> CompactProgram {
        let mut words = vec![U256::from(COMPACT_OPCODE_VERSION)];
        for instruction in &self.instructions {
            encode_instruction(instruction, &mut words);
        }
        CompactProgram { words }
    }
}

#[derive(Clone, Debug)]
pub struct CompactProgram {
    words: Vec<U256>,
}

impl CompactProgram {
    pub fn words(&self) -> &[U256] {
        &self.words
    }

    pub fn word_len(&self) -> usize {
        self.words.len()
    }

    pub fn byte_len(&self) -> usize {
        self.words.len() * 32
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        self.words.iter().flat_map(|word| word.to_be_bytes::<32>()).collect()
    }

    pub fn paginate(&self, page_size_bytes: usize) -> CompactProgramPages {
        assert!(page_size_bytes > 0 && page_size_bytes % 32 == 0);

        let bytes = self.to_bytes();
        let pages = bytes.chunks(page_size_bytes).map(|chunk| chunk.to_vec()).collect::<Vec<_>>();

        let mut offset_words = 0usize;
        let mut page_word_offsets = Vec::with_capacity(pages.len());
        let mut page_word_counts = Vec::with_capacity(pages.len());
        for page in &pages {
            let words = page.len() / 32;
            page_word_offsets.push(offset_words);
            page_word_counts.push(words);
            offset_words += words;
        }

        CompactProgramPages {
            manifest: CompactProgramManifest {
                opcode_version: COMPACT_OPCODE_VERSION,
                page_size_bytes,
                program_words: self.word_len(),
                page_word_offsets,
                page_word_counts,
                max_memory_ptr: 0,
            },
            pages,
        }
    }
}

#[derive(Clone, Debug)]
pub struct CompactProgramManifest {
    pub opcode_version: u32,
    pub page_size_bytes: usize,
    pub program_words: usize,
    pub page_word_offsets: Vec<usize>,
    pub page_word_counts: Vec<usize>,
    pub max_memory_ptr: usize,
}

#[derive(Clone, Debug)]
pub struct CompactProgramPages {
    pub manifest: CompactProgramManifest,
    pub pages: Vec<Vec<u8>>,
}

fn header(opcode: u8, len_words: u8) -> U256 {
    (U256::from(opcode) << 248) | (U256::from(len_words) << 240)
}

fn encode_instruction(instruction: &CompactInstruction, out: &mut Vec<U256>) {
    match instruction {
        CompactInstruction::MstoreConst { dst, value } => {
            out.push(header(OP_MSTORE_CONST, 3));
            out.push(U256::from(*dst));
            out.push(*value);
        }
        CompactInstruction::MstoreMem { dst, src } => {
            out.push(header(OP_MSTORE_MEM, 3));
            out.push(U256::from(*dst));
            out.push(U256::from(*src));
        }
        CompactInstruction::Mstore8 { dst, value } => {
            out.push(header(OP_MSTORE8, 3));
            out.push(U256::from(*dst));
            out.push(U256::from(*value));
        }
        CompactInstruction::ScalarNeg { dst, operand } => {
            out.push(header(OP_SCALAR_NEG, 4));
            out.push(U256::from(*dst));
            encode_operand(operand, out);
        }
        CompactInstruction::ScalarAdd { dst, lhs, rhs } => {
            out.push(header(OP_SCALAR_ADD, 6));
            out.push(U256::from(*dst));
            encode_operand(lhs, out);
            encode_operand(rhs, out);
        }
        CompactInstruction::ScalarMul { dst, lhs, rhs } => {
            out.push(header(OP_SCALAR_MUL, 6));
            out.push(U256::from(*dst));
            encode_operand(lhs, out);
            encode_operand(rhs, out);
        }
        CompactInstruction::CalldataScalar { dst, offset } => {
            out.push(header(OP_CALLDATA_SCALAR, 3));
            out.push(U256::from(*dst));
            out.push(U256::from(*offset));
        }
        CompactInstruction::CalldataPointUncompressed { dst, offset, coord_bytes } => {
            out.push(header(OP_CALLDATA_POINT_UNCOMPRESSED, 4));
            out.push(U256::from(*dst));
            out.push(U256::from(*offset));
            out.push(U256::from(*coord_bytes));
        }
        CompactInstruction::CopyPoint { dst, src } => {
            out.push(header(OP_COPY_POINT, 3));
            out.push(U256::from(*dst));
            out.push(U256::from(*src));
        }
        CompactInstruction::Keccak { dst, ptr, len } => {
            out.push(header(OP_KECCAK, 4));
            out.push(U256::from(*dst));
            out.push(U256::from(*ptr));
            out.push(U256::from(*len));
        }
        CompactInstruction::StaticCall { precompile, cd_ptr, rd_ptr } => {
            out.push(header(OP_STATICCALL, 4));
            out.push(U256::from(*precompile));
            out.push(U256::from(*cd_ptr));
            out.push(U256::from(*rd_ptr));
        }
        CompactInstruction::AssertOne { ptr } => {
            out.push(header(OP_ASSERT_ONE, 2));
            out.push(U256::from(*ptr));
        }
        CompactInstruction::PointFromLimbs { dst, bits, x_limbs, y_limbs } => {
            assert_eq!(x_limbs.len(), y_limbs.len());
            let len = 4 + (x_limbs.len() + y_limbs.len()) * 2;
            out.push(header(OP_POINT_FROM_LIMBS, len as u8));
            out.push(U256::from(*dst));
            out.push(U256::from(*bits));
            out.push(U256::from(x_limbs.len()));
            for limb in x_limbs {
                encode_operand(limb, out);
            }
            for limb in y_limbs {
                encode_operand(limb, out);
            }
        }
        CompactInstruction::ModFromMem { dst, src } => {
            out.push(header(OP_MOD_FROM_MEM, 3));
            out.push(U256::from(*dst));
            out.push(U256::from(*src));
        }
        CompactInstruction::ScalarNegMem { dst, src } => {
            out.push(header(OP_SCALAR_NEG_MEM, 3));
            out.push(U256::from(*dst));
            out.push(U256::from(*src));
        }
        CompactInstruction::ScalarAddMemMem { dst, lhs, rhs } => {
            out.push(header(OP_SCALAR_ADD_MEM_MEM, 4));
            out.push(U256::from(*dst));
            out.push(U256::from(*lhs));
            out.push(U256::from(*rhs));
        }
        CompactInstruction::ScalarMulMemMem { dst, lhs, rhs } => {
            out.push(header(OP_SCALAR_MUL_MEM_MEM, 4));
            out.push(U256::from(*dst));
            out.push(U256::from(*lhs));
            out.push(U256::from(*rhs));
        }
    }
}

fn encode_operand(operand: &CompactOperand, out: &mut Vec<U256>) {
    match operand {
        CompactOperand::Memory(ptr) => {
            out.push(U256::from(OPERAND_TAG_MEM));
            out.push(U256::from(*ptr));
        }
        CompactOperand::Constant(value) => {
            out.push(U256::from(OPERAND_TAG_CONST));
            out.push(*value);
        }
    }
}
