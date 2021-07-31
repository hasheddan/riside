use num_traits::FromPrimitive;
use num_derive::{FromPrimitive, ToPrimitive};


#[cfg(test)]
mod tests {
    use crate::{Format, Instruction, Mnemonic, GPR};

    #[test]
    fn it_works() {
        let ins = Instruction::new_from_binary("00000000101101010000010100111011".to_string()).unwrap();
        assert_eq!(ins.format, Format::R);
        assert_eq!(ins.mnemonic, Mnemonic::ADDW);
        assert_eq!(ins.rd, Some(GPR::A0));
        assert_eq!(ins.rs1, Some(GPR::A0));
        assert_eq!(ins.rs2, Some(GPR::A1));
    }
}

#[derive(Debug)]
pub enum RisideError {
    ParseError
}

#[derive(Debug, PartialEq, FromPrimitive, ToPrimitive)]
pub enum GPR {
    ZERO,
    RA,
    SP,
    GP,
    TP,
    T0,
    T1,
    T2,
    S0,
    S1,
    A0,
    A1,
    A2,
    A3,
    A4,
    A5,
    A6,
    A7,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    T3,
    T4,
    T5,
    T6,
}

#[derive(PartialEq, PartialOrd, Debug)]
pub enum Format {
    I,
    U,
    UJ,
    S,
    SB,
    R,
}

impl Default for Format {
    fn default() -> Self {
        Format::I
    }
}

impl Format {
    pub fn parse(ins: &mut Instruction) -> Result<(), RisideError> {
        match ins.format {
            Format::I => {
                let rd_val = i32::from_str_radix(&ins.binary[20..25], 2).unwrap();
                ins.rd = FromPrimitive::from_i32(rd_val);
            }
            Format::U => {}
            Format::UJ => {}
            Format::S => {}
            Format::SB => {}
            Format::R => {
                let rd_val = i32::from_str_radix(&ins.binary[20..25], 2).unwrap();
                ins.rd = FromPrimitive::from_i32(rd_val);

                let rs1_val = i32::from_str_radix(&ins.binary[12..17], 2).unwrap();
                ins.rs1 = FromPrimitive::from_i32(rs1_val);

                let rs2_val = i32::from_str_radix(&ins.binary[7..12], 2).unwrap();
                ins.rs2 = FromPrimitive::from_i32(rs2_val);
            }
        }
        Ok(())
    }
}

#[derive(PartialEq, PartialOrd, Debug)]

pub enum Mnemonic {
    LB,
    LH,
    LW,
    LD,
    LBU,
    LHU,
    LWU,
    FENCE,
    FENCEI,
    ADDI,
    SLLI,
    SLTI,
    SLTIU,
    XORI,
    SRLI,
    SRAI,
    ORI,
    ANDI,
    AUIPC,
    ADDIW,
    SLLIW,
    SRLIW,
    SRAIW,
    SB,
    SH,
    SW,
    SD,
    ADD,
    SUB,
    SLL,
    SLT,
    SLTU,
    XOR,
    SRL,
    SRA,
    OR,
    AND,
    LUI,
    ADDW,
    SUBW,
    SLLW,
    SRLW,
    SRAW,
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
    JALR,
    JAL,
    ECALL,
    EBREAK,
    CSRRW,
    CSRRS,
    CSRRC,
    CSRRWI,
    CSRRSI,
    CSRRCI,

    BEQZ,
    BNEZ,
    J,
    JR,
    LA,
    LI,
    MV,
    NEG,
    NOP,
    NOT,
    RET,
    SEQZ,
    SNEZ,
}

impl Default for Mnemonic {
    fn default() -> Self {
        Mnemonic::ADD
    }
}

impl Mnemonic {
    pub fn get_info(&self) -> (&'static str, &'static str, &'static str) {
        match self {
            // TODO(hasheddan): finish implementing
            Mnemonic::LB => ("lb", "Load Byte", "R[rd] = {56;bM[](7),M[R[rs1]+imm](7:0)}"),
            Mnemonic::LH => ("lhu", "Load Halfword", "R[rd] = {48'bM[](15),M[R[rs1]_imm](15:0)}"),
            Mnemonic::LW => ("lw", "Load Word", ""),
            Mnemonic::LD => ("ld", "Load Doubleword", ""),
            Mnemonic::LBU => ("lbu", "Load Byte Unsigned", ""),
            Mnemonic::LHU => ("lhu", "Load Halfword Unsigned", ""),
            Mnemonic::LWU => ("lwu", "Load Word Unsigned", ""),
            Mnemonic::FENCE => ("fence", "Synchronize Thread", ""),
            Mnemonic::FENCEI => ("fence.i", "Synchronize Instructions & Data", ""),
            Mnemonic::ADDI => ("addi", "Add Immediate", ""),
            Mnemonic::SLLI => ("slli", "Shift Left Immediate", ""),
            Mnemonic::SLTI => ("slti", "", ""),
            Mnemonic::SLTIU => ("sltiu", "", ""),
            Mnemonic::XORI => ("xori", "", ""),
            Mnemonic::SRLI => ("srli", "", ""),
            Mnemonic::SRAI => ("srai", "", ""),
            Mnemonic::ORI => ("ori", "", ""),
            Mnemonic::ANDI => ("andi", "", ""),
            Mnemonic::AUIPC => ("auipc", "", ""),
            Mnemonic::ADDIW => ("addiw", "Add Immediate Word", ""),
            Mnemonic::SLLIW => ("slliw", "", ""),
            Mnemonic::SRLIW => ("srliw", "", ""),
            Mnemonic::SRAIW => ("sraiw", "", ""),
            Mnemonic::SB => ("sb", "", ""),
            Mnemonic::SH => ("sh", "", ""),
            Mnemonic::SW => ("sw", "", ""),
            Mnemonic::SD => ("sd", "", ""),
            Mnemonic::ADD => ("add", "", ""),
            Mnemonic::SUB => ("sub", "", ""),
            Mnemonic::SLL => ("sll", "", ""),
            Mnemonic::SLT => ("slt", "", ""),
            Mnemonic::SLTU => ("sltu", "", ""),
            Mnemonic::XOR => ("xor", "", ""),
            Mnemonic::SRL => ("srl", "", ""),
            Mnemonic::SRA => ("sra", "", ""),
            Mnemonic::OR => ("or", "", ""),
            Mnemonic::AND => ("and", "", ""),
            Mnemonic::LUI => ("LUI", "", ""),
            Mnemonic::ADDW => ("addw", "", ""),
            Mnemonic::SUBW => ("subw", "", ""),
            Mnemonic::SLLW => ("sllw", "", ""),
            Mnemonic::SRLW => ("srlw", "", ""),
            Mnemonic::SRAW => ("sraw", "", ""),
            Mnemonic::BEQ => ("beq", "", ""),
            Mnemonic::BNE => ("bne", "", ""),
            Mnemonic::BLT => ("blt", "", ""),
            Mnemonic::BGE => ("bge", "", ""),
            Mnemonic::BLTU => ("bltu", "", ""),
            Mnemonic::BGEU => ("bgeu", "", ""),
            Mnemonic::JALR => ("jalr", "", ""),
            Mnemonic::JAL => ("jal", "", ""),
            Mnemonic::ECALL => ("ecall", "", ""),
            Mnemonic::EBREAK => ("ebreak", "", ""),
            Mnemonic::CSRRW => ("csrrw", "", ""),
            Mnemonic::CSRRS => ("csrrs", "", ""),
            Mnemonic::CSRRC => ("csrrc", "", ""),
            Mnemonic::CSRRWI => ("csrrwi", "", ""),
            Mnemonic::CSRRSI => ("csrrsi", "", ""),
            Mnemonic::CSRRCI => ("csrrci", "", ""),

            Mnemonic::BEQZ => ("beqz", "", ""),
            Mnemonic::BNEZ => ("bnez", "", ""),
            Mnemonic::J => ("j", "", ""),
            Mnemonic::JR => ("jr", "", ""),
            Mnemonic::LA => ("la", "", ""),
            Mnemonic::LI => ("li", "", ""),
            Mnemonic::MV => ("mv", "", ""),
            Mnemonic::NEG => ("neg", "", ""),
            Mnemonic::NOP => ("nop", "", ""),
            Mnemonic::NOT => ("not", "", ""),
            Mnemonic::RET => ("ret", "", ""),
            Mnemonic::SEQZ => ("seqz", "", ""),
            Mnemonic::SNEZ => ("snez", "", ""),
        }
    }
}

#[derive(Default)]
pub struct Instruction {
    binary: String,
    hex: String,
    ins: String,
    format: Format,
    mnemonic: Mnemonic,

    opcode: String,
    rd: Option<GPR>,
    rs1: Option<GPR>,
    rs2: Option<GPR>,
    funct3: Option<String>,
    funct7: Option<String>,
    imm: Option<i32>,
}

impl Instruction {
    fn new_from_binary(binary: String) -> Result<Instruction, RisideError> {
        if binary.len() != 32 {
            return Err(RisideError::ParseError);
        }

        let seg_three = &binary[17..20];
        let seg_six = &binary[..7];

        let mut ins = Instruction{
            opcode: binary[25..].to_string(),
            ..Default::default()
        };

        match ins.opcode.as_str() {
            "0000011" => {
                ins.format = Format::I;
                match seg_three {
                    "000" => {
                        ins.mnemonic = Mnemonic::LB;
                    }
                    "001" => {
                        ins.mnemonic = Mnemonic::LH;
                    }
                    "010" => {
                        ins.mnemonic = Mnemonic::LW;
                    }
                    "011" => {
                        ins.mnemonic = Mnemonic::LD;
                    }
                    "100" => {
                        ins.mnemonic = Mnemonic::LBU;
                    }
                    "101" => {
                        ins.mnemonic = Mnemonic::LHU;
                    }
                    "110" => {
                        ins.mnemonic = Mnemonic::LWU;
                    }
                    _ => return Err(RisideError::ParseError)
                }
            }
            "0001111" => {
                ins.format = Format::I;
                match seg_three {
                    "000" => {
                        ins.mnemonic = Mnemonic::FENCE;
                    }
                    "001" => {
                        ins.mnemonic = Mnemonic::FENCEI;
                    }
                    _ => return Err(RisideError::ParseError)
                }
            }
            "0010011" => {
                ins.format = Format::I;
                match seg_three {
                    "000" => {
                        ins.mnemonic = Mnemonic::ADDI;
                    }
                    "001" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::SLLI;
                        }
                        _ => return Err(RisideError::ParseError)
                    },
                    "010" => {
                        ins.mnemonic = Mnemonic::SLTI;
                    }
                    "011" => {
                        ins.mnemonic = Mnemonic::SLTIU;
                    }
                    "100" => {
                        ins.mnemonic = Mnemonic::XORI;
                    }
                    "101" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::SRLI;
                        }
                        "0100000" => {
                            ins.mnemonic = Mnemonic::SRAI;
                        }
                        _ => return Err(RisideError::ParseError)
                    },
                    "110" => {
                        ins.mnemonic = Mnemonic::ORI;
                    }
                    "111" => {
                        ins.mnemonic = Mnemonic::ANDI;
                    }
                    _ => return Err(RisideError::ParseError)
                }
            }
            "0010111" => {
                ins.format = Format::U;
                ins.mnemonic = Mnemonic::AUIPC;
            }
            "0011011" => {
                ins.format = Format::I;
                match seg_three {
                    "000" => {
                        ins.mnemonic = Mnemonic::ADDIW;
                    }
                    "001" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::SLLIW;
                        }
                        _ => return Err(RisideError::ParseError)
                    },
                    "101" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::SRLIW;
                        }
                        "0100000" => {
                            ins.mnemonic = Mnemonic::SRAIW;
                        }
                        _ => return Err(RisideError::ParseError)
                    },
                    _ => return Err(RisideError::ParseError)
                }
            }
            "0100011" => {
                ins.format = Format::S;
                match seg_three {
                    "000" => {
                        ins.mnemonic = Mnemonic::SB;
                    }
                    "001" => {
                        ins.mnemonic = Mnemonic::SH;
                    }
                    "010" => {
                        ins.mnemonic = Mnemonic::SW;
                    }
                    "011" => {
                        ins.mnemonic = Mnemonic::SD;
                    }
                    _ => return Err(RisideError::ParseError)
                }
            }
            "0110011" => {
                ins.format = Format::R;
                match seg_three {
                    "000" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::ADD;
                        }
                        "0100000" => {
                            ins.mnemonic = Mnemonic::SUB;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    "001" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::SLL;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    "010" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::SLT;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    "011" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::SLTU;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    "100" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::XOR;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    "101" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::SRL;
                        }
                        "0100000" => {
                            ins.mnemonic = Mnemonic::SRA;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    "110" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::OR;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    "111" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::AND;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    _ => return Err(RisideError::ParseError)
                }
            }
            "0110111" => {
                ins.format = Format::U;
                ins.mnemonic = Mnemonic::LUI;
            }
            "0111011" => {
                ins.format = Format::R;
                match seg_three {
                    "000" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::ADDW;
                        }
                        "0100000" => {
                            ins.mnemonic = Mnemonic::SUBW;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    "001" =>  {
                        ins.mnemonic = Mnemonic::SLLW;
                    }
                    "101" => match seg_six {
                        "0000000" => {
                            ins.mnemonic = Mnemonic::SRLW;
                        }
                        "0100000" => {
                            ins.mnemonic = Mnemonic::SRAW;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    _ => return Err(RisideError::ParseError)
                }
            }
            "1100011" => {
                ins.format = Format::SB;
                match seg_three {
                    "000" => {
                        ins.mnemonic = Mnemonic::BEQ;
                    }
                    "001" => {
                        ins.mnemonic = Mnemonic::BNE;
                    }
                    "100" => {
                        ins.mnemonic = Mnemonic::BLT;
                    }
                    "101" => {
                        ins.mnemonic = Mnemonic::BGE;
                    }
                    "110" => {
                        ins.mnemonic = Mnemonic::BLTU;
                    }
                    "111" => {
                        ins.mnemonic = Mnemonic::BGEU;
                    }
                    _ => return Err(RisideError::ParseError)
                }
            }
            "1100111" => {
                ins.format = Format::I;
                match seg_three {
                    "000" => {
                        ins.mnemonic = Mnemonic::JALR;
                    }
                    _ => return Err(RisideError::ParseError)
                }
            }
            "1101111" => {
                ins.format = Format::UJ;
                ins.mnemonic = Mnemonic::JAL;
            }
            "1110011" => {
                ins.format = Format::I;
                match seg_three {
                    "000" => match seg_six {
                        "000000000000" => {
                            ins.mnemonic = Mnemonic::ECALL;
                        }
                        "000000000001" => {
                            ins.mnemonic = Mnemonic::EBREAK;
                        }
                        _ => return Err(RisideError::ParseError)
                    }
                    "001" =>  {
                        ins.mnemonic = Mnemonic::CSRRW;
                    }
                    "010" =>  {
                        ins.mnemonic = Mnemonic::CSRRS;
                    }
                    "011" =>  {
                        ins.mnemonic = Mnemonic::CSRRC;
                    }
                    "101" =>  {
                        ins.mnemonic = Mnemonic::CSRRWI;
                    }
                    "110" =>  {
                        ins.mnemonic = Mnemonic::CSRRSI;
                    }
                    "111" =>  {
                        ins.mnemonic = Mnemonic::CSRRCI;
                    }
                    _ => return Err(RisideError::ParseError)
                }
            }
            _ => return Err(RisideError::ParseError),
        }
        ins.binary = binary;
        Format::parse(&mut ins)?;
        Ok(ins)
    }
}
