use isla_lib::bitvector::BV;

use rand::Rng;

use std::convert::TryFrom;
use std::fmt;

#[derive(Debug)]
pub enum Sexp<'a> {
    Item(&'a str),
    Seq(Vec<Sexp<'a>>),
}

#[derive(Debug)]
pub enum Operand<'a> {
    Addressing(&'a str, &'a str),
    Register(&'a str),
}

#[derive(Debug)]
pub struct Instr<'a, B:BV> {
    pub name: &'a str,
    pub opcode: B,
    pub opcode_in_reg: Option<u8>,
    pub opcode_remainder: &'a [Sexp<'a>],
    pub operands: Vec<Operand<'a>>,
    pub implementation: &'a Sexp<'a>,
    pub exceptions: &'a Sexp<'a>,
}

impl<'a> fmt::Display for Sexp<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexp::Item(s) => write!(f, "{}", s),
            Sexp::Seq(sexps) => {
                write!(f, "(")?;
                for e in sexps {
                    write!(f, "{}", e)?;
                }
                write!(f, ")")
            }
        }
    }
}

// TODO: print nicely
impl<'a> fmt::Display for Operand<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<'a, B:BV> fmt::Display for Instr<'a, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {:?} [", self.name, self.opcode, self.opcode_in_reg)?;
        for s in self.opcode_remainder {
            write!(f, "{} ", s)?;
        }
        let mut oper_iter = self.operands.iter().peekable();
        loop {
            match oper_iter.next() {
                Some(oper) => {
                    let suffix = if oper_iter.peek().is_some() { ", " } else { "" };
                    write!(f, "{}{}", oper, suffix)?;
                }
                None => break,
            }
        }
        write!(f, "] {} {}", self.implementation, self.exceptions)
    }
}

fn parse_opcode<'a, B:BV>(sexp: &'a Sexp<'a>) -> Result<(B, Option<u8>, &'a [Sexp<'a>]), String> {
    use Sexp::*;
    match sexp {
        Seq(items) =>
            match items[..] {
                [Item("OP"), Item(":OP"), Item(opcode), ref rest @ ..] => {
                    let (reg, rest) = match rest {
                        [Item(":REG"), Item(reg), ref rest @ ..] =>
                            (Some(B::from_str(reg).unwrap().lower_u8()), rest),
                        rest => (None, rest),
                    };
                    let opcode = B::from_str(opcode).ok_or_else(|| format!("Bad opcode: {}", opcode))?;
                    if opcode.len() % 8 == 0 {
                        Ok((opcode, reg, rest))
                    } else {
                        Ok((opcode.zero_extend(opcode.len() + 8 - (opcode.len() % 8)), reg, rest))
                    }
                }
                _ => Err(format!("Bad opcode: {:?}", sexp)),
            }
        _ => Err(format!("Bad opcode: {:?}", sexp)),
    }
}

fn parse_operand<'a>(sexp: &Sexp<'a>) -> Result<Operand<'a>, String> {
    use Sexp::*;
    use Operand::*;
    match sexp {
        Seq(items) =>
            match items[..] {
                [Item(reg)] => Ok(Register(reg)),
                [Item(method), Item(typ)] => Ok(Addressing(method, typ)),
                _ => Err(format!("Bad operand: {:?}", sexp)),
            }
        Item(_) => Err(format!("Bad operand: {:?}", sexp)),
    }
}

fn parse_arg<'a>(sexp: &Sexp<'a>) -> Result<Vec<Operand<'a>>, String> {
    use Sexp::*;
    match sexp {
        Seq(items) =>
            match &items[..] {
                [Item("ARG"), Item(":OP1"), op1] => Ok(vec![parse_operand(op1)?]),
                [Item("ARG"), Item(":OP1"), op1, Item(":OP2"), op2] => Ok(vec![parse_operand(op1)?, parse_operand(op2)?]),
                [Item("ARG"), Item(":OP1"), op1, Item(":OP2"), op2, Item(":OP3"), op3] => Ok(vec![parse_operand(op1)?, parse_operand(op2)?, parse_operand(op3)?]),
                [Item("ARG"), Item(":OP1"), op1, Item(":OP2"), op2, Item(":OP3"), op3, Item(":OP4"), op4] => Ok(vec![parse_operand(op1)?, parse_operand(op2)?, parse_operand(op3)?, parse_operand(op4)?]),
                _ => Err(format!("Bad arg: {:?}", sexp)),
            }
        Item("NIL") => Ok(vec![]),
        _ => Err(format!("Bad arg: {:?}", sexp)),
    }
}

impl<'a, B:BV> TryFrom<&'a Sexp<'a>> for Instr<'a, B> {
    type Error = String;

    fn try_from(sexp: &'a Sexp<'a>) -> Result<Self, Self::Error> {
        use Sexp::*;
        let fail = || format!("Bad instruction: {:?}", sexp);
        let items = match sexp { Seq(v) => v, Item(_) => return Err(fail()) };
        match &items[..] {
            [Item("INST"), Item(name), op, arg, implementation, exceptions, ..] => {
                let (opcode, opcode_in_reg, opcode_remainder) = parse_opcode(op)?;
                let operands = parse_arg(arg)?;
                Ok(Instr { name, opcode, opcode_in_reg, opcode_remainder, operands, implementation, exceptions })
            }
            _ => return Err(fail()),
        }
    }
}

impl<'a, B:BV> Instr<'a, B> {
    fn small_description(self: &Instr<'a,B>) -> String {
        format!("{} {:?}", self.name, self.operands)
    }
}

// TODO: should also filter on the mode
fn undefined_or_unsupported<'a, B: BV>(instr: &Instr<'a, B>) -> bool {
    // Avoid segment stuff for now
    if instr.name == "far JMP" {
        true
    } else if instr.opcode_remainder.iter().any(|i| matches!(i, Sexp::Item(":FEAT"))) {
        true
    } else {
        match instr.opcode_remainder {
            [Sexp::Item(":MODE"), Sexp::Item(":I64"), ..] => true,
            _ => match instr.implementation {
                Sexp::Item("NIL") => true,
                Sexp::Seq(items) => matches!(items[..], [Sexp::Item("X86-ILLEGAL-INSTRUCTION" | ":NO-INSTRUCTION"), ..]),
                _ => false,
            }
        }
    }
}

pub fn parse_instrs<'a, B:BV>(sexp: &'a Sexp<'a>) -> Result<Vec<Instr<'a, B>>, String> {
    use Sexp::*;
    let items = match sexp { Seq(v) => v, Item(_) => return Err(format!("Instruction list is not a sequence: {:?}", sexp)) };
    let results: Result<Vec<Instr<'a, B>>, String> = items.iter().map(Instr::try_from).collect();
    results.map(|mut l| l.drain(..).filter(|instr| !undefined_or_unsupported(instr)).collect())
}

fn imm_size<'a>(ty: &'a str) -> usize {
    let opsize = 4;
    match ty {
        // TODO: operand-size attr for C P PD? PS? S? SD? SS? V X Y Z
        "A" => panic!("Memory-only type for immediate operand"),
        "B" => 1,
        "D" => 4,
        "DQ" => 16,     
        "PI" => 16,
        "Q" => 8,
        "SI" => 4,
        "V" => opsize,
        "W" => 2,
        "Y" => 2*opsize, // maybe assert opsize != 1?
        "Z" => if opsize == 2 { 2 } else { 4 },
        _ => panic!("Don't support type {} yet", ty),
    }
}

enum ModRM {
    Reg,
    RMReg,
    RM,
}

pub fn sample<'a,B:BV>(instructions: &[Instr<'a, B>]) -> (B, String) {
    use Operand::*;
    use ModRM::*;

    let mut rng = rand::thread_rng();
    let i = rng.gen_range(0, instructions.len());
    let instr = &instructions[i];
    let mut modrm_reg: Option<u8> = instr.opcode_in_reg.map(|b| b << 3);
    let mut modrm_rm: Option<u8> = None;
    let mut sib: Option<u8> = None;
    let mut imm_bytes = 0;
    let mut disp_bytes = 0;
    let mut fill_modrm = |how| match how {
        Reg =>
            match modrm_reg {
                Some(_) => panic!("Double ModR/M reg operand"),
                None => modrm_reg = Some(rng.gen()),
            }
        RMReg =>
            match modrm_rm {
                Some(_) => panic!("Double ModR/M rm operand"),
                None => modrm_rm = Some(rng.gen()),
            }
        RM =>
            match modrm_rm {
                Some(_) => panic!("Double ModR/M rm operand"),
                None => {
                    let byte = rng.gen();
                    modrm_rm = Some(byte);
                    if byte & 0xc0 == 0 {
                        if byte & 0x7 == 0b100 {
                            sib = Some(rng.gen());
                        } else if byte & 0x7 == 0b101 {
                            disp_bytes = 4;
                        }
                    } else if byte & 0xc0 == 0x40 {
                        disp_bytes = 1;
                        if byte & 0x7 == 0b100 {
                            sib = Some(rng.gen());
                        }
                    } else if byte & 0xc0 == 0x80 {
                        disp_bytes = 4;
                        if byte & 0x7 == 0b100 {
                            sib = Some(rng.gen());
                        }
                    }
                }
            }
    };
    for operand in &instr.operands {
        match operand {
            Addressing("E", _) => fill_modrm(RM),
            Addressing("G", _) => fill_modrm(Reg),
            Addressing("I" ,ty) => imm_bytes += imm_size(ty),
            Addressing("J", ty) => imm_bytes += imm_size(ty),
            Addressing("L", _) => imm_bytes += 1,
            Addressing("M", _) => fill_modrm(RM), // TODO: only memory?
            Addressing("R", _) => fill_modrm(RMReg),
            Addressing("U", _) => fill_modrm(RMReg),
            Addressing("V", _) => fill_modrm(Reg),
            Addressing("W", _) => fill_modrm(RM),
            Addressing("X", _) => (),
            Addressing("Y", _) => (),
            // TODO: Cue for REX prefix?
            Register(_) => (),
            _ => {
                eprintln!("Instruction sampling failure: don't support operand {} for instruction {} yet", operand, instr);
                return sample(instructions);
            }
        }
    }
    // TODO: more operands, prefixes, superscripts
    let modrm = match (modrm_rm, modrm_reg) {
        (None, None) => None,
        _ => {
            let rm = modrm_rm.unwrap_or_else(|| rng.gen());
            let reg = modrm_reg.unwrap_or_else(|| rng.gen());
            Some((rm & 0xc7) | (reg & 0x38))
        }
    };
    let mut encoding_be =
        if let Some(byte) = modrm {
            let e = instr.opcode.append(B::new(byte as u64, 8)).unwrap();
            if let Some(byte) = sib {
                e.append(B::new(byte as u64, 8)).unwrap()
            } else {
                e
            }
        } else {
            instr.opcode
        };
    for _i in 0..disp_bytes {
        encoding_be = encoding_be.append(B::new(rng.gen_range(0,256), 8)).unwrap();
    }
    for _i in 0..imm_bytes {
        encoding_be = encoding_be.append(B::new(rng.gen_range(0,256), 8)).unwrap();
    }
    // The opcode maps are in big endian (?!), and we also add modrm
    // in the least significant byte, so reverse it.
    let encoding = B::from_bytes(&encoding_be.to_le_bytes());
    (encoding, instr.small_description())
}
