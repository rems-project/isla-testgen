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
    pub operands: Vec<Operand<'a>>,
}

impl<'a> fmt::Display for Operand<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<'a, B:BV> fmt::Display for Instr<'a, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} [", self.name, self.opcode)?;
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
        write!(f, "]")
    }
}

fn parse_opcode<'a, B:BV>(sexp: &Sexp<'a>) -> Result<B, String> {
    use Sexp::*;
    match sexp {
        Seq(items) =>
            match items[..] {
                [Item("OP"), Item(":OP"), Item(opcode), ..] => {
                    let opcode = B::from_str(opcode).ok_or_else(|| format!("Bad opcode: {}", opcode))?;
                    if opcode.len() % 8 == 0 {
                        Ok(opcode)
                    } else {
                        Ok(opcode.zero_extend(opcode.len() + 8 - (opcode.len() % 8)))
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

impl<'a, B:BV> TryFrom<&Sexp<'a>> for Instr<'a, B> {
    type Error = String;

    fn try_from(sexp: &Sexp<'a>) -> Result<Self, Self::Error> {
        use Sexp::*;
        let fail = || format!("Bad instruction: {:?}", sexp);
        let items = match sexp { Seq(v) => v, Item(_) => return Err(fail()) };
        match &items[..] {
            [Item("INST"), Item(name), op, arg, ..] => {
                let opcode = parse_opcode(op)?;
                let operands = parse_arg(arg)?;
                Ok(Instr { name, opcode, operands })
            }
            _ => return Err(fail()),
        }
    }
}

pub fn parse_instrs<'a, B:BV>(sexp: &Sexp<'a>) -> Result<Vec<Instr<'a, B>>, String> {
    use Sexp::*;
    let items = match sexp { Seq(v) => v, Item(_) => return Err(format!("Instruction list is not a sequence: {:?}", sexp)) };
    items.iter().map(Instr::try_from).collect()
}

pub fn sample<'a,B:BV>(instructions: &[Instr<'a, B>]) -> (B, &'a str) {
    use Operand::*;

    let mut rng = rand::thread_rng();
    let i = rng.gen_range(0, instructions.len());
    let instr = &instructions[i];
    let mut modrm: Option<u8> = None;
    let mut fill_modrm = || match modrm { Some(_) => (), None => modrm = Some(rng.gen()) };
    for operand in &instr.operands {
        match operand {
            Addressing("E", _) => fill_modrm(),
            Addressing("G", _) => fill_modrm(),
            Addressing("M", _) => fill_modrm(),
            // TODO: Cue for REX prefix?
            Register(_) => (),
            _ => panic!("Don't support operand {} yet", operand),
        }
    }
    // TODO: more operands, prefixes
    let encoding_be =
        if let Some(byte) = modrm {
            instr.opcode.append(B::new(byte as u64, 8)).unwrap()
        } else {
            instr.opcode
        };
    // The opcode maps are in big endian (?!), and we also add modrm
    // in the least significant byte, so reverse it.
    let encoding = B::from_bytes(&encoding_be.to_le_bytes());
    (encoding, instr.name)
}
