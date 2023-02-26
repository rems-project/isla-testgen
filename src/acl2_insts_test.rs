use std::io;

use isla_lib::bitvector::b129::B129;

use isla_testgen::acl2_insts_parser;
use isla_testgen::acl2_insts::parse_instrs;
use isla_testgen::acl2_insts::sample;

fn main() {
    let input = io::read_to_string(io::stdin()).unwrap();
    let sexp = acl2_insts_parser::SexpParser::new().parse(&input).unwrap();
    let instrs = parse_instrs::<B129>(&sexp).unwrap();
    for instr in &instrs {
        println!("{}", instr);
    }
    let (encoding, description) = sample(&instrs);
    println!("Random instruction: {} {}", encoding, description);
}
