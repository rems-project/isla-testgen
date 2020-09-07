use isla_testgen::asl_tag_files;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut opts = getopts::Options::new();
    opts.optmulti("t", "tag-file", "Tag file for encodings", "FILE");
    opts.optmulti("", "exclude", "exclude matching instructions from tag file", "<regexp>");
    let matches = opts.parse(&args[1..]).expect("Bad arguments");
    let filename = matches.opt_str("t").expect("No tag file given");
    let exclusions = matches.opt_strs("exclude");
    let encodings = asl_tag_files::read_tag_file(&filename, &exclusions);
    for opcode in matches.free {
        let hex = if opcode.starts_with("0x") { &opcode[2..] } else { &opcode };
        let val = u32::from_str_radix(hex, 16).unwrap_or_else(|_| panic!("Bad hex {}", opcode));
        println!("{} is {:?}", opcode, encodings.search(asl_tag_files::Encoding::A64, val));
    }
}
