// BSD 2-Clause License
//
// Copyright (c) 2020 Brian Campbell
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
use isla_testgen::asl_tag_files;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut opts = getopts::Options::new();
    opts.optflag("h", "help", "print this help message");
    opts.optmulti("t", "tag-file", "Tag file for encodings", "FILE");
    opts.optmulti("", "exclude", "exclude matching instructions from tag file", "<regexp>");
    let matches = opts.parse(&args[1..]).unwrap_or_else(|err| {
        eprintln!("{}", err);
        std::process::exit(1);
    });

    if matches.opt_present("help") {
        print!("{}", opts.usage("Usage: zencode [options] <string> ..."));
        std::process::exit(0);
    }

    let file_names = matches.opt_strs("t");
    let exclusions = matches.opt_strs("exclude");
    let encodings = asl_tag_files::read_tag_files(&file_names, &exclusions);
    for opcode in matches.free {
        let hex = if opcode.starts_with("0x") { &opcode[2..] } else { &opcode };
        let val = u32::from_str_radix(hex, 16).unwrap_or_else(|_| panic!("Bad hex {}", opcode));
        println!("{} is {:?}", opcode, encodings.search(asl_tag_files::Encoding::A64, val));
    }
}
