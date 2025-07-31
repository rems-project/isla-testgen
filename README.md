# Model based instruction set test generation

Isla-testgen produces short tests of instruction behaviour from Sail
models of an instruction set architecture.  It's primary use was to
check for consistency between the Sail model of the experimental
Morello instruction set, derived from Arm's ASL specifications, and
implementations.  This was described in

> [Verified Security for the Morello Capability-enhanced Prototype Arm
> Architecture](https://doi.org/10.1007/978-3-030-99336-8_7).  Thomas
> Bauereiss, Brian Campbell, Thomas Sewell, Alasdair Armstrong,
> Lawrence Esswood, Ian Stark, Graeme Barnes, Robert N. M. Watson,
> Peter Sewell, ESOP 2022.

alongside our formal proof and other validation work.

See the [LICENSE file](LICENSE) for copyright information and funding
acknowledgements.  In addition, Arm provided valuable cooperation
during the development of this software and the testing of the Morello
specifications.

## Building tests for CHERIoT

This is the most recently used target for testing, and generates tests
that can be run on the Sonata system under verilator simulation.  The
tests finish by sending OK, FAILED, or BAD TEST (if it failed to
construct a capability during setup), then go into a loop.  So when
running the tests set a limit to the number of cycles to execute.

Several pieces of software are required to build the test generator, a
version of the CHERIoT model that's mildly adapted for it, and a
random instruction generator:

1. Ensure that you have
   [Rust](https://www.rust-lang.org/learn/get-started) installed,
   including its "cargo" package manager, and OCaml's
   [opam](https://opam.ocaml.org/) package manager.  These
   instructions were tested with OCaml 5.2.1.
   
   You also need a copy of Z3.  One can be installed using opam if
   necessary.
   
   CHERIoT LLVM should also be built and in your `PATH`.

2. Install [Sail](https://github.com/rems-project/sail).  This was tested
   with an in-development version rather than a release, for
   compatibility clone the repository at commit `bfdeb8cc` and install
   it locally with
   ```
   opam install .
   ```

3. Clone the test generator repository, including the Isla submodule:
   ```
   git clone --recurse-submodules https://github.com/rems-project/isla-testgen.git
   cd isla-testgen
   cargo build --release
   cd isla/isla-sail
   make
   cd ../../..
   ```

4. Clone and build the adapted CHERIoT model:
   ```
   PATH=$PATH:`pwd`/isla-testgen/isla/isla-sail
   git clone https://github.com/bacam/2025-lowrisc-cheriot-sail.git cheriot-sail
   cd cheriot-sail
   make generated_definitions/riscv_model_RV32.ir
   ```
   
5. Clone and build the random instruction generator:
   ```
   git clone https://github.com/rems-project/sail-riscv-test-generation.git
   cd sail-riscv-test-generation
   make
   ```

7. The file `sonata-command` contains an example command line
   to generate a single test with five randomly chosen instructions, and can be
   run with `bash`.  There are a couple of commented out lines at the
   bottom which would generate a set of larger tests.
   
   A set of tests for all of the feasible paths of one instruction
   given by `--all-paths-for` and the number of the instruction in the
   sequence (starting at 0).

### Running the Sail C simulator with coverage

1. Build the coverage support tool and library for Sail

  ```
  cd sail/sailcov
  make
  cd `sail --dir`/lib/coverage
  cargo build --release
  ```

2. Build the C simulator with coverage support

  ```
  cd cheriot-sail
  make csim SAILCOV=yes
  ```

3. Run some tests (adjusting the paths as necessary)

  ```
  for f in *.elf; do .../cheriot-sail/c_emulator/cheriot_sim -l 1000 $f; done
  ```

  The raw coverage information will be appended to `sail_coverage`.

4. Generate a coverage report in the current directory.

  ```
  .../sail/sailcov/sailcov -t sail_coverage -a .../cheriot-sail/generated_definitions/c/all_branches .../cheriot-sail/src/*.sail .../cheriot-sail/sail-riscv/model/*.sail --index index --colour-by-count
  ```
  Multiple `-t` options can be given to combine several `sail_coverage` files.

## Building tests for Morello

The `morello-public` tag matches the instructions below, but uses
quite old versions of the software.  The HEAD will require more recent
versions of the dependencies, but might have suffered a little due to
work on other targets.

### Building and generating tests

Several pieces of software are required to build the test generator, a
version of the Morello model that's adapted for it, and a file with
the instruction encodings:

1. Ensure that you have
   [Rust](https://www.rust-lang.org/learn/get-started) installed,
   including its "cargo" package manager, and OCaml's
   [opam](https://opam.ocaml.org/) package manager.  These
   instructions were tested with OCaml 4.12.1.
   
   You also need a copy of Z3.  One can be installed using opam if
   necessary.

2. Install [Sail](https://github.com/rems-project/sail).  Isla
   currently uses an in-development version rather than a release, for
   compatibility clone the repository at commit `e5bbe70f` and install
   it locally with
   ```
   opam install .
   ```

3. Clone the test generator repository, including the Isla submodule:
   ```
   git clone --recurse-submodules https://github.com/rems-project/isla-testgen.git
   cd isla-testgen
   cargo build --release
   cd isla/isla-sail
   make
   cd ../../..
   ```

4. Clone and build the Morello model:
   ```
   PATH=$PATH:`pwd`/isla-testgen/isla/isla-sail
   git clone https://github.com/CTSRD-CHERI/sail-morello.git
   cd sail-morello
   make gen_testgen
   ```
   
   The "testgen" build of the model includes some assertions to avoid
   a few unsupported situations, and partially modelling of exclusive
   memory access instructions.
   
   If you also want to run tests against the Sail generated C simulator run
   ```
   make gen_c DEVICES=devices.sail
   ```
5. Clone tools for handling Arm XML specs (to process the instruction encodings)
   ```
   git clone https://github.com/rems-project/mra_tools.git
   ```

6. Download [Arm's Morello ISA
   XML](https://developer.arm.com/documentation/ddi0606/latest) that
   the instruction encodings can be extracted from.  Then use the
   tools to produce the "tag" file:
   ```
   mra_tools/bin/instrs2asl.py --altslicesyntax --demangle --verbose -o morello ISA_A64_xml_morelloA-2022-01
   ```

7. The file `public-morello-command` contains an example command line
   to generate a single test with a couple of instructions, and can be
   run with `bash`.  There are a couple of commented out lines at the
   bottom which would generate a set of larger tests.
   
   One of the instructions in the trace can be allowed to take
   processor exceptions using the `--exceptions-at` option, and a test
   generated for all of the paths through one instruction given by
   `--all-paths-for`.
   
   Tests can be run against the Sail C simulator (which can be built
   from the sail-morello repository above), and qemu:
   ```
   sail-morello/c/morello -e test.elf
   qemu-system-morello -machine morello -cpu morello -nographic -monitor none -kernel test.elf
   ```
