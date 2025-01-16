# *ASLp* - ASL Partial Evaluator

This forks ASLi to extract usable semantics from the
architecture specifications.
The semantics produced are in ASL but are reduced to contain
only simple control flow and scalar types,
for use in further static analysis.

## Introduction

Example implementation of Arm's Architecture Specification Language (ASL).

The ASL interpreter is a collection of resources to help you to
understand and make use of Arm's architecture specifications.
It consists of lexer, parser, typechecker and interpreter for the ASL language
and an interactive interface for evaluating ASL statements and expressions.

There is a [blog post](https://alastairreid.github.io/using-asli/)
describing how to use ASLi with Arm's v8.6-A ISA specification.

## Requirements

To build and run the ASL interpreter, you will need:

  * OCaml version 4.14 or later
  * OPAM OCaml version 2.0.5 (other versions may work)
  * The following OPAM packages
      * ocaml     - OCaml compiler
      * odoc      - OCaml documentation generator (optional)
      * dune      - OCaml build system
      * menhir    - parser generator tool
      * ott       - tool for defining language grammars and semantics
      * linenoise - OCaml line editing library
      * pprint    - OCaml pretty-printing library
      * z3        - OCaml bindings for the Z3 SMT solver
      * zarith    - OCaml multiprecision arithmetic library



## Building and development

### Directory structure

This interpreter consists of a single directory organized as follows

  * Metadata, documentation, etc:
      * `LICENCE`             - Software licence
      * `README.md`           - This file
      * `Makefile`            - build system file
  * Source code consisting of
      * Lexer
          * `libASL/lexer.mll`       - ASL lexer (ocamllex file)
          * `libASL/lexersupport.ml` - indentation-based parsing support
      * Grammar and Parser
          * `libASL/asl.ott`         - used to generate the ASL parser and abstract syntax tree (OTT file)
          * `libASL/asl_visitor.ml`  - code to traverse abstract syntax tree
          * `libASL/asl_utils.ml`    - code to transform abstract syntax tree
      * Typechecker
          * `libASL/tcheck.ml`       - typechecker
      * Interpreter
          * `libASL/primops.ml`      - implementation of ASL builtin types and operations
          * `libASL/value.ml`        - interpreter support code
          * `libASL/eval.ml`         - evaluator for ASL language
      * **ASLp additions**
          * `libASL/dis.ml`          - main partial evaluation disassembler (follows structure of eval.ml)
          * `libASL/symbolic.ml`     - primitives for working with and simplifying symbolic bitvector values
          * `libASL/rws.ml`          - the reader-writer-state monad, used in dis.ml
          * `libASL/testing.ml`      - differential testing of ASLp against the ASLi interpreter
      * ASL standard library
          * `libASL/prelude.asl`     - builtin types and functions
      * Programs
          * `bin/asli.ml`         - interactive ASL tool
          * `bin/testlexer.ml`    - test program that converts ASL code to list of tokens
      * Misc
          * `libASL/utils.ml`        - utility code
  * Code copied from other open source projects
      * `libASL/visitor.ml`

### Installing with Nix

ASLp can be installed as a Nix package from https://github.com/katrinafyi/pac-nix.
The _aslp_ provides ASLp bundled with ARM's specifications.
If you don't plan on modifying the tool, this is a fast and easy way to get started.
If installed via Nix, the following installation steps are not necessary.

### Installing dependencies

Platform specific instructions:
```
    MacOS:
        brew install opam
        brew install gmp mpir
    Ubuntu:
        sudo apt-get install opam libpcre3-dev
    OpenSUSE:
        sudo zypper install ocaml opam ocaml-ocaml-compiler-libs-devel
```

First-time only (if you have not previously set up an opam switch environment):

```bash
    opam init  # answer y/n depending on your preference
    opam switch create ocaml.4.14.2  # or later
    eval `opam env`
```

Platform-independent instructions:

```bash
    # Install dependencies from asli.opam file
    opam install --deps-only --with-test ./asli.opam

    # the following are optional and only needed if modifying asli code
    opam install odoc
    opam install ocamlformat

    # On OSX, you may need to use this command to install zarith
    env CFLAGS="-I$HOME/homebrew/include/" LDFLAGS="-L$HOME/homebrew/lib/" opam install zarith
```

You may also need to execute this command

```
    MacOS: export DYLD_LIBRARY_PATH=`opam config var z3:lib`
    Linux: export LD_LIBRARY_PATH=`opam config var z3:lib`
```


### Building

To build the ASL lexer and ASL interpreter, execute this command.

```
    make install
```

If you get a lot of linker errors involving Z3, double-check that you installed
the right version.

### Building for use in other projects

If you need to use ASLp or libASL as a dependency in another OCaml project,
these steps will install the package in a location discoverable by opam and dune.

After installing dependencies and testing the build, run these commands in this directory:
```
    dune build
    dune install -p asli
```
Once complete, you can verify the package is installed by running `ocamlfind query asli`.

#### ASLp Offline OCaml lifter

To build the offline lifter, which depends on the main ASLp package, first install the ASLp
package as above.
Then, use:
```bash
dune build -p aslp_offline
dune install -p aslp_offline
```
Note: this uses the installed copy of ASLp to generate the offline lifter.
If you want to simultaneously build ASLp and use this version to generate the lifter,
use `dune build offlineASL`.

Basically, `-p` acts as if all packages other than the one listed
do not exist in this dune project, forcing it to look elsewhere.
This can be useful when building and installing packages individually.



### Using ASL lexer

This displays a list of tokens in an ASL file including the indent
and dedent tokens used to support indentation-based parsing.

```
    $ dune exec bin/testlexer.exe prelude.asl
```

### Using ASL interpreter

This reads ASL files specified on the command line and
provides an interactive environment for executing ASL
statements and expressions.

```
    $ asli
                _____  _       _    ___________________________________
        /\     / ____|| |     (_)   ASL interpreter
       /  \   | (___  | |      _    Copyright Arm Limited (c) 2017-2019
      / /\ \   \___ \ | |     | |
     / ____ \  ____) || |____ | |   Version 0.1.1 alpha
    /_/    \_\|_____/ |______||_|   ___________________________________

    Type :? for help
    ASLi> 1+1
    2
    ASLi> ZeroExtend('11', 32)
    '00000000000000000000000000000011'
    ASLi> bits(32) x = ZeroExtend('11', 32);
    ASLi> x
    '00000000000000000000000000000011'
    ASLi> :quit
```

### Using the ASL partial evaluator

Arm's specification files are shipped with the ASLp fork in the mra\_tools/ subfolder.
We also define a small number of overrides in tests/override.asl and tests/override.prj.
These provide alternative but equivalent definitions of some pre-defined functions
which are more suitable for partial evaluation.
(See [alastairreid/asl-interpreter](https://github.com/alastairreid/asl-interpreter#using-asl-interpreter-with-arms-public-specifications) for more details.)

These specification files will be automatically loaded when running ASLp
through dune.
For example, to print the partially-evaluated semantics of the `add x1, x2, x3, LSL 4` instruction:
```bash
$ dune exec asli
ASLi> :sem A64 0x8b031041
Decoding instruction A64 8b031041
__array _R [ 1 ] = add_bits.0 {{ 64 }} ( __array _R [ 2 ],append_bits.0 {{ 60,4 }} ( __array _R [ 3 ] [ 0 +: 60 ],'0000' ) ) ;
ASLi>

```
LLVM can be used to obtain the bytecode for a particular instruction mnemonic:
```bash
$ echo 'add x1, x2, x3, LSL 4' |
    clang -x assembler -target aarch64 - -c -o/dev/stdout |
    llvm-objdump - -d --section=.text |
    tail -n1
0: 8b031041      add     x1, x2, x3, lsl #4
```

To obtain the semantics in a more machine-readable format, called "aslt", you can use the `:ast` command
(the output below has been manually wrapped for clarity).
```bash
ASLi> :ast A64 0x8b031041
Stmt_Assign(
  LExpr_Array(LExpr_Var("_R"),1),
  Expr_TApply("add_bits.0",[64],[
    Expr_Array(Expr_Var("_R"),2);
    Expr_TApply("append_bits.0",[60;4],[
      Expr_Slices(Expr_Array(Expr_Var("_R"),3),[Slice_LoWd(0,60)]);'0000'])]))
```
The aslt format is also produced by the aslp-server program which serves a HTTP endpoint to request
disassembly of opcodes.
We provide an ANTLR grammar for this format, available at [libASL/Semantics.g4](libASL/Semantics.g4).

The interpreter's evaluation (inherited from the original ASLi) can be tested with these commands:
```
:init globals
:init regs
:set +eval:concrete_unknown
:project tests/test.prj
```

This test program prints the line "Test" so you should see output like this
```
ASLi> :project tests/test.prj
Loading ELF file tests/test_O2.elf.
Entry point = 0x400168
Test
Program exited by writing ^D to TUBE
Exception taken
```

Enjoy!

### Testing

The project's tests are defined within the tests/ directory and you can invoke them through dune.
This command will run the regular test suite, taking about 30 seconds.
Included in this suite, we have basic tests of the disassembling opcodes and parsing the aslt output with ANTLR
(the ANTLR tests require Java on your PATH and will fail without them).
```bash
dune runtest
```
To run a more thorough test, taking at least 5 minutes, use this command (see next section for more details).
```bash
dune build @coverage
```

Most of the tests are [cram tests](https://dune.readthedocs.io/en/latest/reference/cram.html) which describe shell
commands to run alongside their expected output.
This means they can be useful to see examples of ASLp's output formats.
[tests/aslt/test_dis.t](tests/aslt/test_dis.t) processes a short list of common instructions to obtain their their pretty-printed and aslt semantics.
[tests/aslt/test_cntlm.t](tests/aslt/test_cntlm.t) runs a list of instructions extracted from a binary program, but the output is from the ANTLR test harness
so it is less readable.

For the coverage tests, the tests are simple diff tests against an expected output file.

In both cases, dune will report test failures as a difference against the expected output.
[`dune promote`](https://dune.readthedocs.io/en/latest/concepts/promotion.html)
can be used to update the expected files with the output from the latest run.

#### Differential testing

The `:coverage` command is used to test equivalence of the partial evaluator and the interpreter.
It takes a regular expression of an instruction group, then generates and evaluates the partially evaluated
ASL as well as the original ASL and compares the final states.
Instruction groups can be found in the [mra_tools/arch/arch_instrs.asl](mra_tools/arch/arch_instrs.asl) file.
```
ASLi> :coverage A64 aarch64_integer.+
[...]
0x1ac04c3f: [sf=0 ; Rm=0 ; C=0 ; sz=3 ; Rn=1 ; Rd=31] --> UNDEFINED (file "./mra_tools/arch/arch_decode.asl" line 3715 char 66 - line 3716 char 28)
0x1ac04fe0: [sf=0 ; Rm=0 ; C=0 ; sz=3 ; Rn=31 ; Rd=0] --> UNDEFINED (file "./mra_tools/arch/arch_decode.asl" line 3715 char 66 - line 3716 char 28)
0x1ac04fe1: [sf=0 ; Rm=0 ; C=0 ; sz=3 ; Rn=31 ; Rd=1] --> UNDEFINED (file "./mra_tools/arch/arch_decode.asl" line 3715 char 66 - line 3716 char 28)
0x1ac04fff: [sf=0 ; Rm=0 ; C=0 ; sz=3 ; Rn=31 ; Rd=31] --> UNDEFINED (file "./mra_tools/arch/arch_decode.asl" line 3715 char 66 - line 3716 char 28)
0x1ac05000: [sf=0 ; Rm=0 ; C=1 ; sz=0 ; Rn=0 ; Rd=0] --> OK
0x1ac05001: [sf=0 ; Rm=0 ; C=1 ; sz=0 ; Rn=0 ; Rd=1] --> OK
0x1ac0501f: [sf=0 ; Rm=0 ; C=1 ; sz=0 ; Rn=0 ; Rd=31] --> OK
0x1ac05020: [sf=0 ; Rm=0 ; C=1 ; sz=0 ; Rn=1 ; Rd=0] --> OK
[...]
```

"OK" indicates the machine state after both executions are the same,
as we would expect if the partial evaluation is correct.
UNDEFINED means that particular bytecode is an undefined case in the architecture.
If an exception occurs somewhere else in the process, that will be reported as well.

## Publication

- Lam, K., & Coughlin, N. (2023).
Lift-off: Trustworthy ARMv8 semantics from formal specifications.
In A. Nadel & K. Y. Rozier (Eds.),
_Proceedings of the 23rd Conference on Formal Methods in Computer-Aided Design – FMCAD 2023_
(pp. 274–283).
TU Wien Academic Press.
[10.34727/2023/isbn.978-3-85448-060-0_36](https://doi.org/10.34727/2023/isbn.978-3-85448-060-0_36)

## License and contribution

The software is provided under the [BSD-3-Clause licence](https://spdx.org/licenses/BSD-3-Clause.html).
Contributions to this project are accepted under the same licence.

This software includes code from one other open source projects

 * The [CIL project](https://people.eecs.berkeley.edu/~necula/cil/)
   defines a useful
   [visitor class](https://github.com/cil-project/cil/blob/936b04103eb573f320c6badf280e8bb17f6e7b26/src/cil.ml#L931)
   for traversing C ASTs.
   The file `visitor.ml` is a modified copy of this class that generalizes
   the type to work with an arbitrary AST.

   CIL is distributed under a [BSD-3-Clause licence](https://github.com/cil-project/cil/blob/develop/LICENSE).
