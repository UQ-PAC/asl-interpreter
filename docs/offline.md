# Offline partial evaluation

## Motivation

The offline partial evaluation is motivated by improving the experience
for users seeking to integrate ASLp within other tools.
With the original online method,
only one opcode could be processed at a time, and
each new opcode would require a complete traversal and simplification
of the ASL specification.
This is obviously inefficient
and necessitates a tight coupling between ASLp
and programs looking to use it.

## Introduction

Offline partial evaluation aims to improve this
by performing much of the partial evaluation _ahead-of-time_
instead of once per-instruction.
In the offline method,
partial evaluation operates with only the knowledge
that the opcode is constant,
but without knowledge of the _value_ of the opcode.

Further,
we desire a separation of the "decoding" phase
(where opcode bits are examined to determine _which_ instruction is represented),
and the "execution" phase (where opcodes are executed and their actions performed).
This delineation is implemented by hand-written lifters,
where the language of the semantics IR is separate from the language used to implement the lifter itself.

ASL itself has no such separation, but we can compute it with a _binding-time analysis_.
In this analysis,
constants and the instruction opcode are marked as *lift-time*, then the analysis
traverses the AST in this way:
- if an expression uses only lift-time values, it is also marked as *lift-time*, otherwise
- the expression is marked as *run-time*.
Lift-time values are simply emitted into the lifter's language, and
will not be visible within the final semantics.
Run-time-marked values are translated to a `gen_` prefixed function,
indicating that this should be emitted into the semantics and deferred until run-time.
This gives us an AST for a program which takes an opcode and then constructs a residual program
representing the semantics of the instruction.

In particular, this representation
within an AST
enables efficient translation of the lifter to arbitrary lifter languages and semantics languages.
This is desirable, entirely eliminating the need to (de)serialise
the semantics and communicate across language boundaries.

## Overview

The entry-point for the offline transformation process is the `run` function,
near the end of [symbolic_lifter.ml](/libASL/symbolic_lifter.ml).
Here, the process is divided into stages:
- **Stage 1** - mock decoder & instruction encoding definitions:
  Converts the ASL decoder tree into separate functions making up a proper ASL program.
  Makes use of [decoder_program.ml](/libASL/decoder_program.ml).
- **Stage 2** - call graph construction:
  Identifies reachable functions, using [call_graph.ml](/libASL/call_graph.ml).
- **Stage 3** - simplification:
  Minor cleanup of temporary dynamic-length bit-vectors and unsupported structures.
- **Stage 4** - specialisation:
  Performs requirement analysis to ensure bit-vector lengths
  and loop iterations are statically known.
  Inserts splits to branch on conditions determining these quantities. [req_analysis.ml](/libASL/req_analysis.ml).
- **Stage 5** - disassembly:
  Invokes the online partial evaluation to reduce and inline structures, then
  simplifies with BDDs (an opcode-sensitive value analysis to, e.g., eliminate always-true assertions),
- **Stage 6** - cleanup:
  Remove unused variables within each instruction function.
- **Stage 7** - offline transform:
  Performs binding-time analysis and transformations,
  then BDD-based copy-propagation transform and one final cleanup. [offline_opt.ml](/libASL/offline_opt.ml).

After the lifter is generated, it is passed to a "backend"
which performs the (mostly syntactic) translation
to a targeted lifter language.

## Backends

TODO: mechanism of a backend and how to implement one.

- given a set of instruction functions
- instruction-building interface
- required: mutable variables, bitvector, bool, and int representations
