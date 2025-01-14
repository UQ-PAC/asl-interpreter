# Online partial evaluation

## Background

Online partial evaluation traverses the specification,
closely mirroring concrete evaluation,
and specialises expressions as it encounters them.
It does this "online" by recording,
for each variable,
whether that variable is a concrete, symbolic, or unknown value
(in order of simplification potential).

- Concrete values are simple literals which can almost always be immediately evaluated
  in expressions.
- Pure symbolic expressions are pure transformations of a combination
  of concrete and symbolic/unknown values.
  For example, this includes "(x + 1) - 1" and this can be used to simplify
  using algebraic properties of integers and bitvectors.
- The last type, unknown, is any computation which is opaque at partial-evaluation time.
  Most often, this is register and memory accesses.
  When encountered in an expression, this will emit code to perform the computation and store
  it into a read-only variable, transforming it into a pure symbolic expression.

## Implementation

Within ASLp, the partial evaluation features are implemented by three files
with different responsibilities.
These are: symbolic.ml, dis.ml, and transforms.ml.
This corresponds to the order from lower-level concepts (expressions)
to higher-level ones (statements and programs).

### symbolic.ml

In the implementation, this begins at the [symbolic.ml](/libASL/symbolic.ml)
file which decribes expression-level symbolic operations.
Here, the type of `sym` is defined simply as either
a concrete value or a pure symbolic expression
(the concept of "unknown" values lives outside this file).

Moreover, this file implements symbolic analogues
of existing primitive operations on concrete values
([value.ml](/libASL/value.ml) and [primops.ml](/libASL/primops.ml])).
Essentially, these functions perform a concrete evaluation
if all (or sufficiently many) operands are concretely known, and
return a symbolic expression otherwise.
The expression may be simplified through the
expression-level simplification whenever
its structure allows.
Some notable instances are:
- identities of bitwise "and" and "or" and integer "mul", "add", and "sub",
- slices of slices,
- (sign/zero) extension of extensions.

### dis.ml

[dis.ml](/libASL/dis.ml) performs a recursive traversal of the ASL AST,
calling functions from symbolic.ml as needed.
This file is responsible for inter-statement and inter-procedural effects,
including the collection of the residual program.

The structure in this file is designed to mirror that of the interpreter's
evaluation methods ([eval.ml](/libASL/eval.ml)).
For instance, there are corresponding functions for expressions:
```ocaml
val dis_expr : AST.l -> AST.expr -> sym rws
val eval_expr : AST.l -> Env.t -> AST.expr -> value
```
Here, the _'a rws_ return value is a computation inside the reader-writer-state monad (discussed below).

The entry-point to the entire partial evaluator is the _dis\_core_ method.
This invokes the appropriate "dis" functions then performs a number of post-processing
transformations, described next.

#### LocalEnv / DisEnv

The LocalEnv structure stores and manipulates location-sensitive information during the
partial evaluation.
Most importantly, this includes the stack 
mappings of variables to their concrete value or pure symbolic expression.
To facilitate easier debugging, this also manually records a stack of the
AST nodes currently being evaluated
(the ordinary stack trace is not useful in the presence of the monad abstraction).

The DisEnv contains the _'a rws_ type &mdash; a reader-writer-state monad:
```ocaml
type 'a rws = Eval.Env.t -> LocalEnv.t -> ('a, LocalEnv.t, stmt list)
```
This implements an abstraction for:
- a read-only view of globals and constants ("eval env"),
- a mutable LocalEnv state ("local env"), and
- a write-only list of statements making up the residual program.

This mechanism is invoked by the `let@` and `let+` syntaxes
which composes RWS computations in a sensible way.
As an example, with many type annotations, consider
```ocaml
val int_is_zero : int rws -> bool rws =
  fun (x : int rws) ->
    let@ y : int = x in
    DisEnv.pure (y = 0)  
```
Essentially, the `let@` notation has the function of "unwrapping" a rws computation
and placing it within another rws computation.
`let+` can be used where the final result (at the bottom of the let expression)
is a `DisEnv.pure` computation.
By using `let+`, the `DisEnv.pure` can be omitted.
Other functions exist to manipulate particular rws computations in particular ways
(e.g. a list of rws can become a rws of list).

The DisEnv struct also contains methods to retrieve variables
(searching the local bindings and then the global bindings),
all returning rws computations.
To emit a statement into the residual program, it provides a `write` function.

### transforms.ml

[transforms.ml](/libASL/transforms.ml) implements transforms which are executed after the
main partial evaluation phase.
Some of these are conventional compiler transformations
(e.g. removing unused variables, common subexpression factoring, and copy-propagation).
The majority, however, are designed to address deficiencies
(verbosity or unsupported constructs) in the residual program.
We list a few transformations which are of particular interest.

- StatefulIntToBits / IntToBits:
  This transformation converts expressions involving arbitrary-precision integers
  into expressions of fixed-length bitvectors
  by way of an interval analysis.

  The StatefulIntToBits modules implements this through abstract interpretation
  with a domain of $\text{Width}\times \text{IsSigned} \times \mathbb Z^2$,
  recording bit-width, signedness, and lower and upper bounds.

- RedundantSlice: Eliminates slice operations which do not reduce the bit-width.
  Crucially, this is also responsible for converting slices with non-static indices
  into shift/truncate operations.
- bits_coerce_narrow: Pushes slices into sub-expressions where possible.
- CaseSimp: Removes unreachable assertions placed after exhaustive case checks.
- RemoveRegisters: Replaces expressions of ASL's register type with ordinary bit-vectors.
- CopyProp
- CommonSubExprElim
- RemoveUnused

## Grammar

The ASL grammar is defined in [asl.ott](/libASL/asl.ott).
The ott program translates this into a Menhir grammar
which then generates a parser and an associated Ocaml AST.
The generated code modules include Asl_ast, Asl_parser, and Asl_parser_pp.


For printing AST nodes and other structures, functions beginning with `pp_` are available
in [asl_utils.ml](/libASL/asl_utils.ml) and [utils.ml](/libASL/utils.ml).
These will produce an indented human-readable string.
To emit AST nodes in the structured "aslt" format,
use `Utils.to_string (Asl_parser_pp.pp_raw_stmt stmt)` or similar.

