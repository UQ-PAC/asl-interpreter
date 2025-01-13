(****************************************************************
 * CPU interface
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

type gen_backend =
    | Ocaml
    | Cpp
    | Scala

type gen_function = Asl_ast.ident -> Eval.fun_sig -> Eval.fun_sig Asl_utils.Bindings.t -> Eval.fun_sig Asl_utils.Bindings.t -> string -> unit

type cpu = {
    env      : Eval.Env.t;
    denv     : Dis.env;
    reset    : unit -> unit;
    step     : unit -> unit;
    getPC    : unit -> Primops.bigint;
    setPC    : Primops.bigint -> unit;
    elfwrite : Int64.t -> char -> unit;
    opcode   : string -> Primops.bigint -> unit;
    sem      : string -> Primops.bigint -> unit;
    gen      : string -> string -> bool -> gen_backend -> string -> unit;
}

val mkCPU : Eval.Env.t -> Dis.env -> cpu

(****************************************************************
 * End
 ****************************************************************)
