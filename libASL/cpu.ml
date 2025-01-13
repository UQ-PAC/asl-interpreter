(****************************************************************
 * CPU interface
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

module AST = Asl_ast

open Asl_utils

type gen_backend =
    | Ocaml
    | Cpp
    | Scala

type gen_function = AST.ident -> Eval.fun_sig -> Eval.fun_sig Bindings.t -> Eval.fun_sig Bindings.t -> string -> unit

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

let mkCPU (env : Eval.Env.t) (denv: Dis.env): cpu =
    let loc = AST.Unknown in

    let reset (_ : unit): unit =
        Eval.eval_proccall loc env (AST.FIdent ("__TakeColdReset", 0)) [] []

    and step (_ : unit): unit =
        Eval.eval_proccall loc env (AST.FIdent ("__InstructionExecute", 0)) [] []

    and getPC (_ : unit): Primops.bigint =
        let r = Eval.eval_funcall loc env (AST.FIdent ("__getPC", 0)) [] [] in
        Value.to_integer loc r

    and setPC (x : Primops.bigint): unit =
        let a = Value.VInt x in
        Eval.eval_proccall loc env (AST.FIdent ("__setPC", 0)) [] [a]

    and elfwrite (addr: Int64.t) (b: char): unit =
        let a = Value.VBits (Primops.mkBits 64 (Z.of_int64 addr)) in
        let b = Value.VBits (Primops.mkBits  8 (Z.of_int (Char.code b))) in
        Eval.eval_proccall loc env (AST.FIdent ("__ELFWriteMemory", 0)) [] [a; b]

    and opcode (iset: string) (opcode: Primops.bigint): unit =
        let decoder = Eval.Env.getDecoder env (Ident iset) in
        Eval.eval_decode_case AST.Unknown env decoder opcode

    and sem (iset: string) (opcode: Primops.bigint): unit =
        let decoder = Eval.Env.getDecoder env (Ident iset) in
        List.iter
            (fun s -> Printf.printf "%s\n" (pp_stmt s))
            (Dis.dis_decode_entry env denv decoder opcode)

    and gen (iset: string) (pat: string) (include_pc: bool) (backend: gen_backend) (dir: string): unit =
        if not (Sys.file_exists dir) then failwith ("Can't find target dir " ^ dir);

        (* Build the symbolic lifter *)
        let (decoder_id,decoder_fnsig,tests,instrs) = Symbolic_lifter.run_marshal include_pc iset pat env in

        let run_gen_backend : gen_function =
            match backend with
            | Ocaml -> Ocaml_backend.run
            | Cpp -> Cpp_backend.run
            | Scala -> Scala_backend.run
        in

        (* Build backend program *)
        run_gen_backend decoder_id decoder_fnsig tests instrs dir

    in
    {
        env      = env;
        denv     = denv;
        reset    = reset;
        step     = step;
        getPC    = getPC;
        setPC    = setPC;
        elfwrite = elfwrite;
        opcode   = opcode;
        sem      = sem;
        gen      = gen
    }

(****************************************************************
 * End
 ****************************************************************)
