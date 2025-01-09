(****************************************************************
 * Test ASL evaluator
 *
 * Copyright Arm Limited (c) 2017-2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

open LibASL
open Asl_utils
open AST

module TC  = Tcheck
module AST = Asl_ast

let mra_tools () = List.map (fun x -> LoadASL.FileSource x) [
    "../../../mra_tools/arch/regs.asl";
    "../../../mra_tools/types.asl";
    "../../../mra_tools/arch/arch.asl";
    "../../../mra_tools/arch/arch_instrs.asl";
    "../../../mra_tools/arch/arch_decode.asl";
    "../../../mra_tools/support/aes.asl";
    "../../../mra_tools/support/barriers.asl";
    "../../../mra_tools/support/debug.asl";
    "../../../mra_tools/support/feature.asl";
    "../../../mra_tools/support/hints.asl";
    "../../../mra_tools/support/interrupts.asl";
    "../../../mra_tools/support/memory.asl";
    "../../../mra_tools/support/stubs.asl";
    "../../../mra_tools/support/fetchdecode.asl"
]

let format_value f v = Format.fprintf f "%s" (Value.pp_value v)
let value = Alcotest.testable format_value ( = )

let check_int what l r = Alcotest.check value what l (Value.VInt (Z.of_int r))

let eval tcenv env (input : string): Value.value =
    let loc = AST.Unknown in
    let e = LoadASL.read_expr tcenv loc input in
    Eval.eval_expr loc env e

let test_arith tcenv env () : unit =
    check_int "1+1 == 2" (eval tcenv env "1+1") 2;
    check_int "5 DIV 3 == 1" (eval tcenv env "5 DIV 3") 1

let compare_env (env1: Eval.Env.t) (env2: Eval.Env.t) (opcode: string): unit =
    List.iter (fun (key, v1) ->
        if not (Bindings.mem key (Eval.Env.getGlobals env2).bs) then
            Alcotest.failf "disEvalEnv does not contain variable: %s\n" (pprint_ident key)
        else
            let v2 = Bindings.find key (Eval.Env.getGlobals env2).bs in
            Alcotest.check value (opcode ^ ": evalEnv." ^ (pprint_ident key) ^ " = disEvalEnv." ^ (pprint_ident key)) v1 v2
    ) (Bindings.bindings (Eval.Env.getGlobals env1).bs)

let test_compare env () : unit =
    let decoder = Eval.Env.getDecoder env (Ident "A64") in
    let inchan = open_in "../../../tests/instructions_short.txt" in
    (try
        while true do
            (* Set up our environments *)
            let initEnv = Eval.Env.copy env in
            (* Obtain and set random initial values for _R registers. *)
            Random.self_init ();
            let vals = (List.init 64 (fun _ -> Z.of_int64 (Random.int64 Int64.max_int))) in
            Eval.initializeRegistersAndMemory initEnv vals;
            (* Replace remaining VUninitialized with default zero values. *)
            Eval.initializeGlobals initEnv;

            (*  Disassembly uses original uninitialised environment.
                Others use the randomly initialised environment for full evaluation. *)
            let disEnv = Eval.Env.copy env in
            let evalEnv = Eval.Env.copy initEnv in
            let disEvalEnv = Eval.Env.copy initEnv in
            let lenv = Dis.build_env disEnv in

            let opcode = input_line inchan in
            let op = Z.of_string opcode in

            (try
                (* Evaluate original instruction *)
                Eval.eval_decode_case AST.Unknown evalEnv decoder op;

                (try
                    (* Generate and evaluate partially evaluated instruction *)
                    let disStmts = Dis.dis_decode_entry disEnv lenv true decoder op in
                    List.iter (Eval.eval_stmt disEvalEnv) disStmts;

                    compare_env evalEnv disEvalEnv opcode
                with
                    Value.EvalError (loc, message) -> Alcotest.failf "Disassembled statement eval failed: %s\n" message
                )
            with
                Value.EvalError _ -> () (* We don't care what our implementation does if the original evaluation fails *)
            )
        done
    with
    | End_of_file ->
        close_in inchan
    )

let tests : unit Alcotest.test_case list =
    let prelude = LoadASL.read_file (FileSource "../../../prelude.asl") true false in
    let mra = List.map (fun tool -> LoadASL.read_file tool false false) (mra_tools ()) in
    let tcenv   = TC.Env.mkEnv !TC.env0 in
    let env     = Eval.build_evaluation_environment (prelude @ List.concat mra) in
    [
        ("arith", `Quick, test_arith tcenv env);
        ("compare", `Quick, test_compare env)
    ]

let () = Alcotest.run "libASL" [("asl", tests)]

(****************************************************************
 * End
 ****************************************************************)
