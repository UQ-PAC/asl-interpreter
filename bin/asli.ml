(****************************************************************
 * ASL interactive frontend
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** ASL interactive frontend *)

open LibASL

open Asl_ast
open Value
open Eval
open Asl_utils

module Parser = Asl_parser
module TC     = Tcheck
module PP     = Asl_parser_pp
module AST    = Asl_ast

let opt_prelude : string ref = ref "prelude.asl"
let opt_filenames : string list ref = ref []
let opt_print_version = ref false
let opt_no_default_aarch64 = ref false
let opt_export_aarch64_dir = ref ""
let opt_verbose = ref false


let () = 
    Printexc.record_backtrace true ;
    Printexc.register_printer
    (function
    | Value.EvalError (loc, msg) ->
        Some (Printf.sprintf "EvalError at %s: %s" (pp_loc loc) msg)
    | _ -> None)

let help_msg = [
    {|:? :help                       Show this help message|};
    {|:elf <file>                    Load an ELF file|};
    {|:opcode <instr-set> <int>      Decode and execute opcode|};
    {|:sem <instr-set> <int>         Decode and print opcode semantics|};
    {|:ast <instr-set> <int> [file]  Decode and write opcode semantics to stdout or a file, in a structured ast format|};
    {|:gen <instr-set> <regex>       Generate an offline lifter using the given backend|};
    {|      [pc-option] [backend] [dir]|};
    {|:project <file>                Execute ASLi commands in <file>|};
    {|:q :quit                       Exit the interpreter|};
    {|:run                           Execute instructions|};
    {|:set impdef <string> = <expr>  Define implementation defined behavior|};
    {|:set +<flag>                   Set flag|};
    {|:set -<flag>                   Clear flag|};
    {|:init globals                  Initializes global variables to concrete values (for evaluation)|};
    {|:init regs                     Initializes registers to concrete values (for evaluation)|};
    {|:coverage <instr-set> <regex>  Runs differential testing of partial and concrete evaluation|};
    {|<expr>                         Execute ASL expression|};
    {|<stmt> ;                       Execute ASL statement|}
]

(** supported backends for :gen and their default output directories *)
let gen_backends = [
    ("scala", (Cpu.Scala, "offlineASL-scala/lifter/src/generated"));
    ("ocaml", (Cpu.Ocaml, "offlineASL"));
    ("cpp",   (Cpu.Cpp, "offlineASL-cpp/subprojects/aslp-lifter"));
]

let () = Random.self_init ()

let rec process_command (tcenv: TC.Env.t) (cpu: Cpu.cpu) (fname: string) (input0: string): unit =
    let input = String.trim input0 in
    (match String.split_on_char ' ' input with
    | [""] ->
        ()
    | [":init"; "globals"] ->
        Eval.initializeGlobals cpu.env;
    | [":init"; "regs"] ->
        let vals = (List.init 64 (fun _ -> Z.of_int64 (Random.int64 Int64.max_int))) in
        Eval.initializeRegistersAndMemory cpu.env vals;
    | ":enumerate" :: iset :: tail ->
        let (start,stop,fname) = (match tail with
        | [start;stop;fname] -> (int_of_string start, int_of_string stop, fname)
        | [] -> (0, Int.shift_left 1 32, "ops.txt")
        | _ -> invalid_arg "invalid argument to :enumerate") in

        let decoder = Eval.Env.getDecoder cpu.env (Ident iset) in
        Testing.enumerate_opcodes cpu.env decoder start stop fname
    | [":coverage"; iset; instr] ->
        let open Testing in
        let encodings = get_opcodes opt_verbose iset instr cpu.env in
        List.iter (fun (enc, fields, opt_opcodes) ->
            Printf.printf "\nENCODING: %s\n" enc;
            match opt_opcodes with
            | None -> Printf.printf "(encoding unused)\n";
            | Some opcodes ->
                List.iter (fun (op, valid) ->
                    let fs = fields_of_opcode fields op in
                    Printf.printf "%s: %s --> " (hex_of_int op) (pp_enc_fields fs);
                    flush stdout;
                    if valid then
                        let result = op_test_opcode cpu.env iset op in
                        Printf.printf "%s\n" (pp_opresult (fun _ -> "OK") result)
                    else Printf.printf "(invalid)\n";
                ) opcodes
        ) encodings;
    | [":compare"; iset; file] ->
        let decoder = Eval.Env.getDecoder cpu.env (Ident iset) in
        let inchan = open_in file in
        (try
            while true do
                (* Set up our environments *)
                let initEnv = Eval.Env.copy cpu.env in
                (* Obtain and set random initial values for _R registers. *)
                let vals = (List.init 64 (fun _ -> Z.of_int64 (Random.int64 Int64.max_int))) in
                Eval.initializeRegistersAndMemory initEnv vals;
                (* Replace remaining VUninitialized with default zero values. *)
                Eval.initializeGlobals initEnv;

                (* Disassembly uses original uninitialised environment.
                   Others use the randomly initialised environment for full evaluation. *)
                let disEnv = Eval.Env.copy cpu.env in
                let evalEnv = Eval.Env.copy initEnv in
                let disEvalEnv = Eval.Env.copy initEnv in
                let lenv = Dis.build_env disEnv in

                let opcode = input_line inchan in
                let op = Z.of_string opcode in

                (* Printf.printf "PRE Eval env: %s\n\n" (Testing.pp_eval_env evalEnv);
                Printf.printf "PRE Dis eval env: %s\n\n" (Testing.pp_eval_env disEvalEnv); *)

                (try
                    (* Evaluate original instruction *)
                    Eval.eval_decode_case AST.Unknown evalEnv decoder op;

                    (try
                        (* Generate and evaluate partially evaluated instruction *)
                        let disStmts = Dis.dis_decode_entry disEnv lenv decoder op in
                        List.iter (eval_stmt disEvalEnv) disStmts;

                        if Eval.Env.compare evalEnv disEvalEnv then
                            Printf.printf "No errors detected\n"
                        else
                            Printf.printf "Environments not equal\n";
                    with
                        EvalError (loc, message) -> Printf.printf "Dis error: %s\n" message
                    )
                with
                    EvalError (loc, message) -> Printf.printf "Eval error: %s\n" message;
                );
                (* Printf.printf "POST Eval env: %s\n\n" (Testing.pp_eval_env evalEnv);
                Printf.printf "POST Dis eval env: %s\n\n" (Testing.pp_eval_env disEvalEnv); *)
            done
        with
        | End_of_file ->
            close_in inchan
        )
    | [":elf"; file] ->
        Printf.printf "Loading ELF file %s.\n" file;
        let entry = Elf.load_file file cpu.elfwrite in
        Printf.printf "Entry point = 0x%Lx\n" entry
    | [":help"] | [":?"] ->
        List.iter print_endline help_msg;
        print_endline "\nFlags:";
        Flags.StringMap.iter (fun nm v -> Printf.printf "  %s%s\n" (if v then "+" else "-") nm) (Flags.get_flags ())
    | [":opcode"; iset; opcode] ->
        (* todo: make this code more robust *)
        let op = Z.of_string opcode in
        Printf.printf "Decoding and executing instruction %s %s\n" iset (Z.format "%x" op);
        cpu.opcode iset op
    | [":opcodes"; iset; instr] ->
        let open Testing in
        let encodings = get_opcodes opt_verbose iset instr cpu.env in
        List.iter (fun (_, _, opt_opcodes) ->
            match opt_opcodes with
            | None -> ()
            | Some opcodes ->
                List.iter (fun (op, valid) ->
                    if valid then
                        let op' = (String.sub (hex_of_int op) 2 8) in
                        Printf.printf "%c" (String.get op' 6);
                        Printf.printf "%c " (String.get op' 7);
                        Printf.printf "%c" (String.get op' 4);
                        Printf.printf "%c " (String.get op' 5);
                        Printf.printf "%c" (String.get op' 2);
                        Printf.printf "%c " (String.get op' 3);
                        Printf.printf "%c" (String.get op' 0);
                        Printf.printf "%c " (String.get op' 1);
                ) opcodes
        ) encodings;
    | [":sem"; iset; opcode] ->
        let cpu' = Cpu.mkCPU cpu.env cpu.denv in
        let op = Z.of_string opcode in
        Printf.printf "Decoding instruction %s %s\n" iset (Z.format "%x" op);
        cpu'.sem iset op
    | ":ast" :: iset :: opcode :: rest when List.length rest <= 1 ->
        let op = Z.of_string opcode in
        let decoder = Eval.Env.getDecoder cpu.env (Ident iset) in
        let chan_opt = Option.map open_out (List.nth_opt rest 0) in
        let chan = Option.value chan_opt ~default:stdout in
        List.iter
            (fun s -> Printf.fprintf chan "%s\n" (Utils.to_string (PP.pp_raw_stmt s)))
            (Dis.dis_decode_entry cpu.env cpu.denv decoder op);
        Option.iter close_out chan_opt
    | ":gen" :: iset :: id :: rest when List.length rest <= 3 ->
        let pc_option = Option.value List.(nth_opt rest 1) ~default:"false" in
        let backend_str = Option.value List.(nth_opt rest 0) ~default:"ocaml" in
        Printf.printf "Generating lifter for %s %s with pc option %s using %s backend\n" iset id pc_option backend_str;

        let pc_option = match String.lowercase_ascii pc_option with
        | "false" -> false
        | "true" -> true
        | _ -> invalid_arg @@ Printf.sprintf "unkown pc option %s (expected: true, false)" pc_option in

        let (backend, default_dir) = match List.assoc_opt backend_str gen_backends with
            | Some x -> x
            | None -> invalid_arg @@ Printf.sprintf "unknown backend %s (supported: %s)"
                                     backend_str (String.concat ", " List.(map fst gen_backends)) in

        let dir = Option.value List.(nth_opt rest 2) ~default:default_dir in
        let cpu' = Cpu.mkCPU cpu.env cpu.denv in
        cpu'.gen iset id pc_option backend dir;
        Printf.printf "Done generating %s lifter into '%s'.\n" backend_str dir;
    | ":dump" :: iset :: opcode :: rest ->
        let fname = 
            (match rest with 
            | [] -> "sem.aslb"
            | [x] -> x 
            | _ -> invalid_arg "expected at most 3 arguments to :dump")
        in
        let cpu' = Cpu.mkCPU (Eval.Env.copy cpu.env) cpu.denv in
        let op = Z.of_string opcode in
        let decoder = Eval.Env.getDecoder cpu'.env (Ident iset) in
        let stmts = Dis.dis_decode_entry cpu'.env cpu.denv decoder op in
        let chan = open_out_bin fname in
        Printf.printf "Dumping instruction semantics for %s %s" iset (Z.format "%x" op);
        Printf.printf " to file %s\n" fname;
        (* NOTE: .aslb file is a marshalled `stmt list` *)
        Marshal.to_channel chan (stmts : stmt list) [];
        close_out chan
    | (":set" :: "impdef" :: rest) ->
        Eval.set_impdef tcenv cpu.env fname rest
    | [":set"; flag] ->
        Flags.set_flag flag
    | [":project"; prj] ->
        let inchan = open_in prj in
        (try
            while true do
                process_command tcenv cpu prj (input_line inchan)
            done
        with
        | End_of_file ->
            close_in inchan
        )
    | [":q"] | [":quit"] ->
        exit 0
    | [":run"] ->
        (try
            while true do
                cpu.step ()
            done
        with
        | Value.Throw (_, Primops.Exc_ExceptionTaken) ->
            Printf.printf "Exception taken\n"
        )
    | _ ->
        if ';' = String.get input (String.length input - 1) then begin
            let s = LoadASL.read_stmt tcenv input in
            Eval.eval_stmt cpu.env s
        end else begin
            let loc = LoadASL.mkLoc fname input in
            let e   = LoadASL.read_expr tcenv loc input in
            let v   = Eval.eval_expr loc cpu.env e in
            print_endline (Value.pp_value v)
        end
    )

let rec repl (tcenv: TC.Env.t) (cpu: Cpu.cpu): unit =
    flush stdout;
    (match LNoise.linenoise "ASLi> " with
    | None -> ()
    | Some input ->
        LNoise.history_add input |> ignore;
        (try
            LoadASL.report_eval_error (fun _ -> ()) (fun _ ->
                LoadASL.report_type_error (fun _ -> ()) (fun _ ->
                    LoadASL.report_parse_error (fun _ -> ()) (fun _ ->
                        process_command tcenv cpu "<stdin>" input
                    )
                )
            )
        with
        | exc ->
            Printf.printf "  Error %s\n" (Printexc.to_string exc);
            Printexc.print_backtrace stdout;
            (* truncate backtrace to 1000 characters. *)
            (* let bt = Printexc.get_backtrace () in
            let k = if 1000 < String.length bt then String.index_from bt 1000 '\n' else String.length bt in
            Printf.printf "%s\n[...]\n" (String.sub bt 0 k) *)
        );
        repl tcenv cpu
    )

let options = Arg.align ([
    ( "-x", Arg.Set_int Dis.debug_level,      "       Partial evaluation debugging (requires debug level argument >= 0)");
    ( "-v", Arg.Set opt_verbose,              "       Verbose output");
    ( "--no-aarch64", Arg.Set opt_no_default_aarch64 ,    "       Disable bundled AArch64 semantics");
    ( "--export-aarch64", Arg.Set_string opt_export_aarch64_dir,  "       Export bundled AArch64 MRA to the given directory");
    ( "--version", Arg.Set opt_print_version, "       Print version");
    ( "--prelude", Arg.Set_string opt_prelude,"       ASL prelude file (default: ./prelude.asl)");
    ( "--flag", Arg.String Flags.set_flag,          "       Behaviour flags to set (+) or unset (-)");
] )

let version = "ASL 0.2.0 alpha"

let banner = [
    {|            _____  _       _    ___________________________________|};
    {|    /\     / ____|| |     (_)   ASL interpreter                    |};
    {|   /  \   | (___  | |      _    Copyright Arm Limited (c) 2017-2019|};
    {|  / /\ \   \___ \ | |     | |                                      |};
    {| / ____ \  ____) || |____ | |   |} ^ version;
    {|/_/    \_\|_____/ |______||_|   ___________________________________|}
]
let usage_msg =
    ( version
    ^ "\nusage: asl <options> <file1> ... <fileN>\n"
    )

let _ =
  Arg.parse options
    (fun s -> opt_filenames := (!opt_filenames) @ [s])
    usage_msg


let main () =
    if !opt_print_version then Printf.printf "%s\n" version
    else if "" <> !opt_export_aarch64_dir then
        let dir = !opt_export_aarch64_dir in
        ignore @@ Sys.readdir dir;
        List.iter LoadASL.(write_source dir) Arm_env.(prelude_blob :: asl_blobs);
    else begin
        if !opt_verbose then List.iter print_endline banner;
        if !opt_verbose then print_endline "\nType :? for help";

        let sources = List.map (fun x -> LoadASL.FileSource x) !opt_filenames in
        (* Note: .prj files are handled by `evaluation_environment`. *)
        let env_opt =
            if (!opt_no_default_aarch64)  
            then evaluation_environment (FileSource !opt_prelude) sources !opt_verbose
            else begin
                if List.length (!opt_filenames) != 0 then
                    Printf.printf
                        "Warning: asl file arguments ignored without --no-aarch64 (%s)\n"
                        (String.concat " " !opt_filenames)
                else ();
                Arm_env.aarch64_evaluation_environment ~verbose:!opt_verbose ();
            end in

        let env = (match env_opt with 
            | Some e -> e
            | None -> failwith "Unable to build evaluation environment.") in

        if !opt_verbose then Printf.printf "Built evaluation environment\n";

        LNoise.history_load ~filename:"asl_history" |> ignore;
        LNoise.history_set ~max_length:100 |> ignore;
        
        let denv = Dis.build_env env in
        let tcenv = TC.Env.mkEnv !TC.env0 and cpu = Cpu.mkCPU env denv in

        repl tcenv cpu
    end

let _ = ignore (main ())

(****************************************************************
 * End
 ****************************************************************)
