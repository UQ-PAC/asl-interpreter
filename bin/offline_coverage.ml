open LibASL
open Testing
open Asl_ast
open Value

let () = Printexc.register_printer
    (function
    | Value.EvalError (loc, e) ->
        Some ("EvalError at " ^ pp_loc loc ^ ": " ^ e)
    | _ -> None)

let op_dis (op: int): stmt list opresult =
  let bv = Primops.prim_cvt_int_bits (Z.of_int 32) (Z.of_int op) in
  try
    let stmts = OfflineASL.Offline.run  bv in
    Result.Ok stmts
  with
    | e -> Result.Error (Op_DisFail e)

let op_test_opcode (env: Env.t) (iset: string) (op: int): Env.t opresult =
  let op' = Z.of_int op in

  let initenv = Env.copy env in
  Random.self_init ();
  Eval.randomRegistersAndMemory initenv;
  Eval.initializeGlobals initenv;

  let initenv = Env.freeze initenv in

  let (let*) = Result.bind in
  let* evalenv = op_eval initenv iset op' in
  let* disstmts = op_dis op in
  let* disevalenv = op_diseval initenv disstmts in
  op_compare (evalenv, disevalenv)

let run opt_verbose instr env =
  let iset = "A64" in
  let encodings = get_opcodes opt_verbose iset instr env in
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
                  let result = op_test_opcode env iset op in
                  Printf.printf "%s\n" (pp_opresult (fun _ -> "OK") result)
              else Printf.printf "(invalid)\n";
          ) opcodes
  ) encodings

let opt_instr = ref []
let options = Arg.align ([])
let usage_msg = ""

let _ =
  Arg.parse options
    (fun s -> opt_instr := (!opt_instr) @ [s])
    usage_msg

let rec process_command tcenv env cmd =
  match String.split_on_char ' ' cmd with
  | (":set" :: "impdef" :: rest) ->
        let cmd = String.concat " " rest in
        let (x, e) = LoadASL.read_impdef tcenv Unknown cmd in
        let v = Eval.eval_expr Unknown env e in
        Eval.Env.setImpdef env x v
  | [":project"; prj] ->
      let inchan = open_in prj in
      (try
          while true do
              process_command tcenv env (input_line inchan)
          done
      with
      | End_of_file ->
          close_in inchan
      )
  | [""] -> ()
  | _ -> Printf.printf "Ignoring: %s\n" cmd

let main () = 
  let opt_verbose = ref false in
  let env = match Arm_env.aarch64_evaluation_environment ~verbose:!opt_verbose () with
  | Some e -> e
  | _ -> failwith "Unable to build evaluation environment." in
  List.map (fun instr -> run opt_verbose instr env) !opt_instr

let _ = ignore (main())
