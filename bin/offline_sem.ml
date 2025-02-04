open LibASL
open Asl_ast
open Asl_utils

let run (opcode: string) (pc: int option) =
  let op = Z.of_string opcode in
  let bv = Primops.prim_cvt_int_bits (Z.of_int 32) op in
  let stmts = match pc with 
    | None -> OfflineASL.Offline.run  bv 
    | Some x -> OfflineASL_pc.Offline.run ~pc:x bv in
  List.iter (fun s -> Printf.printf "%s\n" (pp_stmt s)) stmts

let opt_instr = ref []
let opt_pc = ref (-1) 
let options = Arg.align ([
    ( "--pc", Arg.Set_int opt_pc , "set program counter (does nothing if lifter generated does not support it)");
])
let usage_msg = ""

let _ =
  Arg.parse options
    (fun s -> opt_instr := (!opt_instr) @ [s])
    usage_msg

let main () = 
  let pc = if (!opt_pc <> -1) then Some !opt_pc else None in
  List.map (fun instr -> run instr pc) !opt_instr 

let _ = main()
