module AST = Asl_ast
module Env = Eval.Env

open AST
open Value
open Asl_utils

(****************************************************************
 * Opcode decoding without evaluation.
 ****************************************************************)

(* Copies of eval_decode_alt and eval_decode_case which do not evaluate their opcodes.
   These "try" decoding each opcode. *)

(** Try to evaluate an "encoding" block to the given opcode. *)
let rec try_encoding (env: Env.t) (x: encoding) (op: Primops.bigint): bool =
  let Encoding_Block (nm, iset, fields, opcode, guard, unpreds, b, loc) = x in
  (* todo: consider checking iset *)
  (* Printf.printf "Checking opcode match %s == %s\n" (Utils.to_string (PP.pp_opcode_value opcode)) (pp_value op); *)
  let trace_instruction = ref false in
  match Eval.eval_opcode_guard loc opcode op with
  | Some op ->
      if !trace_instruction then Printf.printf "TRACE: instruction %s\n" (pprint_ident nm);
      List.iter (function (IField_Field (f, lo, wd)) ->
          let v = extract_bits' loc op lo wd in
          if !trace_instruction then Printf.printf "      %s = %s\n" (pprint_ident f) (pp_value v);
          Env.addLocalVar loc env f v
      ) fields;
      if to_bool loc (Eval.eval_expr loc env guard) then begin
          List.iter (fun (i, b) ->
              if eval_eq loc (extract_bits' loc op i 1) (from_bitsLit b) then
                  raise (Throw (loc, Exc_Unpredictable))
          ) unpreds;
          (* try_encoding: do NOT evaluate __decode block because this may
             require IMPDEF values.
             assume its conditions are verified by earlier decode case matches. *)
          (* List.iter (eval_stmt env) b; *)
          true
      end else begin
          false
      end
  | None -> false

(** Tests whether the given opcode can be decoded by the given decode case. *)
and try_decode_case (loc: AST.l) (env: Env.t) (x: decode_case) (op: Primops.bigint): ident option =
    (match x with
    | DecoderCase_Case (ss, alts, loc) ->
            let vs = List.map (fun s -> Eval.eval_decode_slice loc env s op) ss in
            let rec eval alts =
                (match alts with
                | (alt :: alts') ->
                        (match try_decode_alt loc env alt vs op with
                        | Some e -> Some e
                        | None -> eval alts')
                | [] ->
                        None (*raise (EvalError (loc, "unmatched decode pattern"))*)
                )
            in
            eval alts
    )

(** Tests whether the given opcode is decodable by the given decode case alternative.  *)
and try_decode_alt (loc: AST.l) (env: Env.t) (DecoderAlt_Alt (ps, b)) (vs: value list) (op: Primops.bigint): ident option =
    if List.for_all2 (Eval.eval_decode_pattern loc) ps vs then
        (match b with
        | DecoderBody_UNPRED loc -> raise (Throw (loc, Exc_Unpredictable))
        | DecoderBody_UNALLOC loc -> raise (Throw (loc, Exc_Undefined))
        | DecoderBody_NOP loc -> None (* Some (Ident "__NOP") *)
        | DecoderBody_Encoding (encname, l) ->
                let (enc, opost, cond, exec) = Env.getInstruction loc env encname in
                if try_encoding env enc op then begin
                    Some encname
                end else begin
                    None
                end
        | DecoderBody_Decoder (fs, c, loc) ->
                (* let env = Env.empty in  *)
                List.iter (function (IField_Field (f, lo, wd)) ->
                    let op = Value.from_bitsInt (lo+wd) op in
                    Env.addLocalVar loc env f (extract_bits' loc op lo wd)
                ) fs;
                try_decode_case loc env c op
        )
    else
        None

(****************************************************************
 * Data type for storing intervals of integers in a compressed format.
 ****************************************************************)

(** A list of intervals, where the pair (lo,hi) indicates that all
    integers x such that lo <= x <= hi are in the list. *)
type pair_list = (int * int) list

let pair_list_cons i: pair_list -> pair_list =
  function
  | (l,r)::rest when i = succ r -> (l,i)::rest
  | rest -> (i,i)::rest

let pp_pair_list =
  Utils.pp_list (fun (x,y) -> string_of_int x ^ "," ^ string_of_int y)

let rec pair_list_mem (xs: pair_list) (x: int): bool =
  match xs with
  | [] -> false
  | (l,r)::rest ->
    if l <= x && x <= r then
      true
    else
      pair_list_mem rest x

type pair_array = (int * int) array

(** Searches for value in given interval array.
    Assumes array's intervals are in *increasing* order.  *)
let pair_array_mem (xs: pair_array) (x: int): bool =
  let l = ref 0
  and r = ref (Array.length xs - 1) in
  while !l < !r do
    let m = (!l + !r) / 2 in
    if x > snd (Array.get xs m) then
      l := m + 1
    else
      r := m
  done;
  let (lo,hi) = Array.get xs !l in
  lo <= x && x <= hi

  (****************************************************************
 * Opcode enumeration functions.
 ****************************************************************)

let enumerate_opcodes (env: Env.t) (case: decode_case) start stop fname: unit =

  let debug_interval = Int.shift_left 1 20 in
  let i = ref start in
  let j = ref 1 in

  let t0 = (Sys.time ()) in
  let nprev = ref 0 in
  let tprev = ref t0 in
  let yes = ref 0 in
  let no = ref 0 in

  let result = ref Bindings.empty in

  let f = open_out fname in

  while !i <> stop do
    let opresult =
      (try try_decode_case Unknown env case (Z.of_int !i)
      with Throw _ -> None) in

    (match opresult with
    | Some e ->
        result := Bindings.update e
        (function
        | None -> Some [(!i,!i)]
        | Some old -> Some (pair_list_cons !i old)) !result;
        yes := succ !yes;
    | None ->
        no := succ !no);

    if (!j = debug_interval) then begin
      let n = !yes + !no in
      let t = Sys.time () -. t0 in

      let dn = n - !nprev in
      let dt = t -. !tprev in

      Printf.printf "t: %f, 0x%08x (%d): average %f/s (+%d in %f, %f/s), valid: %d, invalid: %d\n"
        t
        !i !i (float n /. t)
        dn dt (float dn /. dt)
        !yes !no;
      Stdlib.flush stdout;

      Printf.fprintf f "0x%08x (%d): %s\n" !i !i (pp_bindings (pp_pair_list) !result);
      Stdlib.flush f;
      result := Bindings.empty;

      nprev := n;
      tprev := t;
      j := 0;
    end;
    j := succ !j;
    i := succ !i;
  done

(* load opcodes interval file stored as lines of pairs,
   where each line is the difference from the previous line.

   for example:
   0x1,0x2
   0x4,0x6
   0x5,0x7

   is stored as:
   0x1,0x2
   0x3,0x4
   0x1,0x1
   *)
let load_opcode_file (p: string): (int * int) array =
  let f = open_in p in
  let l = ref 0
  and r = ref 0 in
  let ops = ref [] in
  (try
    while true do
      let line = input_line f in
      match String.split_on_char ',' line with
      | [l';r' ] ->
        let l' = int_of_string l'
        and r' = int_of_string r' in
        l := !l + l';
        r := !r + r';
        ops := (!l, !r) :: !ops
      | _ -> assert false
    done
  with End_of_file -> ());
  close_in_noerr f;
  let a = Array.of_list !ops in
  Array.fast_sort compare a;
  a

let load_opcodes (directory: string): (int*int) array Bindings.t option =
  try
    let files = Array.to_list @@ Sys.readdir directory in
    Some (mk_bindings
      (List.map
        (fun f -> (Ident f, load_opcode_file (Filename.concat directory f)))
        files))
  with
    Sys_error _ -> None

(****************************************************************
 * Opcode coverage testing.
 ****************************************************************)

module IntMap = Map.Make(struct
  type t = int
  let compare = compare
end)

let pp_intmap (f: 'a -> string) (m: 'a IntMap.t): string =
  let pairs = List.map (fun (k,v) -> Printf.sprintf "%d: %s" k (f v)) (IntMap.bindings m) in
  "{ " ^ String.concat ", " pairs ^ " }"

let hex_of_int = Printf.sprintf "0x%08x"


(** A tree of possible opcodes for a given encoding. *)
type encoding_tree =

  (* A single opcode. *)
  | Op of int

  (* A field branching into different subtrees depending on the value this
     field takes. The map is keyed by this field's values and has values of subtrees. *)
  | Field of instr_field * encoding_tree IntMap.t

let rec pp_enc_tree =
  function
  | Op i -> hex_of_int i
  | Field (f, t) ->
    let f' = pp_instr_field f in
    let t' = pp_intmap pp_enc_tree t in
    "[\"" ^ f' ^ "\": " ^ t' ^ "]"

type fields = (instr_field * int) list

let rec list_of_enc_tree (t: encoding_tree): int list =
  match t with
  | Op x -> [x]
  | Field (f, t') ->
    List.concat
      (List.map (fun (_,v) ->
        list_of_enc_tree v)
        (IntMap.bindings t'))

let pp_enc_fields (f: fields): string =
  Utils.pp_list (fun (f,i) -> pp_instr_field f ^ "=" ^ string_of_int i) f


let pp_enc_list (encs: (fields * int) list): string =
  String.concat "\n"
    (List.map (Utils.pp_pair pp_enc_fields hex_of_int) encs)

(* Functions for manipulating opcodes as integers. *)

let fields_of_opcode (fields: instr_field list) (op: int): fields =
  List.map (fun f ->
    let IField_Field(_,lo,wd) = f in
    let mask = Int.shift_left 1 wd - 1 in
    (f, Int.logand mask (Int.shift_right_logical op lo))
  ) fields

let set_field (IField_Field(_,lo,wd): instr_field) (op: int) (v: int) =
  (* assert that value is within bounds for given width. *)
  assert (0 <= v);
  assert (v < Int.shift_left 1 wd);

  (* mask to zero bits for the field before applying given value. *)
  let ones_wd = Int.shift_left 1 wd - 1 in
  let mask = Int.lognot (Int.shift_left ones_wd lo) in

  Int.logor (Int.logand op mask) (Int.shift_left v lo)

let int_of_opcode: opcode_value -> int =
  function
  | Opcode_Bits bits ->
    int_of_string ("0b" ^ drop_chars bits ' ')
  | Opcode_Mask mask ->
    let v = String.map (function | 'x' -> '0' | c -> c) mask in
    int_of_string ("0b" ^ drop_chars v ' ')


(* Functions for enumerating encodings with encoding_tree. *)

let field_vals_flags_only (enc: encoding) (name: string) (wd: int): int list =
  let Encoding_Block (instr, _, _, _, _, _, _, _) = enc in
  let bound = Int.shift_left 1 wd in
  let ones = bound - 1 in
  match (instr, name) with
  | Ident "aarch64_branch_unconditional_eret", "Rn" -> [0b11111]
  | Ident "aarch64_branch_unconditional_register", "Rn" -> [0; 1; 0b11111]
  | _, "cond" -> [1]
  | _ when Utils.startswith name "R" && name <> "R" -> [0;1;ones]
  | _ when Utils.startswith name "X" && name <> "X" -> [0;1;ones]
  | _ when Utils.startswith name "imm" -> [0;1;ones]
  | _ when Utils.startswith name "uimm" -> [1]
  | _ when Utils.startswith name "scale" -> [0]
  | _, ("b40") -> [0;1;ones]
  | _ -> List.init bound (fun x -> x)

let enumerate_encoding (enc: encoding) (field_vals: string -> int -> int list): encoding_tree =
  let Encoding_Block(name, iset, fields, opcode, guard, unpreds, stmts, loc) = enc in
  let rec go op fs =
    (match fs with
    | [] -> Op op
    | (IField_Field(name,lo,wd) as f)::rest ->
      let vals = field_vals (pprint_ident name) wd in
      let pairs = List.map (fun v -> (v, go (set_field f op v) rest)) vals in
      Field(f, IntMap.of_seq (List.to_seq pairs))
  ) in
  go (int_of_opcode opcode) fields


(* Automatic step-by-step testing of a particular opcode. *)

type operror =
  | Op_EvalFail of exn
  | Op_DisFail of exn
  | Op_DisEvalFail of exn
  | Op_DisEvalNotEqual

let pp_operror: operror -> string =
  function
  | Op_EvalFail (Throw (loc, Exc_Undefined)) -> "UNDEFINED (" ^ pp_loc loc ^ ")"
  | Op_EvalFail e -> "[1] Evaluation failure: " ^ Printexc.to_string e
  | Op_DisFail e -> "[2] Disassembly failure: " ^ Printexc.to_string e
  | Op_DisEvalFail e -> "[3] Dissassembled evaluation failure: " ^ Printexc.to_string e
  | Op_DisEvalNotEqual -> "[4] Evaluation results not equal"

type 'a opresult = ('a, operror) Result.t

let pp_opresult f = Result.fold ~ok:f ~error:pp_operror

let op_eval (env: Env.t) (iset: string) (op: Primops.bigint): Env.t opresult =
  let evalenv = Env.copy env in
  let decoder = Eval.Env.getDecoder evalenv (Ident iset) in
  try
    Eval.eval_decode_case AST.Unknown evalenv decoder op;
    Result.Ok evalenv
  with
    | e -> Result.Error (Op_EvalFail e)

let op_dis (env: Env.t) (iset: string) (op: Primops.bigint): stmt list opresult =
  let env = Env.copy env in
  let lenv = Dis.build_env env in
  let decoder = Eval.Env.getDecoder env (Ident iset) in
  try
    Dis.check_rasl := true;
    let stmts = Dis.dis_decode_entry env lenv decoder op in
    Result.Ok stmts
  with
    | e -> Result.Error (Op_DisFail e)

let op_diseval (env: Env.t) (stmts: stmt list): Env.t opresult =
  let env = Env.copy env in
  try
    List.iter (Eval.eval_stmt env) stmts;
    Result.Ok env
  with
    | e -> Result.Error (Op_DisEvalFail e)

let op_compare ((evalenv, disenv): Env.t * Env.t): Env.t opresult =
  if Env.compare evalenv disenv then
    Result.Ok evalenv
  else
    Result.Error (Op_DisEvalNotEqual)

let op_test_opcode (env: Env.t) (iset: string) (op: int): Env.t opresult =
  let op = Z.of_int op in

  let initenv = Env.copy env in
  Random.self_init ();
  let vals = (List.init 64 (fun _ -> Z.of_int64 (Random.int64 Int64.max_int))) in
  Eval.initializeRegistersAndMemory initenv vals;
  Eval.initializeGlobals initenv;

  let initenv = Env.freeze initenv in

  let (let*) = Result.bind in
  let* evalenv = op_eval initenv iset op in
  let* disstmts = op_dis env iset op in
  let* disevalenv = op_diseval initenv disstmts in
  op_compare (evalenv, disevalenv)

let get_opcodes (opt_verbose: bool ref) (iset: string) (instr: string) (env: Env.t): (string * instr_field list * ((int * bool) list) option) list =
  if !opt_verbose then Printf.printf "Coverage for encoding %s\n" instr;

  let re = Str.regexp instr in
  let encoding_matches = function
      | (Encoding_Block (Ident nm, Ident is, _, _, _, _, _, _)) ->
          is = iset && Str.string_match re nm 0
      | _ -> assert false
  in
  let encs = List.map (fun (x,_,_,_) -> x) (Env.listInstructions env) in
  let encs' = List.filter encoding_matches encs in
  (* List.iter (function (Encoding_Block (Ident mn, _,_,_,_,_,_,_)) -> Printf.printf "%s\n" mn | _ -> assert false) encs'; *)

  let opcodes = load_opcodes "encodings" in
  let get_opcodes nm =
      (match opcodes with
      | Some opcodes' -> Option.value (Bindings.find_opt nm opcodes') ~default:[||]
      | None -> [| (0, Int.max_int) |]
  ) in

  (match opcodes with
  | None ->
      Printf.printf "WARNING: encodings/ directory missing, assuming all opcodes are valid.\n";
      Printf.printf "         If encodings.tar.gz exists, it should be extracted.\n\n"
  | Some x ->
      let add_opcodes = Array.to_list (get_opcodes (Ident "ADD_Z_ZI__")) in
      let expected = [(0x2520c000, 0x2520ffff); (0x2560c000,0x2560ffff); (0x25a0c000,0x25a0ffff); (0x25e0c000,0x25e0ffff)] in
      (* check that encodings file has been parsed to correct values.
          if this fails, it is likely your encodings/ directory has the
          incorrect format. *)
      assert (add_opcodes = expected);
      if !opt_verbose then Printf.printf "Loaded opcodes for %d encodings\n" (Bindings.cardinal x)
  );

  List.fold_left (fun encs enc ->
      let Encoding_Block (nm,_,fields,_,_,_,_,_) = enc in
      let newEnc = pprint_ident nm in
      let t = enumerate_encoding enc (field_vals_flags_only enc) in
      let l = list_of_enc_tree t in
      let opcodes = (match get_opcodes nm with
      | [||] -> 
        None
      | ops ->
          Some (List.fold_left (fun codes op ->
              if pair_array_mem ops op then
                codes @ [(op, true)]
              else
                codes @ [(op, false)]
          ) [] l)
      ) in
      encs @ [(newEnc, fields, opcodes)]
  ) [] encs'
