open Asl_ast
open Asl_utils
open Gen_backend

(****************************************************************
 * Write State
 ****************************************************************)

type st = {
  mutable depth : int;
  mutable skip_seq : bool;
  oc : out_channel;
  mutable ref_vars : IdentSet.t;
}

let inc_depth st =
  st.depth <- st.depth + 2

let dec_depth st =
  st.depth <- st.depth - 2

let is_ref_var v st =
  IdentSet.mem v st.ref_vars

let clear_ref_vars st =
  st.ref_vars <- IdentSet.empty

let add_ref_var v st =
  st.ref_vars <- IdentSet.add v st.ref_vars

(****************************************************************
 * String Utils
 ****************************************************************)

let replace s =
  String.fold_left (fun acc c ->
    if c = '.' then acc ^ "_"
    else if c = '#' then acc ^ "HASH"
    else acc ^ (String.make 1 c)) "" s

let name_of_ident v =
  let s = (match v with
  | Ident n -> "v_" ^ n
  | FIdent (n,0) -> "f_" ^ n
  | FIdent (n,i) -> "f_" ^ n ^ "_" ^ (string_of_int i)) in
  replace s

let rec name_of_lexpr l =
  match l with
  | LExpr_Var v -> name_of_ident v
  | LExpr_Field (l, f) ->
      let l = name_of_lexpr l in
      let f = name_of_ident f in
      l ^ "." ^ f
  | LExpr_Wildcard -> "_"
  | _ -> failwith @@ "name_of_lexpr: " ^ (pp_lexpr l)

(****************************************************************
 * File IO
 ****************************************************************)

let write_preamble opens st =
  Printf.fprintf st.oc "(* AUTO-GENERATED LIFTER FILE *)\n\n";
  List.iter (fun n ->
    let s = String.capitalize_ascii n in
    Printf.fprintf st.oc "open %s\n" s) opens;
  Printf.fprintf st.oc "\n"

let write_epilogue use_pc fid st =
  let conv_pc = "let pc = (mkBits (Z.of_int 64) (Z.of_int pc)) in" in
  let dis_call = (match use_pc with
    | true ->  Printf.sprintf "%s\n  %s enc pc" conv_pc
    | false ->  Printf.sprintf "%s enc"
  ) (name_of_ident fid)
  in
  let pc_arg = if use_pc then " ~(pc:int)" else "" in
  Printf.fprintf st.oc "let run%s enc =\n  reset_ir ();\n  %s;\n  get_ir ()\n" pc_arg dis_call

let write_line s st =
  let padding = String.concat "" (List.init st.depth (fun _ -> " ")) in
  Printf.fprintf st.oc  "%s%s" padding s

let write_seq st =
  if st.skip_seq then
    st.skip_seq <- false
  else Printf.fprintf st.oc ";\n"

let write_nl st =
  Printf.fprintf st.oc "\n"

(****************************************************************
 * Expr Printing
 ****************************************************************)

let rec prints_expr e st =
  match e with
  (* Boolean Expressions *)
  | Expr_Var(Ident "TRUE") -> "true"
  | Expr_Var(Ident "FALSE") -> "false"
  | Expr_TApply(FIdent("and_bool", 0), [], [a;b]) ->
      Printf.sprintf "(%s) && (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("or_bool", 0), [], [a;b]) ->
      Printf.sprintf "(%s) || (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("implies_bool", 0), [], [a;b]) ->
      Printf.sprintf "not (%s) || (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("not_bool", 0), [], [a]) ->
      "not (" ^ prints_expr a st ^ ")"

  (* State Accesses *)
  | Expr_Var(v) ->
      let n = name_of_ident v in
      if is_ref_var v st then "!" ^ n else n
  | Expr_Field(e, f) ->
      prints_expr e st ^ "." ^ name_of_ident f
  | Expr_Array(a,i) ->
      Printf.sprintf "List.nth (%s) (%s)" (prints_expr a st) (prints_expr i st)

  (* Int Expressions using Z *)
  | Expr_LitInt i -> "Z.of_string \"" ^ i ^ "\""
  | Expr_TApply(FIdent("add_int", 0), [], [a;b]) ->
      Printf.sprintf "Z.add (%s) (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("sub_int", 0), [], [a;b]) ->
      Printf.sprintf "Z.sub (%s) (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("mul_int", 0), [], [a;b]) ->
      Printf.sprintf "Z.mul (%s) (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("frem_int", 0), [], [a;b]) ->
      Printf.sprintf "frem_int (%s) (%s)" (prints_expr a st) (prints_expr b st)

  (* Other operations *)
  | Expr_LitBits b -> "from_bitsLit \"" ^ b ^ "\""
  | Expr_Slices(e,[Slice_LoWd(i,w)]) ->
      let e = prints_expr e st in
      let i = prints_expr i st in
      let w = prints_expr w st in
      Printf.sprintf "extract_bits (%s) (%s) (%s)" e i w
  | Expr_TApply(f, targs, args) ->
      let f = name_of_ident f in
      let args = List.map (fun e -> prints_expr e st) (targs @ args) in
      f ^ " (" ^ (String.concat ") (" args) ^ ")"

  | Expr_LitString s -> "\"" ^ s ^ "\""
  | Expr_Tuple(es) -> "(" ^ (String.concat "," (List.map (fun e -> prints_expr e st) es)) ^ ")"
  | Expr_Unknown(ty) -> default_value ty st
  | Expr_If (ty, c, t, [], e) -> Printf.sprintf "(if (%s) then (%s) else (%s))" (prints_expr c st) (prints_expr t st) (prints_expr e st)

  | _ -> failwith @@ "prints_expr: " ^ pp_expr e

and default_value t st =
  match t with
  | Type_Bits w ->
      Printf.sprintf "mkBits (%s) Z.zero" (prints_expr w st)
  | Type_Constructor (Ident "boolean") -> "true"
  | Type_Constructor (Ident "integer") -> "Z.zero"
  | Type_Constructor (Ident "rt_label") -> "0"
  | Type_Constructor (Ident "rt_expr") -> "undefined ()"
  | Type_Array(Index_Range(lo, hi),ty) ->
      let lo = prints_expr lo st in
      let hi = prints_expr hi st in
      let d = default_value ty st in
      Printf.sprintf "List.init ((Z.to_int (%s)) - (Z.to_int (%s)) + 1) (fun _ -> %s)" hi lo d
  | _ -> failwith @@ "Unknown type for default value: " ^ (pp_type t)

let prints_ret_type t =
  match t with
  | Some (Type_Constructor (Ident "boolean")) -> "bool"
  | None -> "unit"
  | Some t -> failwith @@ "Unknown return type: " ^ (pp_type t)

(****************************************************************
 * Prim Printing
 ****************************************************************)

let write_fun_return e st =
  let s = Printf.sprintf "(%s)" e in
  write_line s st

let write_proc_return st =
  write_line "()" st

let write_assert s st =
  let s = Printf.sprintf "assert (%s)" s in
  write_line s st

let write_unsupported st =
  write_line "failwith \"unsupported\"" st

let write_call f targs args st =
  let f = name_of_ident f in
  let args = targs @ args in
  let call = f ^ " (" ^ (String.concat ") (" args) ^ ")" in
  write_line call st

let write_ref v e st =
  let name = name_of_ident v in
  let s = Printf.sprintf "let %s = ref (%s) in\n" name e in
  st.skip_seq <- true;
  write_line s st;
  add_ref_var v st

let write_let v e st =
  let v = name_of_ident v in
  let s = Printf.sprintf "let %s = %s in\n" v e in
  st.skip_seq <- true;
  write_line s st

let write_if_start c st =
  let s = Printf.sprintf "if %s then begin\n" c in
  write_line s st

let write_if_elsif c st =
  write_nl st;
  let s = Printf.sprintf "end else if %s then begin\n" c in
  write_line s st

let write_if_else st =
  write_nl st;
  write_line "end else begin\n" st

let write_if_end st =
  write_nl st;
  write_line "end" st

(****************************************************************
 * Stmt Printing
 ****************************************************************)

let rec write_assign v e st =
  match v with
  | LExpr_Wildcard ->
      let s = Printf.sprintf "let _ = %s in\n" e in
      st.skip_seq <- true;
      write_line s st

  | LExpr_Var v ->
      let v = name_of_ident v in
      let s = Printf.sprintf "%s := %s" v e in
      write_line s st

  | LExpr_Array (LExpr_Var v, i) ->
      let i = prints_expr i st in
      let v = name_of_ident v in
      let s = Printf.sprintf "%s := list_update (%s) (%s) (%s)" v v i e in
      write_line s st

  | LExpr_Field (l, f) ->
      let v = name_of_lexpr l in
      let s = Printf.sprintf "%s = %s" v e in
      write_line s st

  | LExpr_Tuple (ls) ->
      let vars = List.init (List.length ls) (fun i -> "tmp" ^ (string_of_int i)) in
      let v = "(" ^ String.concat "," vars ^ ")" in
      let s = Printf.sprintf "let %s = %s in\n" v e in
      st.skip_seq <- true;
      write_line s st;
      List.iter2 (fun l e ->
        write_seq st;
        write_assign l e st
      ) ls vars

  | _ -> failwith @@ "write_assign: " ^ (pp_lexpr v)

let rec write_stmt s st =
  match s with
  | Stmt_VarDeclsNoInit(ty, vs, loc) ->
      let e = default_value ty st in
      List.iter (fun v -> write_ref v e st) vs

  | Stmt_VarDecl(ty, v, e, loc) ->
      let e = prints_expr e st in
      write_ref v e st

  | Stmt_ConstDecl(ty, v, e, loc) ->
      let e = prints_expr e st in
      write_let v e st

  | Stmt_Assign(l, r, loc) ->
      let e = prints_expr r st in
      write_assign l e st

  | Stmt_TCall(f, tes, es, loc) ->
      let tes = List.map (fun e -> prints_expr e st) tes in
      let es = List.map (fun e -> prints_expr e st) es in
      write_call f tes es st

  | Stmt_FunReturn(e, loc) ->
      write_fun_return (prints_expr e st) st

  | Stmt_ProcReturn(loc) ->
      write_proc_return st

  | Stmt_Assert(e, loc) ->
      write_assert (prints_expr e st) st

  | Stmt_Throw _ ->
      write_unsupported st

  | Stmt_If(c, t, els, f, loc) ->
      let rec iter = function
      | S_Elsif_Cond(c,b)::xs ->
          write_if_elsif (prints_expr c st) st;
          write_stmts b st;
          iter xs
      | [] -> () in
      write_if_start (prints_expr c st) st;
      write_stmts t st;
      iter els;
      if f <> [] then (write_if_else st; write_stmts f st);
      write_if_end st

  | _ -> failwith @@ "write_stmt: " ^ (pp_stmt s);

and write_stmts s st =
  inc_depth st;
  match s with
  | [] ->
      write_proc_return st;
      dec_depth st
  | x::xs ->
      write_stmt x st;
      List.iter (fun s ->
        write_seq st;
        write_stmt s st
      ) xs;
      dec_depth st
      (*assert (not st.skip_seq)*)

let build_args targs args =
  if List.length targs = 0 && List.length args = 0 then "()"
  else String.concat " " (List.map name_of_ident (targs@args))

let write_fn name (ret_tyo,_,targs,args,_,body) st =
  clear_ref_vars st;
  let args = build_args targs args in
  let ret = prints_ret_type ret_tyo in
  Printf.fprintf st.oc "let %s %s : %s = \n" (name_of_ident name) args ret;
  write_stmts body st;
  Printf.fprintf st.oc "\n\n"

(****************************************************************
 * Directory Setup
 ****************************************************************)

let init_st oc = { depth = 0; skip_seq = false; oc ; ref_vars = IdentSet.empty }
let global_deps = ["Offline_utils"]
let offline_utils_file = [%blob "../offlineASL/template_offline_utils.ml"]

(* Write an instruction file, containing just the behaviour of one instructions *)
let write_instr_file fn fnsig dir =
  let m = name_of_FIdent fn in
  let path = dir ^ "/" ^ m ^ ".ml" in
  let oc = open_out path in
  let st = init_st oc in
  write_preamble global_deps st;
  write_fn fn fnsig st;
  close_out oc;
  name_of_FIdent fn

(* Write the test file, containing all decode tests *)
let write_test_file tests dir =
  let m = "decode_tests" in
  let path = dir ^ "/" ^ m ^".ml" in
  let oc = open_out path in
  let st = init_st oc in
  write_preamble global_deps st;
  Bindings.iter (fun i s -> write_fn i s st) tests;
  close_out oc;
  m

(* Write the decoder file - should depend on all of the above *)
let write_decoder_file use_pc fn fnsig deps dir =
  let m = "offline" in
  let path = dir ^ "/" ^ m ^ ".ml" in
  let oc = open_out path in
  let st = init_st oc in
  write_preamble (global_deps @ deps) st;
  write_fn fn fnsig st;
  write_epilogue use_pc fn st;
  close_out oc;
  m

let write_new_dune_file use_pc files dir  : unit =
  let target_gen_files = String.concat "" @@ List.map (fun k ->
    Printf.sprintf "    %s.ml\n" k
  ) files in
  let oc = open_out (dir ^ "/dune.generated.new") in
  Printf.fprintf oc "; AUTO-GENERATED BY OCAML BACKEND\n";
  Printf.fprintf oc "(rule
  (targets
    dune.generated.new\n%s
  )
  (deps gen-command)
  (action (with-stdin-from gen-command (run asli)))
)" target_gen_files ;
  Printf.fprintf oc "\n\n";
  let name = if use_pc then "offlineASL_pc" else "offlineASL" in
  Printf.fprintf oc "
  (library
    (name %s)
    (public_name aslp_offline.%s)
    (flags
      (:standard -w -27 -w -33 -cclib -lstdc++))
    (modules \n"
    name
    (if use_pc then "pc_aarch64" else "aarch64") ;
    List.iter (fun k ->
      Printf.fprintf oc "    %s\n" k
    ) (files);
    Printf.fprintf oc "  )
    (libraries asli.libASL-stage0))" ;
    Printf.fprintf oc  "\n(alias (name default) (deps (package aslp_offline) ../aslp_offline.install))"


(* Write the dune build file *)
(* XXX: this function is not used anymore? *)
let write_dune_file use_pc files dir =
  let oc = open_out (dir ^ "/dune.inc") in
  Printf.fprintf oc "; AUTO-GENERATED BY OCAML BACKEND
(library
  (name offlineASL)
  (public_name aslp_offline.%s)
  (flags
    (:standard -w -27 -w -33 -cclib -lstdc++))
  (modules \n"
  (if use_pc then "pc_aarch64" else "aarch64") ;
  List.iter (fun k ->
    Printf.fprintf oc "    %s\n" k
  ) files;
  Printf.fprintf oc "  )
  (libraries asli.libASL-stage0))";
  close_out oc

let write_ibi dir =
  let oc = open_out (dir ^ "/Offline_utils.ml") in
  output_string oc offline_utils_file ;
  close_out oc

(* Write all of the above, expecting offline_utils.ml to already be present in dir *)
let run config dfn dfnsig tests fns =
  let dir = config.output_directory in
  let files = Bindings.fold (fun fn fnsig acc -> (write_instr_file fn fnsig dir)::acc) fns [] in
  let files = (write_test_file tests dir)::files in
  let decoder = write_decoder_file config.use_pc dfn dfnsig files dir in
  write_ibi dir ;
  try
  write_new_dune_file config.use_pc (decoder::files@global_deps) dir
  with
    | Sys_error _ as e -> Printf.eprintf "failed to write dune file\n%s" (Printexc.to_string e); Printexc.print_backtrace stderr

module OcamlBackend : Backend = struct
  let run ~(config:conf) dfn dfnsig tests fns = run config dfn dfnsig tests fns
end

