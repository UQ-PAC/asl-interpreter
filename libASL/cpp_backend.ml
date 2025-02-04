open Asl_ast
open Asl_utils
open Gen_backend

(****************************************************************
 * Write State
 ****************************************************************)

type st = {
  mutable depth : int;
  mutable skip_seq : bool;
  file: string;
  oc : out_channel;
  mutable ref_vars : IdentSet.t;

  (* symbols declared within semantics, e.g. non-global variables and other generated functions *)
  mutable genvars : ident list;
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
  let s =
    String.fold_left (fun acc c ->
      if c = '.' then acc ^ "_"
      else if c = '#' then acc ^ "HASH"
      else acc ^ (String.make 1 c)) "" s in
  s

let name_of_ident v =
  let s = (match v with
  | Ident n -> "v_" ^ n
  | FIdent (n,0) -> "f_" ^ n
  | FIdent (n,i) -> "f_" ^ n ^ "_" ^ (string_of_int i)) in
  replace s

let prefixed_name_of_ident st v =
  let name = name_of_ident v in
  match v with
  (* non-generated functions and variables are translated to methods on an interface object. *)
  | FIdent _ when not (List.mem v st.genvars) -> "iface." ^ name
  | Ident _ when not (List.mem v st.genvars) -> "iface." ^ name ^ "()"
  | _ -> name

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

let write_preamble opens ?(header = true) ?(exports = []) st =
  Printf.fprintf st.oc "/* AUTO-GENERATED LIFTER FILE */\n\n";
  if header then Printf.fprintf st.oc "#pragma once\n";
  List.iter (fun s ->
    Printf.fprintf st.oc "#include <%s>\n" s) opens;
  List.iter (fun s ->
    Printf.fprintf st.oc "#include <%s> // IWYU pragma: export\n" s) exports;
  Printf.fprintf st.oc "\n";
  Printf.fprintf st.oc "namespace aslp {\n\n"

let write_epilogue fid st =
  Printf.fprintf st.oc "\n} // namespace aslp"

let write_line s st =
  let padding = String.concat "" (List.init st.depth (fun _ -> " ")) in
  output_string st.oc padding;
  output_string st.oc s

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
      Printf.sprintf "(%s) ? (%s) : true" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("not_bool", 0), [], [a]) ->
      "! (" ^ prints_expr a st ^ ")"

  (* State Accesses *)
  | Expr_Var(v) ->
      let n = prefixed_name_of_ident st v in
      if is_ref_var v st then "" ^ n else n
  | Expr_Field(e, f) ->
      prints_expr e st ^ "." ^ name_of_ident f
  | Expr_Array(a,i) ->
      Printf.sprintf "List.nth (%s) (%s)" (prints_expr a st) (prints_expr i st)

  (* Int Expressions *)
  | Expr_LitInt i ->
      Printf.sprintf "iface.bigint_lit(\"%s\")" i
  | Expr_TApply(FIdent("add_int", 0), [], [a;b]) ->
      Printf.sprintf "(%s) + (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("sub_int", 0), [], [a;b]) ->
      Printf.sprintf "(%s) - (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("mul_int", 0), [], [a;b]) ->
      Printf.sprintf "(%s) * (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("frem_int", 0), [], [a;b]) ->
      Printf.sprintf "(%s) %% (%s)" (prints_expr a st) (prints_expr b st)

  (* Other operations *)
  | Expr_LitBits b ->
      let len = String.length b in
      Printf.sprintf "iface.bits_lit(%dU, \"%s\")" len b
  | Expr_Slices(e,[Slice_LoWd(i,w)]) ->
      let e = prints_expr e st in
      let i = prints_expr i st in
      let w = prints_expr w st in
      Printf.sprintf "iface.extract_bits(%s, /*lo*/ %s, /*wd*/ %s)" e i w
  | Expr_TApply(f, targs, args) ->
      let f = prefixed_name_of_ident st f in
      (* let args = List.map (fun e -> prints_expr e st) (targs @ args) in *)
      let args = List.map (fun e -> prints_expr e st) ([] @ args) in
      f ^ "(" ^ (String.concat ", " args) ^ ")"

  | Expr_LitString s -> "\"" ^ s ^ "\""
  | Expr_Tuple(es) -> "std::make_tuple(" ^ (String.concat "," (List.map (fun e -> prints_expr e st) es)) ^ ")"
  | Expr_Unknown(ty) -> default_value ty st
  | Expr_If(_, c, t, [], e) -> Printf.sprintf "((%s) ? (%s) : (%s))" (prints_expr c st) (prints_expr t st) (prints_expr e st)

  | _ -> failwith @@ "prints_expr: " ^ pp_expr e

and default_value t st =
  match t with
  | Type_Bits w ->
      Printf.sprintf "iface.bits_zero(%s)" (prints_expr w st)
  | Type_Constructor (Ident "boolean") -> "true"
  | Type_Constructor (Ident "integer") -> "iface.bigint_zero()"
  | Type_Constructor (Ident "rt_label") -> "typename Traits::rt_label{}"
  | Type_Constructor (Ident "rt_expr") -> "typename Traits::rt_expr{}"
  | Type_Array(Index_Range(lo, hi),ty) ->
      let lo = prints_expr lo st in
      let hi = prints_expr hi st in
      let d = default_value ty st in
      Printf.sprintf "std::vector{(%s)-(%s), %s}" hi lo d
  | _ -> failwith @@ "Unknown type for default value: " ^ (pp_type t)

let prints_type t =
  match t with
  | Type_Constructor (Ident "boolean") -> "bool"
  | Type_Bits _ -> "typename Traits::bits"
  | Type_Constructor (Ident "integer") -> "typename Traits::bigint"
  | Type_Constructor (Ident "rt_label") -> "typename Traits::rt_label"
  | Type_Constructor (Ident "rt_expr") -> "typename Traits::rt_expr"
  | Type_Constructor (Ident "rt_sym") -> "typename Traits::rt_lexpr"
  | _ -> failwith @@ Asl_utils.pp_type t

let prints_ret_type = Option.fold ~none:"void" ~some:prints_type

(****************************************************************
 * Prim Printing
 ****************************************************************)

let write_fun_return e st =
  let s = Printf.sprintf "return (%s)" e in
  write_line s st

let write_proc_return st =
  write_line "return" st

let write_assert s st =
  let s = Printf.sprintf "assert(%s)" s in
  write_line s st

let write_unsupported st =
  write_line {|throw std::runtime_error{"aslp_lifter: unsupported! " + std::string{__func__} + " @ " + std::string{__FILE__} + ":" + std::to_string(__LINE__)}|} st

let write_call f targs args st =
  let f = prefixed_name_of_ident st f in
  let args = [] @ args in
  let call = f ^ "(" ^ (String.concat ", " args) ^ ")" in
  write_line call st

let write_ref ty v e st =
  (* let t = prints_type ty in *)
  let t = "auto" in
  let name = prefixed_name_of_ident st v in
  let s = Printf.sprintf "%s %s = %s" t name e in
  write_line s st;
  add_ref_var v st

let write_let ty v e st =
  (* let t = prints_type ty in *)
  let t = "auto" in
  let v = prefixed_name_of_ident st v in
  let s = Printf.sprintf "const %s %s = %s" t v e in
  write_line s st

let write_if_start c st =
  let s = Printf.sprintf "if (%s) {\n" c in
  write_line s st

let write_if_elsif c st =
  let s = Printf.sprintf "} else if (%s) {\n" c in
  write_line s st

let write_if_else st =
  write_line "} else {\n" st

let write_if_end st =
  write_line "} // if\n" st;
  st.skip_seq <- true

(****************************************************************
 * Stmt Printing
 ****************************************************************)

let rec write_lexpr v st =
  match v with
  | LExpr_Wildcard ->
      "std::ignore"

  | LExpr_Var v ->
      name_of_ident v

  | LExpr_Array (LExpr_Var v, i) ->
      let i = prints_expr i st in
      let v = name_of_ident v in
      Printf.sprintf "%s.at(%s)" v i

  | LExpr_Field (l, f) ->
      let v = name_of_lexpr l in
      Printf.sprintf "%s" v

  | LExpr_Tuple (ls) ->
      let vars = List.map (fun l -> write_lexpr l st) ls in
      let v = String.concat "," vars in
      Printf.sprintf "std::tie(%s)" v

  | _ -> failwith @@ "write_assign: " ^ (pp_lexpr v)

let rec write_stmt s st =
  match s with
  | Stmt_VarDeclsNoInit(ty, vs, loc) ->
      let e = default_value ty st in
      st.genvars <- vs @ st.genvars;
      List.iter (fun v -> write_ref ty v e st) vs

  | Stmt_VarDecl(ty, v, e, loc) ->
      let e = prints_expr e st in
      st.genvars <- v :: st.genvars;
      write_ref ty v e st

  | Stmt_ConstDecl(ty, v, e, loc) ->
      let e = prints_expr e st in
      st.genvars <- v :: st.genvars;
      write_let ty v e st

  | Stmt_Assign(l, r, loc) ->
      let e = prints_expr r st in
      let l = write_lexpr l st in
      write_line (Printf.sprintf "%s = %s" l e) st

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
      write_seq st;
      dec_depth st
  | x::xs ->
      write_stmt x st;
      write_seq st;
      List.iter (fun s ->
        write_stmt s st;
        write_seq st;
      ) xs;
      dec_depth st;
      assert (not st.skip_seq)

(* XXX: assumes all function arguments are bits. *)
let build_args prefix targs args =
  let inner = String.concat " " @@
    List.map
      (fun s -> prefix ^ "bits " ^ name_of_ident s)
      (targs@args) in
  "(" ^ inner ^ ")"

let typenames = ["bits"; "bigint"; "rt_expr"; "rt_lexpr"; "rt_label"]
let template_header = "template <typename Traits>\n"
let template_args = "<Traits>"

(** tuple of return type, function name, function arguments (parenthesised) *)
type cpp_fun_sig = {
  rty: string;
  prefix: string;
  name: ident;
  args: string;
  file: string;
}

let write_fn name (ret_tyo,_,targs,args,_,body) st : cpp_fun_sig =
  clear_ref_vars st;
  let oldvars = st.genvars in
  st.genvars <- (targs @ args) @ oldvars;

  let prefix = "aslp_lifter" ^ template_args ^ "::" in
  let fname = name_of_ident name in
  let args = build_args "typename Traits::" targs args in
  let ret = prints_ret_type ret_tyo in

  write_line template_header st;
  Printf.fprintf st.oc "%s %s%s%s {\n" ret prefix fname args;
  write_stmts body st;
  Printf.fprintf st.oc "\n} // %s\n\n" fname;

  st.genvars <- oldvars;
  { rty = ret; prefix; name; args; file = st.file; }

(****************************************************************
 * Directory Setup
 ****************************************************************)

let init_st (genfns: cpp_fun_sig list) prefix file =
  let genvars = List.map (fun {name;_} -> name) genfns in
  let path = Filename.concat prefix file in
  Utils.mkdir_p (Filename.dirname path);
  let oc = open_out path in

  { depth = 0; skip_seq = false; file; oc; ref_vars = IdentSet.empty ;
    genvars; }

(* prefix used to access all generated header files. *)
let export_prefix = "aslp/generated"
(* directory for generated template headers. *)
let gen_dir = "include"
(* directory for generated source files for explicit instantiation. *)
let instantiate_dir = "src/generated"
(* headers required by all files. note aslp/interface.hpp is NOT generated. *)
let stdlib_deps = ["cassert"; "tuple"; "variant"; "vector"; "stdexcept"; "aslp/interface.hpp"]
(* headers required by instruction semantics files.
   includes forward declaration of lifter class. *)
let global_deps = stdlib_deps @ [export_prefix^"/aslp_lifter.hpp"]


(** Write an instruction file, containing just the behaviour of one instructions *)
let write_instr_file fn fnsig prefix dir =
  let m = name_of_FIdent fn in
  let path = dir ^ "/" ^ m ^ ".hpp" in
  let st = init_st [] prefix path in
  write_preamble global_deps st;
  let gen = write_fn fn fnsig st in
  write_epilogue () st;
  close_out st.oc;
  gen

(* Write the test file, containing all decode tests *)
let write_test_file tests prefix dir =
  let m = "decode_tests" in
  let path = dir ^ "/" ^ m ^ ".hpp" in
  let st = init_st [] prefix path in
  write_preamble global_deps st;
  let gens = List.map (fun (i,s) -> write_fn i s st) @@ Bindings.bindings tests in
  write_epilogue () st;
  close_out st.oc;
  gens

(* Write the decoder file *)
let write_decoder_file fn fnsig genfns prefix dir =
  let m = name_of_FIdent fn in
  let path = dir ^ "/" ^ m ^ ".hpp" in
  let st = init_st genfns prefix path in
  write_preamble (global_deps@[export_prefix^"/decode_tests.hpp"]) st;
  let gen = write_fn fn fnsig st in
  write_epilogue fn st;
  close_out st.oc;
  gen


(* Write the public-facing header file. For compilation speed, this declares but does not define. *)
let write_header_file fn fnsig semfns testfns prefix dir =
  let name = "aslp_lifter" in
  let path = dir ^ "/" ^ name ^ ".hpp" in
  let st = init_st [] prefix path in
  write_preamble stdlib_deps st;

  write_line template_header st;
  write_line "class aslp_lifter {\n" st;

  inc_depth st;
  write_line ("public: using interface = lifter_interface" ^ template_args ^ ";\n") st;
  write_line "private: interface& iface;\n" st;
  write_line "public:\n" st;
  write_line "aslp_lifter(interface& iface) : iface{iface} { }\n" st;

  write_line "/* generated semantics */\n" st;
  List.iter
    (fun {rty; name; args; _} -> write_line (rty ^ " " ^ name_of_ident name ^ args ^ ";\n") st)
    semfns;
  write_line "/* generated decode test conditions */\n" st;
  List.iter
    (fun {rty; name; args; _} -> write_line (rty ^ " " ^ name_of_ident name ^ args ^ ";\n") st)
    testfns;

  dec_depth st;
  write_line "};\n" st;

  write_epilogue fn st;
  close_out st.oc;
  (name, semfns @ testfns)

(** Writes the template implementation file. If needed, this can be used to instantiate the entire lifter.
    However, it is fairly slow. *)
let write_impl_file allfns prefix dir =
  let name = "aslp_lifter_impl" in
  let path = dir ^ "/" ^ name ^ ".hpp" in
  let st = init_st [] prefix path in
  let exports = Utils.nub @@ List.map (fun {file;_} -> file) allfns in
  write_preamble stdlib_deps ~exports st;

  write_epilogue () st;
  close_out st.oc;
  name

(* Creates a directory of explicit instantiations, supporting parallel compilation. *)
let write_explicit_instantiations cppfuns prefix dir =
  let write_instantiation file (cppfuns : cpp_fun_sig list) =
    let dep = file in
    let file = Filename.(chop_extension (basename file)) in
    let path = dir ^ "/" ^ file ^ ".cpp" in
    let st = init_st [] prefix path in

    write_preamble ~header:false stdlib_deps ~exports:[dep] st;

    write_line "#ifdef ASLP_LIFTER_INSTANTIATE\n" st;
    write_line "using Traits = ASLP_LIFTER_INSTANTIATE;\n" st;
    List.iter
      (fun {rty; name; args; _} ->
        let fname = name_of_ident name in
        let s = Printf.sprintf "template %s %s%s::%s%s;\n" rty "aslp_lifter" template_args fname args in
        write_line s st)
      cppfuns;
    write_line "#endif\n" st;

    write_epilogue () st;
    close_out st.oc;
    (path, cppfuns)
  in
  (* group by the .hpp file where each template is defined. *)
  let files = Utils.nub @@ List.map (fun x -> x.file) cppfuns in
  List.map
    (fun file ->
      write_instantiation file (List.filter (fun x -> x.file = file) cppfuns))
    files


(* Finalises the generation by writing build-system files. *)
let write_build_files instdir funs dir =
  let meson_template = [%blob "../offlineASL-cpp/subprojects/aslp-lifter/meson.build.in"] in
  let interface_file = [%blob "../offlineASL-cpp/subprojects/aslp-lifter/include/aslp/interface.hpp"] in

  close_out @@ open_out_bin @@ dir ^ "/dummy.cpp";

  let headers_dir = dir ^ "/include/aslp" in
  Utils.mkdir_p headers_dir;
  let exported = ["aslp_lifter.hpp"; "aslp_lifter_impl.hpp"] in
  List.iter (fun h ->
    let f = open_out_bin @@ headers_dir ^ "/" ^ h in
    Printf.fprintf f {|#include "generated/%s" // IWYU pragma: export%s|} h "\n";
    close_out f
  ) exported;

  let f = open_out_bin @@ headers_dir ^ "/interface.hpp" in
  output_string f interface_file;
  close_out f;

  let re = Str.regexp_string {|["SRCFILES"]|} in
  let instfiles =
    List.map fst funs
    |> Utils.nub
    |> List.map (fun file -> Printf.sprintf {|  '%s/%s',%s|} instdir file "\n") in
  let srcfiles = "[\n" ^ String.concat "" instfiles ^ "]\n" in
  let f = open_out_bin @@ dir ^ "/meson.build" in
  output_string f @@ Str.global_replace re srcfiles meson_template;
  close_out f

(* Write all of the above, generating all necessary files for a minimal meson project *)
let run dfn dfnsig tests fns root =

  let genprefix = root ^ "/" ^ gen_dir in
  let instprefix = root ^ "/" ^ instantiate_dir in

  let semfns = Bindings.fold (fun fn fnsig acc -> (write_instr_file fn fnsig genprefix export_prefix)::acc) fns [] in
  let testfns = write_test_file tests genprefix export_prefix in
  let allfns = semfns @ testfns in

  let dfn = write_decoder_file dfn dfnsig allfns genprefix export_prefix in
  let allfns = dfn :: allfns in

  let _header = write_header_file dfn dfnsig (dfn :: semfns) testfns genprefix export_prefix in
  let explicits = write_explicit_instantiations allfns instprefix "." in

  let _impl = write_impl_file allfns genprefix export_prefix in

  let () = write_build_files instantiate_dir explicits root in

  if not (Sys.file_exists (root ^ "/meson.build")) then
    Printf.eprintf "Warning: cpp gen directory '%s' is missing build system files. These might need to be copied manually.\n\n" root;

  ()

module CppBackend : Backend = struct
  let run ~(config:conf) dfn dfnsig tests fns = run dfn dfnsig tests fns config.output_directory
end
