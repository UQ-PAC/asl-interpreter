open Asl_ast
open Asl_utils
open Asl_visitor
open Visitor

(* TODO:
  dis:
  - Improve simplifications based on branching conditions
  - For loop support
  - BitTuple support
  - Investigate CSE performance issues

  symbolic_lifter:
  - Remove unsupported_set with overrides.asl instead
  - Move supported globals to backend
*)

(* Set of functions we do not want to analyse / inline due to their complexity *)
let unsupported_set = IdentSet.of_list [
  FIdent ("AArch64.TranslateAddress", 0);
  FIdent ("AArch64.Abort", 0);
  FIdent ("Unreachable", 0);
  FIdent ("AArch64.ExclusiveMonitorsPass", 0);
  FIdent ("AArch64.SetExclusiveMonitors", 0);
]

(* Backend specific: Globals we want to keep in the result *)
let supported_globals = IdentSet.of_list [
  Ident("PSTATE.C");
  Ident("PSTATE.Z");
  Ident("PSTATE.V");
  Ident("PSTATE.N");
  Ident("_PC");
  Ident("_R");
  Ident("_Z");
  Ident("SP_EL0");
  Ident("FPSR");
  Ident("FPCR");
]

(* Backend specific: Globals we are confident we can ignore *)
let ignored_globals = IdentSet.of_list [
  Ident("__BranchTaken");
  Ident("BTypeNext");
]

(** Trivial walk to replace unsupported calls with a corresponding throw *)
module RemoveUnsupported = struct
  let assert_false loc = Stmt_Throw(Ident ("UNSUPPORTED"), loc)

  class expr_visitor unsupported env = object
    inherit Asl_visitor.nopAslVisitor
    val mutable seen = false
    method! vexpr e =
      (match e with
      | Expr_TApply (f, _, _) ->
          if unsupported f then (seen <- true; SkipChildren)
          else DoChildren
      | Expr_ImpDef(t, Some(s)) ->
          (try
            let _ = Eval.Env.getImpdef Unknown env s in
            DoChildren
          with _ ->
            match t with
            | Type_Constructor(Ident "boolean") -> ChangeTo (Symbolic.expr_false)
            | _ -> (seen <- true; DoChildren))
      | Expr_ImpDef _ -> (seen <- true; DoChildren)
      | _ -> DoChildren)
    method has_unsupported = seen
  end

  let contains_unsupported e unsupported env =
    let v = new expr_visitor unsupported env in
    let _ = visit_expr v e in
    v#has_unsupported

  class call_visitor unsupported env = object
    inherit Asl_visitor.nopAslVisitor

    method! vstmt e =
      singletonVisitAction (match e with
      | Stmt_Assert(e, loc) ->
          if contains_unsupported e unsupported env then ChangeTo (assert_false loc)
          else DoChildren

      | Stmt_VarDeclsNoInit _
      | Stmt_ProcReturn _ -> DoChildren

      | Stmt_FunReturn (e, loc) ->
          if contains_unsupported e unsupported env then ChangeTo (assert_false loc)
          else DoChildren

      | Stmt_VarDecl(ty, v, e, loc) ->
          if contains_unsupported e unsupported env then ChangeTo (assert_false loc)
          else DoChildren

      | Stmt_ConstDecl(ty, v, e, loc) ->
          if contains_unsupported e unsupported env then ChangeTo (assert_false loc)
          else DoChildren

      | Stmt_Assign(v, e, loc) ->
          if contains_unsupported e unsupported env then ChangeTo (assert_false loc)
          else DoChildren

      | Stmt_TCall (f, tes, es, loc) ->
          if unsupported f then ChangeTo (assert_false loc)
          else if List.exists (fun e -> contains_unsupported e unsupported env) (tes @ es) then ChangeTo (assert_false loc)
          else DoChildren

      | Stmt_If (c, t, alts, f, loc) ->
          if contains_unsupported c unsupported env then ChangeTo (assert_false loc)
          else if List.exists (fun (S_Elsif_Cond(c,_)) -> contains_unsupported c unsupported env) alts then ChangeTo (assert_false loc)
          else DoChildren

      | Stmt_Case (e, alts, odefault, loc) ->
          if contains_unsupported e unsupported env then ChangeTo (assert_false loc)
          else DoChildren

      | Stmt_While (c, b, loc) ->
          if contains_unsupported c unsupported env then ChangeTo (assert_false loc)
          else DoChildren

      | Stmt_For(var, start, dir, stop, body, loc) ->
          if contains_unsupported start unsupported env then ChangeTo (assert_false loc)
          else if contains_unsupported stop unsupported env then ChangeTo (assert_false loc)
          else DoChildren

      | Stmt_Dep_Undefined loc
      | Stmt_Undefined loc
      | Stmt_Unpred loc
      | Stmt_ConstrainedUnpred loc
      | Stmt_ImpDef (_, loc)
      | Stmt_ExceptionTaken loc
      | Stmt_Dep_Unpred loc
      | Stmt_Dep_ImpDef (_, loc)
      | Stmt_See (_, loc)
      | Stmt_Throw (_, loc)
      | Stmt_DecodeExecute (_, _, loc)
      | Stmt_Try (_, _, _, _, loc)
      | Stmt_Repeat (_, _, loc) -> ChangeTo (assert_false loc))
  end

  let run unsupported env body =
    let v = new expr_visitor unsupported env in
    let body = visit_stmts v body in
    let v = new call_visitor unsupported env in
    visit_stmts v body

end

let unsupported f = IdentSet.mem f unsupported_set

let get_inlining_frontier =
  (* Collect all functions dis will not inline *)
  let l1 = IdentSet.of_list (Symbolic.prims_impure ()) in
  let l2 = IdentSet.of_list (Symbolic.prims_pure ()) in
  (* Union with the unsupported function set *)
  IdentSet.union l1 l2

(* Count individual stmts present after disassembly *)
let rec stmt_count s =
  match s with
  | Stmt_If (_,t,[],f,_) ->
      1 + stmts_count t + stmts_count f
  | _ -> 1
and stmts_count s =
  List.fold_right (fun s acc -> stmt_count s + acc) s 0

module Cleanup = struct

  let rec is_throw_unsupported s =
    match s with
    | (Stmt_Throw (Ident "UNSUPPORTED", loc))::xs -> true
    | x::xs -> is_throw_unsupported xs
    | _ -> false

  (* Remove unsupported instr bodies *)
  class call_visitor = object
    inherit nopAslVisitor
    method! vstmt e =
      let reduce e = (match e with
      | Stmt_Throw(_,loc)
      | Stmt_Unpred(loc)
      | Stmt_ConstrainedUnpred(loc)
      | Stmt_ImpDef(_, loc)
      | Stmt_Undefined(loc)
      | Stmt_ExceptionTaken(loc)
      | Stmt_Dep_Unpred(loc)
      | Stmt_Dep_ImpDef(_, loc)
      | Stmt_Dep_Undefined(loc)
      | Stmt_See(_, loc)
      | Stmt_Assert(Expr_Var (Ident "FALSE"), loc) ->
          (RemoveUnsupported.assert_false loc)

      | Stmt_If(c, t, els, f, loc) ->
          if is_throw_unsupported t &&
              List.for_all (fun (S_Elsif_Cond(_,b)) -> is_throw_unsupported b) els &&
                is_throw_unsupported f then
            (RemoveUnsupported.assert_false loc)
          else e
      | _ -> e) in
      singletonVisitAction @@ ChangeDoChildrenPost(e, reduce)
  end

  let rec trim_post_term stmts =
    List.fold_right (fun stmt acc ->
      match stmt with
      | Stmt_Throw _ -> [stmt]
      | Stmt_If (c, t, [], f, loc) ->
          let t = trim_post_term t in
          let f = trim_post_term f in
          (match t, f with
          | [Stmt_Throw _], [Stmt_Throw _] -> t
          | _ -> Stmt_If (c, t, [], f, loc)::acc)
      | _ -> stmt::acc) stmts []

  let run verb stmts =
    let v = new call_visitor in
    let stmts = (visit_stmts v) stmts in
    trim_post_term stmts

end

module DecoderCleanup = struct

  (* Remove unsupported decode tests *)
  class expr_visitor unsupported = object
    inherit nopAslVisitor
    method! vexpr e =
      (match e with
      | Expr_TApply (f, _, _) ->
          let suffix = "_decode_test" in
          if String.ends_with ~suffix (name_of_FIdent f) && unsupported f then ChangeTo (Symbolic.expr_true)
          else DoChildren
      | _ -> DoChildren)
  end

  let rec is_throw_unsupported s =
    match s with
    | (Stmt_Throw (Ident "UNSUPPORTED", loc))::xs -> true
    | x::xs -> is_throw_unsupported xs
    | _ -> false

  (* Remove unsupported instr bodies *)
  class call_visitor unsupported  = object
    inherit nopAslVisitor
    method! vstmt e =
      let reduce e = (match e with
      | Stmt_TCall (f, _, _, loc) ->
          if unsupported f then (RemoveUnsupported.assert_false loc)
          else e
      | Stmt_Throw(_, loc)
      | Stmt_Unpred(loc)
      | Stmt_ConstrainedUnpred(loc)
      | Stmt_ImpDef(_, loc)
      | Stmt_Undefined(loc)
      | Stmt_ExceptionTaken(loc)
      | Stmt_Dep_Unpred(loc)
      | Stmt_Dep_ImpDef(_, loc)
      | Stmt_Dep_Undefined(loc)
      | Stmt_See(_, loc)
      | Stmt_Assert(Expr_Var (Ident "FALSE"), loc) ->
          (RemoveUnsupported.assert_false loc)

      | Stmt_If(c, t, els, f, loc) ->
          if is_throw_unsupported t &&
              List.for_all (fun (S_Elsif_Cond(_,b)) -> is_throw_unsupported b) els &&
                is_throw_unsupported f then
            (RemoveUnsupported.assert_false loc)
          else e
      | _ -> e) in
      singletonVisitAction @@ ChangeDoChildrenPost(e, reduce)
  end

  let run unsupported dsig =
    let v = new expr_visitor unsupported in
    let dsig = (visit_stmts v) dsig in
    let v = new call_visitor unsupported in
    let dsig = (visit_stmts v) dsig in
    dsig
end

let unsupported_inst tests instrs f =
  not (Bindings.mem f tests || Bindings.mem f instrs)

let dis_wrapper fn fnsig env =
  let (lenv,globals) = Dis.build_env env in
  let body = fnsig_get_body fnsig in
  let args = fnsig_get_typed_args fnsig in
  let config = {Dis.eval_env = env ; unroll_bound = Z.of_int64 Int64.max_int; } in
  try
    (* Setup initial environment based on function arguments *)
    let lenv =
      (match args with
      | [tenc, enc ; tpc, pc] ->
          let (_,lenv,_) = Dis.declare_assign_var Unknown tenc enc (Symbolic.Exp (Expr_Var enc)) config lenv in
          Dis.LocalEnv.setVar Unknown (Var (0, "_PC")) (Symbolic.Exp (Expr_Var pc)) lenv
      | [tenc, enc] ->
          let (_,lenv,_) = Dis.declare_assign_var Unknown tenc enc (Symbolic.Exp (Expr_Var enc)) config lenv in
          lenv
      | _ -> failwith @@ "Unexpected fn args: " ^ Utils.pp_list (fun (t,v) -> pp_type t ^ " " ^ pprint_ident v) args) in

    (* Run dis over the function body and extract the residual program *)
    let ((),lenv',stmts) = Dis.dis_stmts body config lenv in
    let stmts = Dis.flatten stmts [] in

    (* Optional post-pass to prune unsupported globals and their fields *)
    let stmts' = if false then
      let flattened_globals = Transforms.UnsupportedVariables.flatten_vars (Eval.Env.readGlobals env) in
      let unsupported_globals = IdentSet.diff flattened_globals supported_globals in
      Transforms.UnsupportedVariables.do_transform ignored_globals unsupported_globals stmts
    else stmts in

    (* Cleanup transforms *)
    let stmts' = Transforms.RemoveUnused.remove_unused globals @@ stmts' in
    let stmts' = Transforms.RedundantSlice.do_transform Bindings.empty stmts' in
    let stmts' = Transforms.StatefulIntToBits.run (Dis.enum_types env) stmts' in
    let stmts' = Transforms.IntToBits.ints_to_bits stmts' in
    (*let stmts' = Transforms.CommonSubExprElim.do_transform stmts' in*)
    let stmts' = Transforms.CopyProp.copyProp stmts' in
    let stmts' = Transforms.RemoveUnused.remove_unused globals @@ stmts' in
    let stmts' = Transforms.CaseSimp.do_transform stmts' in
    let stmts' = Transforms.RemoveRegisters.run stmts' in
    let stmts' = Cleanup.run false stmts' in
    let stmts' = Transforms.RemoveUnused.remove_unused globals @@ stmts' in
    let stmts' = Transforms.FixRedefinitions.run (globals : IdentSet.t) stmts' in
    Some stmts'
  with
  | e ->
      let m = Printexc.to_string e in
      let m = if String.length m > 100 then String.sub m 0 100 ^ "..." else m in
      Printf.printf "Error: %s %s\n" (name_of_FIdent fn) m;
      None

type  offline_result = ident * Eval.fun_sig * Eval.fun_sig Bindings.t * Eval.fun_sig Bindings.t

(* Produce a lifter for the desired parts of the instruction set *)
let run include_pc iset pat env : offline_result =
  Printf.printf "Stage 1: Mock decoder & instruction encoding definitions\n";
  let ((did,dsig),tests,instrs) = Decoder_program.run include_pc iset pat env in
  flush stdout;
  Printf.printf "  Collected %d instructions\n\n" (Bindings.cardinal instrs);

  Printf.printf "Stage 2: Call graph construction\n";
  flush stdout;
  let frontier = get_inlining_frontier in
  let (callers, reachable) = Call_graph.run (bindings_domain instrs) frontier env in
  let fns = IdentSet.fold (fun id acc -> Bindings.add id (Eval.Env.getFun Unknown env id) acc) reachable Bindings.empty in
  Printf.printf "  Collected %d functions\n\n" (Bindings.cardinal fns);

  Printf.printf "Stage 3: Simplification\n";
  flush stdout;
  (* Remove temporary dynamic bitvectors where possible *)
  let fns = Bindings.map (fnsig_upd_body (Transforms.RemoveTempBVs.do_transform false)) fns in
  (* Remove calls to problematic functions & impdefs *)
  let fns = Bindings.map (fnsig_upd_body (RemoveUnsupported.run unsupported env)) fns in
  Printf.printf "\n";

  Printf.printf "Stage 4: Specialisation\n";
  flush stdout;
  (* Run requirement collection over the full set *)
  let fns = Req_analysis.run fns callers in
  Printf.printf "\n";

  Printf.printf "Stage 5: Disassembly\n";
  flush stdout;
  (* Build an environment with these new function definitions *)
  let env' = Eval.Env.copy env in
  Bindings.iter (fun  fn fnsig  -> Eval.Env.addFun Unknown env' fn fnsig) fns;
  (* Run dis over the entry set identifiers with this new environment *)

  let fns = Bindings.filter_map (fun fn fnsig ->
    if (not (Bindings.mem fn instrs)) then None
    else Option.map (fnsig_set_body fnsig) (dis_wrapper fn fnsig env')) fns in
  Printf.printf "  Succeeded for %d instructions\n\n" (Bindings.cardinal fns);

  let decoder = Eval.Env.getDecoder env (Ident iset) in
  let decoderst : Transforms.DecoderChecks.st = Transforms.DecoderChecks.do_transform decoder in
  let fns = Transforms.BDDSimp.transform_all fns decoderst in
  let (_,globals) = Dis.build_env env in
  let fns = Bindings.map (fnsig_upd_body (Transforms.RemoveUnused.remove_unused globals)) fns in

  Printf.printf "Stmt Counts\n";
  flush stdout;
  let l = Bindings.fold (fun fn fnsig acc -> (fn, stmts_count (fnsig_get_body fnsig))::acc) fns [] in
  let l = List.sort (fun (_,i) (_,j) -> compare i j) l in
  List.iter (fun (fn,c) -> Printf.printf "  %d\t:\t%s\n" c (name_of_FIdent fn)) l;
  Printf.printf "\n";

  Printf.printf "Stage 6: Cleanup\n";
  flush stdout;
  (* TODO: Defer *)
  let tests = Bindings.map (fun s -> fnsig_upd_body (Transforms.RemoveUnused.remove_unused IdentSet.empty) s) tests in
  Printf.printf "\n";

  (* Perform offline PE *)
  Printf.printf "Stages 7-8: Offline Transform\n";
  flush stdout;
  let offline_fns = Offline_transform.run fns env in
  let offline_fns = Bindings.mapi (fun k -> fnsig_upd_body (Offline_opt.DeadContextSwitch.run k)) offline_fns in

  let freachable k = 
    let k = match k with 
      | FIdent (n, _) -> Ident n
      | n -> n in
    Bindings.find k decoderst.instrs 
  in

  let offline_fns = Bindings.mapi (fun k -> fnsig_upd_body (Offline_opt.RtCopyProp.run k (freachable k))) offline_fns in
  Transforms.BDDSimp.print_unknown_prims (); 

  let dsig = fnsig_upd_body (DecoderCleanup.run (unsupported_inst tests offline_fns)) dsig in
  let dsig = fnsig_upd_body (Transforms.RemoveUnused.remove_unused IdentSet.empty) dsig in
  Printf.printf "\n";

  (did,dsig,tests,offline_fns)


let run_marshal include_pc iset pat env : offline_result = 
  let fname = Printf.sprintf "marshalled-offline-lifter-%x" 
    (*FIXME: I don't think this is working as expected *)
    (Hashtbl.seeded_hash 1234 (Printf.sprintf "%b %s %s" include_pc iset pat))
  in
  if (Sys.file_exists fname) 
  then begin
    Printf.printf "Using marshalled lifter (pc: %b iset: %s pat: %s):  %s\n" include_pc iset pat fname;
    let ic = open_in_bin fname in
    let r: offline_result = Marshal.from_channel ic in
    close_in ic;
    r
    end
  else 
    let r: offline_result = run include_pc iset pat env in
    let oc = open_out_bin fname in
    Printf.printf "Writing marshalled lifter (pc: %b iset: %s pat: %s):  %s\n" include_pc iset pat fname;
    Marshal.to_channel oc r []; close_out oc;
    r
