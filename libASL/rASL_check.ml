

module AST = Asl_ast
module Env = Eval.Env

open AST
open Visitor
open Asl_utils 
open Asl_visitor

(****************************************************************
 * Check invariants of the reduced asl language
 ****************************************************************)

type rasl_structure_error =  [`NonemptyElseIf | `IllegalStatement | `LoadSingle | `IllegalIntrinsic of string 
    | `IllegalExpr of expr | `IllegalSlice of expr | `IllegalLExpr of lexpr]

type error_info = {
  at_statement: stmt option; 
  violation: rasl_structure_error
}


let show_violation = function 
  | `LoadSingle -> "Loads are limited to rhs of constdecl"
  | `IllegalIntrinsic s -> "Illegal intrinsic: '" ^ s ^ "'"
  | `NonemptyElseIf -> "If statements contains an else-if branch"
  | `IllegalStatement -> "Illegal statement type"
  | `IllegalExpr e -> "Illegal expression: '" ^ (pp_expr e) ^ "'"
  | `IllegalSlice e -> "Illegal slice expr (must have single slice of constant values) type: '" ^ (pp_expr e) ^ "'"
  | `IllegalLExpr e -> "Illegal lexpr (not var field or array): '" ^ (pp_lexpr e) ^ "'"

let show_error_info (e: error_info) = 
  Printf.sprintf "%s at %s" (show_violation e.violation) 
    ((Option.map (fun s -> pp_stmt s) e.at_statement) |> function | Some x -> x | None -> "")

exception RASLInvariantFailed of (error_info list)

let () = Printexc.register_printer (function 
    | RASLInvariantFailed es -> Some (Printf.sprintf "RASL invariant(s) failed: %s" (String.concat "; " (List.map show_error_info es)))
    | _ -> None
  )

module type InvChecker  = sig
  val check_stmts : stmt list -> error_info list
  val check_expr : expr -> error_info list
  val check_stmt : stmt -> error_info list
end


module type InvCheckerExc = sig 
  include InvChecker
  val check_stmts_exc : ?suppress:(rasl_structure_error -> bool) -> stmt list -> unit
end

module MakeInvCheckerExc(E : InvChecker) : InvCheckerExc = struct 
  include E

  let check_stmts_exc ?(suppress=fun _ -> false) s =
    match (List.filter (fun e -> suppress e.violation) (check_stmts s)) with
    | [] -> ()
    | es -> raise (RASLInvariantFailed es)
end

module LoadStatmentInvariant : InvChecker = struct 

  class single_load (vars) = object (self)
    inherit Asl_visitor.nopAslVisitor
    (* Ensures loads only appear in statements of the form lhs := Mem_load(v) *)

    val mutable violating = []
    val mutable curstmt = None
    method get_violating () = violating

    method!vexpr e = match e with 
        | Expr_TApply(f, _, _) when (name_of_FIdent f = "Mem.read") ->  (
          violating <- {at_statement=curstmt; violation=`LoadSingle}::violating ;
          SkipChildren
        )
        | _ -> DoChildren

    method!vstmt s = 
      curstmt <- Some s ; 
      match s with 
      | Stmt_ConstDecl(t, ident, Expr_TApply(f, _, _), loc) when (name_of_FIdent f = "Mem.read") -> SkipChildren
      | _ -> DoChildren

  end

  let check_stmts s = 
    let v = new single_load () in
    ignore @@ visit_stmts v s ;
    v#get_violating ()

  let check_stmt s = check_stmts [s]

  let check_expr e = 
    let v = new single_load () in
    ignore @@ visit_expr v e ;
    v#get_violating ()

end

module AllowedIntrinsics: InvChecker = struct 

  (*
  Ensure the only intrinsic function calls are appear in the following list.
  Note that this list is distinct to Symbolic.prims_pure, as late transform
  passes ensure only a limited set of pure primitives are produced.
   *)
  let prims_pure_out () =
    [
      FIdent("LSL",0);
      FIdent("LSR",0);
      FIdent("ASR",0);
      FIdent("SignExtend",0);
      FIdent("ZeroExtend",0);
      FIdent("asr_bits",0);
      FIdent("lsr_bits",0);
      FIdent("lsl_bits",0);
      FIdent("slt_bits",0);
      FIdent("sle_bits",0);
      FIdent("sdiv_bits",0);
      FIdent("ite",0);
      FIdent("eq_bool",0);
      FIdent("ne_bool",0);
      FIdent("not_bool",0);
      FIdent("and_bool",0);
      FIdent("or_bool",0);
      FIdent("implies_bool",0);
      FIdent("cvt_bits_sint",0);
      FIdent("cvt_bits_uint",0);
      FIdent("eq_bits",0);
      FIdent("ne_bits",0);
      FIdent("add_bits",0);
      FIdent("sub_bits",0);
      FIdent("mul_bits",0);
      FIdent("and_bits",0);
      FIdent("or_bits",0);
      FIdent("eor_bits",0);
      FIdent("not_bits",0);
      FIdent("replicate_bits",0);
      FIdent("append_bits",0);
      FIdent("cvt_bv_bool",0);
      FIdent("cvt_bool_bv",0);
    ] @ (if !Symbolic.use_vectoriser then [
      FIdent("Elem.set",0);
      FIdent("Elem.read",0);
      FIdent("add_vec",0);
      FIdent("sub_vec",0);
      FIdent("mul_vec",0);
      FIdent("sdiv_vec",0);
      FIdent("lsr_vec",0);
      FIdent("asr_vec",0);
      FIdent("lsl_vec",0);
      FIdent("ite_vec",0);
      FIdent("sle_vec",0);
      FIdent("slt_vec",0);
      FIdent("eq_vec",0);
      FIdent("zcast_vec",0);
      FIdent("scast_vec",0);
      FIdent("trunc_vec",0);
      FIdent("select_vec",0);
      FIdent("shuffle_vec",0);
      FIdent("reduce_add",0);
    ] else [])

  let allowed_set () =
    IdentSet.add_seq (List.to_seq (prims_pure_out ())) @@
    IdentSet.add_seq (List.to_seq (Symbolic.prims_impure ())) @@
    IdentSet.of_list []

  class allowed_intrinsics (intrinsics) = object (self)
    inherit Asl_visitor.nopAslVisitor
    (* Ensures loads only appear in statements of the form lhs := Mem_load(v) *)

    val mutable violating = []
    val mutable curstmt = None
    method get_violating () = violating

    method!vexpr e = match e with
        | Expr_TApply(f, _, _) when (not @@ IdentSet.mem f intrinsics) ->  (
          let f = (name_of_FIdent f) in
          violating <- {at_statement=curstmt; violation=(`IllegalIntrinsic f)}::violating ;
          DoChildren
        )
        | _ -> DoChildren

    method!vstmt s =
      curstmt <- Some s ;
      match s with
      | Stmt_TCall(f, _, _, _) when (not @@ IdentSet.mem f intrinsics) ->
          let f = (name_of_FIdent f) in
          violating <- {at_statement=curstmt; violation=(`IllegalIntrinsic f)}::violating ;
          DoChildren
      | _ -> DoChildren

  end

  let check_stmts s =
    let i = allowed_set () in
    let v = new allowed_intrinsics i in
    ignore @@ visit_stmts v s ;
    v#get_violating ()

  let check_stmt s = check_stmts [s]

  let check_expr e =
    let i = allowed_set () in
    let v = new allowed_intrinsics i in
    ignore @@ visit_expr v e ;
    v#get_violating ()

end

module AllowedLanguageConstructs: InvChecker = struct 

  (*
  Only the following statements are allowed: 
    VarDeclsNoInit, VarDecl, ConstDecl, TCall, Assign, Assert, Throw, If (with no elseif)
  Only the following expressions are allowd:
    Var, Field, Array, TApply, LitBits, LitInt, Slices
   *)

  let is_const = function
    | Expr_LitInt _ -> true
    | Expr_LitHex _ -> true
    | _ -> false

  class allowed_constructs() = object (self)
    inherit Asl_visitor.nopAslVisitor
    (* Ensures loads only appear in statements of the form lhs := Mem_load(v) *)

    val mutable curstmt = None
    val mutable violating : error_info list = []
    method get_violating () : error_info list = violating

    method!vstmt s = 
      curstmt <- Some s ; 
      match s with 
        | Stmt_TCall _ ->  DoChildren
        | Stmt_VarDeclsNoInit _ -> DoChildren
        | Stmt_VarDecl _ -> DoChildren
        | Stmt_ConstDecl _ -> DoChildren
        | Stmt_Assign _ -> DoChildren
        | Stmt_Assert _ -> DoChildren
        | Stmt_Throw _ -> DoChildren
        | Stmt_If (_, _, [], _ , _) -> DoChildren
        | Stmt_If (_, _, elseif, _, _) -> violating <- {at_statement=Some s; violation=`NonemptyElseIf} :: violating ; DoChildren
        | _ -> violating <- {at_statement=Some s; violation=`IllegalStatement}::violating; DoChildren


    method!vexpr e = match e with 
      | Expr_Var _ -> DoChildren
      | Expr_Field _ -> DoChildren
      | Expr_Array _ -> DoChildren
      | Expr_TApply _  -> DoChildren
      | Expr_LitBits _ -> DoChildren
      | Expr_Slices (e, [Slice_LoWd(l,w)]) when is_const(l) && is_const(w) -> DoChildren
      | Expr_Slices _ ->  violating <- {at_statement=curstmt; violation=(`IllegalSlice e)}::violating ; DoChildren
      | _ -> violating <- {at_statement=curstmt; violation=(`IllegalExpr e)}::violating ; DoChildren

    method! vlexpr e = match e with 
      | LExpr_Var _ -> DoChildren
      | LExpr_Field _ -> DoChildren
      | LExpr_Array _ -> DoChildren
      | _ -> violating <- {at_statement=curstmt; violation=(`IllegalLExpr e)}::violating ; DoChildren

  end

  let check_stmts s = 
    let v = new allowed_constructs () in
    ignore @@ visit_stmts v s ;
    v#get_violating ()

  let check_stmt s = check_stmts [s]

  let check_expr e = 
    let v = new allowed_constructs () in
    ignore @@ visit_expr v e ;
    v#get_violating ()

end

module LoadStatementInvariantExc = MakeInvCheckerExc(LoadStatmentInvariant)
module AllowedIntrinsicsExc = MakeInvCheckerExc(AllowedIntrinsics)
module AllowedLanguageConstructsExc = MakeInvCheckerExc(AllowedLanguageConstructs)
