

module AST = Asl_ast
module Env = Eval.Env

open AST
open Visitor
open Asl_utils 
open Asl_visitor

(****************************************************************
 * Check invariants of the reduced asl language
 ****************************************************************)

type error_info = {
  at_statment: stmt option; 
  violation: [`LoadSingle | `DisallowedIntrinsic of string];
}

let show_violation = function 
  | `LoadSingle -> "Loads are limited to rhs of constdecl"
  | `DisallowedIntrinsic s -> "Illegal intrinsic :'" ^ s ^ "'"

let show_error_info (e: error_info) = 
  Printf.sprintf "%s at %s" (show_violation e.violation) 
    ((Option.map (fun s -> pp_stmt s) e.at_statment) |> function | Some x -> x | None -> "")

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
  val check_stmts_exc : ?suppress:bool -> stmt list -> unit
end

module MakeInvCheckerExc(E : InvChecker) : InvCheckerExc = struct 
  include E

  let check_stmts_exc ?(suppress=false) s = if (not suppress) then check_stmts s |> 
    function 
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
          violating <- {at_statment=curstmt; violation=`LoadSingle}::violating ;
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
   *)
  let allowed_intrinsics =
    StringSet.of_list
      [
        "Mem.read";
        "Mem.set";
        "Elem.read";
        "Elem.set";
        "AtomicEnd";
        "AtomicStart";
        "FPAdd";
        "FPDiv";
        "FPMul";
        "FPMulX";
        "FPMulAdd";
        "FPMulAddH";
        "FPSub";
        "FPSqrt";
        "FPRSqrtStepFused";
        "FPCompare";
        "FPCompareGT";
        "FPCompareGE";
        "FPCompareEQ";
        "FPMax";
        "FPMin";
        "FPMaxNum";
        "FPMinNum";
        "FPToFixedJS_impl";
        "FPRecipEstimate";
        "FPRecipStepFused";
        "FPRecpX";
        "BFAdd";
        "BFMul";
        "FPCompare";
        "FixedToFP";
        "FPToFixed";
        "FPConvert";
        "FPConvertBF";
        "FPRoundInt";
        "FPRoundIntN";
        "not_bool";
        "and_bool";
        "or_bool";
        "cvt_bool_bv";
        "SignExtend";
        "ZeroExtend";
        "add_bits";
        "and_bits";
        "append_bits";
        "asr_bits";
        "lsl_bits";
        "lsr_bits";
        "cvt_bits_uint";
        "eor_bits";
        "eq_bits";
        "ne_bits";
        "ite";
        "mul_bits";
        "not_bits";
        "or_bits";
        "sdiv_bits";
        "sub_bits";
        "sle_bits";
        "slt_bits";
        "replicate_bits";
        "select_vec";
        "ite_vec";
        "eq_vec";
        "add_vec";
        "sub_vec";
        "asr_vec";
        "trunc_vec";
        "zcast_vec";
        "shuffle_vec";
        "scast_vec";
      ]

  class allowed_intrinsics (vars) = object (self)
    inherit Asl_visitor.nopAslVisitor
    (* Ensures loads only appear in statements of the form lhs := Mem_load(v) *)

    val mutable violating = []
    val mutable curstmt = None
    method get_violating () = violating

    method!vexpr e = match e with 
        | Expr_TApply(f, _, _) when (not @@ StringSet.mem (name_of_FIdent f) allowed_intrinsics) ->  (
          let f = (name_of_FIdent f) in
          violating <- {at_statment=curstmt; violation=(`DisallowedIntrinsic f)}::violating ;
          DoChildren
        )
        | _ -> DoChildren

    method!vstmt s = 
      curstmt <- Some s ; 
      match s with 
      | Stmt_ConstDecl(t, ident, Expr_TApply(f, _, _), loc) when (name_of_FIdent f = "Mem.read") -> SkipChildren
      | Stmt_TCall(f, _, _, _) when (not @@ StringSet.mem (name_of_FIdent f) allowed_intrinsics) -> 
          let f = (name_of_FIdent f) in
          violating <- {at_statment=curstmt; violation=(`DisallowedIntrinsic f)}::violating ;
          DoChildren
      | _ -> DoChildren

  end

  let check_stmts s = 
    let v = new allowed_intrinsics () in
    ignore @@ visit_stmts v s ;
    v#get_violating ()

  let check_stmt s = check_stmts [s]

  let check_expr e = 
    let v = new allowed_intrinsics () in
    ignore @@ visit_expr v e ;
    v#get_violating ()

end

module LoadStatementInvariantExc = MakeInvCheckerExc(LoadStatmentInvariant)
module AllowedIntrinsicsExc = MakeInvCheckerExc(AllowedIntrinsics)
