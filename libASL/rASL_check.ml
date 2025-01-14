

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
  at_statement: stmt option; 
  violation: [`LoadSingle | `DisallowedIntrinsic of string];
}

let show_violation = function 
  | `LoadSingle -> "Loads are limited to rhs of constdecl"
  | `DisallowedIntrinsic s -> "Illegal intrinsic: '" ^ s ^ "'"

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
  val check_stmts_exc : ?suppress:bool -> stmt list -> unit
end

module MakeInvCheckerExc(E : InvChecker) : InvCheckerExc = struct 
  include E

  let check_stmts_exc ?(suppress=false) s =
    if suppress then ()
    else match check_stmts s with
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
   *)

  let impure = List.to_seq (Symbolic.prims_impure ())
  let pure = List.to_seq @@  [
        FIdent("ite",0);
        FIdent("ite_vec",0);
        FIdent("Elem.set",0);
        FIdent("Elem.read",0);
  ]  @ (Symbolic.prims_pure ())

  let allowed_intrinsics =
    IdentSet.add_seq pure @@
    IdentSet.add_seq impure @@
    IdentSet.of_list []

  class allowed_intrinsics (vars) = object (self)
    inherit Asl_visitor.nopAslVisitor
    (* Ensures loads only appear in statements of the form lhs := Mem_load(v) *)

    val mutable violating = []
    val mutable curstmt = None
    method get_violating () = violating

    method!vexpr e = match e with 
        | Expr_TApply(f, _, _) when (not @@ IdentSet.mem f allowed_intrinsics) ->  (
          let f = (name_of_FIdent f) in
          violating <- {at_statement=curstmt; violation=(`DisallowedIntrinsic f)}::violating ;
          DoChildren
        )
        | _ -> DoChildren

    method!vstmt s = 
      curstmt <- Some s ; 
      match s with 
      | Stmt_TCall(f, _, _, _) when (not @@ IdentSet.mem f allowed_intrinsics) -> 
          let f = (name_of_FIdent f) in
          violating <- {at_statement=curstmt; violation=(`DisallowedIntrinsic f)}::violating ;
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
