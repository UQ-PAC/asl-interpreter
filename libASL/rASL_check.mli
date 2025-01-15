
module AST = Asl_ast
module Env = Eval.Env

open AST


type rasl_structure_error =  [`NonemptyElseIf | `IllegalStatement | `LoadSingle | `IllegalIntrinsic of string 
    | `IllegalExpr of expr | `IllegalSlice of expr | `IllegalLExpr of lexpr]

type error_info = {
  at_statement: stmt option; 
  violation: rasl_structure_error
}

exception RASLInvariantFailed of (error_info list)

module type InvChecker  = sig
  val check_stmts : stmt list -> error_info list
  val check_expr : expr -> error_info list
  val check_stmt : stmt -> error_info list
end

module type InvCheckerExc = sig 
  include InvChecker
  val check_stmts_exc : ?suppress:(rasl_structure_error -> bool) -> stmt list -> unit
end

module MakeInvCheckerExc : functor (E: InvChecker) -> InvCheckerExc

module LoadStatmentInvariant : InvChecker 
module AllowedIntrinsics : InvChecker
module LoadStatementInvariantExc : InvCheckerExc
module AllowedIntrinsicsExc : InvCheckerExc
module AllowedLanguageConstructs : InvChecker
module AllowedLanguageConstructsExc : InvCheckerExc
