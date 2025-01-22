

module AST = Asl_ast
open Asl_utils


type conf = {
  use_pc : bool;
  output_directory: string;
}

module type Backend = sig 
  val run : config:conf -> AST.ident -> Eval.fun_sig -> Eval.fun_sig Bindings.t -> Eval.fun_sig Bindings.t -> unit
end
