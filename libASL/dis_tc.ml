open Asl_visitor
open Asl_ast
open Asl_utils

(*
Get the types of expressions in a function body after performing dis.
*)

module LocalVarTypes = struct
  class var_visitor = object
    inherit nopAslVisitor
    val mutable types = Bindings.empty
    method! vstmt s =
      (match s with
      | Stmt_VarDeclsNoInit(ty, [v], _)
      | Stmt_VarDecl(ty, v, _, _)
      | Stmt_ConstDecl(ty, v, _, _) -> types <- Bindings.add v ty types
      | _ -> ());
      DoChildren
    method get_types = types
  end

  let run args targs body =
    let v = new var_visitor in
    let _ = visit_stmts v body in
    let types = v#get_types in
    let types = List.fold_right (fun (t,i) -> Bindings.add i t) args types in
    List.fold_right (fun i -> Bindings.add i Value.type_integer) targs types
end

let prim_type fi targs =
  match name_of_FIdent fi, targs with
  | ("eq_enum",           [      ])     -> Some (Symbolic.type_bool )
  | ("ne_enum",           [      ])     -> Some (Symbolic.type_bool )
  | ("eq_bool",           [      ])     -> Some (Symbolic.type_bool )
  | ("ne_bool",           [      ])     -> Some (Symbolic.type_bool )
  | ("or_bool",           [      ])     -> Some (Symbolic.type_bool )
  | ("and_bool",          [      ])     -> Some (Symbolic.type_bool )
  | ("implies_bool",      [      ])     -> Some (Symbolic.type_bool )
  | ("equiv_bool",        [      ])     -> Some (Symbolic.type_bool )
  | ("not_bool",          [      ])     -> Some (Symbolic.type_bool )
  | ("eq_int",            [      ])     -> Some (Symbolic.type_bool )
  | ("ne_int",            [      ])     -> Some (Symbolic.type_bool )
  | ("le_int",            [      ])     -> Some (Symbolic.type_bool )
  | ("lt_int",            [      ])     -> Some (Symbolic.type_bool )
  | ("ge_int",            [      ])     -> Some (Symbolic.type_bool )
  | ("gt_int",            [      ])     -> Some (Symbolic.type_bool )
  | ("is_pow2_int",       [      ])     -> Some (Symbolic.type_bool )
  | ("neg_int",           [      ])     -> Some (Value.type_integer )
  | ("add_int",           [      ])     -> Some (Value.type_integer )
  | ("sub_int",           [      ])     -> Some (Value.type_integer )
  | ("shl_int",           [      ])     -> Some (Value.type_integer )
  | ("shr_int",           [      ])     -> Some (Value.type_integer )
  | ("mul_int",           [      ])     -> Some (Value.type_integer )
  | ("zdiv_int",          [      ])     -> Some (Value.type_integer )
  | ("zrem_int",          [      ])     -> Some (Value.type_integer )
  | ("fdiv_int",          [      ])     -> Some (Value.type_integer )
  | ("frem_int",          [      ])     -> Some (Value.type_integer )
  | ("mod_pow2_int",      [      ])     -> Some (Value.type_integer )
  | ("align_int",         [      ])     -> Some (Value.type_integer )
  | ("pow2_int",          [      ])     -> Some (Value.type_integer )
  | ("pow_int_int",       [      ])     -> Some (Value.type_integer )
  | ("round_tozero_real", [      ])     -> Some (Value.type_integer)
  | ("round_down_real",   [      ])     -> Some (Value.type_integer )
  | ("round_up_real",     [      ])     -> Some (Value.type_integer )
  | ("cvt_bits_sint",     [     n])     -> Some (Value.type_integer )
  | ("cvt_bits_uint",     [     n])     -> Some (Value.type_integer )
  | ("eq_real",           [      ])     -> Some (Symbolic.type_bool )
  | ("ne_real",           [      ])     -> Some (Symbolic.type_bool )
  | ("le_real",           [      ])     -> Some (Symbolic.type_bool )
  | ("lt_real",           [      ])     -> Some (Symbolic.type_bool )
  | ("ge_real",           [      ])     -> Some (Symbolic.type_bool )
  | ("gt_real",           [      ])     -> Some (Symbolic.type_bool )
  | ("in_mask",           [     n])     -> Some (Symbolic.type_bool )
  | ("notin_mask",        [     n])     -> Some (Symbolic.type_bool )
  | ("eq_bits",           [     n])     -> Some (Symbolic.type_bool )
  | ("ne_bits",           [     n])     -> Some (Symbolic.type_bool )
  | ("add_bits",          [     n])     -> Some (Type_Bits n)
  | ("sub_bits",          [     n])     -> Some (Type_Bits n)
  | ("mul_bits",          [     n])     -> Some (Type_Bits n)
  | ("and_bits",          [     n])     -> Some (Type_Bits n)
  | ("or_bits",           [     n])     -> Some (Type_Bits n)
  | ("eor_bits",          [     n])     -> Some (Type_Bits n)
  | ("not_bits",          [     n])     -> Some (Type_Bits n)
  | ("zeros_bits",        [     n])     -> Some (Type_Bits n)
  | ("ones_bits",         [     n])     -> Some (Type_Bits n)
  | ("replicate_bits",    [n; m  ])     -> Some (Type_Bits (Expr_TApply (FIdent ("mul_int", 0), [], [n;m])))
  | ("append_bits",       [n; m  ])     -> Some (Type_Bits (Expr_TApply (FIdent ("add_int", 0), [], [n;m])))
  | ("cvt_int_bits",      [     n])     -> Some (Type_Bits n)
  | ("lsl_bits",          [     n])     -> Some (Type_Bits n)
  | ("lsr_bits",          [     n])     -> Some (Type_Bits n)
  | ("asr_bits",          [     n])     -> Some (Type_Bits n)
  | ("sle_bits",          [     n])     -> Some (Symbolic.type_bool)
  | ("slt_bits",          [     n])     -> Some (Symbolic.type_bool)

  | ("eq_str",            [      ])     -> Some(Symbolic.type_bool)
  | ("ne_str",            [      ])     -> Some(Symbolic.type_bool)
  | ("is_cunpred_exc",    [      ])     -> Some(Symbolic.type_bool)
  | ("is_exctaken_exc",   [      ])     -> Some(Symbolic.type_bool)
  | ("is_impdef_exc",     [      ])     -> Some(Symbolic.type_bool)
  | ("is_see_exc",        [      ])     -> Some(Symbolic.type_bool)
  | ("is_undefined_exc",  [      ])     -> Some(Symbolic.type_bool)
  | ("is_unpred_exc",     [      ])     -> Some(Symbolic.type_bool)
  | ("asl_file_open",     [      ])     -> Some(Value.type_integer)
  | ("asl_file_getc",     [      ])     -> Some(Value.type_integer)
  | ("cvt_bool_bv",       [      ])     -> Some(Type_Bits(Expr_LitInt("1")))
  | ("cvt_bv_bool",       [      ])     -> Some(Symbolic.type_bool)

  | _ -> None

let get_ret_type f targs env =
  match Eval.Env.getFun Unknown env f with
  | (Some ty,_,targs_s,_,_,_) -> 
      let subst = List.fold_right2 Bindings.add targs_s targs Bindings.empty in
      Some (subst_type subst ty)
  | _ -> None

let infer_type (e: expr) vars env =
  match e with
  | Expr_Var (Ident "TRUE")
  | Expr_Var (Ident "FALSE") -> (Some(Type_Constructor(Ident ("boolean"))))
  | Expr_Var v -> Bindings.find_opt v vars
  | Expr_LitInt _ -> (Some(Value.type_integer))
  | Expr_LitBits bv -> (Some(Type_Bits(Expr_LitInt (string_of_int (String.length bv)))))
  | Expr_Slices(x, [Slice_LoWd(l,w)]) -> (Some(Type_Bits(w)))
  | Expr_If(ty, c, t, els, e) -> (Some(ty))
  | Expr_Unknown(ty) -> (Some(ty))
  | Expr_TApply(FIdent("extract_int", 0), _, [_;_;w]) -> (Some(Type_Bits(w)))
  | Expr_TApply(f, targs, args) ->
      (match prim_type f targs with
      | Some t -> Some t 
      | None -> get_ret_type f targs env)
  | _ -> None
