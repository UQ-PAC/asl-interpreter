module AST = Asl_ast

open AST
open Value
open Asl_utils
open Primops

let use_vectoriser = ref false

type sym =
  | Val of value
  | Exp of expr

type 'a sym_pattern =
  | SymPat_LitInt of bitsLit
  | SymPat_LitHex of bitsLit
  | SymPat_LitBits of bitsLit
  | SymPat_LitMask of bitsLit
  | SymPat_Const of ident
  | SymPat_Wildcard
  | SymPat_Tuple of pattern list
  | SymPat_Set of pattern list
  | SymPat_Range of 'a * 'a
  | SymPat_Single of 'a

type 'a sym_expr =
  | SymExpr_If of 'a * 'a * ('a * 'a) list * 'a
  | SymExpr_Binop of 'a * binop * 'a
  | SymExpr_Unop of unop * 'a
  | SymExpr_Field of 'a * ident
  | SymExpr_Fields of 'a * ident list
  | SymExpr_Slices of 'a * ('a * 'a) list
  | SymExpr_In of 'a * 'a sym_pattern
  | SymExpr_Var of ident
  | SymExpr_Parens of 'a
  | SymExpr_Tuple of 'a list
  | SymExpr_Unknown of ty
  | SymExpr_ImpDef of ty * string option
  | SymExpr_TApply of ident * 'a list * 'a list
  | SymExpr_Array of 'a * 'a
  | SymExpr_LitInt of string
  | SymExpr_LitHex of string
  | SymExpr_LitReal of string
  | SymExpr_LitBits of string
  | SymExpr_LitMask of string
  | SymExpr_LitString of string


type sym' =
  | Val' of value
  | Exp' of ty * (sym' sym_expr)

let is_val (x: AST.expr): bool =
    (match x with
    | Expr_LitInt _ -> true
    | Expr_LitBits _ -> true
    | Expr_LitReal _ -> true
    | Expr_LitString _ -> true
    | Expr_Tuple _ -> true
    | x -> false
    )

let rec val_expr (v: Value.value): AST.expr =
  match v with
  | VBool b -> Expr_Var(if b then Ident "TRUE" else Ident "FALSE")
  | VEnum (id, n) -> Expr_LitInt(string_of_int n)
  | VInt n -> Expr_LitInt(Z.to_string n)
  | VReal n -> Expr_LitReal(Q.to_string n)
  | VBits {n; v} -> Expr_LitBits(Z.format ("%0" ^ string_of_int n ^ "b") v)
  | VString s -> Expr_LitString(s)
  | VTuple vs -> Expr_Tuple(List.map val_expr vs)
  | VMask {n; v; m} ->
      let v = Z.format ("%0" ^ string_of_int n ^ "b") v in
      let m = Z.format ("%0" ^ string_of_int n ^ "b") m in
      Expr_LitMask (String.mapi (fun i c -> if String.get m i = '1' then c else 'x') v)
  | _ -> failwith @@ "Casting unhandled value type to expression: " ^ pp_value v

let rec val_initialised (v: value): bool =
  match v with
  | VUninitialized _ -> false
  | VRecord bs -> Bindings.for_all (fun _ -> val_initialised) bs
  | VTuple vs -> List.for_all val_initialised vs
  | VArray (vs, _) -> Primops.ImmutableArray.for_all (fun _ -> val_initialised) vs
  | _ -> true

let rec expr_to_lexpr (e: expr): lexpr =
  match e with
  | Expr_Var x -> LExpr_Var x
  | Expr_Field (e,f) -> LExpr_Field (expr_to_lexpr e, f)
  | Expr_Fields (e,fs) -> LExpr_Fields (expr_to_lexpr e, fs)
  | Expr_Slices (e,ss) -> LExpr_Slices (expr_to_lexpr e, ss)
  | Expr_Tuple es -> LExpr_Tuple (List.map expr_to_lexpr es)
  | Expr_Array (e,i) -> LExpr_Array (expr_to_lexpr e, i)
  | Expr_TApply (FIdent (nm, n), tes, es) when Utils.endswith nm ".read" ->
    (match String.split_on_char '.' nm with
    | [nm'; "read"] -> LExpr_Write (FIdent (nm' ^ ".write", n), tes, es)
    | _ -> raise (EvalError (Unknown, "expr_to_lexpr: cannot derive lexpr for " ^ pp_expr e)))
  | _ -> raise (EvalError (Unknown, "unexpected expression in expr_to_lexpr coercion: " ^ pp_expr e))

let int_of_expr (e: expr): int =
  match e with
  | Expr_LitInt(i) ->    Z.to_int (Z.of_string i)
  | Expr_LitHex(i) ->    Z.to_int (Z.of_string_base 16 (drop_chars i '_'))
  | _ -> failwith @@ "int_of_expr: cannot coerce to int " ^ pp_expr e

let sym_of_int (n: int): sym =
  Val (VInt (Z.of_int n))

let expr_of_int n =
  Expr_LitInt (string_of_int n)

(** Coerces the expression to a symbolic expression, converting
    literal expressions into values. *)
let sym_of_expr (e: expr): sym =
  match e with
  | Expr_LitInt(i) ->    (Val (from_intLit i))
  | Expr_LitHex(i) ->    (Val (from_hexLit i))
  | Expr_LitReal(r) ->   (Val (from_realLit r))
  | Expr_LitBits(b) ->   (Val (from_bitsLit b))
  | Expr_LitMask(b) ->   (Val (from_maskLit b))
  | Expr_LitString(s) -> (Val (from_stringLit s))
  | _ -> Exp e

let rec lexpr_to_expr (loc: l) (x: lexpr): expr =
  (match x with
  | LExpr_Var(id) -> Expr_Var(id)
  | LExpr_Field(l,f) -> Expr_Field(lexpr_to_expr loc l,f)
  | LExpr_Array(l,i) -> Expr_Array(lexpr_to_expr loc l,i)
  | _ -> raise (EvalError (Unknown, "unexpected expression in lexpr_to_expr coercion: " ^ pp_lexpr x)))

let filter_uninit (v: value option): value option =
  match v with
  | Some (VUninitialized _) -> None
  | _ -> v

let sym_value_unsafe (x: sym): value =
  match x with
  | Val v -> v
  | Exp e -> failwith ("sym_value_unsafe: required value but got " ^ pp_expr e)

let sym_expr (x: sym): expr =
  match x with
    | Val v -> val_expr v
    | Exp e -> e

let sym_pair_has_exp (pair: sym * sym): bool =
  match pair with
  | Exp _, _ -> true
  | _, Exp _ -> true
  | _ -> false

let sym_initialised (x: sym): sym option =
  match x with
  | Val v -> if val_initialised v then Some x else None
  | Exp _ -> Some x

(** Constructs a sym of a tuple when given a sym for each element in the tuple.
    Result is a Val iff all components are Val.  *)
let rec sym_tuple (syms: sym list): sym =
  match syms with
  | [] -> Val (VTuple [])
  | Val v::rest ->
    (match sym_tuple rest with
    | Val (VTuple vs) -> Val (VTuple (v::vs))
    | Exp (Expr_Tuple es) -> Exp (Expr_Tuple (val_expr v :: es))
    | _ -> failwith "unreachable: sym_tuple should only return tuple in values or expressions.")
  | Exp e::_ -> Exp (Expr_Tuple (List.map sym_expr syms))

let pp_sym (rs: sym): string =
    match rs with
    | Val v -> Printf.sprintf "Val(%s)" (pp_value v)
    | Exp e -> Printf.sprintf "Exp(%s)" (pp_expr e)

let int_of_sym (e: sym): int =
  match e with
  | Val (VInt n) -> Z.to_int n
  | Exp e        -> int_of_expr e
  | _ -> failwith @@ "int_of_sym: cannot coerce to int " ^ pp_sym e

let sym_of_tuple (loc: AST.l) (v: sym): sym list  =
  match v with
  | Val (VTuple vs) -> (List.map (fun v -> Val v) vs)
  | Exp (Expr_Tuple vs) -> (List.map (fun v -> Exp v) vs)
  | _ -> raise (EvalError (loc, "tuple expected. Got "^ pp_sym v))

let eval_lit (x: sym) =
  match x with
  | Val _ -> x
  | Exp e -> sym_of_expr e

(* Types *)

let type_bool = Type_Constructor(Ident "boolean")
let type_unknown = Type_Constructor(Ident "unknown")

(* Primitives *)

let prim_binop_targs (f: string) (loc: l) (x: sym) (y: sym): value list =
  let fail () = raise (EvalError (loc,
    "cannot infer type arguments for primitive binop: " ^
    f ^ " " ^ pp_sym x ^ ", " ^ pp_sym y))
  in
  match f with
  | "eq_bits" ->
    (match x,y with
    | Val (VBits {n=n; _}), _
    | _, Val (VBits {n=n; _}) -> [VInt (Z.of_int n)]
    | _ -> fail())
  | "in_mask" ->
    (match x,y with
    | Val (VBits {n=n; _}), _
    | _, Val (VMask {n=n; _}) -> [VInt (Z.of_int n)]
    | _ -> fail ())
  | _ -> [] (* assume other binops have no type arguments. *)

(** Apply a primitive operation to two arguments
  *)
let prim_binop (f: string) (loc: AST.l) (x: sym) (y: sym) : sym  =
  let targs = prim_binop_targs f loc x y in
  (match (x,y) with
  | (Val x,Val y) ->
      (match eval_prim f targs [x;y] with
      | Some v -> Val v
      | None -> raise (EvalError (loc, "Unknown primitive operation: "^ f)))
  | (x,y) -> Exp (Expr_TApply(
      FIdent(f,0),
      List.map val_expr targs,
      [sym_expr x; sym_expr y])))

(** Coerces sym to value but DOES NOT return correct uninitialised
    structures with types. *)
let sym_val_or_uninit_unsafe (x: sym): value =
  match x with
  | Val v -> v
  | Exp e -> VUninitialized (Type_OfExpr e)

let expr_prim f tes es =
  Expr_TApply (f, tes, es)

let expr_prim' f = expr_prim (FIdent (f, 0))

let sym_prim (f: ident) (tes: sym list) (es: sym list): sym =
  let tes_vals = List.map sym_val_or_uninit_unsafe tes
  and es_vals = List.map sym_val_or_uninit_unsafe es in
  match eval_prim (name_of_FIdent f) tes_vals es_vals with
  | None -> Exp (expr_prim f (List.map sym_expr tes) (List.map sym_expr es))
  | Some v -> Val (v)

let sym_true     = Val (from_bool true)
let sym_false    = Val (from_bool false)
let expr_true    = Expr_Var (Ident "TRUE")
let expr_false   = Expr_Var (Ident "FALSE")
let sym_zeros n  = Val (VBits (prim_zeros_bits (Z.of_int n)))

let rec sym_eq_int loc x y =
  let x = eval_lit x in
  let y = eval_lit y in
  match x, y with
  | Val x, Val y -> Val (VBool (prim_eq_int (to_integer loc x) (to_integer loc y)))
  (* (x = x) = True *)
  | Exp x, Exp y when x = y -> Val (VBool (true))
  (* (x = x + v) = (v = 0) *)
  | Exp x, Exp (Expr_TApply (FIdent ("add_int", 0), [], [x'; y])) when x = x' ->
      sym_eq_int loc (Exp y) (Val (VInt Z.zero))
  (* TODO: Could benefit from add_int/sub_int reductions by phrasing as x - y = 0 *)
  | _ -> Exp (Expr_TApply (FIdent ("eq_int", 0), [], [sym_expr x; sym_expr y]) )

let sym_le_int   = prim_binop "le_int"

let sym_eq_bits  = prim_binop "eq_bits"

let sym_eq_real  = prim_binop "eq_real"

let sym_eq (loc: AST.l) (x: sym) (y: sym): sym =
  (match (x,y) with
  | (Val x,Val y) -> Val (from_bool (eval_eq loc x y))
  | (Exp _,Val v) | (Val v, Exp _) ->
      (match v with
      | VBits _ -> sym_eq_bits loc x y
      | VInt _
      | VEnum _ -> sym_eq_int loc x y
      | VReal _ -> sym_eq_real loc x y
      | _ -> failwith @@ "sym_eq: unknown value type " ^ (pp_sym x) ^ " " ^ (pp_sym y))
  | (_,_) -> failwith "sym_eq: insufficient info to resolve type")

let rec is_pure_exp (e: expr) =
  match e with
  | Expr_TApply (FIdent (f, 0), targs, args) ->
      (List.mem f prims_pure) && List.for_all (is_pure_exp) targs && List.for_all (is_pure_exp) args
  | Expr_Slices(e, ss) ->
      is_pure_exp e && List.for_all is_pure_slice ss
  | Expr_Var _ -> true
  | Expr_LitInt _ -> true
  | _ -> false

and is_pure_slice (s: slice) =
  match s with
  | Slice_Single i -> is_pure_exp i
  | Slice_HiLo(hi, lo) -> is_pure_exp hi && is_pure_exp lo
  | Slice_LoWd(lo, wd) -> is_pure_exp lo && is_pure_exp wd

let vint_eq cmp = function
  | VInt x when Z.equal cmp x -> true
  | _ -> false

let is_zero = vint_eq Z.zero
let is_one = vint_eq Z.one

(* Hook into add_int calls to enforce (expr + val) form and apply simple identities. *)
let sym_add_int loc (x: sym) (y: sym) =
  let x = eval_lit x in
  let y = eval_lit y in
  match (x, y) with
  | (Val (VInt x), Val (VInt y)) -> Val (VInt (Z.add x y))
  (* Zero Identity *)
  | (Val z, Exp x)
  | (Exp x, Val z) when is_zero z -> Exp x
  (* Chained constant add *)
  | (Exp (Expr_TApply (FIdent ("add_int", 0), _, [x1; Expr_LitInt v])), Val (VInt y)) ->
      let n = Z.of_string v in
      let e = Expr_LitInt (Z.to_string (Z.add n y)) in
      Exp (Expr_TApply (FIdent ("add_int", 0), [], [x1; e]))
  (* Normalise *)
  | (Val _, Exp _) ->
      Exp (Expr_TApply (FIdent ("add_int", 0), [], [sym_expr y; sym_expr x]))
  | _ -> Exp (Expr_TApply (FIdent ("add_int", 0), [], [sym_expr x; sym_expr y]))

let rec find_elim_term loc (e: expr) (f: expr -> sym option) =
  match f e with
  | Some e' -> Some e'
  | None ->
      (match e with
      | Expr_TApply (FIdent ("add_int", 0), _, [x1; x2]) ->
          (match find_elim_term loc x2 f with
           | Some e' -> Some (sym_add_int loc (Exp x1) e')
           | _ -> (match find_elim_term loc x1 f with
                  | Some e' -> Some (sym_add_int loc e' (Exp x2))
                  | _ -> None))
      | _ -> None)

let rec sym_sub_int loc (x: sym) (y: sym) =
  let x = eval_lit x in
  let y = eval_lit y in
  let t = Exp (Expr_TApply (FIdent ("sub_int", 0), [], [sym_expr x; sym_expr y])) in
  match (x,y) with
  | (Val (VInt x), Val (VInt y)) -> Val (VInt (Z.sub x y))
  (* Zero Identity *)
  | (Exp x, Val z) when is_zero z -> Exp x
  (* Breakdown RHS *)
  | (Exp x, Exp (Expr_TApply (FIdent ("add_int", 0), _, [y; z]))) ->
      let x' = sym_sub_int loc (Exp x) (Exp y) in
      let y' = sym_sub_int loc x' (Exp z) in
      y'
  (* Chained constant add *)
  | (Exp (Expr_TApply (FIdent ("add_int", 0), _, [x1; Expr_LitInt v])), Val (VInt y)) ->
      let n = Z.of_string v in
      let e = Expr_LitInt (Z.to_string (Z.sub n y)) in
      Exp (Expr_TApply (FIdent ("add_int", 0), [], [x1; e]))
  (* Elim term *)
  | (Exp x, Exp y) when is_pure_exp y ->
      (match find_elim_term loc x (fun v -> if y = v then Some (Val (VInt Z.zero)) else None) with
      | Some e -> e
      | _ -> t)
  | _ -> t

let rec sym_mul_int (loc: l) (x: sym) (y: sym) =
  match x, y with
  | Val x, Val y -> Val (VInt (prim_mul_int (to_integer loc x) (to_integer loc y)))
  (* x * 1 = x *)
  | Val x, y
  | y, Val x when is_one x -> y
  (* (x + c) * c' = x * c' + c * c' *)
  | Exp (Expr_TApply (FIdent ("add_int", 0), [], [x; Expr_LitInt lit])), Val (VInt c') ->
      let c = Z.of_string lit in
      let offset = Val (VInt (Z.mul c c')) in
      let base = sym_mul_int loc (Exp x) y in
      sym_add_int loc base offset
  | _ -> Exp (Expr_TApply (FIdent ("mul_int", 0), [], [sym_expr x; sym_expr y]))

let sym_zdiv_int (loc: l) (x: sym) (y: sym) =
  match x, y with
  | Val x, Val y -> Val (VInt (prim_zdiv_int (to_integer loc x) (to_integer loc y)))
  (* x / 1 = x *)
  | _, Val (VInt i) when i = Z.one -> x
  | _ -> Exp (Expr_TApply (FIdent ("zdiv_int", 0), [], [sym_expr x; sym_expr y]))

(*** Symbolic Boolean Operations ***)

let sym_not_bool loc (x: sym) =
  match x with
  | Val b -> Val (VBool (not (to_bool loc b)))
  | _ -> Exp (Expr_TApply(FIdent("not_bool",0), [], [sym_expr x]))

let sym_and_bool loc (x: sym) (y: sym) =
  match x, y with
  | Val x, Val y -> Val (VBool (to_bool loc x && to_bool loc y))
  | Val x, _ -> if to_bool loc x then y else sym_false
  | _, Val y -> if to_bool loc y then x else sym_false
  | _ -> Exp (Expr_TApply(FIdent("and_bool",0), [], [sym_expr x;sym_expr y]))

let sym_or_bool loc (x: sym) (y: sym) =
  match x, y with
  | Val x, Val y -> Val (VBool (to_bool loc x || to_bool loc y))
  | Val x, _ -> if to_bool loc x then sym_true else y
  | _, Val y -> if to_bool loc y then sym_true else x
  | _ -> Exp (Expr_TApply(FIdent("or_bool",0), [], [sym_expr x;sym_expr y]))

let sym_ite_bool loc b lhs rhs =
  let nb = sym_not_bool loc b in
  sym_or_bool loc (sym_and_bool loc b lhs) (sym_and_bool loc nb rhs)

let sym_cvt_bool_bv loc (x: sym) =
  match x with
  | Val x -> Val (VBits (prim_cvt_bool_bv (to_bool loc x)))
  | _ -> Exp (Expr_TApply(FIdent("cvt_bool_bv",0), [], [sym_expr x]))

(*** Symbolic Bitvector Operations ***)

let is_zero_bits = function
  | (VBits {n = _; v = v}) -> Z.equal Z.zero v
  | _ -> false

let is_one_bits = function
  | VBits b -> prim_eq_bits (prim_not_bits b) (prim_zeros_bits (Z.of_int b.n))
  | _ -> false

let expr_zeros n =
  Expr_LitBits (String.init n (fun _ -> '0'))

let val_zeros n =
  VBits {n=n; v=Z.zero}

let sym_not_bits loc w (x: sym) =
  match x with
  | Val x -> Val (VBits (prim_not_bits (to_bits loc x)))
  | _ -> Exp (Expr_TApply (FIdent ("not_bits", 0), [w], [sym_expr x]) )

let sym_and_bits loc w (x: sym) (y: sym) =
  match x, y with
  | Val x, Val y -> Val (VBits (prim_and_bits (to_bits loc x) (to_bits loc y)))
  | Val x, y when is_zero_bits x -> Val x
  | x, Val y when is_zero_bits y -> Val y
  | Val x, y when is_one_bits x -> y
  | x, Val y when is_one_bits y -> x
  | _ -> Exp (Expr_TApply (FIdent ("and_bits", 0), [w], [sym_expr x; sym_expr y]) )

let sym_add_bits loc w (x: sym) (y: sym) =
  match x, y with
  | Val x, Val y -> Val (VBits (prim_add_bits (to_bits loc x) (to_bits loc y)))
  | Val x, y when is_zero_bits x -> y
  | x, Val y when is_zero_bits y -> x
  | _ -> Exp (Expr_TApply (FIdent ("add_bits", 0), [w], [sym_expr x; sym_expr y]) )

let sym_inmask loc v mask =
  match v with
  | Val x -> Val (VBool (prim_in_mask (to_bits loc x) mask))
  | Exp e ->
      let n = mask.n in
      let ne = Expr_LitInt (string_of_int n) in
      let m = Val (VBits {v = mask.m; n}) in
      let v = Val (VBits {v = mask.v; n}) in
      sym_eq_bits loc (sym_and_bits loc ne (Exp e) m) v

let rec sym_or_bits loc w (x: sym) (y: sym) =
  match x, y with
  | Val x, Val y -> Val (VBits (prim_or_bits (to_bits loc x) (to_bits loc y)))
  | Val x, y when is_one_bits x -> Val x
  | x, Val y when is_one_bits y -> Val y
  | Val x, y when is_zero_bits x -> y
  | x, Val y when is_zero_bits y -> x
  (* (a /\ b) \/ !a ~> b \/ !a *)
  | Exp (Expr_TApply (FIdent ("and_bits", 0), _, [a; x])), Exp (Expr_TApply (FIdent ("not_bits", 0), _, [a'])) when a = a' ->
      sym_or_bits loc w (sym_of_expr x) y
  | _ -> Exp (Expr_TApply (FIdent ("or_bits", 0), [w], [sym_expr x; sym_expr y]) )

(** Construct a ITE expression from bitvector operations. Expects arguments to be 1 bit wide. *)
let sym_ite_bits loc (b: sym) (x: sym) (y: sym) =
  let w = Expr_LitInt "1" in
  let b = sym_cvt_bool_bv loc b in
  let nb = sym_not_bits loc w b in
  sym_or_bits loc w (sym_and_bits loc w b x) (sym_and_bits loc w nb y)

let int_expr i = Expr_LitInt (string_of_int i)

(** Append two bitvector symbols and explicitly provide their widths *)
let rec sym_append_bits (loc: l) (xw: int) (yw: int) (x: sym) (y: sym): sym =
  (match (x,y) with
  | (Val (VBits {n=0; _}), y) -> y
  | (x, Val (VBits {n=0; _})) -> x
  | (Val (VBits x),Val (VBits y)) -> Val (VBits (prim_append_bits x y))

  (* special case: if y is already an append operation, fuse x into its y's left argument. *)
  | (Val (VBits v), Exp (Expr_TApply (FIdent ("append_bits", 0),
      [Expr_LitInt lw; rw], [Expr_LitBits l;r]))) ->

    let l = (to_bits Unknown (from_bitsLit l)) in
    let l' = val_expr (VBits (prim_append_bits v l)) in
    Exp (expr_prim' "append_bits"
      [expr_of_int (xw + int_of_string lw); rw]
      [l'; r])

  (* Match append of top-bit replicate expressions, turn into sign extend *)
  | (Exp (Expr_TApply (FIdent ("replicate_bits", 0), [Expr_LitInt "1"; w], [e;_])), Exp r) when sym_slice loc (Exp r) (yw - 1) 1 = Exp e ->
      Exp (Expr_TApply (FIdent ("SignExtend", 0), [int_expr yw;int_expr (xw+yw)], [r; int_expr (xw + yw)]))

  | (x,y) ->
    Exp (expr_prim' "append_bits" [expr_of_int xw; expr_of_int yw] [sym_expr x;sym_expr y])
  )

and sym_replicate (xw: int) (x: sym) (n: int): sym =
  match n with
  | _ when n < 0 -> failwith @@ "sym_replicate: negative replicate count"
  | 0 -> Val (from_bitsLit "")
  | 1 -> x
  | _ ->
    match x with
    | Val (VBits b) -> Val (VBits (prim_replicate_bits b (Z.of_int n)))
    | Val _ -> failwith @@ "sym_replicate: invalid replicate value " ^ pp_sym x
    | Exp e -> Exp (
      Expr_TApply (
        FIdent ("replicate_bits", 0),
        [expr_of_int xw; expr_of_int n],
        [e; expr_of_int n]))

(** Extract a slice from a symbolic bitvector given known bounds.
    Applies optimisations to collapse consecutive slice operations and
    distributes slices across bitvector append operations.
  *)
and sym_slice (loc: l) (x: sym) (lo: int) (wd: int): sym =
  let x = eval_lit x in
  match x with
  | Val v -> Val (extract_bits'' loc v (VInt (Z.of_int lo)) (VInt (Z.of_int wd)))
  | Exp e ->
    if wd = 0 then Val (VBits empty_bits) else
    let slice_expr =
      (Expr_Slices (e, [Slice_LoWd (int_expr lo, int_expr wd)])) in
    (match e with

    (* Combine nested slices *)
    | (Expr_Slices (e', [Slice_LoWd (Expr_LitInt l',_)])) ->
        let l2 = int_of_string l' in
        sym_slice loc (sym_of_expr e') (l2 + lo) wd
    | (Expr_Slices (e', [Slice_LoWd (lo',wd')])) when lo = 0 ->
        Exp (Expr_Slices (e', [Slice_LoWd (lo', int_expr wd)]))

    (* Match slice of a single bit replication, turn into shorter replication *)
    | (Expr_TApply (FIdent ("replicate_bits", 0), [Expr_LitInt "1"; Expr_LitInt t2], [x;_])) ->
        Exp (Expr_TApply (FIdent ("replicate_bits", 0), [Expr_LitInt "1"; int_expr wd], [x; int_expr wd]))

    | (Expr_TApply (FIdent ("ZeroExtend" as ext_type, 0), [Expr_LitInt t1; Expr_LitInt t2], [x;_])) ->
      (* only handle ZeroExtend cases to avoid introducing replicate_bits expressions. *)
      let t1 = int_of_string t1 in (* old width *)
      let t2 = int_of_string t2 in (* extended width *)
      let ext_wd = (t2 - t1) in (* width of extend bits *)
      let ext_bit =
        match ext_type with
        | "ZeroExtend" -> Val (from_bitsLit "0")
        | "SignExtend" -> sym_slice loc (sym_of_expr x) (t1-1) 1
        | _ -> assert false
      in
      let ext = sym_replicate 1 ext_bit ext_wd in
      sym_slice loc
        (sym_append_bits loc ext_wd t1 ext (sym_of_expr x))
        lo wd

    | (Expr_TApply (FIdent ("or_bits", 0), [w], [x1; x2])) ->
        sym_or_bits loc (int_expr wd)
          (sym_slice loc (Exp x1) lo wd)
          (sym_slice loc (Exp x2) lo wd)

    | (Expr_TApply (FIdent ("and_bits", 0), [w], [x1; x2])) ->
        sym_and_bits loc (int_expr wd)
          (sym_slice loc (Exp x1) lo wd)
          (sym_slice loc (Exp x2) lo wd)

    (* (x + y)[wd +: 0] = (x[wd +: 0] + y[wd +: 0]) *)
    | (Expr_TApply (FIdent ("add_int", 0), [], [x1; x2])) when lo = 0 ->
        sym_add_bits loc (int_expr wd)
          (sym_slice loc (Exp x1) lo wd)
          (sym_slice loc (Exp x2) lo wd)

    (* UInt{wd}(x)[wd +: 0] = x[wd +: 0] *)
    | (Expr_TApply (FIdent ("cvt_bits_uint", 0), [Expr_LitInt w'], [x1])) when lo = 0 && int_of_string w' = wd ->
        Exp x1

    | (Expr_TApply (FIdent ("append_bits", 0), [Expr_LitInt t1; Expr_LitInt t2], [x1; x2])) ->
      let t2 = int_of_string t2 in
      if t2 < 0 then
        (* don't statically know the widths of append, don't optimise *)
        Exp slice_expr
      else if (lo >= t2) then
        (* slice is entirely within upper part (i.e. significant bits). *)
        sym_slice loc (sym_of_expr x1) (lo - t2) wd
      else if (lo + wd <= t2) then
        (* entirely within lower part. *)
        sym_slice loc (sym_of_expr x2) lo wd
      else
        (* getting bits from both *)
        let w2 = t2 - lo in
        let w1 = wd - w2 in
        let x2' = sym_slice loc (sym_of_expr x2) lo w2 in
        let x1' = sym_slice loc (sym_of_expr x1) 0 w1 in
        sym_append_bits loc  w1 w2 x1' x2'
    | _ -> Exp slice_expr)

(** Wrapper around sym_slice to handle cases of symbolic slice bounds *)
let sym_extract_bits loc v i w =
  match (v, i, w) with
  (* Constant slice *)
  | _, Val i', Val w' ->
      let i' = to_int loc i' in
      let w' = to_int loc w' in
      sym_slice loc v i' w'
  (* Nested slice *)
  | Exp (Expr_Slices (e, [Slice_LoWd (lo,wd)])), lo', wd' ->
      let lo = sym_add_int loc (Exp lo) lo' in
      Exp (Expr_Slices (e, [Slice_LoWd (sym_expr lo, sym_expr wd')]))
  | _ -> Exp (Expr_Slices (sym_expr v, [Slice_LoWd (sym_expr i, sym_expr w)]))

let sym_zero_extend num_zeros old_width e =
  match sym_append_bits Unknown num_zeros old_width (Val (val_zeros num_zeros)) e with
  | Val v -> Val v
  | Exp _ ->
      let n' = expr_of_int (num_zeros + old_width) in
      Exp (expr_prim' "ZeroExtend" [expr_of_int old_width; n'] [sym_expr e; n'])

let sym_sign_extend num_zeros old_width (e: sym): sym =
  match e with
  | Exp (Expr_TApply (FIdent ("ZeroExtend",0), [Expr_LitInt oldsize; Expr_LitInt newsize], [x; _])) ->
    let size' = string_of_int (num_zeros + int_of_string newsize) in
    Exp (Expr_TApply (FIdent ("ZeroExtend",0), [Expr_LitInt oldsize; Expr_LitInt size'], [x; Expr_LitInt size']))
  | _ ->
    let sign = sym_slice Unknown e (old_width-1) 1 in
    let rep = sym_replicate 1 sign num_zeros in
    match sym_append_bits Unknown num_zeros old_width rep e with
    | Val v -> Val v
    | Exp _ ->
      let n' = expr_of_int (num_zeros + old_width) in
      Exp (expr_prim' "SignExtend" [expr_of_int old_width; n'] [sym_expr e; n'])

(** Shift a bitvector x of width w to the left by y bits *)
let sym_lsl_bits loc w x y =
  match x, y with
  | _, Val (VInt y) ->
      let diff = w - (Z.to_int y) in
      let slice = sym_slice loc x (Z.to_int y) diff in
      let zeros = Val (VBits (prim_zeros_bits y)) in
      let res = sym_append_bits loc diff (Z.to_int y) slice zeros in
      res
  | _ ->
      sym_prim (FIdent ("LSL", 0)) [sym_of_int w] [x;y]

(** Overwrite bits from position lo up to (lo+wd) exclusive of old with the value v.
    Needs to know the widths of both old and v to perform the operation.
    Assumes width of v is equal to wd.
  *)
let sym_insert_bits loc (old_width: int) (old: sym) (lo: sym) (wd: sym) (v: sym): sym =
  match (old, lo, wd, v) with
  | (Val old', Val i', Val w', Val v') -> Val (insert_bits loc old' i' w' v')
  | (_, Val lo', Val wd', _) ->
      let lo = to_int loc lo' in
      let wd = to_int loc wd' in
      let up = lo + wd in
      if old_width <= up then
        (* Overwriting the top bits of old *)
        sym_append_bits loc wd lo v (sym_slice loc old 0 lo)
      else
        sym_append_bits loc (old_width - up) up (sym_slice loc old up (old_width - up))
          (sym_append_bits loc wd lo v (sym_slice loc old 0 lo))
  | (_, _, Val wd', _) when Primops.prim_zrem_int (Z.of_int old_width) (to_integer Unknown wd') = Z.zero && !use_vectoriser ->
      (* Elem.set *)
      let pos = sym_zdiv_int loc lo wd in
      Exp ( Expr_TApply (FIdent("Elem.set", 0), [expr_of_int old_width ; sym_expr wd],
          List.map sym_expr [old ; pos ; wd ; v]) )
  | (_, Val (VInt l), _, _) when l = Z.zero && !use_vectoriser ->
      Exp (Expr_TApply (FIdent ("Elem.set", 0), [expr_of_int old_width ; sym_expr wd],
          List.map sym_expr [old ; lo ; wd ; v]))

  | (_, _, Val wd', _) ->
      (* Build an insert out of bitvector masking operations *)
      let wd = to_int loc wd' in
      let we = expr_of_int old_width in
      let ones = Val (VBits (mkBits old_width (Z.pred (Z.pow (Z.succ (Z.one)) wd)))) in
      let mask = sym_not_bits loc we (sym_lsl_bits loc old_width ones lo) in
      let inject = sym_lsl_bits loc old_width (sym_zero_extend (old_width - wd) wd v) lo in
      sym_or_bits loc we (sym_and_bits loc we old mask) inject
  | _ ->
      failwith "sym_insert_bits: Width of inserted bitvector is unknown"

let sym_concat (loc: AST.l) (xs: (int * sym) list): sym =
  let body = fun (w,x) (yw,y) -> let b = sym_append_bits loc w yw x y in (w + yw,b) in
  match xs with
  | [] -> Val (VBits empty_bits)
  | x::xs -> let (_,r) = List.fold_left body x xs in r

(* Identify the bits in an expression that might be 1.
   Represent these as a bitvector with 1s in their position, of width w. *)
let rec maybe_set (w: Z.t) (e: expr): bitvector =
  let r = (match e with
  | Expr_LitBits v ->
      let x' = drop_chars v ' ' in
      mkBits (String.length x') (Z.of_string_base 2 x')
  | Expr_TApply (FIdent ("and_bits", 0), _, [x1; x2]) ->
      prim_and_bits (maybe_set w x1) (maybe_set w x2)
  | Expr_TApply (FIdent ("or_bits", 0), _, [x1; x2]) ->
      prim_or_bits (maybe_set w x1) (maybe_set w x2)
  | Expr_TApply (FIdent ("ZeroExtend", 0), [Expr_LitInt w;_], [x1; Expr_LitInt n]) ->
      let n = Z.of_string n in
      let w = Z.of_string w in
      prim_append_bits (prim_zeros_bits n) (maybe_set w x1)
  | Expr_Slices (v, [Slice_LoWd (Expr_LitInt l, Expr_LitInt w)]) ->
      let l = Z.of_string l in
      let w = Z.of_string w in
      prim_extract (maybe_set (Z.add l w) v) l w
  | Expr_TApply (FIdent ("append_bits", 0), [Expr_LitInt l1;Expr_LitInt l2], [x1; x2]) ->
      let l1 = Z.of_string l1 in
      let l2 = Z.of_string l2 in
      prim_append_bits (maybe_set l1 x1) (maybe_set l2 x2)
  | _ -> prim_ones_bits w) in
  prim_extract r Z.zero w

(* Identify whether the bitvector is a trivial mask, consisting of one continuous run of 1s *)
let is_insert_mask (b: bitvector): (int * int) option =
  let x = Z.format ("%0" ^ string_of_int b.n ^ "b") b.v in
  let f1 = String.index_opt x '1' in
  let l1 = String.rindex_opt x '1' in
  match f1, l1 with
  | Some f1, Some l1 ->
      let w = l1 - f1 + 1 in
      let l = String.length x - l1 - 1 in
      let m = String.sub x f1 w in
      if String.contains m '0' then None
      else begin
        Some (l, w)
      end
  | _ -> None

let sym_prim_simplify (name: string) (tes: sym list) (es: sym list): sym option =
  let loc = Unknown in

  (* Utility to overwrite outer[wd:lo] with inner[wd:lo] *)
  let insert w outer lo wd inner =
    let mid = sym_slice loc inner lo wd in
    sym_insert_bits loc (Z.to_int w) outer (sym_of_int lo) (sym_of_int wd) mid in

  (match (name, tes, es) with
  | ("add_int",  [ ], [x1; x2]) -> Some (sym_add_int loc x1 x2)
  | ("sub_int",  [ ], [x1; x2]) -> Some (sym_sub_int loc x1 x2)
  | ("mul_int",  [ ], [x1; x2]) -> Some (sym_mul_int loc x1 x2)
  | ("eq_int",   [ ], [x1; x2]) -> Some (sym_eq_int loc x1 x2)
  | ("add_bits", [w], [x1; x2]) -> Some (sym_add_bits loc (sym_expr w) x1 x2)

  | ("append_bits", [Val t1; _],      [_; x2])            when is_zero t1 -> Some x2
  | ("append_bits", [_; Val t2],      [x1; _])            when is_zero t2 -> Some x1

  | ("LSL",         _,                [x1; Val x2])       when is_zero x2 -> Some x1
  | ("LSL",         [Val (VInt w)],   [x1; Val (VInt s)]) ->
      let si = Z.to_int s in
      let u = Z.to_int w - si in
      let z = Val (VBits (prim_zeros_bits s)) in
      let upper = sym_slice loc x1 0 u in
      Some (sym_append_bits loc u si upper z)

  | ("LSR",         _,                [x1; Val x2])       when is_zero x2 -> Some x1
  | ("LSR",         [Val (VInt w)],   [x1; Val (VInt s)]) ->
      let si = Z.to_int s in
      let u = Z.to_int w - si in
      let z = Val (VBits (prim_zeros_bits s)) in
      let lower = sym_slice loc x1 si u in
      Some (sym_append_bits loc si u z lower)

  | ("ZeroExtend",  [Val (VInt v1); Val (VInt v2)], [x1;_]) when Z.equal v1 v2 -> Some x1

  | ("eq_enum",     _,                [x; Val (VBool true)])
  | ("eq_enum",     _,                [Val (VBool true); x]) -> Some x
  | ("eq_enum",     _,                [x; Val (VBool false)])
  | ("eq_enum",     _,                [Val (VBool false); x]) -> Some (sym_not_bool loc x)

  | ("or_bits",     _,                [Val x1; x2])       when is_zero_bits x1 -> Some x2
  | ("or_bits",     _,                [x1; Val x2])       when is_zero_bits x2 -> Some x1
  | ("or_bits",     _,                [Val x1; x2])       when is_one_bits x1 -> Some (Val x1)
  | ("or_bits",     _,                [x1; Val x2])       when is_one_bits x2 -> Some (Val x2)
  | ("or_bits",     [Val (VInt n)],   [x1; x2]) ->
      (* Identify whether the arguments are disjoint in terms of their maybe set bits *)
      let m1 = maybe_set n (sym_expr x1) in
      let m2 = maybe_set n (sym_expr x2) in
      let r = prim_and_bits m1 m2 in
      if Z.equal Z.zero r.v then
        (* If so, attempt to extract a trivial insert mask *)
        (match is_insert_mask m1, is_insert_mask m2 with
        | Some (l,w), _ -> Some (insert n x2 l w x1)
        | _, Some (l,w) -> Some (insert n x1 l w x2)
        | _ -> None)
      else None

  | ("and_bits",     _,               [Val x1; x2])       when is_zero_bits x1 -> Some (Val x1)
  | ("and_bits",     _,               [x1; Val x2])       when is_zero_bits x2 -> Some (Val x2)
  | ("and_bits",     _,               [Val v; x])         when is_one_bits v -> Some x
  | ("and_bits",     _,               [x; Val v])         when is_one_bits v -> Some x
  | ("and_bits",    [Val (VInt n)],   [Val (VBits m); x])
  | ("and_bits",    [Val (VInt n)],   [x; Val (VBits m)]) ->
      let z = Val (VBits (prim_zeros_bits n)) in
      (* Check if the and operation is a trivial mask *)
      (match is_insert_mask m, is_insert_mask (prim_not_bits m) with
      | Some (l,w), _ -> Some (insert n z l w x)
      | _, Some (l,w) -> Some (insert n x l w z)
      | _ -> None)

  | _ -> None)

let rec val_type (v: value): ty =
  let unsupported () = failwith @@ "val_type unsupported: " ^ pp_value v in
  match v with
  | VBool _ -> type_builtin "boolean"
  | VEnum (ident, _) -> Type_Constructor ident
  | VInt _ -> type_builtin "integer"
  | VReal _ -> type_builtin "real"
  | VBits {n=n; _} -> type_bits (string_of_int n)
  | VMask mask -> unsupported ()
  | VString _ -> type_builtin "string"
  | VExc _ -> type_builtin "__Exception"
  | VTuple vs -> Type_Tuple (List.map val_type vs)
  | VRecord (_) -> unsupported ()
  | VArray (arr, def) -> unsupported ()
  | VRAM _ -> type_builtin "__RAM"
  | VUninitialized ty -> ty

let sym_type =
  function
  | Val v -> val_type v
  | Exp e -> Type_OfExpr e (* FIXME: add type annotation to sym Exp constructor. *)

let stmt_loc (s: stmt): l =
  match s with
  | Stmt_VarDeclsNoInit (_, _, l) -> l
  | Stmt_VarDecl (_, _, _, l) -> l
  | Stmt_ConstDecl (_, _, _, l) -> l
  | Stmt_Assign (_, _, l) -> l
  | Stmt_FunReturn (_, l) -> l
  | Stmt_ProcReturn (l) -> l
  | Stmt_Assert (_, l) -> l
  | Stmt_Unpred (l) -> l
  | Stmt_ConstrainedUnpred (l) -> l
  | Stmt_ImpDef (_, l) -> l
  | Stmt_Undefined (l) -> l
  | Stmt_ExceptionTaken (l) -> l
  | Stmt_Dep_Unpred (l) -> l
  | Stmt_Dep_ImpDef (_, l) -> l
  | Stmt_Dep_Undefined (l) -> l
  | Stmt_See (_, l) -> l
  | Stmt_Throw (_, l) -> l
  | Stmt_DecodeExecute (_, _, l) -> l
  | Stmt_TCall (_, _, _, l) -> l
  | Stmt_If (_, _, _, _, l) -> l
  | Stmt_Case (_, _, _, l) -> l
  | Stmt_For (_, _, _, _, _, l) -> l
  | Stmt_While (_, _, l) -> l
  | Stmt_Repeat (_, _, l) -> l
  | Stmt_Try (_, _, _, _, l) -> l

(** Structure to represent a chain of reference expressions *)

type access_chain =
  | Field of ident
  | Index of value
  | SymIndex of expr

let pp_access_chain =
  function
  | Field id -> "Field " ^ pprint_ident id
  | Index v -> "Index " ^ pp_value v
  | SymIndex e -> "SymIndex " ^ pp_expr e

let pp_access_chain_list = Utils.pp_list pp_access_chain

(* note: for all access_chain lists below, they are ordered with the first
   elements being the inner-most accessor.

   for example:
   a[0][1][2] --> [Index 0; Index 1; Index 2]
   *)

(** "get_access_chain loc v a" returns the reference defined by "a"
    inside the structure "v".  *)
let rec get_access_chain (loc: l) (v: value) (a: access_chain list) : value =
  (match a with
  | (Field f)::a -> (get_access_chain loc (get_field loc v f) a)
  | (Index i)::a -> (get_access_chain loc (get_array loc v i) a)
  | (SymIndex e)::a ->
      assert (a = []);
      (match v with
      | VArray (x, d) -> assert (ImmutableArray.cardinal x = 0); d
      | _ -> failwith "unreachable")
  | [] -> v)

(** "set_access_chain loc v a r" sets the reference defined by "a"
    in the structure "v" to be "r". *)
let rec set_access_chain (loc: l) (v: value) (a: access_chain list) (r: value): value =
  (match a with
  | (Field f)::a -> set_field loc v f (set_access_chain loc (get_field loc v f) a r)
  | (Index i)::a -> set_array loc v i (set_access_chain loc (get_array loc v i) a r)
  | (SymIndex e)::a ->
      assert (a = []);
      (match v with
      | VArray (x, d) -> assert (ImmutableArray.cardinal x = 0); VArray(x, d)
      | _ -> failwith "unreachable")
  | [] -> r)

(** Returns an lexpr for accessing the given reference within the given lexpr. *)
let rec lexpr_access_chain (x: lexpr) (a: access_chain list): lexpr =
  (match a with
  | (Field f)::a -> lexpr_access_chain (LExpr_Field(x,f)) a
  | (Index i)::a -> lexpr_access_chain (LExpr_Array(x,val_expr i)) a
  | (SymIndex e)::a -> lexpr_access_chain (LExpr_Array(x,e)) a
  | [] -> x)

(** Returns an expr for accessing the given reference within the given expr. *)
let rec expr_access_chain (x: expr) (a: access_chain list): expr =
  (match a with
  | (Field f)::a -> expr_access_chain (Expr_Field(x,f)) a
  | (Index i)::a -> expr_access_chain (Expr_Array(x,val_expr i)) a
  | (SymIndex e)::a -> expr_access_chain (Expr_Array(x,e)) a
  | [] -> x)

(****************************************************************)
(** {2 Function and Expression Purity}                          *)
(****************************************************************)

(** Primitives that can be evaluated, reordered, duplicated and eliminated.
    Semantically, should have no influence on the evaluation trace. *)
let prims_pure () =
  (List.map (fun f -> FIdent(f,0)) Value.prims_pure) @
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
    FIdent("add_bits",0);
    FIdent("and_bits",0);
    FIdent("eor_bits",0);
    FIdent("eq_bits",0);
    FIdent("ne_bits",0);
    FIdent("mul_bits",0);
    FIdent("not_bits",0);
    FIdent("or_bits",0);
    FIdent("sub_bits",0);
    FIdent("replicate_bits",0);
    FIdent("append_bits",0);
    FIdent("not_bool",0);
    FIdent("and_bool",0);
    FIdent("or_bool",0);
    FIdent("cvt_bool_bv",0);
    FIdent("cvt_bits_uint",0);
    FIdent("cvt_int_bits",0);
    FIdent("select_vec",0);
    FIdent("eq_vec",0);
    FIdent("add_vec",0);
    FIdent("sub_vec",0);
    FIdent("asr_vec",0);
    FIdent("trunc_vec",0);
    FIdent("zcast_vec",0);
    FIdent("shuffle_vec",0);
    FIdent("scast_vec",0);
  ] @ (if !use_vectoriser then [
    FIdent("Elem.set",0);
    FIdent("Elem.read",0);
  ] else [])

(** Primitives that are placed into the evaluation trace. They must be
    preserved in the output, retaining their ordering with respect to each other
    and any accesses to global state. *)
let prims_impure () =
  (List.map (fun f -> FIdent(f,0)) Value.prims_impure) @
  [
    FIdent("FPConvert",0);
    FIdent("FPRoundInt",0);
    FIdent("FPRoundIntN",0);
    FIdent("FPToFixed",0);
    FIdent("FixedToFP",0);
    FIdent("FPCompare",0);
    FIdent("FPCompareEQ",0);
    FIdent("FPCompareGE",0);
    FIdent("FPCompareGT",0);
    FIdent("FPToFixedJS_impl",0);
    FIdent("FPSqrt",0);
    FIdent("FPAdd",0);
    FIdent("FPMul",0);
    FIdent("FPDiv",0);
    FIdent("FPMulAdd",0);
    FIdent("FPMulAddH",0);
    FIdent("FPMulX",0);
    FIdent("FPMax",0);
    FIdent("FPMin",0);
    FIdent("FPMaxNum",0);
    FIdent("FPMinNum",0);
    FIdent("FPSub",0);
    FIdent("FPRecpX",0);
    FIdent("FPRecipStepFused",0);
    FIdent("FPRSqrtStepFused",0);
    FIdent("FPRoundBase",0);
    FIdent("FPConvertBF",0);
    FIdent("BFRound",0);
    FIdent("BFAdd",0);
    FIdent("BFMul",0);
    FIdent("FPRecipEstimate",0);
    FIdent("Mem.read",0);
    FIdent("Mem.set",0);
    FIdent("AtomicStart",0);
    FIdent("AtomicEnd",0);
    FIdent("AArch64.MemTag.read",0);
    FIdent("AArch64.MemTag.set",0);
    FIdent("SetTagCheckedInstruction",0);
    FIdent("SpeculativeStoreBypassBarrierToPA",0);
    FIdent("SpeculationBarrier",0);
    FIdent("SpeculativeStoreBypassBarrierToVA",0);
  ]

(** Test if an expression is only over constants, variables and pure operations. Does not
    determine whether a variable access can be considered pure. *)
let rec is_pure e =
  match e with
  | Expr_Var _ -> true
  | Expr_LitBits _ -> true
  | Expr_LitInt _ -> true
  | Expr_Slices(e, [Slice_LoWd(lo, wd)]) ->
      is_pure e && is_pure lo && is_pure wd
  | Expr_TApply(f, tes, es) ->
      List.mem f (prims_pure ()) &&
      List.for_all is_pure tes &&
      List.for_all is_pure es
  | Expr_Field(e,_) -> is_pure e
  | Expr_Array(e,i) -> is_pure e && is_pure i
  | _ -> false
