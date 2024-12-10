open Asl_utils

open AST
open Visitor
open Asl_visitor
open Symbolic
open Value

(* TODO: Central definition of prims in result + sanity test pass *)
let pure_prims =
  (List.map (fun f -> FIdent(f,0)) Value.prims_pure) @
  [
    FIdent("SignExtend",0);
    FIdent("ZeroExtend",0);
    FIdent("asr_bits",0);
    FIdent("lsr_bits",0);
    FIdent("lsl_bits",0);
    FIdent("slt_bits",0);
    FIdent("sle_bits",0);
  ]

let infer_type (e: expr): ty option =
  match e with
  | Expr_LitBits bv -> (Some(Type_Bits(Expr_LitInt (string_of_int (String.length bv)))))
  | Expr_Slices(x, [Slice_LoWd(l,w)]) -> Some(Type_Bits(w))
  | Expr_TApply((FIdent(name, _) | Ident(name)), [], _) -> begin
    match name with
    | "eq_enum"            -> Some(type_bool)
    | "ne_enum"            -> Some(type_bool)
    | "eq_bool"            -> Some(type_bool)
    | "ne_bool"            -> Some(type_bool)
    | "and_bool"           -> Some(type_bool)
    | "or_bool"            -> Some(type_bool)
    | "equiv_bool"         -> Some(type_bool)
    | "not_bool"           -> Some(type_bool)
    | "eq_int"             -> Some(type_bool)
    | "ne_int"             -> Some(type_bool)
    | "le_int"             -> Some(type_bool)
    | "lt_int"             -> Some(type_bool)
    | "ge_int"             -> Some(type_bool)
    | "gt_int"             -> Some(type_bool)
    | "is_pow2_int"        -> Some(type_bool)
    | "neg_int"            -> Some(type_integer)
    | "add_int"            -> Some(type_integer)
    | "sub_int"            -> Some(type_integer)
    | "shl_int"            -> Some(type_integer)
    | "shr_int"            -> Some(type_integer)
    | "mul_int"            -> Some(type_integer)
    | "zdiv_int"           -> Some(type_integer)
    | "zrem_int"           -> Some(type_integer)
    | "fdiv_int"           -> Some(type_integer)
    | "frem_int"           -> Some(type_integer)
    | "mod_pow2_int"       -> Some(type_integer)
    | "align_int"          -> Some(type_integer)
    | "pow2_int"           -> Some(type_integer)
    | "pow_int_int"        -> Some(type_integer)
    | "eq_real"            -> Some(type_bool)
    | "ne_real"            -> Some(type_bool)
    | "le_real"            -> Some(type_bool)
    | "lt_real"            -> Some(type_bool)
    | "ge_real"            -> Some(type_bool)
    | "round_tozero_real"  -> Some(type_integer)
    | "round_down_real"    -> Some(type_integer)
    | "round_up_real"      -> Some(type_integer)
    | "in_mask"            -> Some(type_bool)
    | "notin_mask"         -> Some(type_bool)
    | "eq_str"             -> Some(type_bool)
    | "ne_str"             -> Some(type_bool)
    | "is_cunpred_exc"     -> Some(type_bool)
    | "is_exctaken_exc"    -> Some(type_bool)
    | "is_impdef_exc"      -> Some(type_bool)
    | "is_see_exc"         -> Some(type_bool)
    | "is_undefined_exc"   -> Some(type_bool)
    | "is_unpred_exc"      -> Some(type_bool)
    | "asl_file_open"      -> Some(type_integer)
    | "asl_file_getc"      -> Some(type_integer)
    | "cvt_bool_bv"        -> Some(Type_Bits(Expr_LitInt("1")))
    | "cvt_bv_bool"        -> Some(type_bool)
    | _ -> None
    end
  | Expr_TApply((FIdent(name, _) | Ident(name)), [Expr_LitInt(_) as num], _) -> begin
    match name with
    | "ram_read"           -> Some(Type_Bits(num))
    | "add_bits"           -> Some(Type_Bits(num))
    | "sub_bits"           -> Some(Type_Bits(num))
    | "mul_bits"           -> Some(Type_Bits(num))
    | "sdiv_bits"          -> Some(Type_Bits(num))
    | "and_bits"           -> Some(Type_Bits(num))
    | "or_bits"            -> Some(Type_Bits(num))
    | "eor_bits"           -> Some(Type_Bits(num))
    | "not_bits"           -> Some(Type_Bits(num))
    | "zeros_bits"         -> Some(Type_Bits(num))
    | "ones_bits"          -> Some(Type_Bits(num))
    | "replicate_bits"     -> Some(Type_Bits(num))
    | "append_bits"        -> Some(Type_Bits(num))
    | "cvt_int_bits"       -> Some(Type_Bits(num))
    | "LSL"                -> Some(Type_Bits(num))
    | "LSR"                -> Some(Type_Bits(num))
    | "ASR"                -> Some(Type_Bits(num))
    | "cvt_bits_uint"      -> Some(type_integer)
    | "cvt_bits_sint"      -> Some(type_integer)
    | "eq_bits"            -> Some(type_bool)
    | "ne_bits"            -> Some(type_bool)
    | "sle_bits"           -> Some(type_bool)
    | "slt_bits"           -> Some(type_bool)
    | _ -> None
    end
  | Expr_TApply((FIdent(name, _) | Ident(name)), [Expr_LitInt(v1) as num1; Expr_LitInt(v2) as num2], _) -> begin
    (* These are... dubious. None appear in value.ml, so they're all based on what "looks correct". *)
    match name with
    | "ZeroExtend"         -> Some(Type_Bits(num2))
    | "SignExtend"         -> Some(Type_Bits(num2))
    | "lsl_bits"           -> Some(Type_Bits(num1))
    | "lsr_bits"           -> Some(Type_Bits(num1))
    | "asl_bits"           -> Some(Type_Bits(num1))
    | "asr_bits"           -> Some(Type_Bits(num1))
    | "append_bits"        ->
      Some(Type_Bits(Expr_LitInt(string_of_int((int_of_string v1) + (int_of_string v2)))))
    | _ -> None
    end
  | _ -> None

(** Remove variables which are unused at the end of the statement list. *)
module RemoveUnused = struct
  let rec is_false = function
    | Expr_Var (Ident "FALSE") -> true
    | Expr_TApply (FIdent ("or_bool", 0), [], [a;b]) -> is_false a && is_false b
    | Expr_TApply (FIdent ("and_bool", 0), [], [a;b]) -> is_false a || is_false b
    | _ -> false

  let rec is_true = function
    | Expr_Var (Ident "TRUE") -> true
    | Expr_TApply (FIdent ("and_bool", 0), [], [a;b]) -> is_true a && is_true b
    | Expr_TApply (FIdent ("or_bool", 0), [], [a;b]) -> is_true a || is_true b
    | _ -> false

  let rec remove_unused (globals: IdentSet.t) xs = fst (remove_unused' globals IdentSet.empty xs)

  and remove_unused' globals (used: IdentSet.t) (xs: stmt list): (stmt list * IdentSet.t) =
    List.fold_right (fun stmt (acc, used) ->

      let pass = (acc, used)
      and emit (s: stmt) = (s::acc, IdentSet.union used (fv_stmt s))
      and halt (s: stmt) = ([stmt], IdentSet.empty)
      in

      match stmt with
      | Stmt_VarDeclsNoInit(ty, vs, loc) ->
        let vs' = List.filter (fun i -> IdentSet.mem i used) vs in
        (match vs' with
        | [] -> pass
        | _ -> emit (Stmt_VarDeclsNoInit(ty, vs', loc)))
      | Stmt_VarDecl(ty, v, i, loc) ->
        if IdentSet.mem v used
          then emit stmt
          else pass
      | Stmt_ConstDecl(ty, v, i, loc) ->
        if IdentSet.mem v used
          then emit stmt
          else pass
      | Stmt_Assign(le, r, loc) ->
        let lvs = assigned_vars_of_stmts [stmt] in
        if not (IdentSet.disjoint lvs used) || not (IdentSet.disjoint lvs globals)
          then emit stmt
          else pass

      (* Skip if structure if possible - often seen in decode tests *)
      | Stmt_If(c, tstmts, elsif, fstmts, loc) when is_true c ->
          let (tstmts',tused) = remove_unused' globals used tstmts in
          (tstmts'@acc,tused)

      | Stmt_If(c, tstmts, [], fstmts, loc) when is_false c ->
          let (fstmts',tused) = remove_unused' globals used fstmts in
          (fstmts'@acc,tused)

      | Stmt_If(c, tstmts, elsif, fstmts, loc) ->
        let (tstmts',tused) = remove_unused' globals used tstmts in
        let (fstmts',fused) = remove_unused' globals used fstmts in
        let elsif' = List.map
          (fun (S_Elsif_Cond (c,ss)) ->
            let (b, bused) = remove_unused' globals used ss in
            let bused = IdentSet.union bused (fv_expr c) in
            (S_Elsif_Cond (c,b), bused))
          elsif in
        let used = List.fold_right (fun (_,u) -> IdentSet.union u) elsif' (IdentSet.union tused fused) in
        let used = IdentSet.union used (fv_expr c) in
        (match (tstmts',fstmts',elsif') with
        | [], [], [] -> pass
        | _, _, _ -> (Stmt_If(c, tstmts', List.map fst elsif', fstmts', loc)::acc,used))

      | Stmt_For(var, start, dir, stop, body, loc) ->
          (* Assumes we have a non-zero loop, so things will be decled *)
          let rec loop used =
            let (body',used') = remove_unused' globals used body in
            if IdentSet.equal used used' then (body',used') else loop used'
          in
          let (body,used) = loop used in
          (Stmt_For(var, start, dir, stop, body, loc)::acc,used)

      | Stmt_Assert (c, _) when is_true c -> pass
      (* Unreachable points *)
      | Stmt_Assert (c, _) when is_false c -> halt stmt
      | Stmt_Throw _ -> halt stmt

      | x -> emit x

    ) xs ([], used)
end

module StatefulIntToBits = struct
  type interval = (Z.t * Z.t)
  type abs = (int * bool * interval)
  (* Track vars we change to bvs, ints we leave as ints *)
  type state = {
    changed: bool;
    vars: abs Bindings.t;
    ints: abs Bindings.t;
  }

  let next_pow_of_2 i =
    let bits = Z.numbits (Z.of_int (i - 1)) in
    let i2 = Z.to_int (Z.pow (Z.succ Z.one) bits) in
    i2

  (** Compute the bitvector width needed to represent an interval *)
  let width_of_interval  ?(force_signed=false) ((u,l): interval): int * bool =
    if not force_signed && Z.geq l Z.zero then
      let i = max (Z.log2up (Z.succ u)) 1 in
      let i2 = next_pow_of_2 i in
      (i2,false)
    else
      let u' = if Z.gt u Z.zero then 1 + (Z.log2up (Z.succ u)) else 1 in
      let l' = if Z.lt l Z.zero then 1 + (Z.log2up (Z.neg l)) else 1 in
      let i = max u' l' in
      let i2 = next_pow_of_2 i in
      (i2,true)

  (** Build an abstract point to represent a constant integer *)
  let abs_of_const (c: Z.t): abs =
    let i = (c,c) in
    let (w,s) = width_of_interval i in
    (w,s,i)

  (** Build an abstract point for all values possible in a bv of width w *)
  let abs_of_width (w: int): abs =
    let t = Z.succ (Z.one) in
    let u = Z.pred (Z.pow t (w - 1)) in
    let l = Z.neg (Z.pow t (w - 1)) in
    (w, true, (u,l))

  (** Build an abstract point for unsigned integer in signed representation *)
  let abs_of_uwidth (w: int): abs =
    let t = Z.succ (Z.one) in
    let u = Z.pred (Z.pow t w) in
    let l = Z.zero in
    (w, false, (u,l))

  let abs_of_interval (u: int) (l: int): abs =
    let i = (Z.of_int u, Z.of_int l) in
    let (w,s) = width_of_interval i in
    (w, s, i)

  (* Basic merge of abstract points *)
  let merge_abs ((lw,ls,(l1,l2)): abs) ((rw,rs,(r1,r2)): abs): abs =
    let s = ls || rs in
    let lw = if s && not ls then lw * 2 else lw in
    let rw = if s && not rs then rw * 2 else rw in
    (max lw rw,s,(Z.max r1 l1,Z.min r2 l2))

  (** Max and min of a list of integers *)
  let maxAll (z: Z.t list): Z.t =
    match z with
    | x::xs -> List.fold_left Z.max x xs
    | _ -> invalid_arg ""
  let minAll (z: Z.t list): Z.t =
    match z with
    | x::xs -> List.fold_left Z.min x xs
    | _ -> invalid_arg ""

  (** Brute force the bop and uop cases for range analysis *)
  let bopInterval ((l1,l2): interval) ((r1,r2): interval) (bop: Z.t -> Z.t -> Z.t) =
    (maxAll [bop l1 r1;bop l1 r2;bop l2 r1;bop l2 r2],
     minAll [bop l1 r1;bop l1 r2;bop l2 r1;bop l2 r2])
  let uopInterval ((l1,l2): interval) (uop: Z.t -> Z.t) =
    (maxAll [uop l1;uop l2],
     minAll [uop l1;uop l2])

  (** Preserve abstract points over bops and uops *)
  let abs_of_bop ((lw,ls,li): abs) ((rw,rs,ri): abs) (bop: Z.t -> Z.t -> Z.t): abs =
    let i = bopInterval li ri bop in
    let (iw,s) = width_of_interval ~force_signed:(ls||rs) i in
    let lw = if s && not ls then lw * 2 else lw in
    let rw = if s && not rs then rw * 2 else rw in
    let w = max (max lw rw) iw in
    (w,s,i)
  let abs_of_uop ((lw,ls,li): abs) (uop: Z.t -> Z.t): abs =
    let i = uopInterval li uop in
    let (iw,s) = width_of_interval ~force_signed:ls i in
    let lw = if s && not ls then lw * 2 else lw in
    let w = max lw iw in
    (w,s,i)

  (** Special case the range analysis for division, considering positive and negative denominators *)
  let abs_of_div (num: abs) ((dw,ds,(upper,lower)): abs): abs =
    let abs_of i = abs_of_bop num (dw,ds,i) Primops.prim_zdiv_int in
    let n_one = Z.neg (Z.one) in
    (* Consider ranges from upper to 1 and -1 to lower, excluding 0 *)
    let n_abs = abs_of (Z.min n_one upper, Z.min n_one lower) in
    let p_abs = abs_of (Z.max Z.one upper, Z.max Z.one lower) in
    (* Ignore abstract points that aren't in the denominator's range *)
    if Z.geq lower Z.zero then p_abs (* also captures (0,0) interval *)
    else if Z.leq upper Z.zero then n_abs
    else merge_abs n_abs p_abs

  let width (n,_,_) = n
  let signed (_,s,_) = s
  let interval (_,_,i) = i
  let lower (_,_,(_,l)) = l
  let upper (_,_,(u,_)) = u

  (** Convert abstract point width into exprs & symbols *)
  let expr_of_abs a =
    Expr_LitInt (string_of_int (width a))
  let sym_of_abs a: sym =
    sym_of_int (width a)

  (* Covert an expression and its abstract information to a signed representation *)
  let force_signed (e,old) =
    if signed old then (e,old)
    else
      let abs = (width old * 2, true, interval old) in
      (sym_zero_extend (width old) (width old) e, abs)

  (** Extend an expression coupled with its abstract information to a width *)
  let extend (abs) ((e,old) : sym * abs) =
    (* Only extending *)
    assert (width old <= width abs);
    (* Only going from unsigned to signed *)
    assert ((not (signed old)) || signed abs);
    if signed abs && not (signed old) then
      let e = sym_zero_extend (width old) (width old) e in
      let w = width old * 2 in
      if w = width abs then e
      else sym_sign_extend (width abs - w) w e
    else if width abs = width old then e
    else if not (signed abs) then sym_zero_extend (width abs - width old) (width old) e
    else sym_sign_extend (width abs - width old) (width old) e

  let is_power_of_2 n =
    n <> 0 && 0 = Int.logand n (n-1)

  let is_pos (_,abs) =
    let (_,l) = interval abs in
    Z.geq l Z.zero

  (** Integer variable reads that are successfully converted into
      bitvectors are wrapped in the following function call and
      subsequently unwrapped in a later pass.

      Variable reads that are not wrapped imply a integer variable
      use that this analysis fails to match. To remain compatible,
      these variable reads are subsequently converted back to integers. *)
  let wrapper_ident = FIdent ("StatefulIntToBit_wrapper", 0)

  let build_div x y =
      let wx = width (snd x) in
      let wy = width (snd y) in
      let abs = abs_of_div (snd x) (snd y) in
      let mgr = merge_abs (snd x) (snd y) in
      let base_div = sym_prim (FIdent ("sdiv_bits", 0)) [sym_of_abs mgr] [extend mgr x; extend mgr y] in
      if wy > wx then begin
        (base_div, abs)
      end
      else begin
        assert (width mgr = wx);
        if width abs = wx then begin
          (base_div, abs)
        end else begin
          let ex = extend abs in
          (* Test if denom is -1 *)
          let negone = VBits {n = wy ; v = Z.pred (Z.pow (Z.succ Z.one) wy)} in
          let den = sym_prim (FIdent ("eq_bits", 0)) [sym_of_abs (snd y)] [fst y; Val negone] in
          (* Test if num is INT_MIN *)
          let intmin = VBits {n = wx ; v = Z.pow (Z.succ Z.one) (wx - 1)} in
          let num = sym_prim (FIdent ("eq_bits", 0)) [sym_of_abs (snd x)] [fst x; Val intmin] in
          (* Overflow result *)
          let res = VBits {n = width abs; v = Z.pow (Z.succ Z.one) (wx - 1)} in
          let test = sym_prim (FIdent ("and_bool", 0)) [] [num;den] in
          (sym_prim (FIdent ("ite", 0)) [sym_of_abs abs] [test; Val res; ex (base_div,mgr)], abs)
        end
      end

  (** Covert an integer expression tree into a bitvector equivalent *)
  let rec bv_of_int_expr (st: state) (e: expr): (sym * abs) =
    match e with
    (* Directly translate integer constants into bitvector constants *)
    | Expr_LitInt n
    | Expr_LitHex n ->
        let n = Z.of_string (Value.drop_chars n ' ') in
        let w = abs_of_const n in
        let a = Z.extract n 0 (width w) in
        (sym_of_expr (Expr_LitBits (Z.format ("%0" ^ string_of_int (width w) ^ "b") a)),w)

    (* Assume variables have been declared at this point *)
    | Expr_Var i ->
        (match Bindings.find_opt i (st.vars) with
        | Some v -> (sym_prim wrapper_ident [] [Exp e], v)
        | _ ->
            match Bindings.find_opt i st.ints with
            | Some v ->
                let w = Expr_LitInt (string_of_int (width v)) in
                (Exp (Expr_TApply(FIdent ("cvt_int_bits", 0), [w], [Expr_Var i; w])), v)
            | _ ->
            failwith @@ "bv_of_int_expr: Unknown identifier: " ^ (pprint_ident i))

    | Expr_TApply (FIdent ("cvt_bits_uint", 0), [t], [e]) ->
        let n = int_of_expr t in
        let w = abs_of_uwidth n in
        (sym_of_expr e,w)
    | Expr_TApply (FIdent ("cvt_bits_sint", 0), [t], [e]) ->
        let n = int_of_expr t in
        let w = abs_of_width n in
        (sym_of_expr e,w)

    | Expr_TApply (FIdent ("add_int", 0), [], [x;y]) ->
        let x = bv_of_int_expr st x in
        let y = bv_of_int_expr st y in
        let w = abs_of_bop (snd x) (snd y) Primops.prim_add_int in
        let ex = extend w in
        let f = sym_prim (FIdent ("add_bits", 0)) [sym_of_abs w] [ex x;ex y] in
        (f,w)
    | Expr_TApply (FIdent ("sub_int", 0), [], [x;y]) ->
        let x = bv_of_int_expr st x in
        let y = bv_of_int_expr st y in
        let w = abs_of_bop (snd x) (snd y) Primops.prim_sub_int in
        let ex = extend w in
        let f = sym_prim (FIdent ("sub_bits", 0)) [sym_of_abs w] [ex x;ex y] in
        (f,w)
    | Expr_TApply (FIdent ("mul_int", 0), [], [x;y]) ->
        let x = bv_of_int_expr st x in
        let y = bv_of_int_expr st y in
        let w = abs_of_bop (snd x) (snd y) Primops.prim_mul_int in
        let ex = extend w in
        let f = sym_prim (FIdent ("mul_bits", 0)) [sym_of_abs w] [ex x;ex y] in
        (f,w)

    (* Interface only supports zero rounding division at present, force fdiv result to be positive *)
    | Expr_TApply (FIdent ("fdiv_int", 0), [], [x; y]) ->
        let x = force_signed (bv_of_int_expr st x) in
        let y = force_signed (bv_of_int_expr st y) in
        assert (is_pos x = is_pos y);
        build_div x y

    (* when the divisor is a power of 2, mod can be implemented by truncating. *)
    | Expr_TApply (FIdent ("frem_int", 0), [], [n;Expr_LitInt d]) when is_power_of_2 (int_of_string d) ->
        let digits = Z.log2 (Z.of_string d) in
        let n = bv_of_int_expr st n in
        if width (snd n) <= digits then n
        else
          let f = sym_slice Unknown (fst n) 0 digits in
          let w = abs_of_uwidth digits in
          (f,w)

    | Expr_TApply (FIdent ("neg_int", 0), [], [x]) ->
        let x = bv_of_int_expr st x in
        let w = abs_of_uop (snd x) Primops.prim_neg_int in
        let ex = extend w in
        let z = Val (VBits {v=Z.zero; n=width w}) in
        let f = sym_prim (FIdent ("sub_bits", 0)) [sym_of_abs w] [z; ex x] in
        (f,w)

    (* TODO: Somewhat haphazard translation from old approach *)
    | Expr_TApply (FIdent ("shl_int", 0), [], [x; y]) ->
        let x = bv_of_int_expr st x in
        let y = force_signed (bv_of_int_expr st y) in
        (match fst y with
        | Val (VBits bv) ->
            let yshift = Z.to_int (Primops.prim_cvt_bits_sint bv) in
            let size = width (snd x) + yshift in
            let abs = if signed (snd x) then abs_of_width size else abs_of_uwidth size in
            (sym_append_bits Unknown (width (snd x)) yshift (fst x) (sym_zeros yshift),abs)
        | _ ->
            let (u,_) = interval (snd y) in
            (* in worst case, could shift upper bound on y, adding y bits *)
            let size = width (snd x) + (Z.to_int (Z.max u Z.zero)) in
            let abs = if signed (snd x) then abs_of_width size else abs_of_uwidth size in
            let ex = extend abs in
            let f = sym_prim (FIdent ("lsl_bits", 0)) [sym_of_int size; sym_of_abs (snd y)] [ex x;fst y] in
            (f,abs)
        )

    (* TODO: Over-approximate range on result, could be a little closer *)
    | Expr_TApply (FIdent ("shr_int", 0), [], [x; y]) ->
        let x = force_signed (bv_of_int_expr st x) in
        let y = force_signed (bv_of_int_expr st y) in
        (sym_prim (FIdent ("asr_bits", 0)) [sym_of_abs (snd x); sym_of_abs (snd y)] [fst x;fst y],snd x)

    | Expr_TApply (FIdent ("round_tozero_real",0), [], [x]) ->
        bv_of_real_expr st x

    | _ -> failwith @@ "bv_of_int_expr: Unknown integer expression: " ^ (pp_expr e)

  and bv_of_real_expr (st: state) (e: expr): sym * abs =
    match e with
    | Expr_LitReal n ->
        (* Assume it can be parsed as an integer. TODO: Haven't actually got a bv rep. of a float *)
        bv_of_int_expr st (Expr_LitInt n)

    | Expr_TApply (FIdent ("divide_real",0), [], [x; y]) ->
        let x = force_signed (bv_of_real_expr st x) in
        let y = force_signed (bv_of_real_expr st y) in
        build_div x y

    | Expr_TApply (FIdent ("cvt_int_real", 0), [], [x]) ->
        bv_of_int_expr st x

    | _ -> failwith @@ "bv_of_real_expr: Unknown real expression: " ^ (pp_expr e)

  let bv_of_int_expr_opt (st: state) (e: expr): (sym * abs) option =
    try
      Some(bv_of_int_expr st e)
    with _ -> None

  (** AST traversal to identify the roots of int expr and convert them to bv *)
  class transform_int_expr (st) = object (self)
    inherit Asl_visitor.nopAslVisitor
    method! vexpr e =
      let e' = match e with
      (* Slice may take bitvector or integer as first argument, allow for failure in bv case *)
      (* TODO: Would prefer to type check x, rather than allowing for failure *)
      | Expr_Slices(x, [Slice_LoWd(Expr_LitInt l,Expr_LitInt w)]) ->
          let l = int_of_expr (Expr_LitInt l) in
          let w = int_of_expr (Expr_LitInt w) in
          (match bv_of_int_expr_opt st x with
          | Some (e,a) ->
              if width a = l + w && l = 0 then sym_expr e else
              let x = if width a <= l + w then extend (l+w,signed a,interval a) (e,a) else e in
              sym_expr @@ sym_slice Unknown x l w
          | None -> e)

      (* Other translation from int to bit *)
      | Expr_TApply (FIdent ("cvt_int_bits", 0), [t], [e;_]) ->
          let (e,a) = force_signed (bv_of_int_expr st e) in
          let w = int_of_expr t in
          if w < width a then
            sym_expr @@ sym_slice Unknown e 0 w
          else
            let abs = (int_of_expr t,true,(Z.zero,Z.zero)) in
            sym_expr @@ extend abs (e,a)

      | Expr_TApply (FIdent ("eq_int", 0), [], [x;y]) ->
          let x = bv_of_int_expr st x in
          let y = bv_of_int_expr st y in
          (* If y is strictly greater, must be false *)
          if Z.gt (lower (snd y)) (upper (snd x)) then expr_false
          (* If x is strictly greater, must be false *)
          else if Z.gt (lower (snd x)) (upper (snd y)) then expr_false
          else
            let w = merge_abs (snd x) (snd y) in
            let ex = extend w in
            sym_expr @@ sym_prim (FIdent ("eq_bits", 0)) [sym_of_abs w] [ex x; ex y]

      | Expr_TApply (FIdent ("ne_int", 0), [], [x;y]) ->
          let x = bv_of_int_expr st x in
          let y = bv_of_int_expr st y in
          (* If y is strictly greater, must be true *)
          if Z.gt (lower (snd y)) (upper (snd x)) then expr_true
          (* If x is strictly greater, must be true *)
          else if Z.gt (lower (snd x)) (upper (snd y)) then expr_true
          else
            let w = merge_abs (snd x) (snd y) in
            let ex = extend w in
            sym_expr @@ sym_prim (FIdent ("ne_bits", 0)) [sym_of_abs w] [ex x; ex y]

      (* x >= y  iff  y <= x  iff  x - y >= 0*)
      | Expr_TApply (FIdent ("ge_int", 0), [], [x;y])
      | Expr_TApply (FIdent ("le_int", 0), [], [y;x]) ->
          let x = force_signed (bv_of_int_expr st x) in
          let y = force_signed (bv_of_int_expr st y) in
          (* if largest y is smaller or equal than smallest x, must be true *)
          if Z.leq (upper (snd y)) (lower (snd x)) then expr_true
          (* if smallest y is greater than largest x, must be false *)
          else if Z.gt (lower (snd y)) (upper (snd x)) then expr_false
          else
            let w = merge_abs (snd x) (snd y) in
            let ex x = sym_expr (extend w x) in
            expr_prim' "sle_bits" [expr_of_abs w] [ex y;ex x]

      (* x < y  iff  y > x  iff x - y < 0 *)
      | Expr_TApply (FIdent ("lt_int", 0), [], [x;y])
      | Expr_TApply (FIdent ("gt_int", 0), [], [y;x]) ->
          let x = force_signed (bv_of_int_expr st x) in
          let y = force_signed (bv_of_int_expr st y) in
          (* if largest y is smaller or equal than smallest x, must be true *)
          if Z.lt (upper (snd x)) (lower (snd y)) then expr_true
          (* if smallest y is greater than largest x, must be false *)
          else if Z.geq (lower (snd x)) (upper (snd y)) then expr_false
          else
            let w = merge_abs (snd x) (snd y) in
            let ex x = sym_expr (extend w x) in
            expr_prim' "slt_bits" [expr_of_abs w] [ex x;ex y]

      (* Translation from enum to bit *)
      | Expr_TApply (FIdent ("eq_enum", n), [], [x;y]) when n > 0 ->
          let x = bv_of_int_expr st x in
          let y = bv_of_int_expr st y in
          (* If y is strictly greater, must be false *)
          if Z.gt (lower (snd y)) (upper (snd x)) then expr_false
          (* If x is strictly greater, must be false *)
          else if Z.gt (lower (snd x)) (upper (snd y)) then expr_false
          else
            let w = merge_abs (snd x) (snd y) in
            let ex = extend w in
            (sym_expr @@ sym_prim (FIdent ("eq_bits", 0)) [sym_of_abs w] [ex x; ex y])

      | Expr_TApply (FIdent ("ne_enum", n), [], [x;y]) when n > 0 ->
          let x = bv_of_int_expr st x in
          let y = bv_of_int_expr st y in
          (* If y is strictly greater, must be true *)
          if Z.gt (lower (snd y)) (upper (snd x)) then expr_true
          (* If x is strictly greater, must be true *)
          else if Z.gt (lower (snd x)) (upper (snd y)) then expr_true
          else
            let w = merge_abs (snd x) (snd y) in
            let ex = extend w in
            (sym_expr @@ sym_prim (FIdent ("ne_bits", 0)) [sym_of_abs w] [ex x; ex y])

      (* these functions take bits as first argument and integer as second. just coerce second to bits. *)
      (* TODO: primitive implementations of these expressions expect the shift amount to be signed,
               but a negative shift is invalid anyway. Can't it just be unsigned? *)
      | Expr_TApply (FIdent ("LSL", 0), [size], [x; n]) ->
          let (n,w) = force_signed (bv_of_int_expr st n) in
          expr_prim' "lsl_bits" [size; expr_of_abs w] [x;sym_expr n]
      | Expr_TApply (FIdent ("LSR", 0), [size], [x; n]) ->
          let (n,w) = force_signed (bv_of_int_expr st n) in
          expr_prim' "lsr_bits" [size; expr_of_abs w] [x;sym_expr n]
      | Expr_TApply (FIdent ("ASR", 0), [size], [x; n]) ->
          let (n,w) = force_signed (bv_of_int_expr st n) in
          expr_prim' "asr_bits" [size; expr_of_abs w] [x;sym_expr n]

      | e -> e
      in
      ChangeDoChildrenPost(e', fun e -> e)
  end

  (** Cleanup pass to remove wrapper and introduce necessary bit->int conversions *)
  class cleanup (vars) = object (self)
    inherit Asl_visitor.nopAslVisitor
    method! vexpr e =
      match e with
      | Expr_TApply (f, [], [e]) when f = wrapper_ident -> ChangeTo e
      | Expr_Var v ->
          (match Bindings.find_opt v vars with
          | Some w ->
              (*Printf.printf "transform_int_expr: Found root var: %s\n" (match v with Ident s -> s | _ -> "");*)
              let prim = if signed w then "cvt_bits_sint" else "cvt_bits_uint" in
              ChangeTo (expr_prim' prim [expr_of_abs w] [e])
          | None -> SkipChildren)
      | _ -> DoChildren
  end

  (** Get a variable's abstract rep with a default initial value *)
  let get_default (v: ident) (w: int option) (st: state): abs =
    match w, Bindings.find_opt v st.vars with
    | Some w, _ -> abs_of_uwidth w
    | _, Some (a,b,_) -> (a,b,(Z.zero,Z.zero))
    | _, _ -> abs_of_const Z.zero

  (** Declare a new variable with an initial abstract rep *)
  let assign (v: ident) (i: abs) (st: state): state =
    match Bindings.find_opt v st.vars with
    | Some j ->
        (* Entry doesn't change, nothing to do *)
        if i = j then st
        (* Same width and sign, but redecl resets range, not a real change *)
        else if width i = width j && signed i = signed j then {st with vars = Bindings.add v i st.vars}
        else
          (* Merge width and sign, but keep new range for range analysis *)
          let (w,s,_) = merge_abs i j in
          let m = (w,s,interval i) in
          {st with changed = true ; vars = Bindings.add v m st.vars}
    | None ->
        {st with changed = true ; vars = Bindings.add v i st.vars}

  (** Same as above, but keep as int TODO: This shouldn't be necessary, simplify in future. *)
  let assign_int (v: ident) (i: abs) (st: state): state =
    match Bindings.find_opt v st.ints with
    | Some j ->
        (* Entry doesn't change, nothing to do *)
        if i = j then st
        (* Same width and sign, but redecl resets range, not a real change *)
        else if width i = width j && signed i = signed j then {st with ints = Bindings.add v i st.ints}
        else
          (* Merge width and sign, but keep new range for range analysis *)
          let (w,s,_) = merge_abs i j in
          let m = (w,s,interval i) in

          {st with ints = Bindings.add v m st.ints}
    | None ->
        {st with changed = true ; ints = Bindings.add v i st.ints}

  (** Simple test of existence in state *)
  let tracked (v: ident) (st: state): bool =
    Bindings.mem v st.vars

  (** Merge two states at a control flow join *)
  let merge st1 st2 =
    { changed = st1.changed || st2.changed ;
      vars = Bindings.merge (fun k l r ->
      match l, r with
      | Some l, Some r -> Some (merge_abs l r)
      | Some l, None
      | None, Some l -> Some l
      | _, _ -> None) st1.vars st2.vars ;
    ints = Bindings.merge (fun k l r ->
      match l, r with
      | Some l, Some r -> Some (merge_abs l r)
      | Some l, None
      | None, Some l -> Some l
      | _, _ -> None) st1.ints st2.ints }

  (* Identify variable types to track, possibly with a minimum initial width for enums *)
  let capture_type enum_types ty: int option option =
    if ty = type_integer then Some None
    else match ty with
    | Type_Constructor i ->
        (match enum_types i with
        | Some w ->
            let w = next_pow_of_2 w in
            Some (Some w)
        | None -> None)
    | _ -> None

  (** Statement list walk to establish variable widths and visit all expressions *)
  (*
     TODO: This won't respect local scopes within If stmts
  *)
  let rec walk enum_types st (s: stmt list): (state * stmt list) =
    List.fold_left (fun (st,acc) stmt ->
      let v = new transform_int_expr st in
      match stmt with
      | Stmt_If (e, tstmts, [], fstmts, loc) -> (* Walk the If structure *)
          let e = visit_expr v e in
          let (t,tstmts) = walk enum_types st tstmts in
          let (f,fstmts) = walk enum_types st fstmts in
          (merge t f,acc@[Stmt_If(e, tstmts, [], fstmts, loc)])

      | Stmt_For (var, start, dir, stop, body, loc) ->
          (* Get loop bounds & setup interval for loop index *)
          let start' = Z.of_int (int_of_expr start) in
          let stop' = Z.of_int (int_of_expr stop) in
          let (w,s) = width_of_interval ~force_signed:true (Z.max start' stop',Z.min start' stop') in
          let abs v = (w,s,(v,v)) in

          (* Walk to unroll loop in abstract domain, maintain the final state
             along with the merge of all states at loop entry. *)
          let rec walks final acc n =
            let final = assign_int var (abs n) final in
            let (st,_) = walk enum_types final body in
            let next = (match dir with Direction_Up ->  Z.succ n | _ -> Z.pred n) in
            if n = stop' then (st,acc) else walks st (merge acc st) next
          in

          (* Run the walk, then transform the body given the most general loop entry state *)
          let (st,merged) = walks st st start' in
          let (_,body) = walk enum_types merged body in
          (st,acc@[Stmt_For(var,start,dir,stop,body,loc)])

      | _ -> (* Otherwise, we have no statement nesting *)
        let stmt = Asl_visitor.visit_stmt_single v stmt in
        let (st,stmt) = (match stmt with

        (* Match integer writes *)
        | Stmt_VarDeclsNoInit(t, [v], loc) ->
            (match capture_type enum_types t with
            | Some w ->
                let lhs = get_default v w st in
                let e = Stmt_VarDeclsNoInit (type_bits (string_of_int (width lhs)), [v], loc) in
                let st = assign v lhs st in
                (st,e)
            | None -> (st,stmt))
        | Stmt_ConstDecl(t, v, e, loc) ->
            (match capture_type enum_types t with
            | Some w ->
                let lhs = get_default v w st in
                let rhs = bv_of_int_expr st e in
                let w = merge_abs lhs (snd rhs) in
                let s = sym_expr (extend w rhs) in
                let s = Stmt_ConstDecl (type_bits (string_of_int (width w)), v, s, loc) in
                let st = assign v w st in
                (st,s)
            | None -> (st,stmt))
        | Stmt_VarDecl(t, v, e, loc) ->
            (match capture_type enum_types t with
            | Some w ->
                let lhs = get_default v w st in
                let rhs = bv_of_int_expr st e in
                let w = merge_abs lhs (snd rhs) in
                let s = sym_expr (extend w rhs) in
                let s = Stmt_VarDecl (type_bits (string_of_int (width w)), v, s, loc) in
                let st = assign v w st in
                (st,s)
            | None -> (st,stmt))
        | Stmt_Assign(LExpr_Var(v), e, loc) when tracked v st ->
            let lhs = get_default v None st in
            let rhs = bv_of_int_expr st e in
            let w = merge_abs lhs (snd rhs) in
            let s = sym_expr (extend w rhs) in
            let s = Stmt_Assign (LExpr_Var(v), s, loc) in
            let st = assign v w st in
            (st,s)

        (* Ignore all other stmts *)
        | Stmt_VarDeclsNoInit _
        | Stmt_Assign _
        | Stmt_Assert _
        | Stmt_Throw _
        | Stmt_TCall _ -> (st,stmt)
        | _ -> failwith "walk: invalid IR") in
        (st,acc@[stmt])
    ) (st,[]) s

  let rec fixedPoint (enum_types: ident -> int option) (vars: abs Bindings.t) (ints: abs Bindings.t)  (s: stmt list): stmt list =
    let st = { changed = false ; vars ; ints } in
    let (st',res) = walk enum_types st s in
    if st'.changed then fixedPoint enum_types st'.vars st'.ints s
    else Asl_visitor.visit_stmts (new cleanup vars) res

  let run (enum_types: ident -> int option) (s: stmt list): stmt list =
    fixedPoint enum_types Bindings.empty Bindings.empty s

end



(** Transforms expressions of integers into equivalent expressions over
    bit-vectors. *)
module IntToBits = struct
  type interval = (Z.t * Z.t)
  let empty_interval = (Z.zero, Z.minus_one)


  (** Returns the number of bits needed to represent n (where n >= 0),
      assuming the bits are interpreted as unsigned. *)
  let num_bits_unsigned n =
    assert (Z.geq n Z.zero);
    if Z.equal n Z.zero then
      0
    else
      Z.log2 n + 1

  (** Returns the number of bits needed to represent n, assuming
      the bits are interpreted as signed two's complement.  *)
  let num_bits_signed n =
    if Z.geq n Z.zero then
      (* non-negative n case is same as unsigned + 1 for sign bit. *)
      num_bits_unsigned n + 1
    else
      (* representing -1 requires representing |n|-1 in
         unsigned, then + 1 for sign bit. *)
      num_bits_unsigned (Z.sub (Z.abs n) Z.one) + 1

  (** Returns the number of (signed) bits needed to represent
      all numbers within (lo,hi) inclusive.  *)
  let size_of_interval (lo,hi) =
    assert (Z.leq lo hi);
    max (max (num_bits_signed lo) (num_bits_signed hi)) 1

  (** Returns the interval which is representable by the given number
      of two's complement bits.  *)
  let interval_of_size (n: int): interval =
    assert (n >= 1);
    let magnitude = Z.shift_left Z.one (n - 1) in
    (Z.neg magnitude, Z.sub magnitude Z.one)

  (** Removes all space characters from the given string. *)
  let drop_space x = Value.drop_chars x ' '

  (** Interprets a bit literal as a signed integer. *)
  let sint_of_bits x =
    let x = Value.drop_chars x ' ' in
    let len = String.length x in
    Z.signed_extract (Z.of_string_base 2 x) 0 len


  (** Returns the bit-width of the given expression.
      Requires expression to evaluate to a bit-vector type. *)
  let rec bits_size_of_expr (vars: ty Bindings.t) (e: expr): int =
    match e with
    | Expr_TApply (fn, tes, es) ->
      (match (fn, tes, es) with
      | FIdent ("cvt_bool_bv", 0), _, _ -> 1
      | FIdent ("add_bits", 0), [Expr_LitInt n], _
      | FIdent ("sub_bits", 0), [Expr_LitInt n], _
      | FIdent ("mul_bits", 0), [Expr_LitInt n], _
      | FIdent ("sdiv_bits", 0), [Expr_LitInt n], _
      | FIdent ("and_bits", 0), [Expr_LitInt n], _
      | FIdent ("or_bits", 0), [Expr_LitInt n], _
      | FIdent ("eor_bits", 0), [Expr_LitInt n], _
      | FIdent ("not_bits", 0), [Expr_LitInt n], _
      | FIdent ("zeros_bits", 0), [Expr_LitInt n], _
      | FIdent ("lsl_bits", 0), [Expr_LitInt n; _], _
      | FIdent ("lsr_bits", 0), [Expr_LitInt n; _], _
      | FIdent ("asr_bits", 0), [Expr_LitInt n; _], _
      | FIdent ("ones_bits", 0), [Expr_LitInt n], _ -> int_of_string n
      | FIdent ("append_bits", 0), [Expr_LitInt n; Expr_LitInt m], _ -> int_of_string n + int_of_string m
      | FIdent ("replicate_bits", 0), [Expr_LitInt n; Expr_LitInt m], _ -> int_of_string n * int_of_string m
      | FIdent ("ZeroExtend", 0), [_; Expr_LitInt m], _
      | FIdent ("SignExtend", 0), [_; Expr_LitInt m], _ -> int_of_string m
      | FIdent ("Elem.read", 0), [_; Expr_LitInt m], _ -> int_of_string m
      | FIdent ("Elem.set", 0), [Expr_LitInt v;_], _ -> int_of_string v
      | FIdent ("ite", 0), [Expr_LitInt n], _ -> int_of_string n
      | _ -> failwith @@ "bits_size_of_expr: unhandled " ^ pp_expr e
      )
    | Expr_Parens e -> bits_size_of_expr vars e
    | Expr_LitBits s -> String.length (drop_space s)
    | Expr_Slices (expr, slice_list) ->
      let wds = List.map (function | Slice_LoWd (_,Expr_LitInt n) -> int_of_string n | _ -> assert false) slice_list in
      List.fold_left (+) 0 wds
    | Expr_Var nm ->
      (match Bindings.find_opt nm vars with
      | Some (Type_Bits (Expr_LitInt n)) -> int_of_string n
      | Some (Type_Register (wd, _)) -> int_of_string wd
      | Some t ->
        failwith @@ "bits_size_of_expr: expected bits type but got " ^
        pp_type t ^ " for " ^ pp_expr e
      | None -> failwith @@ "bits_size_of_expr: no type known for " ^ pp_expr e
      )
    | _ -> failwith @@ "bits_size_of_expr: unhandled " ^ pp_expr e

  (** Returns the bit-width of the given value,
      and errors if the value is not a bit value. *)
  let bits_size_of_val (v: value): int =
    match v with
    | VBits {n=n; _} -> n
    | _ -> failwith @@ "bits_size_of_val: unhandled " ^ pp_value v

  (** Returns the bit-width of the given symbolic. *)
  let bits_size_of_sym ?(vars = Bindings.empty)= function
    | Val v -> bits_size_of_val v
    | Exp e -> bits_size_of_expr vars e

  (** Extends the given symbolic to the given size,
      treating it as a signed two's complement expression. *)
  let bits_sign_extend (size: int) (e: sym) =
    let old = bits_size_of_sym e in
    assert (old <= size);
    if old = size
      then e
      else (sym_sign_extend (size - old) old e)

  let bits_coerce_of_expr e =
    let e' =
      match e with
      | Expr_LitInt n
      | Expr_LitHex n ->
        let n' = Z.of_string (drop_space n) in
        let size = num_bits_signed n' in
        let a = Z.extract n' 0 size in
        (Expr_LitBits (Z.format ("%0" ^ string_of_int size ^ "b") a))
      | _ -> e
    in
    sym_of_expr e'

  (** Returns a symbolic bits expression of the given expression
      along with the bit width,
      including coercing integers to two's complement bits where
      needed. *)
  let bits_with_size_of_expr e =
    let e' = bits_coerce_of_expr e in
    e', bits_size_of_sym e'

  let is_power_of_2 n =
    n <> 0 && 0 = Int.logand n (n-1)

  (** Transform integer expressions into bit-vector expressions while
      maintaining precision by widening bit-vector sizes as operations
      are applied. *)
  class bits_coerce_widening = object (self)
    inherit Asl_visitor.nopAslVisitor

    val no_int_conversion = List.map (fun f -> FIdent (f, 0))
      []

    (** Visits an expression, coercing integer expressions into bit-vector
        operations.

        Bit-vectors generated by this conversion are in SIGNED two's complement.
        Each visit case assumes its sub-expressions have already been converted
        to signed bit-vectors.
    *)
    method! vexpr e =
      match e with

      | Expr_TApply (f, _, _) when (List.mem f no_int_conversion) ->
        SkipChildren

        (* match two function calls deep to find truncated division. *)
      | Expr_TApply (FIdent ("round_tozero_real",0), [],
          [Expr_TApply (FIdent ("divide_real",0), [], args)]) ->

        ChangeDoChildrenPost (Expr_Tuple args, fun e' ->
          match e' with
          | Expr_Tuple [x; y] ->
            let (x,xsize) = bits_with_size_of_expr x in
            let (y,ysize) = bits_with_size_of_expr y in
            let size = max xsize ysize + 1 in
            let ex = bits_sign_extend size in
            sym_expr @@ sym_prim (FIdent ("sdiv_bits", 0)) [sym_of_int size] [ex x; ex y]
          | _ -> failwith "expected tuple in round divide real case."
        )


      | Expr_TApply (fn, tes, es) ->
        ChangeDoChildrenPost (e, fun e' ->
          let unsupported () =
            failwith @@ "unsupported integer function: " ^ pp_expr e'
          in
          match e' with
          | Expr_TApply (FIdent ("cvt_bits_uint", 0), [t], [e]) ->
            sym_expr @@ sym_zero_extend 1 (int_of_expr t) (bits_coerce_of_expr e)
          | Expr_TApply (FIdent ("cvt_bits_sint", 0), [t], [e]) ->
            (* seemingly unnecessary slices allow inferring the size of 'e'.
               without this, it is impossible in some cases (e.g. if 'e' is a bare variable). *)
            sym_expr @@ sym_slice Unknown (bits_coerce_of_expr e) 0 (int_of_expr t)
          | Expr_TApply (FIdent ("cvt_int_bits", 0), [t], [e;_]) ->
            let e' = bits_coerce_of_expr e in
            sym_expr @@ bits_sign_extend (int_of_expr t) e'
          | Expr_TApply (FIdent ("add_int", 0), [], [x;y]) ->
            let (x,xsize) = bits_with_size_of_expr x in
            let (y,ysize) = bits_with_size_of_expr y in
            let size = max xsize ysize + 1 in
            let ex = bits_sign_extend size in
            (* Printf.printf "x %s\ny %s\n" (pp_expr x) (pp_expr y) ; *)
            sym_expr @@ sym_prim (FIdent ("add_bits", 0)) [sym_of_int size] [ex x;ex y]

          | Expr_TApply (FIdent ("sub_int", 0), [], [x;y]) ->
            let (x,xsize) = bits_with_size_of_expr x in
            let (y,ysize) = bits_with_size_of_expr y in
            let size = max xsize ysize + 1 in
            let ex = bits_sign_extend size in
            (* Printf.printf "x %s\ny %s\n" (pp_expr x) (pp_expr y) ; *)
            sym_expr @@ sym_prim (FIdent ("sub_bits", 0)) [sym_of_int size] [ex x; ex y]

          | Expr_TApply (FIdent ("eq_int", 0), [], [x;y]) ->
            let (x,xsize) = bits_with_size_of_expr x in
            let (y,ysize) = bits_with_size_of_expr y in
            let size = max xsize ysize in
            let ex = bits_sign_extend size in
            sym_expr @@ sym_prim (FIdent ("eq_bits", 0)) [sym_of_int size] [ex x; ex y]

          | Expr_TApply (FIdent ("ne_int", 0), [], [x;y]) ->
            let (x,xsize) = bits_with_size_of_expr x in
            let (y,ysize) = bits_with_size_of_expr y in
            let size = max xsize ysize in
            let ex = bits_sign_extend size in
            sym_expr @@ sym_prim (FIdent ("ne_bits", 0)) [sym_of_int size] [ex x; ex y]

          | Expr_TApply (FIdent ("mul_int", 0), [], [x;y]) ->
            let (x,xsize) = bits_with_size_of_expr x in
            let (y,ysize) = bits_with_size_of_expr y in
            let size = xsize + ysize in
            let ex = bits_sign_extend size in
            sym_expr @@ sym_prim (FIdent ("mul_bits", 0)) [sym_of_int size] [ex x; ex y]

            (* x >= y  iff  y <= x  iff  x - y >= 0*)
          | Expr_TApply (FIdent ("ge_int", 0), [], [x;y])
          | Expr_TApply (FIdent ("le_int", 0), [], [y;x]) ->
            let (x,xsize) = bits_with_size_of_expr x in
            let (y,ysize) = bits_with_size_of_expr y in
            let size = max xsize ysize in
            let ex x = sym_expr (bits_sign_extend size x) in
            expr_prim' "sle_bits" [expr_of_int size] [ex y;ex x]

            (* x < y  iff  y > x  iff x - y < 0 *)
          | Expr_TApply (FIdent ("lt_int", 0), [], [x;y])
          | Expr_TApply (FIdent ("gt_int", 0), [], [y;x]) ->
            let (x,xsize) = bits_with_size_of_expr x in
            let (y,ysize) = bits_with_size_of_expr y in
            let size = max xsize ysize in
            let ex x = sym_expr (bits_sign_extend size x) in
            expr_prim' "slt_bits" [expr_of_int size] [ex x;ex y]
          (* NOTE: sle_bits and slt_bits are signed less or equal,
             and signed less than.
             These are not primitive in ASL but are defined in BIL so
             we take advantage of them. *)

          | Expr_TApply (FIdent ("neg_int", 0), [], [x]) ->
            let (x,xsize) = bits_with_size_of_expr x in
            let size = xsize + 1 in
            let ex x = sym_expr (bits_sign_extend size x) in
            expr_prim' "neg_bits" [expr_of_int size] [ex x]

          | Expr_TApply (FIdent ("shl_int", 0), [], [x; y]) ->
            let (x,xsize) = bits_with_size_of_expr x in
            let (y,ysize) = bits_with_size_of_expr y in
            (* in worst case, could shift by 2^(ysize-1)-1 bits, assuming y >= 0. *)
            let size = xsize + Int.shift_left 2 (ysize - 1) - 1 in
            let ex x = sym_expr (bits_sign_extend size x) in
            (match y with
            | Val (VBits bv) ->
              (* if shift is statically known, simply append zeros. *)
              let yshift = Z.to_int (Primops.prim_cvt_bits_sint bv) in
              sym_expr @@ sym_append_bits Unknown xsize yshift x (sym_zeros yshift)
            | _ -> expr_prim' "lsl_bits" [expr_of_int size; expr_of_int ysize] [ex x;sym_expr y]
            )

          | Expr_TApply (FIdent ("shr_int", 0), [], [x; y]) ->
            let (x,xsize) = bits_with_size_of_expr x in
            let (y,ysize) = bits_with_size_of_expr y in
            let size = xsize in
            let ex x = sym_expr (bits_sign_extend size x) in
            expr_prim' "asr_bits" [expr_of_int size; expr_of_int ysize] [ex x;sym_expr y]

            (* these functions take bits as first argument and integer as second. just coerce second to bits. *)
          | Expr_TApply (FIdent ("LSL", 0), [size], [x; n]) ->
            let (n,nsize) = bits_with_size_of_expr n in
            expr_prim' "lsl_bits" [size; expr_of_int nsize] [x;sym_expr n]
          | Expr_TApply (FIdent ("LSR", 0), [size], [x; n]) ->
            let (n,nsize) = bits_with_size_of_expr n in
            expr_prim' "lsr_bits" [size; expr_of_int nsize] [x;sym_expr n]
          | Expr_TApply (FIdent ("ASR", 0), [size], [x; n]) ->
            let (n,nsize) = bits_with_size_of_expr n in
            expr_prim' "asr_bits" [size; expr_of_int nsize] [x;sym_expr n]

            (* when the divisor is a power of 2, mod can be implemented by truncating. *)
          | Expr_TApply (FIdent ("frem_int", 0), [], [n;Expr_LitInt d]) when is_power_of_2 (int_of_string d) ->
            let digits = Z.log2 (Z.of_string d) in
            let n,_ = bits_with_size_of_expr n in
            sym_expr @@ sym_zero_extend 1 digits (sym_slice Unknown n 0 digits)

            (* very carefully coerce a signed integer to a "real" by just using its signed representation *)
            (* this will only work for particular operations. *)
          | Expr_TApply (FIdent ("cvt_int_real", 0), [], [x]) ->
            x

          | Expr_TApply (FIdent (f, 0), _, _) when Utils.endswith f "_int" ->
            unsupported ()

          | _ -> e'
        )
    | _ -> DoChildren

  end

  (** A second transform pass which narrows bit-vector expressions which are
      later sliced, by considering the bits needed in that final slice. *)
  class bits_coerce_narrow = object (self)
    inherit Asl_visitor.nopAslVisitor

    val mutable var_types : ty Bindings.t = Bindings.empty;

    method! vstmt s =
      match s with
      | Stmt_ConstDecl(ty, nm, _, _) ->
          var_types <- Bindings.add nm ty var_types;
          DoChildren
      | Stmt_VarDecl(ty, nm, _, _) ->
          var_types <- Bindings.add nm ty var_types;
          DoChildren
      | Stmt_VarDeclsNoInit(ty, [nm], _) ->
          var_types <- Bindings.add nm ty var_types;
        DoChildren
      | _ -> DoChildren

    method! vexpr e =
      match e with
      | Expr_Slices(
          Expr_TApply (f, tes, es) as inner,
          [Slice_LoWd (Expr_LitInt lo, Expr_LitInt wd) as sl] ) ->

        let wd' = int_of_string lo + int_of_string wd in
        let narrow e =
          (* Printf.printf "slicing %s\n" (pp_expr e); *)
          let e' = sym_of_expr e in
          let size = bits_size_of_sym ~vars:var_types e' in
          let ext = wd' - size in
          (* if expression is shorter than slice, extend it as needed. *)
          let e' = if ext > 0 then (sym_sign_extend ext size e') else e' in
          if wd' <> size then
            sym_expr @@ sym_slice Unknown e' 0 wd'
          else
            e
        in
        let narrow_args () = Expr_TApply (f, [expr_of_int wd'], List.map narrow es) in

        (* for some arithmetic expressions, we only need the lowest n bits in order
           to have n bits of precision in the output. *)
        (match name_of_FIdent f with
        | "add_bits" -> ChangeDoChildrenPost (narrow_args (), fun x -> Expr_Slices (x, [sl]))
        | "sub_bits" -> ChangeDoChildrenPost (narrow_args (), fun x -> Expr_Slices (x, [sl]))
        | "mul_bits" -> ChangeDoChildrenPost (narrow_args (), fun x -> Expr_Slices (x, [sl]))
        | _ -> ChangeDoChildrenPost (narrow inner, fun x -> Expr_Slices (x, [sl]))
        )
      | _ -> DoChildren

  end

  let ints_to_bits xs =
    xs
    (*|> Asl_visitor.visit_stmts (new bits_coerce_widening)*)
    |> Asl_visitor.visit_stmts (new bits_coerce_narrow)

end

module CopyProp = struct
  type st = expr Bindings.t
  let debug_cp = false

  (* Extract an access chain for an expr or lexpr, stopping at symbolic indices *)
  let rec get_expr_ac (e: expr): (expr * access_chain list)  =
      match e with
      | Expr_Field (l, f) -> let (l',c) = get_expr_ac l in (l',c@[Field f])
      | Expr_Array (l, Expr_LitInt i) -> let (l',c) = get_expr_ac l in (l',c@[Index (VInt (Z.of_string i))])
      | _ -> (e, [])
  let rec get_lexpr_ac (le: lexpr): (lexpr * access_chain list)  =
    match le with
    | LExpr_Field (l, f) -> let (l',c) = get_lexpr_ac l in (l',c@[Field f])
    | LExpr_Array (l, Expr_LitInt i) -> let (l',c) = get_lexpr_ac l in (l',c@[Index (VInt (Z.of_string i))])
    | _ -> (le, [])

  (* Identify divergence on access paths to avoid clobbering *)
  let rec overlaps (p: 'a list) (l: 'a list): bool =
    match p, l with
    | x::xs, y::ys -> x = y && overlaps xs ys
    | _ -> true

  (* Clobber walk, determine if assigning to the lexpr may change the expression result *)
  class clobber_walk (cl: lexpr) = object (self)
    inherit nopAslVisitor
    val mutable clobbered = false
    method! vexpr expr =
      match expr with
      | Expr_Var _
      | Expr_Field _
      | Expr_Array _ ->
          let (lv,lc) = get_lexpr_ac cl in
          let (v,c) = get_expr_ac expr in
          (match lv, v with
          | LExpr_Var lv, Expr_Var v ->
              (* Clobber if they are the same base variables and lc is a prefix of c *)
              clobbered <- clobbered || (lv = v && overlaps lc c);
              SkipChildren
          | _ ->
              (* Overapprox if base of the operation is not known *)
              if debug_cp then Printf.printf "Copy-Prop over-approx. clobber: %s %s\n" (pp_expr expr) (pp_lexpr cl);
              clobbered <- true;
              SkipChildren)
      | _ -> DoChildren
    method result = clobbered
  end

  let clobber (le: lexpr) (e: expr): bool =
    let visitor = new clobber_walk le in
    let _ = visit_expr visitor e in
    visitor#result

  (* Load walk, identify if the expression is memory dependent *)
  class load_walk = object (self)
    inherit nopAslVisitor
    val mutable clobbered = false
    method! vexpr expr =
      match expr with
      | Expr_TApply (f,_,_) ->
          clobbered <- clobbered || (name_of_FIdent f = "Mem.read");
          DoChildren
      | _ -> DoChildren
    method result = clobbered
  end

  let load (e: expr): bool =
    let visitor = new load_walk in
    let _ = visit_expr visitor e in
    visitor#result

  let remove (i: ident) (copies: st): st =
    try
      Bindings.remove i copies
    with _ -> copies

  let removeAll (i: ident list) (copies: st): st =
    List.fold_right remove i copies

  let add (i: ident) (e: expr) (copies: st): st =
    Bindings.add i e copies

  let rec candidateExpr (e: expr): bool =
    match e with
    | Expr_Var v -> true
    | Expr_Field (e,_) -> candidateExpr e
    | Expr_Array (e,_) -> candidateExpr e
    (*| Expr_TApply (f,_,_) -> (name_of_FIdent f = "Mem.read")*)
    | _ -> false

  let candidateIdent (i: ident) =
    match i with
    | Ident s -> Str.string_match (Str.regexp "Exp") s 0
    | _ -> false

  let removeClobbers (le: lexpr) (copies: st): st =
    Bindings.filter (fun k e -> not (clobber le e) && not (clobber le (Expr_Var k))) copies

  let removeMemory (copies: st): st =
    Bindings.filter (fun k e -> not (load e)) copies

  let merge (l: st) (r: st): st =
    Bindings.merge (fun k l r -> match l, r with Some l,Some r -> if l = r then Some l else None | _ -> None) l r

  let rec copyProp' (xs: stmt list) (copies: st): (stmt list * st) =
    List.fold_left (fun (acc, copies) stmt ->
      match stmt with
      | Stmt_VarDeclsNoInit(ty, vs, loc) ->
          (* Clear any redefinitions *)
          (acc@[stmt], removeAll vs copies)

      | Stmt_ConstDecl(_, v, e, loc)
      | Stmt_VarDecl(_, v, e, loc) ->
          (* Introduce propagations for local decls *)
          let stmt = subst_stmt copies stmt in
          let e = subst_expr copies e in
          let copies = if candidateExpr e then add v e copies else remove v copies in
          (acc@[stmt], copies)

      | Stmt_Assign(le, e, loc) ->
          (* Remove all clobbers *)
          let stmt = subst_stmt copies stmt in
          let copies = removeClobbers le copies in
          let copies = (match le with
          | LExpr_Var(i) -> remove i copies
          | _ -> copies ) in
          (acc@[stmt], copies)

      | Stmt_If (e, tstmts, [], fstmts, loc) ->
          (* Merge if result *)
          let e = subst_expr copies e in
          let (tstmts, tcopies) = copyProp' tstmts copies in
          let (fstmts, fcopies) = copyProp' fstmts copies in
          (acc@[Stmt_If (e, tstmts, [], fstmts, loc)], merge tcopies fcopies)

      (* Don't copy prop across loop (although we probably could) *)
      | Stmt_For (var, start, dir, stop, body, loc) ->
          let (body, _) = copyProp' body Bindings.empty in
          (acc@[Stmt_For (var, start, dir, stop, body, loc)], Bindings.empty)

      | Stmt_Throw _
      | Stmt_Assert (_, _)  ->
          (* Statements that shouldn't clobber *)
          (acc@[subst_stmt copies stmt], copies)

      | Stmt_TCall (FIdent("Mem.set", 0), _, _, _) ->
          (acc@[subst_stmt copies stmt], removeMemory copies)

      | Stmt_TCall (FIdent("AtomicStart", 0), _, _, _)
      | Stmt_TCall (FIdent("AtomicEnd", 0), _, _, _) ->
          (acc@[stmt],removeMemory copies)

      | _ ->
          (* Over-approximate all other situations for soundness *)
          if debug_cp then Printf.printf "Over-approx: %s\n" (pp_stmt stmt);
          (acc@[stmt],Bindings.empty))
    ([], copies) xs

  let copyProp (xs: stmt list): stmt list =
    let (acc, _) = copyProp' xs Bindings.empty in
    acc

end

module RedundantSlice = struct

  let non_const e =
    match  e with
    | Expr_LitInt _ -> false
    | Expr_LitHex _ -> false
    | _ -> true

  let option_or x y =
    match x with
    | Some x' -> Some x'
    | None -> y

  let width_of_slice (slice : slice) : int =
    match slice with
    | Slice_LoWd (lo, wd) -> int_of_expr wd
    | Slice_HiLo (hi, lo) -> int_of_expr hi - int_of_expr lo + 1
    | Slice_Single _ -> 1

  let width_of_slices slices = List.fold_left (+) 0 (List.map width_of_slice slices)

  let bits_type_of_reg_type = function
    | Type_Register (wd, _) -> Type_Bits (Expr_LitInt wd)
    | x -> x

  type ty_option = Just of ty | Clobbered

  class expression_walk (vartypes: ty Bindings.t) = object (self)
    inherit Asl_visitor.nopAslVisitor

    (** map of variable name to type.
      a value of "Clobbered" means that variable is declared multiple times with different types
      and we should not remove any of its slices. *)
    val mutable lvartypes : ty_option Bindings.t = Bindings.empty;

    method update_lvar_types (s: stmt): unit =
      match s with
      | Stmt_VarDecl(ty,id,_,l)
      | Stmt_ConstDecl(ty,id,_,l) ->
        (match Bindings.find_opt id lvartypes with
        | Some (Just ty') -> if ty = ty' then () else lvartypes <- Bindings.add id (Clobbered) lvartypes
        | Some (Clobbered) -> ()
        | None -> lvartypes <- Bindings.add id (Just ty) lvartypes)
      | Stmt_VarDeclsNoInit(ty,ids,l) ->
        List.iter (fun id -> self#update_lvar_types (Stmt_VarDecl(ty,id,Expr_LitInt("ignored"),l))) ids
      | _ -> ()

    method var_type (id: ident): ty option =
      Option.map bits_type_of_reg_type
        (match Bindings.find_opt id lvartypes with
        | Some (Just x) -> Some x
        | _ -> Bindings.find_opt id vartypes)

    method var_type' (e: expr): ty option =
      match e with
      | Expr_Var id -> self#var_type id
      | _ -> None

    method array_val_type (id: ident): ty option =
      match self#var_type id with
      | Some (Type_Array(_ix,ty)) -> Some ty
      | _ -> None

    method! vstmt (s: stmt): stmt list visitAction =
      singletonVisitAction @@ ChangeDoChildrenPost(s, fun s -> self#update_lvar_types s; s)

    method! vexpr (e: expr): expr visitAction =
      ChangeDoChildrenPost(e, fun e ->
      match e with
      (* Last chance to convert dynamic slices into shift & static slice *)
      | Expr_Slices(x, [Slice_LoWd(l,w)]) when non_const l ->
          (match option_or (infer_type x) (self#var_type' x) with
          | Some (Type_Bits xw) ->
              let e = Expr_TApply (FIdent ("LSR", 0), [xw], [x; l]) in
              Expr_Slices(e, [Slice_LoWd (Expr_LitInt "0", w)])
          | _ -> e)
      | Expr_Slices(e', [Slice_LoWd (Expr_LitInt "0", wd)]) ->
          let try_match (opt: ty option): expr =
            match opt with
            | Some(Type_Bits(num)) when num = wd -> e'
            | _ -> e
          in
          (match e' with
          (* note: no fall-through from var_type case to infer_type case,
             but infer_type only works for builtins anyway. *)
          | Expr_Var id -> try_match (self#var_type id)
          | Expr_Array (Expr_Var id, _) -> try_match (self#array_val_type id)
          | _ -> try_match (infer_type e'))
      | _ -> e)
  end

  let do_transform (vartypes: ty Bindings.t) (xs: stmt list): stmt list =
    Asl_visitor.visit_stmts (new expression_walk(vartypes)) xs

end


module CommonSubExprElim = struct
  (* Basic common sub-expression elimination.
     (Theoretical) Pitfalls:
     - Type inference of our factorised subexpressions isn't great. See large match statement in infer_cse_expr_type
     - We only attempt to eliminate TApplys. TApplys are our "primitive functions" and are the
        main goal of this transform but we could also eliminate many other things.
  *)
  exception CSEError of string

  class gather_expressions = object
    inherit Asl_visitor.nopAslVisitor

    val mutable exprs: expr list = ([]: expr list);
    val mutable cand_exprs: expr list = ([]: expr list);

    (* Doubt this will work with loops, skip them for now *)
    method! vstmt s =
      match s with
      | Stmt_For _ -> SkipChildren
      | _ -> DoChildren

    method! vexpr (e: expr): expr visitAction =
      let () = match e with
      (* For now, only gather TApply's that we've seen more than once
         See eval_prim in value.ml for the list of what that covers. *)
      | Expr_TApply(f,_,_) when List.mem f pure_prims ->
          (match infer_type e with
          | Some (Type_Bits _) ->
              if (List.mem e cand_exprs) && not (List.mem e exprs) then
                exprs <- e :: exprs
              else cand_exprs <- e :: cand_exprs;
          | _ -> ())
      | _ ->
        ()
      in
      DoChildren

    method get_info: expr list =
      exprs
  end

  class replace_all_instances = object
    inherit Asl_visitor.nopAslVisitor

    val mutable candidates: (expr * ident) list = []
    val mutable do_replace: bool = true

    method! vexpr (e: expr): expr visitAction =
      let valid_replacement (e: expr): ident option =
        let found = List.filter (fun a -> fst a = e) candidates in
        if List.length found = 1 then
          Some (snd (List.nth found 0))
        else
          None
      in

      let result = match (valid_replacement e) with
      | Some i ->
        if do_replace then ChangeTo(Expr_Var(i)) else DoChildren
      | None ->
        DoChildren
      in
      result

    method! vstmt (s: stmt): stmt list visitAction =
      let () = match s with
      | Stmt_ConstDecl(_, Ident(n), _, Unknown) when (Str.string_match (Str.regexp "Cse") n 0) ->
        do_replace <- false
      | _ ->
        do_replace <- true
      in DoChildren

    method add (name: ident) (value: expr) =
      candidates <- (value, name)::candidates
  end

  let infer_cse_expr_type (e: expr): ty =
    match infer_type e with
    | Some t -> t
    | None -> raise (CSEError ("Can't infer type of strange expr: " ^ (pp_expr e)))

  let insert_into_stmts (xs: stmt list) (x: stmt): (stmt list) =
    let rec move_after_stmts (head: stmt list) (tail: stmt list) (targets: IdentSet.t) (found: IdentSet.t) =
      if IdentSet.subset targets found then
        (head, tail)
      else
        match tail with
          | [] -> raise (CSEError "Couldn't find all vars from CSE target!")
          | next::all ->
            (* "find" the sets of free variables *and* the sets of assigned variables.
               theoretically assigned should be enough but i'm not sure if we might have the case
               where we want to eliminate an expression that directly uses registers, which aren't assigned *)
            let newfound = IdentSet.union found (IdentSet.union (assigned_vars_of_stmts [next]) (fv_stmt next)) in
            move_after_stmts (head @ [next]) all targets newfound
    in

    let targets = IdentSet.filter (fun a ->
      match a with
      | Ident(s) ->
        (* make sure we're not looking for the actual name of our CSE value *)
        not (Str.string_match (Str.regexp "Cse") s 0)
      | _ -> false
    ) (fv_stmt x) in
    let lists = move_after_stmts [] xs targets (IdentSet.empty) in

    (fst lists) @ [x] @ (snd lists)

  let apply_knowledge (xs: stmt list) (knowledge: expr list) (repl): (stmt list) =
    let rec add_exprs_num (xs: stmt list) (k: expr list) (id: int) =
      match k with
      | [] -> xs
      | head::tail ->
        let new_var_name = "Cse" ^ string_of_int id ^ "__5" in
        (* It would be nice to infer the type of the new CSE value *)
        let new_stmt = Stmt_ConstDecl(infer_cse_expr_type head, Ident(new_var_name), head, Unknown) in

        let () = repl#add (Ident(new_var_name)) head in
        (* Do replacement in our remaining eliminate-able expressions
           to ensure that they will continue to match correctly *)
        add_exprs_num (insert_into_stmts xs new_stmt) (visit_exprs repl tail) (id+1)
    in
    add_exprs_num xs knowledge 0

  let rec gain_info_pass (xs: stmt list) (knowledge: expr list) (n: int): (expr list) =
    if (n >= List.length xs) then knowledge else (
      gain_info_pass xs knowledge (n+1)
    )

  let do_transform (xs: stmt list): stmt list =
    let expression_visitor = new gather_expressions in
    let expression_replacer = new replace_all_instances in

    let xs = visit_stmts expression_visitor xs in
    let xs = apply_knowledge xs expression_visitor#get_info expression_replacer in
    let xs = visit_stmts expression_replacer xs in
    xs
end

(* A brute force match for total value mappings, implemented as a series of chained ifs *)
module CaseSimp = struct
  module StringMap = Map.Make(String);;

  (* Match a 'X = BV_CONSTANT' comparison, returning X and BV_CONSTANT *)
  let valid_guard e =
    match e with
    | Expr_TApply (FIdent ("eq_bits", 0), [Expr_LitInt w], [x; Expr_LitBits b]) ->
        Some (int_of_string w, x, b)
    | _ -> None

  (* Match a 'R := BV_CONSTANT' statement, returning R and BV_CONSTANT *)
  let valid_body b =
    match b with
    | Stmt_Assign (LExpr_Var r, Expr_LitBits c, _) ->
        let w = String.length c in
        Some(r, c, w)
    | _ -> None

  (* Match a chain of 'if X = BV_CONSTANT then R := BV_CONSTANT else if ... else assert FALSE'
     given specific X and R expressions, returning a map from test values to assigned values *)
  let rec match_inner stmt x r =
    match stmt with
    | Stmt_If (e, [c], [], [f], _) ->
        (match valid_guard e, valid_body c, match_inner f x r with
        | Some (w, x', b), Some (r', c, w'), Some res when x' = x && r = r' -> Some (StringMap.add b c res)
        | _ -> None)
    | Stmt_Assert (Expr_Var(Ident "FALSE"), _) -> Some StringMap.empty
    | Stmt_Throw _ -> Some StringMap.empty
    | _ -> None

  (* Match a chain of 'if X = BV_CONSTANT then R := BV_CONSTANT else if ... else assert FALSE',
     returning X, R and a map from test values to assigned values *)
  let match_outer stmt =
    match stmt with
    | Stmt_If (e, [t], [], [f], loc) ->
        (match valid_guard e, valid_body t with
        | Some (w, x, b), Some (r, c, w') ->
            (match match_inner f x r with
            | Some res -> Some (x, r, w, w', loc, StringMap.add b c res)
            | _ -> None)
        | _ -> None)
    | _ -> None

  (* Mapping is total if there is an entry for all possible bv values *)
  let is_total w res = Z.to_int (Z.shift_left Z.one w) = (StringMap.cardinal res)

  (* Guesses for the possible mapping from key to value. This is incredibly dumb. *)
  let fn_guess = [
    (fun x y -> x = y),
    (fun r x _ _ loc -> Stmt_Assign(LExpr_Var r, x, loc));
    (fun x y ->
      let diff = String.length y - String.length x in
      if diff > 0 then (String.concat "" (List.init diff (fun _ -> "0"))) ^ x = y
      else false),
    (fun r x w w' loc ->
      let nw = expr_of_int w' in
      Stmt_Assign(LExpr_Var r, expr_prim' "ZeroExtend" [expr_of_int w; nw] [x; nw], loc));
  ]

  class visit_if = object
    inherit Asl_visitor.nopAslVisitor

    (* Assumes x is pure, as it is referenced within a branch condition *)
    method! vstmt (s: stmt): stmt list visitAction =
      match match_outer s with
      | Some (x, r, w, w', loc, res) when is_total w res ->
          (match List.find_opt (fun (test,_) -> StringMap.for_all test res) fn_guess with
          | Some (_,fn) -> ChangeTo [fn r x w w' loc]
          | _ -> DoChildren)
      | _ -> DoChildren

  end

  let do_transform (xs: stmt list): stmt list =
    let stmt_visitor = new visit_if in
    let xs = visit_stmts stmt_visitor xs in
    xs
end

(* Transform the following to remove control flow:

  if cond then         ITESimp_0 := cond
    X1 := E1           X1 := (ITESimp_0 & E1) | (!ITESimp_0 & F1)
    ...                ...
    XN := EN           XN := (ITESimp_0 & EN) | (!ITESimp_0 & F1)
  else            ~>
    X1 := F1
    ...
    XN := F2

  Where:
    - XNs are written on both edges in the same order.
    - XNs are single bit variables.
    - ENs and FNs are pure.

  TODO:
    - Could generalise to mismatched XNs, as long as self-assign is safe.
      Not clear if this is okay semantically.
    - Could generalise to arbitrary bitvectors, if worthwhile.
      Resulting mask might be worse than branch however.
    - Generalised order is difficult given dependencies.
  *)
module BitITESimp = struct
  let one = Expr_LitInt "1"
  let type_bit = Type_Bits one

  (* Test if we can freely perform the operation, even if it wouldn't
     have been performed in the original branching version *)
  let rec is_pure e =
    match e with
    | Expr_Var _ -> true
    | Expr_LitBits _ -> true
    | Expr_LitInt _ -> true
    | Expr_Slices(e, [Slice_LoWd(lo, wd)]) ->
        is_pure e && is_pure lo && is_pure wd
    | Expr_TApply(f, tes, es) ->
        List.mem f pure_prims &&
        List.for_all is_pure tes &&
        List.for_all is_pure es
    | Expr_Field(e,_) -> is_pure e
    | Expr_Array(e,i) -> is_pure e && is_pure i
    | _ -> false

  (* Walk both branches in sync, collect necessary information *)
  let rec match_body t f =
    match t, f with
    | Stmt_Assign(ti,te,loc)::ts, Stmt_Assign(fi,fe,_)::fs
        when ti = fi && is_pure te && is_pure fe &&
          infer_type te = Some type_bit ->
            Option.map (fun rest -> ((ti,te,fe,loc)::rest)) (match_body ts fs)
    | [], [] -> Some []
    | _ -> None

  (* Utility to convert a bool test into a bit value, with some cleanup *)
  let rec bool_to_bit c =
    match c with
    | Expr_TApply (FIdent("and_bool", 0), [], ls) ->
        Expr_TApply (FIdent("and_bits", 0), [one], List.map bool_to_bit ls)
    | Expr_TApply (FIdent("eq_bits", 0), _, [e; Expr_LitBits "1"])
    | Expr_TApply (FIdent("eq_bits", 0), _, [Expr_LitBits "1"; e]) -> e
    | Expr_TApply (FIdent("eq_bits", 0), _, [e; Expr_LitBits "0"])
    | Expr_TApply (FIdent("eq_bits", 0), _, [Expr_LitBits "0"; e]) ->
        Expr_TApply (FIdent ("not_bits", 0), [one], [e])
    | _ -> Expr_TApply (FIdent("cvt_bool_bv", 0), [], [c])

  (* Generate the assignment for a paired expression *)
  let build_stmt cond (i,e,e',loc) =
    let e' = sym_or_bits loc one
        (sym_and_bits loc one cond (sym_of_expr e))
        (sym_and_bits loc one (sym_not_bits loc one cond) (sym_of_expr e')) in
    Stmt_Assign (i, sym_expr e', loc)

  (* Given the analysis has succeeded, build the equivalent series of assignments *)
  let build_assigns cond assigns loc nv =
    let cond_write = Stmt_ConstDecl(type_bit, nv, bool_to_bit cond, loc) in
    let cond_load = Exp (Expr_Var nv) in
    (cond_write::List.map (build_stmt cond_load) assigns)

  class visit_if = object
    inherit Asl_visitor.nopAslVisitor
    val mutable next_var = 0
    method! vstmt (s: stmt): stmt list visitAction =
      match s with
      | Stmt_If (cond, t, [], f, loc) ->
          (match match_body t f with
          | None -> DoChildren
          | Some assigns ->
              let nv = Ident ("ITESimp_" ^ string_of_int next_var) in
              next_var <- next_var + 1;
              ChangeTo (build_assigns cond assigns loc nv))
      | _ -> DoChildren
  end

  let do_transform (xs: stmt list): stmt list =
    let stmt_visitor = new visit_if in
    let xs = visit_stmts stmt_visitor xs in
    xs
end



(* Rewrite expressions with temporary dynamic width bitvectors into equivalent versions with only static bitvectors *)
module RemoveTempBVs = struct

  class expr_walker debug = object
    inherit Asl_visitor.nopAslVisitor
    method !vslice s =
      match s with
      | Slice_HiLo(Expr_TApply(FIdent("add_int", 0), [], [a;Expr_LitInt b]),lo) when a = lo ->
          ChangeTo( Slice_LoWd(lo, Expr_LitInt (string_of_int (int_of_string b + 1))) )
      | _ -> DoChildren
    method !vexpr e =
      match e with
      | Expr_TApply (FIdent("ZeroExtend", 0), [m;Expr_LitInt n], (Expr_TApply(FIdent("Ones", 0), [zw], ones)::xs)) ->
          let ne = Expr_TApply (FIdent("LSR", 0), [Expr_LitInt n], [Expr_TApply(FIdent("Ones", 0), [Expr_LitInt n], [Expr_LitInt n]);
            Expr_TApply (FIdent ("sub_int", 0), [], [Expr_LitInt n; m])]) in
          if debug then Printf.printf "RemoveTempBVs: Changing '%s' to '%s'\n" (pp_expr e) (pp_expr ne);
          ChangeDoChildrenPost(ne, fun e -> e)
      | _ -> DoChildren
  end

  let do_transform debug (xs: stmt list): stmt list =
    let visitor = new expr_walker debug in
    visit_stmts visitor xs

end

module RemoveRegisters = struct

  class type_walker = object
    inherit Asl_visitor.nopAslVisitor
    method !vtype t =
      match t with
      | Type_Register(w,_) -> ChangeTo (Type_Bits (Expr_LitInt w))
      | _ -> DoChildren
  end

  let run =
    let v = new type_walker in
    visit_stmts v

end

(* Turn an append of zeroes into a zero extend *)
module AppendZeros = struct
  class expr_walker = object
    inherit Asl_visitor.nopAslVisitor
    method !vexpr e =
      match e with
      | Expr_TApply(FIdent("append_bits", 0), [Expr_LitInt wl;Expr_LitInt wr], [Expr_LitBits l; r])
          when String.for_all (fun i -> i = '0') l ->
            let nw = Expr_LitInt (Z.to_string (Z.add (Z.of_string wl) (Z.of_string wr))) in
            let e = Expr_TApply (FIdent("ZeroExtend", 0), [Expr_LitInt wr; nw], [r; nw]) in
            ChangeDoChildrenPost(e, fun e -> e)
      | _ -> DoChildren
  end
  let run =
    let v = new expr_walker in
    visit_stmts v
end

module type ScopedBindings = sig
    type 'elt t = 'elt Bindings.t Stack.t

    val push_scope : 'elt t  -> unit -> unit
    val pop_scope : 'elt t  -> unit -> unit
    val add_bind : 'elt t  -> ident -> 'elt -> unit
    val find_binding : 'elt t -> ident -> 'elt option
    val current_scope_bindings : 'elt t -> 'elt Bindings.t
    val init: unit -> 'elt t  
end

module ScopedBindings : ScopedBindings = struct
  type 'elt t = 'elt Bindings.t Stack.t
  let push_scope (b:'elt t) (_:unit) : unit = Stack.push (Bindings.empty) b
  let pop_scope (b:'elt t) (_:unit) : unit = Stack.pop_opt b |> ignore
  let add_bind (b:'elt t) k v : unit = Stack.push (Bindings.add k v (Stack.pop b)) b
  let find_binding (b:'elt t) (i) : 'a option = Seq.find_map (fun s -> Bindings.find_opt i s) (Stack.to_seq b)
  let init (u:unit) : 'elt t = let s = Stack.create () in Stack.push (Bindings.empty) s; s


  (** returns a flattened view of bindings accessible from the current (innermost) scope. *)
  let current_scope_bindings (b:'elt t) : 'elt Bindings.t =
    (* inner bindings shadow outer bindings. *)
    let join = Bindings.union (fun _ inner _outer -> Some inner) in
    Seq.fold_left join Bindings.empty (Stack.to_seq b)
end

module FixRedefinitions = struct
  type var_t = {name: ident ; index: int}

  let ident_for_v (e: var_t) : ident =
    if e.index = 0 then e.name else
    match e.name with
    | Ident s -> Ident (s ^ "_" ^ (string_of_int e.index))
    | FIdent (s, i) -> FIdent ((s ^ "_" ^ (string_of_int e.index), i))

  open ScopedBindings

  class redef_renamer (globals) = object(this)
    inherit Asl_visitor.nopAslVisitor

    val mutable seen = Bindings.empty
    val scoped_bindings : var_t ScopedBindings.t =
      let s = Stack.create () in
      Stack.push (Bindings.empty) s ; s
    val mutable global_bindings : var_t Bindings.t =
      Bindings.empty

    method push_scope (_:unit) : unit = push_scope scoped_bindings ()
    method pop_scope (_:unit) : unit = pop_scope scoped_bindings ()
    method add_bind (n: var_t) : unit = add_bind scoped_bindings n.name n
    method existing_binding (i: ident) : var_t option = find_binding scoped_bindings i
    method global_binding (i: ident) : var_t option = Bindings.find_opt i global_bindings

    method incr_binding (i: ident) : var_t =
      let v = this#global_binding i in
      let r = (match v with
      | Some b -> {b with index = b.index + 1}
      | None -> {name=i; index=0}) in
      global_bindings <- Bindings.add i r global_bindings;
      r

    method! vstmt s =
      singletonVisitAction @@ match s with
        | Stmt_VarDeclsNoInit(ty, vs, loc) ->
            let ns = List.map this#incr_binding vs in
            List.iter this#add_bind ns; DoChildren
        | Stmt_VarDecl(ty, v, i, loc) ->
            let b = this#incr_binding v in
            this#add_bind b; DoChildren
        | Stmt_ConstDecl(ty, v, i, loc) ->
            let b = this#incr_binding v in
            this#add_bind b; DoChildren
        | Stmt_If (c, t, els, e, loc) ->
            let c'   = visit_expr this c in
    (* Don't push or pop scopes anymore so that variables are also unique across branches *)
            (*this#push_scope () ; *)
            let t'   = visit_stmts this t in
            (*this#pop_scope (); this#push_scope () ; *)
            let els' = mapNoCopy (visit_s_elsif this ) els in
            (*this#pop_scope (); this#push_scope () ; *)
            let e'   = visit_stmts this e in
            (*this#pop_scope (); *)
            ChangeTo (Stmt_If (c', t', els', e', loc))
        | Stmt_For (var, start, dir, stop, body, loc) ->
            let start' = visit_expr this start in
            let stop' = visit_expr this stop in
            this#push_scope ();
            let v = this#incr_binding var in
            this#add_bind v;
            let body' = visit_stmts this body in
            this#pop_scope ();
            ChangeTo (Stmt_For (ident_for_v v, start', dir, stop', body', loc))
        (* Statements with child scopes that shouldn't appear towards the end of transform pipeline *)
        | Stmt_Case _ -> failwith "(FixRedefinitions) case not expected"
        | Stmt_While _ -> failwith "(FixRedefinitions) while not expected"
        | Stmt_Repeat _ -> failwith "(FixRedefinitions) repeat not expected"
        | Stmt_Try _ -> failwith "(FixRedefinitions) try not expected"
        | _ -> DoChildren

    method! vlvar e =
       (match (this#existing_binding e) with
          | Some e -> ChangeTo (ident_for_v e)
          | None -> SkipChildren)

    method! vvar e =
       (match (this#existing_binding e) with
          | Some e -> ChangeTo (ident_for_v e)
          | None -> SkipChildren)
    end

  let run (g: IdentSet.t) (s:stmt list) : stmt list =
    let v = new redef_renamer g in
    visit_stmts v s
end

(* Ensure the program does not write or read a set of variables and fields.
   Assumes all record accesses are fully flattened and no name collisions between
   variable names and field accesses with '.' concatenation.
   Reads and writes to unsupported variables are reduced to throws.
   A set of variables and fields can be additionally nominated to be silently ignored,
   such that their updates are removed, however, their reads will still become throws.
   *)
module UnsupportedVariables = struct
  type state = {
    unsupported: IdentSet.t;
    ignored: IdentSet.t;
    debug: bool;
  }

  let throw loc = Stmt_Throw(Ident ("UNSUPPORTED"), loc)

  let concat_ident a b =
    match a, b with
    | Ident a, Ident b -> Ident (a ^ "." ^ b)
    | _ -> invalid_arg "concat_ident"

  (* Reduce a series of field accesses into a single ident *)
  let rec reduce_expr e =
    match e with
    | Expr_Var v -> v
    | Expr_Field (e, f) -> concat_ident (reduce_expr e) f
    | _ -> invalid_arg @@ "reduce_expr: " ^ pp_expr e
  let rec reduce_lexpr e =
    match e with
    | LExpr_Var (v) -> v
    | LExpr_Field (e, f) -> concat_ident (reduce_lexpr e) f
    | LExpr_Array (e, _) -> reduce_lexpr e
    | _ -> invalid_arg @@ "reduce_lexpr: " ^ pp_lexpr e

  (* Test read/write sets, with logging *)
  let unsupported_read name st =
    let r = IdentSet.mem name st.unsupported || IdentSet.mem name st.ignored in
    if r && st.debug then Printf.printf "Unsupported Read: %s\n" (pprint_ident name);
    r
  let ignored_write name st =
    let r = IdentSet.mem name st.ignored in
    if r && st.debug then Printf.printf "Ignored Write: %s\n" (pprint_ident name);
    r
  let unsupported_write name st =
    let r = IdentSet.mem name st.unsupported in
    if r && st.debug then Printf.printf "Unsupported Write: %s\n" (pprint_ident name);
    r

  (* Search a stmt/expr for an unsupported load.
     Assumes the load will be evaluated, i.e., no short-circuiting.
   *)
  class find_unsupported_read st = object
    inherit nopAslVisitor
    val mutable issue = false
    method has_issue = issue
    method! vexpr = function
      | Expr_Var name ->
          if unsupported_read name st then issue <- true;
          SkipChildren
      | Expr_Field _ as e ->
          if unsupported_read (reduce_expr e) st then issue <- true;
          SkipChildren
      | _ -> DoChildren
  end

  let unsupported_stmt stmt st =
    let v = new find_unsupported_read st in
    let _ = visit_stmt v stmt in
    v#has_issue

  let unsupported_expr expr st =
    let v = new find_unsupported_read st in
    let _ = visit_expr v expr in
    v#has_issue

  let rec walk stmts st =
    List.fold_right (fun s acc ->
      match s with
      | Stmt_Assign(lexpr, e, loc) ->
          let name = reduce_lexpr lexpr in
          if ignored_write name st then acc
          else if unsupported_write name st then [throw loc]
          else if unsupported_stmt s st then [throw loc]
          else s::acc
      | Stmt_If(e, tstmts, [], fstmts, loc) when unsupported_expr e st ->
          [throw loc]
      | Stmt_If(e, tstmts, [], fstmts, loc) ->
          let tstmts = walk tstmts st in
          let fstmts = walk fstmts st in
          Stmt_If(e, tstmts, [], fstmts, loc)::acc
      | s ->
          if unsupported_stmt s st then [throw (get_loc s)]
          else s::acc) stmts []

  (* Entry point to the transform *)
  let do_transform ignored unsupported stmts =
    let st = { ignored ; unsupported ; debug = false } in
    walk stmts st

  (* Utility to convert a global state into flattened variable identifiers *)
  let rec flatten_var (k: ident) (v: Value.value) =
    match v with
    | Value.VRecord bs ->
        let fields = Bindings.bindings bs in
        let vals = List.map (fun (f,v) -> flatten_var (concat_ident k f) v) fields in
        List.flatten vals
    | _ -> [k]

  let flatten_vars vars =
    let globals = Bindings.bindings vars in
    IdentSet.of_list (List.flatten (List.map (fun (k,v) -> flatten_var k v) globals))

end

module DecoderChecks = struct
  type sl = (int * int)
  type st = {
    ctx: MLBDD.man;
    vars: sl Bindings.t;
    cur_enc: MLBDD.t;
    unpred: MLBDD.t;
    unalloc: MLBDD.t;
    nop: MLBDD.t;
    instrs: MLBDD.t Bindings.t;
  }

  let init_state =
    let ctx = MLBDD.init ~cache:1024 () in
    {
      ctx ;
      vars = Bindings.empty ;
      cur_enc = MLBDD.dtrue ctx ;
      unpred = MLBDD.dfalse ctx ;
      unalloc = MLBDD.dfalse ctx ;
      nop = MLBDD.dfalse ctx ;
      instrs = Bindings.empty ;
    }

  let get_slice s st  = Bindings.find s st.vars

  let extract_field (IField_Field(f, lo, wd)) st =
    { st with vars = Bindings.add f (lo,wd) st.vars }

  let add_unpred g st =
    { st with unpred = MLBDD.dor st.unpred g }

  let add_unalloc g st =
    { st with unalloc = MLBDD.dor st.unalloc g }

  let add_nop g st =
    { st with nop = MLBDD.dor st.nop g }

  let add_instr k g st =
    let existing = Option.value (Bindings.find_opt k st.instrs) ~default:(MLBDD.dfalse st.ctx) in
    { st with instrs = Bindings.add k (MLBDD.dor existing g) st.instrs }

  let restrict_enc g st =
    { st with cur_enc = MLBDD.dand st.cur_enc g }

  let set_enc g st =
    { st with cur_enc = g }

  let bdd_of_mask bs lo ctx =
    snd @@ String.fold_right (fun c (pos,e) ->
      match c with
      | ' ' -> (pos, e)
      | 'x' -> (* No constraint *)
          (pos + 1, e)
      | '1' -> (* bit hi is true *)
        let bit = MLBDD.ithvar ctx pos in
        (pos + 1, MLBDD.dand bit e)
      | '0' -> (* bit hi is true *)
        let bit = MLBDD.dnot (MLBDD.ithvar ctx pos) in
        (pos + 1, MLBDD.dand bit e)
      | _ -> invalid_arg "bdd_of_mask") bs (lo,MLBDD.dtrue ctx)

  let implicant_to_mask m =
    let chars = List.init 32 (fun i ->
      if List.mem (true, i)  m then '1' else
        if List.mem (false, i) m then '0' else
          'x'
        ) in
    let buf = Buffer.create 32 in
    List.iter (Buffer.add_char buf) (List.rev chars);
    Buffer.contents buf

  let to_string bdd =
    let imps = MLBDD.allprime bdd in
    Utils.pp_list implicant_to_mask imps

  (* Represent slices in terms of their position in enc *)
  let decode_slice s st =
    match s with
    | DecoderSlice_Slice(lo, wd) -> (lo,wd)
    | DecoderSlice_FieldName f   -> get_slice f st
    | DecoderSlice_Concat fs     -> failwith "DecoderSlice_Concat not expected"

  (* Convert decode patterns into BDDs *)
  let rec decode_pattern (lo,wd) p ctx =
    match p with
    | DecoderPattern_Bits b
    | DecoderPattern_Mask b -> bdd_of_mask b lo ctx
    | DecoderPattern_Wildcard _ -> MLBDD.dtrue ctx
    | DecoderPattern_Not p -> MLBDD.dnot (decode_pattern (lo,wd) p ctx)

  (* Combine the various tests due to a guard into one BDD *)
  let decode_case_guard vs ps st =
    List.fold_left2 (fun e s p -> MLBDD.dand e (decode_pattern s p st.ctx)) (st.cur_enc) vs ps

  (* Collect reachability for each instruction encoding IGNORING ordering on alts *)
  let rec tf_decode_case b st =
    match b with
    | DecoderBody_UNPRED loc          -> add_unpred st.cur_enc st
    | DecoderBody_UNALLOC loc         -> add_unalloc st.cur_enc st
    | DecoderBody_NOP loc             -> add_nop st.cur_enc st
    | DecoderBody_Encoding(nm, loc)   -> add_instr nm st.cur_enc st
    | DecoderBody_Decoder(fs, c, loc) ->
        tf_decoder c (List.fold_right extract_field fs st)

  and tf_decoder (DecoderCase_Case(ss, alts, loc)) st =
    let vs = List.map (fun s -> decode_slice s st) ss in
    let (st,_) = List.fold_left ( fun (st,prior) (DecoderAlt_Alt(ps,b))->
      let guard = decode_case_guard vs ps st in
      let st' = tf_decode_case b (set_enc (MLBDD.dand prior guard) st) in
      let prior = MLBDD.dand prior (MLBDD.dnot guard) in
      let st = set_enc st.cur_enc st' in
      (st,prior) ) (st,st.cur_enc) alts in
    st

  let do_transform d : st =
    tf_decoder d init_state

end

module type RTAnalysisLattice = sig
  type rt (* RT lattice type *)
  type olt  (* LT lattice type *)
  val xfer_stmt : olt -> rt  -> stmt -> rt*stmt list
  val join: olt -> olt -> olt -> rt -> rt  -> rt
end

module BDDSimp = struct
  let log = false

  type abs = 
    Top |
    Val of MLBDD.t list |
    Bot

  type state =  {
    man: MLBDD.man;
    vars: abs Bindings.t;
    ctx: MLBDD.t;
    stmts: stmt list;
  }

  module type Lattice = RTAnalysisLattice with type olt = state

  module NopAnalysis = struct  
    type rt = unit
    type olt = state 
    let xfer_stmt o r s = r,[s]
    let join o c j r ro = ()
    let init _ = ()
  end


  let init_state (ctx : MLBDD.t) = {
    man = MLBDD.manager ctx;
    vars = Bindings.empty ;
    ctx ;
    stmts = [] 
  }


  let to_string bdd =
    let imps = MLBDD.allprime bdd in
    Utils.pp_list DecoderChecks.implicant_to_mask imps

  let pp_abs a =
    match a with
    | Top -> "Top"
    | Bot -> "Bot"
    | Val v -> Printf.sprintf "Val (%s)" (Utils.pp_list to_string v)

  let pp_state st =
    Printf.sprintf "{ ctx = %s ; vars = %s }" (to_string st.ctx) (pp_bindings pp_abs st.vars)

  let is_true a st =
    match a with
    | Val [v] -> MLBDD.is_true (MLBDD.imply st.ctx v)
    | _ -> false

  let is_false a st =
    match a with
    | Val [v] -> MLBDD.(is_true (imply st.ctx (dnot v)))
    | _ -> false

  let halt st =
    { st with ctx = MLBDD.dfalse st.man }

  let write s st =
    { st with stmts = st.stmts @ [s] }

  let writeall stmts st =
    { st with stmts = st.stmts @ stmts }

  let get_var v st =
    match Bindings.find_opt v st.vars with
    | Some v -> v
    | _ -> if log then (Printf.printf "no var %s\n" (pprint_ident v)); Top (* logically this should be Bot, but need to init globals *)

  let add_var v abs st =
    { st with vars = Bindings.add v abs st.vars }

  let restrict_ctx cond st =
    match cond with
    | Top -> st
    | Bot -> st
    | Val [cond] -> { st with ctx = MLBDD.dand st.ctx cond }
    | _ -> invalid_arg "restrict_ctx"

  let to_bool abs st =
    match abs with
    | Top 
    | Bot -> MLBDD.dtrue st.man
    | Val [v] -> v
    | _ -> failwith "unexpected to_bool"

  let trivial_eq a b =
    if List.length a <> List.length b then false
    else List.fold_right2 (fun a b acc -> MLBDD.equal a b && acc) a b true

  let join_abs cond a b =
    match cond, a, b with
    | _, Top, _
    | _, _, Top -> Top
    | _, Bot, a
    | _, a, Bot -> a
    | _, Val a, Val b when trivial_eq a b -> Val a
    | Val [c], Val a, Val b when List.length a = List.length b ->
        let a = List.map (MLBDD.dand c) a in
        let ncond = MLBDD.dnot c in
        let b = List.map (MLBDD.dand ncond) b in
        Val (List.map2 MLBDD.dor a b)
    | _, Val a, Val b -> Top

  let join_state cond a b =
    let vars = Bindings.merge (fun k a b ->
      match a, b with
      | Some x, Some y -> Some (join_abs cond x y)
      | Some x, _ -> Some x
      | _, Some y -> Some y
      | _ -> None) a.vars b.vars in
    let ctx = MLBDD.dor a.ctx b.ctx in
    { man = a.man ; vars ; ctx ; stmts = [] }

  let wrap_bop f a b =
    match a, b with
    | Bot, _ 
    | _, Bot -> Bot
    | Top, _
    | _, Top -> Top
    | Val a, Val b -> Val (f a b)

  let wrap_uop f a =
    match a with
    | Top -> Top
    | Bot -> Bot
    | Val a -> Val (f a)

  (****************************************************************)
  (** Boolean Prims                                               *)
  (****************************************************************)

  let and_bool = wrap_bop (fun a b ->
    match a, b with
    | [a], [b] -> [MLBDD.dand a b]
    | _ -> failwith "bad bool width")

  let or_bool = wrap_bop (fun a b ->
    match a, b with
    | [a], [b] -> [MLBDD.dor a b]
    | _ -> failwith "bad bool width")

  let not_bool = wrap_uop (fun a ->
    match a with
    | [a] -> [MLBDD.dnot a]
    | _ -> failwith "bad bool width")

  let eq_bool = wrap_bop (fun a b ->
    match a, b with
    | [a], [b] -> [MLBDD.eq a b]
    | _ -> failwith "bad bool width")

  let ne_bool = wrap_bop (fun a b ->
    match a, b with
    | [a], [b] -> [MLBDD.(dnot (eq a b))]
    | _ -> failwith "bad bool width")

  (****************************************************************)
  (** Bitvector Prims                                             *)
  (****************************************************************)

  let and_bits = wrap_bop (List.map2 MLBDD.dand)
  let or_bits = wrap_bop (List.map2 MLBDD.dor)
  let eor_bits = wrap_bop (List.map2 MLBDD.xor)

  let not_bits = wrap_uop (List.map MLBDD.dnot)

  let eq_bits = wrap_bop (fun a b ->
    let bits = List.map2 MLBDD.eq a b in
    match bits with
    | x::xs -> [List.fold_right MLBDD.dand xs x]
    | _ -> failwith "bad bits width"
  )
  let ne_bits a b = not_bool (eq_bits a b)

  let zero_extend_bits x nw st =
    match x with
    | Val v -> Val (List.init (nw - List.length v) (fun _ -> MLBDD.dfalse st.man) @ v)
    | _ -> x

  let sign_extend_bits x nw st =
    match x with
    | Val (x::xs) -> Val (List.init (nw - List.length xs - 1) (fun _ -> x) @ (x::xs))
    | _ -> x

  let append_bits = wrap_bop (@)

  let rec sublist l start wd =
    match l, start, wd with
    | _, 0, 0 -> []
    | x::xs, 0, n -> x::(sublist xs 0 (n-1))
    | x::xs, n, _ -> sublist xs (n-1) wd
    | _ -> invalid_arg "sublist"

  let extract_bits e lo wd =
    match e with
    | Top -> Top
    | Bot -> Bot
    | Val v -> 
        let start = List.length v - lo - wd in
        Val (sublist v start wd)


  let half_add_bit l r = MLBDD.dand l r, MLBDD.xor l r  (* carry, sum *) 
  let full_add_bit l r carry = 
    let c1,s1 = half_add_bit l r in
    let c2,o = half_add_bit s1 carry in
    let ocarry = MLBDD.dor c1 c2 in
    ocarry,o

  let twos_comp_add (xs : MLBDD.t list) (ys: MLBDD.t list) : MLBDD.t * (MLBDD.t list)= 
      let xs = List.rev xs in let ys = List.rev ys in
      match xs,ys with 
        | hx::tlx,hy::tly ->  
          let lscarry,lsb = half_add_bit hx hy in
          let bits,carry = List.fold_left2
          (fun (acc,carry) (l:MLBDD.t) (r:MLBDD.t)  -> let carry,o = (full_add_bit l r carry) in o::acc , carry) 
            ([lsb], lscarry) tlx tly
          in carry,bits
        | _,_ -> failwith "invalid bit strings"

  let signed_add_wrap x y = let _,bits = twos_comp_add x y in bits

  
  let addone m xs  = let one = MLBDD.dtrue m in
      let xs = List.rev xs  in
      let c,rs = match xs with 
        | hx::tlx ->  
          let lscarry,lsb = half_add_bit hx one in
          let bits,carry = List.fold_left
            (fun (acc,carry) (l:MLBDD.t) -> let carry,o = (half_add_bit l carry) in o::acc, carry) 
            ([lsb], lscarry) tlx
          in carry,bits
        | _ -> failwith "no"
      in rs
    

  let signed_negation m (x:MLBDD.t list) =  addone m (List.map MLBDD.dnot x)

  let signed_sub_wrap m x y = let _,bits = twos_comp_add x (signed_negation m y) in bits

(*
  let signed_lt m x y =  

  let signed_gt m x y = List.map MLBDD.dnot (signed_lt m x y)
  *)



  let eq_bvs a b = 
    let bits = List.map2 MLBDD.eq a b in
    match bits with
      | x::xs -> List.fold_right MLBDD.dand xs x
      | _ -> failwith "bad bits width"

    let sle_bits m x y = 
      MLBDD.dor 
        (MLBDD.dand (List.hd x) (MLBDD.dnot (List.hd y)))
        (MLBDD.dnot (MLBDD.xor (List.hd x) (List.hd y)) )

  (* https://cs.nyu.edu/pipermail/smt-lib/2007/000182.html *)

  let unknown_prims = ref Bindings.empty
  let print_unknown_prims (c:unit) = if log then (Bindings.to_seq !unknown_prims |> List.of_seq |> List.sort (fun a b -> compare (snd a) (snd b)) 
    |> List.iter (fun (id,c) -> Printf.printf "%d \t : %s\n" c (pprint_ident id)))

  let eq_bit a b = MLBDD.dnot (MLBDD.xor a b)

  let bvugt m s t : MLBDD.t = let a, b = (List.fold_left2 (fun (gt, bnotsetfirst) a b ->
      MLBDD.dor gt (MLBDD.dand (bnotsetfirst) ((MLBDD.dand a (MLBDD.dnot b)))), (* false until a > b*)
      MLBDD.dand bnotsetfirst (MLBDD.dnot (MLBDD.dand (MLBDD.dnot gt) (MLBDD.dand b (MLBDD.dnot a)))) (* true until a < b*)
     )
      (MLBDD.dfalse m, MLBDD.dtrue m) (s) (t))
  in (MLBDD.dand a b)

  let bvult m x y : MLBDD.t = bvugt m y x 
  let bvule m x y = MLBDD.dor (bvult m x y) (eq_bvs x y)
  let bvuge m x y = MLBDD.dor (bvugt m x y) (eq_bvs x y)

  let bvslt m x y = MLBDD.dor 
    (MLBDD.dand (List.hd x) (MLBDD.dnot (List.hd y)))
    (MLBDD.dand (eq_bit (List.hd x) (List.hd y)) (bvult m x y))

  let bvsgt m x y = bvslt m y x

  let bvsle m x y = MLBDD.dor 
    (MLBDD.dand (List.hd x) (MLBDD.dnot (List.hd y)))
    (MLBDD.dand (eq_bit (List.hd x) (List.hd y)) (bvule m x y))

  let bvsge m x y = bvsle m y x 

  let wrap_bv_bool f m x y  =  match x , y with 
      | Val x, Val y -> Val [(f m x y)]
      | _,_ -> Top

  (*
    let signed_gte_bits m x y = [MLBDD.dor (eq_bvs x y) (List.hd (signed_gt m x y))]
  *)


  let twos_comp_sub man (xs : MLBDD.t list) (ys: MLBDD.t list) = ()

  let replicate_bits newlen bits = match bits with 
    | Val bits -> if Int.rem newlen (List.length bits) <> 0 then failwith "indivisible rep length"  ;
      let repeats = newlen / (List.length bits) in Val (List.concat (List.init repeats (fun i -> bits)))
    | _ -> Top

  (****************************************************************)
  (** Expr Walk                                                   *)
  (****************************************************************)


  let eval_prim f tes es st = 
    match f, tes, es with
    | "and_bool", [], [x; y] -> and_bool x y
    | "or_bool",  [], [x; y] -> or_bool x y
    | "eq_enum",  [], [x; y] -> eq_bool x y
    | "ne_enum",  [], [x; y] -> ne_bool x y
    | "not_bool", [], [x]    -> not_bool x

    | "and_bits", [w], [x; y] -> and_bits x y
    | "or_bits",  [w], [x; y] -> or_bits  x y
    | "not_bits", [w], [x]    -> not_bits x
    | "eq_bits",  [w], [x; y] -> eq_bits  x y
    | "ne_bits",  [w], [x; y] -> ne_bits  x y
    | "eor_bits", [w], [x; y] -> eor_bits x y

    | "append_bits",    [w;w'], [x; y] -> append_bits x y
    (*| "replicate_bits", [w;Expr_LitInt nw], [x;times] -> replicate_bits (int_of_string nw) x *)

    | "ZeroExtend", [w;Expr_LitInt nw], [x; y] ->
        zero_extend_bits x (int_of_string nw) st
    | "SignExtend", [w;Expr_LitInt nw], [x; y] ->
        sign_extend_bits x (int_of_string nw) st
      
    | "add_bits", [Expr_LitInt w], [x; y] -> (match x,y with 
      | Val x, Val y -> let r = (signed_add_wrap x y) in assert (List.length r == (int_of_string w)); Val r
        | _,_ -> Top)
    | "sub_bits", [w], [x; y] -> (match x,y with 
        | Val x, Val y -> Val (signed_add_wrap x (signed_negation st.man y))
        | _,_ -> Top) 
        
    | "ule_bits", [w], [x; y] -> wrap_bv_bool bvule st.man x y  
    | "uge_bits", [w], [x; y] -> wrap_bv_bool bvuge st.man x y  
    | "sle_bits", [w], [x; y] -> wrap_bv_bool bvsle st.man x y  
    | "sge_bits", [w], [x; y] -> wrap_bv_bool bvsge st.man x y  
    | "slt_bits", [w], [x; y] -> wrap_bv_bool bvslt st.man x y  
    | "sgt_bits", [w], [x; y] -> wrap_bv_bool bvsgt st.man x y  

    (*

    | "lsl_bits", [w], [x; y] -> Top
    | "lsr_bits", [w], [x; y] -> Top
    | "asr_bits", [w], [x; y] -> Top
    | "mul_bits", _, [x; y] -> Top
      *)

    | _, _, _ -> 
        unknown_prims  :=  (Bindings.find_opt (Ident f) !unknown_prims) |> (function Some x -> x + 1 | None -> 0) 
            |> (fun x -> Bindings.add (Ident f) x !unknown_prims) ;
        Top

  let rec eval_expr e st =
    match e with
    | Expr_Var (Ident "TRUE") -> Val ([ MLBDD.dtrue st.man ])
    | Expr_Var (Ident "FALSE") -> Val ([ MLBDD.dfalse st.man ])
    | Expr_LitBits b -> 
        Val (String.fold_right (fun c acc ->
          match c with
          | '1' -> (MLBDD.dtrue st.man)::acc
          | '0' -> (MLBDD.dfalse st.man)::acc
          | _ -> acc) b [])
    | Expr_LitInt e -> Top

    | Expr_Var id -> get_var id st

    (* Simply not going to track these *)
    | Expr_Field _ -> if log then Printf.printf "Overapprox field %s\n" (pp_expr e) ; Top
    | Expr_Array _ -> if log then  Printf.printf "Overapprox array %s\n" (pp_expr e); Top

    (* Prims *)
    | Expr_TApply (FIdent (f, 0), tes, es) ->
        let es = List.map (fun e -> eval_expr e st) es in
        eval_prim f tes es st
    | Expr_Slices(e, [Slice_LoWd(Expr_LitInt lo, Expr_LitInt wd)]) ->
        let lo = int_of_string lo in
        let wd = int_of_string wd in
        let e = eval_expr e st in
        extract_bits e lo wd
    | Expr_Slices(e, [Slice_LoWd(lo,wd)]) -> if log then Printf.printf "Overapprox slice\n" ; Top
    | Expr_Parens(e) -> eval_expr e st
    | Expr_Fields _ -> if log then Printf.printf "unexpected Expr_Fields %s" (pp_expr e); Top
    | Expr_In _ -> if log then Printf.printf "unexpected Expr_In %s" (pp_expr e); Top
    | Expr_Unop _ -> if log then Printf.printf "unexpected Expr_Unop %s" (pp_expr e); Top
    | Expr_Unknown _ -> if log then Printf.printf "unexpected Expr_Unkonwn %s" (pp_expr e); Top
    | Expr_ImpDef _ -> if log then Printf.printf "unexpected Expr_ImpDef %s" (pp_expr e); Top
    | Expr_LitString _ -> if log then Printf.printf "unexpected Expr_LitString %s" (pp_expr e); Top
    | Expr_If _ -> if log then Printf.printf "unexpected Expr_If %s" (pp_expr e); Top

    | _ -> failwith @@ Printf.sprintf "BDDSimp eval_expr: unexpected expr: %s\n"  (pp_expr e)  

  (****************************************************************)
  (** Stmt Walk                                                   *)
  (****************************************************************)

  let join_imps a b =
    List.filter (fun v -> List.mem v b) a

  let ctx_to_mask c =
    let imps = MLBDD.allprime c in
    match imps with 
    | x::xs -> List.fold_right join_imps xs x
    | _ -> invalid_arg "ctx_to_mask"

  let clear_bits a c =
    List.filter (fun (b,v) ->
      if List.mem (b,v) c then false
      else if List.mem (not b,v) c then false
      else true) a


  let bdd_to_expr cond st =
    let bd_to_test b = 
        let bv = Value.to_mask Unknown (Value.from_maskLit b) in
        sym_expr @@ sym_inmask Unknown (Exp (Expr_Var (Ident "enc"))) bv
      in
    match cond with
    | Val [cond] ->
        let imps = MLBDD.allprime cond in
        let rebuild = List.fold_right (fun vars ->
          MLBDD.dor
          (List.fold_right (fun (b,v) ->
            MLBDD.(dand (if b then ithvar st.man v else dnot (ithvar st.man v)))
          ) vars (MLBDD.dtrue st.man))
        ) imps (MLBDD.dfalse st.man) in
        let imps = MLBDD.allprime rebuild in
        let masks = List.map DecoderChecks.implicant_to_mask imps in
        (match masks with
        | [] -> None
        | [b] -> Some (bd_to_test b)
        | b::bs  ->
              let try2 = MLBDD.dnot cond |> MLBDD.allprime |> List.map DecoderChecks.implicant_to_mask in
              match try2 with
                | [b] -> Some (Expr_TApply (FIdent ("not_bool", 0), [], [bd_to_test b]))
                | _ ->  (let r = (let tests = (List.map bd_to_test (b::bs)) in
              let bool_or x y = Expr_TApply(FIdent("or_bool", 0), [], [x;y]) in
              List.fold_left bool_or (List.hd tests) (List.tl tests)) in
              Some r)
          )
    | _ -> None

  let rebuild_expr e cond st = match bdd_to_expr cond st with 
      | Some x -> x
      | None -> if log then Printf.printf "Unable to simplify expr" ; e


  class nopvis = object(self) 
    method xf_stmt (x:stmt) (st:state) : stmt list = [x]
  end

  let nop_transform = new nopvis

  module EvalWithXfer (Xf: Lattice) = struct 

  let rec eval_stmt (xs:Xf.rt) (s:stmt) (st:state) =
      (* (transfer : xs, s, st ->  xs', s' ; eval : st -> s -> st' ; write s' : s' , st' -> st'' ) -> xs' s' st''  *)
    let xs,ns = Xf.xfer_stmt st xs s in
    match s with
    | Stmt_VarDeclsNoInit(t, [v], loc) ->
        let st = add_var v Bot st in
        writeall ns st, xs
    | Stmt_VarDecl(t, v, e, loc) ->
        let abs = eval_expr e st in
        let st = add_var v abs st in
        writeall ns st, xs
    | Stmt_ConstDecl(t, v, e, loc) ->
        let abs = eval_expr e st in
        let st = add_var v abs st in
        writeall ns st,xs
    | Stmt_Assign(LExpr_Var v, e, loc) ->
        let abs = eval_expr e st in
        let st = add_var v abs st in
        writeall ns st,xs

    (* Eval the assert, attempt to discharge it & strengthen ctx *)
    | Stmt_Assert(e, loc) ->
        let abs = eval_expr e st in
        if is_false abs st then st,xs
        else
          let e = rebuild_expr e abs st in
          let st = write (Stmt_Assert(e,loc)) st in
          restrict_ctx abs st, xs

    (* State becomes bot - unreachable *)
    | Stmt_Throw _ -> 
        if log then Printf.printf "%s : %s\n" (pp_stmt s) (pp_state st);
        let st = writeall ns st in
        halt st,xs

    (* If we can reduce c to true/false, collapse *)
    | Stmt_If(c, tstmts, [], fstmts, loc) ->
        let cond = eval_expr c st in

        if is_true cond st then  
          eval_stmts xs tstmts st
        else if is_false cond st then
          eval_stmts xs fstmts st
        else
          let c = rebuild_expr c cond st in
          let ncond = not_bool cond in

          let tst,xsa = eval_stmts xs tstmts (restrict_ctx cond {st with stmts = []}) in
          let fst,xsb = eval_stmts xs fstmts (restrict_ctx ncond {st with stmts = []}) in
          let st' = join_state cond tst fst in
          let xs = Xf.join tst fst st' xsa xsb in

          let st' = writeall st.stmts st' in
          let st' = write (Stmt_If (c, tst.stmts, [], fst.stmts, loc)) st' in
          st',xs

    (* Can't do anything here *)
    | Stmt_Assign _
    | Stmt_TCall _ -> 
        writeall ns st,xs

    | _ -> failwith "unknown stmt"

  and eval_stmts xs stmts st =
    List.fold_left (fun (st,xs) s -> if MLBDD.is_false st.ctx then st,xs else (eval_stmt xs s st)) (st,xs) stmts

  end

  let set_enc st =
    let enc = Val (List.rev (List.init 32 (MLBDD.ithvar st.man))) in
    {st with vars = Bindings.add (Ident "enc") enc st.vars}

  module Eval = EvalWithXfer(NopAnalysis) 

  let just_eval a b c = fst (Eval.eval_stmts (NopAnalysis.init ()) a b)

  let do_transform fn stmts reach =
    let st = init_state reach in
    let st = set_enc st in
    let st',xs = Eval.eval_stmts (NopAnalysis.init ()) stmts st in
    st'.stmts


  let rec split_on_bit imps =
    if List.length imps == 0 then begin
      if log then Printf.printf "Dead end\n";
      1
    end
    else if List.length imps == 1 then begin
      if log then Printf.printf "Match on %s\n" (match imps with [(k,e)] -> pprint_ident k | _ -> failwith "huh");
      1
    end
    else
      (* rank bits by the frequency with which they are constrained *)
      let bits = List.init 32 (fun i ->
        let freq = List.length (List.filter (fun (k,e) -> List.exists (fun (_,j) -> i = j) e) imps) in
        (i,freq)) in
      let max = List.fold_right (fun (i,f) (j,m) -> if f > m then (i,f) else (j,m)) bits (-1,0) in
      if fst max == -1 then begin
        if log then Printf.printf "Ended up with %s\n" (Utils.pp_list (fun (k,s) -> pprint_ident k ^ ":" ^ DecoderChecks.implicant_to_mask s) imps);
        failwith "huh"
      end;
      let set = List.filter (fun (k,e) -> not (List.mem (false,fst max) e)) imps in
      let set = List.map (fun (k,e) -> (k,List.filter (fun (f,i) -> i <> fst max) e)) set in
      let clr = List.filter (fun (k,e) -> not (List.mem (true,fst max) e)) imps in
      let clr = List.map (fun (k,e) -> (k,List.filter (fun (f,i) -> i <> fst max) e)) clr in
      if log then Printf.printf "Splitting on %d, sub-lists %d %d of %d\n" (fst max) (List.length set) (List.length clr) (List.length imps);
      if List.length set + List.length clr <> List.length imps then begin
        if log then Printf.printf "Duplication for %s\n" (Utils.pp_list (fun (k,s) -> pprint_ident k ^ ":" ^ DecoderChecks.implicant_to_mask s) imps);
        1
      end
      else begin
        let d1 = split_on_bit set in
        let d2 = split_on_bit clr in
        1 + (Int.max d1 d2)
      end

  let transform_all instrs (st:DecoderChecks.st)=
    (* get all prim implicants for each instruction, one list *)
    let imps = Bindings.fold (fun k e acc ->
      let imps = MLBDD.allprime e in
      let entries = List.map (fun e -> (k,e)) imps in
      acc@entries) st.instrs [] in

    let res = split_on_bit imps in

    if log then Printf.printf "Max depth of %d\n" res;


    Bindings.mapi (fun nm fnsig ->
      let i = match nm with FIdent(s,_) -> Ident s | s -> s in
      match Bindings.find_opt i st.instrs with
      | Some reach -> fnsig_upd_body (fun b -> 
        if log then Printf.printf "transforming %s\n" (pprint_ident nm);
        do_transform nm b reach) fnsig
      | None -> fnsig) instrs
end

(*
  The analysis attempts to argue that all loop computations
  are in parallel, by encoding their simultaneous calculation given
  the loop's initial state.

  This is encoded in the abstract domain as the following:
    f: var -> state -> value list
  where f(var,state) returns a list of values, where the Nth value
  of the list corresponds to the value of 'var' on the Nth loop
  iteration, when the loop started with state 'state'.

  This function encoding (state -> value list) is encoded in type abs,
  which we conceptually consider as type 'abs = {expr list}'.
  The semantics of this encoding is listed below:

  collate es =
    if List.exists empty es then [] else
    let hds = map hd es in
    let tails = map tail es in
    hds::(collate tails)

  (*
    sem : state -> {expr list} -> value list
    We use {expr list} to represent our abstract type, corresponding to a list
    of expressions implicitly.
    Note that state never changes.
    N is the number of loop iterations.
  *)

  sem state VecOp(op : ident, tes : expr list, es : {expr list} list) : value list =
    (* Types should be constant *)
    let tes' = map (eval state) tes in
    (* Evaluate each argument *)
    let es' = map (sem state) es in
    (* Collapse list of vector args into vector of args *)
    let es' = collate es' in
    (* Apply op to each collection of args *)
    map (fun es -> op(tes', es)) es'

  sem state Read(vec : expr, pos : {expr list}, width : expr) : value list =
    (* Types and width should be constant *)
    let vec' = eval state val in
    let width' = eval state width in
    (* Evaluate pos encoding into a list of values *)
    let pos' = sem state pos in
    (* Map each position to a result *)
    map (fun pos -> Elem.read(vec',pos,width')) pos'

  sem state Constant(e : expr) : value list =
    (* Evaluate the constant expression once *)
    let e' = eval state e in
    (* Produce a vector of this constant N times *)
    init N (fun _ -> e')

  sem state Index(e : expr, mul : expr) : value list =
    (* Evaluate the constant base & mul expressions once *)
    let e' = eval state e in
    let m' = eval state mul in
    (* Produce a vector of this base + mul * i N times *)
    init N (fun i -> e' + m' * i)

  sem state BV(e : {expr list}, w : expr, s : bool) : value list =
    let e' = sem state e in
    let w' = eval state w in
    map (fun e -> int_to_bits(e,w',s)) e'

  sem state Write(var : ident, pos : {expr list}, width : expr, e : {expr list}) : value list =
    let pos' = sem state pos in
    let width' = eval state width in
    let e' = sem state e in
    (* This write corresponds to a full definition of var *)
    (* Knowing this simplifies its subsequent transform into a vector op *)
    assert (unique pos');
    assert (length pos' * width' = width_of_var var);
    (* Sort values based on their position *)
    map snd (sort fst (zip pos' e'))

  We derive these encodings in a single loop pass, assuming no
  interference between loop iterations and no failed assertions.
  These are then validated given the summary of loop effects:
    - asserts over the Write operation are checked
    - interference between loop bodies is checked

  Interference may occur when expressions depend on the results
  of prior loop iterators, e.g., a loop counter i := i + 1.
  In some cases, such as the loop counter, these values can
  be rephrased to be order independent, e.g., Index(i,1) for
  the given example.
  We apply these transforms and re-attempt the summary.
*)
module LoopClassify = struct
  (****************************************************************
   * Symbolic Helpers
   ****************************************************************)

  let mk_ite c w a b =
    match c with
    | Expr_Var (Ident "TRUE" ) -> a
    | Expr_Var (Ident "FALSE") -> b
    | _ -> Expr_TApply (FIdent("ite", 0), [w], [c;a;b])

  let expr_of_Z i = Expr_LitInt (Z.to_string i)
  let print_bv ({n;v} : Primops.bitvector) = (Z.format ("%0" ^ string_of_int n ^ "b") v)
  let expr_of_bv (bv : Primops.bitvector) = Expr_LitBits(print_bv bv)

  let parse_bits s =
    match from_bitsLit s with
    | VBits v -> v
    | _ -> failwith @@ "parse_bits: " ^ s

  let parse_signed_bits s =
    match from_bitsLit s with
    | VBits v -> Primops.z_signed_extract v.v 0 v.n
    | _ -> failwith @@ "parse_signed_bits: " ^ s

  let cvt_int_bits a w =
    match a, w with
    | Expr_LitInt a, Expr_LitInt w ->
        expr_of_bv (Primops.prim_cvt_int_bits (Z.of_string w) (Z.of_string a))
    | _ -> Expr_TApply(FIdent("cvt_int_bits",0), [w], [a; w])

  let add_int a b =
    match a, b with
    | Expr_LitInt a, Expr_LitInt b -> Expr_LitInt (Z.to_string (Z.add (Z.of_string a) (Z.of_string b)))
    | Expr_LitInt "0", b -> b
    | a, Expr_LitInt "0" -> a
    | _ -> Expr_TApply(FIdent("add_int",0), [], [a;b])

  let sub_int a b =
    match a, b with
    | Expr_LitInt a, Expr_LitInt b -> Expr_LitInt (Z.to_string (Z.sub (Z.of_string a) (Z.of_string b)))
    | _ -> Expr_TApply(FIdent("sub_int",0), [], [a;b])

  let mul_int a b =
    match a, b with
    | Expr_LitInt a, Expr_LitInt b -> Expr_LitInt (Z.to_string (Z.mul (Z.of_string a) (Z.of_string b)))
    | _ -> Expr_TApply(FIdent("mul_int",0), [], [a;b])

  let div_int a b =
    match a, b with
    | Expr_LitInt a, Expr_LitInt b -> Expr_LitInt (Z.to_string (Z.div (Z.of_string a) (Z.of_string b)))
    | _ -> Expr_TApply(FIdent("div_int",0), [], [a;b])

  let mod_int a b =
    match a, b with
    | Expr_LitInt a, Expr_LitInt b -> Expr_LitInt (Z.to_string (Z.rem (Z.of_string a) (Z.of_string b)))
    | _ -> Expr_TApply(FIdent("mod_int",0), [], [a;b])

  let eq_int a b =
    match a, b with
    | Expr_LitInt a, Expr_LitInt b when Z.of_string a = Z.of_string b -> Expr_Var (Ident "TRUE")
    | Expr_LitInt a, Expr_LitInt b -> Expr_Var (Ident "FALSE")
    | _ -> Expr_TApply(FIdent("eq_int",0), [], [a;b])

  let ite_int c a b =
    match c, a, b with
    | Expr_Var (Ident "TRUE"), _, _ -> a
    | Expr_Var (Ident "FALSE"), _, _ -> b
    | _, a,b when a = b -> a
    | _ -> Expr_TApply(FIdent("ite_int",0), [], [c;a;b])

  let zero_int = Expr_LitInt "0"

  let add_bits w a b =
    match a, b with
    | Expr_LitBits a, Expr_LitBits b -> expr_of_bv (Primops.prim_add_bits (parse_bits a) (parse_bits b))
    | _ -> Expr_TApply(FIdent("add_bits",0), [w], [a;b])

  let sub_bits w a b =
    match a, b with
    | Expr_LitBits a, Expr_LitBits b -> expr_of_bv (Primops.prim_sub_bits (parse_bits a) (parse_bits b))
    | _ -> Expr_TApply(FIdent("sub_bits",0), [w], [a;b])

  let mul_bits w a b =
    match a, b with
    | Expr_LitBits a, Expr_LitBits b -> expr_of_bv (Primops.prim_mul_bits (parse_bits a) (parse_bits b))
    | _ -> Expr_TApply(FIdent("mul_bits",0), [w], [a;b])

  let zeroes w =
    match w with
    | Expr_LitInt w -> expr_of_bv { v = Z.zero ; n = int_of_string w }
    | _ -> failwith ""

  let neg_bits w a =
    sub_bits w (zeroes w) a

  let cvt_bits_sint a w =
    match a, w with
    | Expr_LitBits bv, Expr_LitInt w ->
        let v = parse_signed_bits bv in
        Expr_LitInt (Z.to_string v)
    | _ -> Expr_TApply(FIdent("cvt_bits_sint",0), [w], [a])

  let cvt_bits_uint a w =
    match a, w with
    | Expr_LitBits bv, Expr_LitInt w ->
        let v = parse_bits bv in
        Expr_LitInt (Z.to_string v.v)
    | _ -> Expr_TApply(FIdent("cvt_bits_uint",0), [w], [a])

  let sign_extend a w =
    match a, w with
    | _ -> Expr_TApply(FIdent("SignExtend",0), [w], [a])

  let zero_extend a w =
    match a, w with
    | _ -> Expr_TApply(FIdent("ZeroExtend",0), [w], [a])

  let append_bits w1 w2 x y =
    match x, y with
    | Expr_LitBits x, Expr_LitBits y -> Expr_LitBits (x ^ y)
    | _ -> Expr_TApply (FIdent ("append_bits", 0), [w1;w2], [x;y])

  (****************************************************************
   * Abstract Domain
   ****************************************************************)

  type abs =
      (* An expression that does not change across loop iterations *)
    Constant of expr |
      (* A vectorized operation, taking a series of type and standard arguments *)
    VecOp of ident * expr list * abs list |
      (* A read operation, given position, element width, vector width *)
    Read of expr * abs * expr * expr |
      (* A write operation, given destination, position, element width, vector width, value *)
    Write of ident * abs * expr * expr * abs |
      (* Base, mult *)
    Index of expr * expr |
      (* Base, mult, width *)
    BVIndex of expr * expr * expr |
    Undecl

  let rec pp_abs e =
    match e with
    | Constant e -> "Constant(" ^ pp_expr e ^ ")"
    | VecOp (f,l,r) -> "VecOp(" ^ pprint_ident f ^ "," ^ Utils.pp_list pp_expr l ^ "," ^ Utils.pp_list pp_abs r ^ ")"
    | Read (v,p,w,w') -> "Read(" ^ pp_expr v ^ "," ^ pp_abs p ^ "," ^ pp_expr w ^ "," ^ pp_expr w' ^ ")"
    | Write (v,p,w,_,e) -> "Write(" ^ pprint_ident v ^ "," ^ pp_abs p ^ "," ^ pp_expr w ^ "," ^ pp_abs e ^ ")"
    | Index (e,m) -> "Index(" ^ pp_expr e ^ "," ^ pp_expr m ^ ")"
    | BVIndex (b,m,w) -> "BVIndex(" ^ pp_expr b ^ "," ^ pp_expr m ^ "," ^ pp_expr w ^ ")"
    | Undecl -> "Undecl"

  let rec deps e =
    match e with
    | Constant e -> fv_expr e
    | VecOp (_,tes,es) ->
        let tes_deps = unionSets (List.map fv_expr tes) in
        let es_deps = unionSets (List.map deps es) in
        IdentSet.union tes_deps es_deps
    | Read (v,p,w,ew) -> unionSets [fv_expr v; deps p; fv_expr w; fv_expr ew]
    | Write (v,p,w,vw,e) -> IdentSet.add v (unionSets [deps p; fv_expr w; deps e; fv_expr vw])
    | Index (b,m) -> IdentSet.union (fv_expr b) (fv_expr m)
    | BVIndex (b,m,_) -> IdentSet.union (fv_expr b) (fv_expr m)
    | Undecl -> IdentSet.empty

  let is_vec_op e =
    match e with
    | Read _ -> true
    | VecOp _ -> true
    | _ -> false

  let is_constant e =
    match e with
    | Constant _ -> true
    | _ -> false

  let force_constant e =
    match e with
    | Constant e -> e
    | _ -> failwith @@ "force_constant: " ^ pp_abs e

  let concat_bits ls =
    let body = fun (w,x) (yw,y) -> let b = append_bits w yw x y in (add_int w yw,b) in
    match ls with
    | x::xs -> let (_,r) = List.fold_left body x xs in r
    | _ -> failwith "concat"

  (*
    Helper to build a select vector operation, where x is bits(elems * elemw) and
    integers in sels are less than elems.
  *)
  let select_vec elems elemw x sels =
    let sels_len = Expr_LitInt (string_of_int (List.length sels)) in
    let w = Expr_LitInt "32" in
    let sels = List.rev sels in
    let sels = concat_bits (List.map (fun e -> (w, cvt_int_bits e w)) sels) in
    (match sels with
    | Expr_LitBits _ -> ()
    | _ -> failwith @@ "Non-constant sels: " ^ pp_expr sels );
    Expr_TApply(FIdent("select_vec",0), [elems; sels_len; elemw], [x; sels])

  let shuffle_vec elems elemw x y sels =
    let sels_len = Expr_LitInt (string_of_int (List.length sels)) in
    let w = Expr_LitInt "32" in
    let sels = List.rev sels in
    let sels = concat_bits (List.map (fun e -> (w, cvt_int_bits e w)) sels) in
    (match sels with
    | Expr_LitBits _ -> ()
    | _ -> failwith @@ "Non-constant sels: " ^ pp_expr sels );
    Expr_TApply(FIdent("shuffle_vec",0), [elems; sels_len; elemw], [x; y; sels])

  let replicate elems elemw x =
    Expr_TApply(FIdent("replicate_bits", 0), [elemw; elems], [x; elems])

  let build_sels length fn =
    match length with
    | Expr_LitInt v -> (List.init (int_of_string v) (fun i -> fn (expr_of_int i)))
    | _ -> failwith @@ "Non-constant length to build_sels: " ^ pp_expr length

  (****************************************************************
   * Analysis State
   ****************************************************************)

  type state = {
    (* Base Loop Properties *)
    iterations: expr;
    (* Variable Classification *)
    vars: abs Bindings.t;
    (* Loop Defined *)
    ld: abs Bindings.t;

    (* Type Info *)
    types: ty Bindings.t;
    env: Eval.Env.t;
  }

  (* Create the state for a single loop analysis, from its definition *)
  let init_state var start stop dir types env =
    let abs = match dir with
    | Direction_Up -> Index(start, expr_of_Z Z.one)
    | Direction_Down -> Index(stop, expr_of_Z (Z.neg Z.one)) in
    let iterations = match dir with
    | Direction_Up   -> add_int (sub_int stop start) (expr_of_Z Z.one)
    | Direction_Down -> add_int (sub_int start stop) (expr_of_Z Z.one) in
    { iterations ; vars = Bindings.empty ; ld = Bindings.add var abs Bindings.empty ; types ; env }

  let get_var v st =
    match Bindings.find_opt v st.ld with
    | Some v -> Some v
    | None -> Bindings.find_opt v st.vars

  let decl_ld v i st =
    {st with ld = Bindings.add v i st.ld}

  let assign_var v i st =
    if Bindings.mem v st.ld then
      {st with ld = Bindings.add v i st.ld}
    else
      {st with vars = Bindings.add v i st.vars}

  let width_of_expr e st =
    match Dis_tc.infer_type e st.types st.env with
    | Some (Type_Bits(Expr_LitInt i)) -> (int_of_string i)
    | Some (Type_Constructor (Ident "boolean")) -> 1
    | Some (Type_Register(w, _)) -> (int_of_string w)
    | _ -> failwith @@ "Unknown expression type: " ^ (pp_expr e)

  (****************************************************************
   * Phase 1: Produce a candidate loop summary
   ****************************************************************)

  let vector_ops = [
    "not_bool";
    "and_bool";
    "or_bool";
    "add_bits";
    "sub_bits";
    "mul_bits";
    "sdiv_bits";
    "sle_bits";
    "slt_bits";
    "eq_bits";
    "asr_bits";
    "lsl_bits";
    "not_bits";
    "and_bits";
    "or_bits";
    "eor_bits";
    "append_bits";
    "ZeroExtend";
    "SignExtend";
  ]

  (* Transfer function for a primitive application *)
  let tf_prim st f i tes es =
    match f, i, tes, es with
    (* Everything is constant, can skip *)
    | f, i, tes, es when List.for_all is_constant tes && List.for_all is_constant es ->
      Constant (Expr_TApply(FIdent(f,i), List.map force_constant tes, List.map force_constant es))

    (* Supported operations over Index expressions *)
    | "cvt_int_bits",  0, [Constant w], [Index(b,m);_] ->
        let base = cvt_int_bits b w in
        let mult = cvt_int_bits m w in
        BVIndex (base, mult, w)
    | "add_int", 0, [], [Index (base,mul);Constant offset]
    | "add_int", 0, [], [Constant offset;Index (base,mul)] ->
        Index (add_int base offset, mul)
    | "sub_int", 0, [], [Index (base,mul);Constant offset] ->
        Index (sub_int base offset, mul)
    | "sub_int", 0, [], [Constant offset;Index (base,mul)] ->
        Index (sub_int offset base, mul_int mul (Expr_LitInt "-1"))
    | "mul_int", 0, [], [Index (base,mul);Constant offset]
    | "mul_int", 0, [], [Constant offset;Index (base,mul)] ->
        Index (mul_int base offset, mul_int mul offset)
    | "sdiv_int", 0, [], [Index(base,mul);Constant div] ->
        Index (div_int base div, div_int mul div)

    (* Supported operations over BVIndex TODO: These don't really handle overflow properly *)
    | "cvt_bits_sint", 0, [Constant w], [BVIndex(b,m,_)] ->
        let base = cvt_bits_sint b w in
        let mult = cvt_bits_sint m w in
        Index (base, mult)
    | "cvt_bits_uint", 0, [Constant w], [BVIndex(b,m,_)] ->
        let base = cvt_bits_uint b w in
        let mult = cvt_bits_uint m w in
        Index (base, mult)
    | "ZeroExtend", 0, [Constant oldw; Constant neww], [BVIndex(b,m,_); _] ->
        let base = zero_extend b neww in
        let mult = zero_extend m neww in
        BVIndex (base, mult, neww)
    | "SignExtend", 0, [Constant oldw; Constant neww], [BVIndex(b,m,_); _] ->
        let base = sign_extend b neww in
        let mult = sign_extend m neww in
        BVIndex (base, mult, neww)
    | "add_bits", 0, [Constant w], [BVIndex(base,mul,_);Constant offset] ->
        BVIndex(add_bits w base offset, mul, w)
    | "sub_bits", 0, [Constant w], [BVIndex(base,mul,_);Constant offset] ->
        BVIndex(sub_bits w base offset, mul, w)

    (* Reading Operations *)
    | "Elem.read", 0, [Constant vecw ; Constant elemw], [Constant v; pos; _] ->
        Read (v, pos, elemw, vecw)

    (* Writing Operations *)
    | "Elem.set", 0, [Constant vecw ; Constant elemw], [Constant (Expr_Var v); pos; _; arg] ->
        Write (v, pos, elemw, vecw, arg)
    (* Match offset Elem.set operations TODO: This would be cleaner as a simp rule later on *)
    | "Elem.set", 0, [Constant vecw ; Constant elemw], [
          Write(v,Index(Expr_LitInt "0",Expr_LitInt "2"),elemw',_,arg');
          Index(Expr_LitInt "1",Expr_LitInt "2"); _; arg]
        when elemw = elemw' ->
          let a = VecOp(FIdent("append_bits",0), [elemw;elemw], [arg;arg']) in
          Write (v, Index(Expr_LitInt "0",Expr_LitInt "1"), add_int elemw elemw', vecw, a)

    (* Vector Operations *)
    | f, 0, tes, es when List.mem f vector_ops && List.exists is_vec_op es && List.for_all is_constant tes ->
        VecOp (FIdent (f,0), List.map force_constant tes, es)

    | _ -> failwith @@ "Unknown loop prim: " ^ f ^ " " ^ Utils.pp_list pp_abs tes ^ " " ^ Utils.pp_list pp_abs es

  (* Transfer function for an expression *)
  let rec tf_expr st e =
    match e with
    | Expr_Var v ->
        (match get_var v st with
        | Some abs -> abs
        | None -> Constant e)
    | Expr_LitBits _ -> Constant e
    | Expr_LitInt _ -> Constant e
    | Expr_TApply(FIdent(f,i), tes, es) ->
        let tes = List.map (tf_expr st) tes in
        let es = List.map (tf_expr st) es in
        tf_prim st f i tes es
    | Expr_Slices(e', [Slice_LoWd(lo,wd)]) ->
        let ow = Expr_LitInt (string_of_int (width_of_expr e' st)) in
        (match tf_expr st e', tf_expr st lo, tf_expr st wd with
        (* Entirely constant, pass it through *)
        | Constant e', Constant lo, Constant wd ->
            Constant (Expr_Slices(e', [Slice_LoWd(lo, wd)]))
        (* Constant slice position over vectorized expression *)
        | e', Constant lo, Constant wd when is_vec_op e' ->
            VecOp(FIdent("slice",0), [ow; wd; lo], [e'])
        (* Index based slice over constant, corresponding to a vector read.
           TODO: There is a more general approach to this.
         *)
        | Constant e', Index(b,m), Constant (Expr_LitInt "1") ->
            Read(e', Index(b,m), Expr_LitInt "1", ow)
        | Constant e', Index(b,m), Constant w when m = w ->
            Read(e', Index(b,Expr_LitInt "1"), w, ow)
        | a, b, c -> failwith @@ "Failed loop slice: " ^ Utils.pp_list pp_abs [a;b;c])
    | _ -> failwith @@ "Failed loop expr: " ^ pp_expr e

  (* Join abs a & b given the condition c *)
  let join_abs w c a b =
    match c, a, b with
    | _, a, b when a = b -> a
    (* This is a trivial result, constant for all loop iterations *)
    | Constant c, Constant a, Constant b ->
        Constant (Expr_TApply(FIdent("ite_bits",0), [w], [c;a;b]))
    (* Vector base ite *)
    | _ when List.for_all (fun v -> is_vec_op v || is_constant v) [c;a;b] ->
        VecOp (FIdent("ite",0), [w], [c;a;b])
    | _ -> failwith @@ "Failed join_abs: " ^ pp_abs c ^ " ? " ^ pp_abs a ^ " : " ^ pp_abs b

  (* Join states a & b given the condition cond *)
  let join_st cond st1 st2 =
    (* Merge loop defined constructs, assume they are defined
       on both paths *)
    let ld = Bindings.merge (fun k l r ->
      match l, r with
      | Some l, Some r when l = r -> Some l
      | Some l, Some r ->
          let w = expr_of_int (width_of_expr (Expr_Var k) st1) in
          Some (join_abs w cond l r)
      | _ -> None) st1.ld st2.ld in
    (* Merge external constructs, support conditional effects *)
    let vars = Bindings.merge (fun k l r ->
      match l, r with
      (* Same effect *)
      | Some l, Some r when l = r -> Some l
      (* Conditional write *)
      | Some (Write(v,pos,w,we,e)), None ->
          let w' = expr_of_int (width_of_expr (Expr_Var k) st1) in
          Some (Write(v,pos,w,we,join_abs w' cond e (Read(Expr_Var v,pos,w,we))))
      | None, Some (Write(v,pos,w,we,e)) ->
          let w' = expr_of_int (width_of_expr (Expr_Var k) st1) in
          Some (Write(v,pos,w,we,join_abs w' cond (Read(Expr_Var v,pos,w,we)) e))
      | Some (Constant e), None ->
          let w' = expr_of_int (width_of_expr (Expr_Var k) st1) in
          Some (join_abs w' cond (Constant e) (Constant (Expr_Var k)))
      (* Conditional write *)
      | _ ->
          failwith @@ "Failed join_st: " ^ pprint_ident k ^ ":" ^
            (Utils.pp_option pp_abs l) ^ " " ^ Utils.pp_option pp_abs r
      ) st1.vars st2.vars in
    { st1 with vars; ld }

  (* Transfer function for a list of statements *)
  let rec tf_stmts st s =
    List.fold_left (fun st stmt ->
      match stmt with
      (* Loop Internal Calculations *)
      | Stmt_ConstDecl(ty, v, e, loc) ->
          let abs = tf_expr st e in
          decl_ld v abs st
      | Stmt_VarDecl(ty, v, e, loc) ->
          let abs = tf_expr st e in
          decl_ld v abs st
      | Stmt_VarDeclsNoInit(ty, [v], loc) ->
          decl_ld v Undecl st
      | Stmt_Assign(LExpr_Var v, e, loc) ->
          let abs = tf_expr st e in
          assign_var v abs st
      | Stmt_If(c, t, [], f, loc) ->
          let abs = tf_expr st c in
          let tst = tf_stmts st t in
          let fst = tf_stmts st f in
          join_st abs tst fst
      | Stmt_Assert(e, loc) ->
          (* TODO: We should actually validate or keep this around *)
          st
      | _ -> failwith @@ "Unknown loop stmt: " ^ pp_stmt stmt) st s

  (****************************************************************
   * Phase 2: Fixed Point Identification
   ****************************************************************)

  (*
    Given summaries of each externally scoped variable write,
    determine if they are trivially parallelized.

    As a first phase, we attempt to show all externally scoped variables
    are only self-referential, i.e., there is no dependence relation
    between externally scoped variables.
    The only exception to this is trivial reductions to functions over
    the loop index, such as x := x + 1.

    Once we know variables are at most self-referential, we determine the
    necessary reduction to capture their cumulative effects.
    This occurs in Phase 3.
  *)

  (* If we pre-load definitions for external values, fix them up here.
     Only handles the case where we define a value to be a function of
     index (x := (base + index * mult) and we anticipate the final value
     to be an additional increment of mult.
   *)
  let amend_pre_load init_st st =
    let vars = Bindings.mapi (fun var def ->
      match def, Bindings.find_opt var init_st.vars with
      | x, None -> x
      | BVIndex(Expr_TApply(FIdent("add_bits",0), [w], [base;mult]),mult',w'), Some (BVIndex(base',mult'',w''))
          when base = base' && mult = mult' && w = w' && mult = mult'' && w = w'' ->
            BVIndex(base',mult'',w'')
      | BVIndex(Expr_TApply(FIdent("sub_bits",0), [w], [base;mult]),mult',w'), Some (BVIndex(base',mult'',w''))
          when  base = base' && neg_bits w mult = mult' && w = w' && mult' = mult'' && w = w'' ->
            BVIndex(base',mult'',w'')
      | x, Some y ->
          failwith @@ "Failed to re-establish initial conditions: " ^ pp_abs x ^ " and " ^ pp_abs y
      ) st.vars in
    { st with vars }

  (* Determine if the summary is valid:
      1. All constants are actually constant
      2. Modified variables are at most self-referential
     Can produce fixes for cases where a constant is not constant, but instead a function of loop index.
   *)
  let validate_summary effects =
    (* Identify possible fixes before validation *)
    let constant_fixes = Bindings.fold (fun var def acc ->
      match def with
      | Constant (Expr_TApply(FIdent("add_bits",0), [w], [Expr_Var var'; b]))
          when var = var' && not (IdentSet.mem var (fv_expr b)) ->
            Bindings.add var (BVIndex(Expr_Var var, b, w)) acc
      | Constant (Expr_TApply(FIdent("sub_bits",0), [w], [Expr_Var var'; b]))
          when var = var' && not (IdentSet.mem var (fv_expr b)) ->
            Bindings.add var (BVIndex(Expr_Var var, neg_bits w b, w)) acc
      | _ -> acc) effects Bindings.empty in
    (* If no fixes, validate *)
    if constant_fixes <> Bindings.empty then constant_fixes else
      let _ = Bindings.iter (fun var def ->
        (* No cross-references *)
        let _ = Bindings.iter (fun var' def' ->
          match var,def,var',def' with
          (* Allow for references to BVIndex vars *)
          | _,BVIndex _,_,_-> ()
          (* Ignore self *)
          | v,_,v',_ when v = v' -> ()
          (* Check for reference to var in def' *)
          | v,d,v',d' when IdentSet.mem v (deps d') ->
            failwith @@ "Cross-reference: " ^ pprint_ident v ^ " := " ^ pp_abs d ^ " && " ^ pprint_ident v' ^ " := " ^ pp_abs d'
          | _ -> ()
        ) effects in
        (* Constants are truely constant *)
        match def with
        | Constant e when IdentSet.disjoint (deps def) (bindings_domain effects) -> ()
        | Constant e -> failwith @@ "Failed to generalise: " ^ pprint_ident var ^ " := " ^ pp_abs def
        | _ -> ()
      ) effects in
      Bindings.empty

  (* Run the analysis from an initial state.
     Re-runs if we identify abstractions for external state.
   *)
  let rec fixed_point init_st body =
    let cand_st = tf_stmts init_st body in
    let cand_st = amend_pre_load init_st cand_st in
    let fixes = validate_summary cand_st.vars in
    if fixes = Bindings.empty then cand_st
    else
      let init_st' = { init_st with vars = fixes } in
      fixed_point init_st' body

  (****************************************************************
   * Phase 3: Build expression from the abstract points
   ****************************************************************)

  (*
    Convert abstract points into expressions.
  *)

  (*
    Build vector primitive operations from the abstract state.
   *)
  let rec build_vec_prim st f i tes es =
    let iters = st.iterations in
    let mul_iters i = mul_int i iters in
    let std_args l = List.map (build_vec_expr st) l in
    let vec_args l = (List.map (build_vec_expr st) l) @ [iters] in

    match f, i, tes, es with
    (* Bool Ops, all applied bit-wise *)
    | "not_bool", 0, [], [x] ->
        Expr_TApply(FIdent("not_bits", 0), [iters], std_args [x])
    | "and_bool", 0, [], [x;y] ->
        Expr_TApply(FIdent("and_bits", 0), [iters], std_args [x;y])
    | "or_bool", 0, [], [x;y] ->
        Expr_TApply(FIdent("or_bits", 0),  [iters], std_args [x;y])

    (* Bit-wise Ops *)
    | "not_bits", 0, [w], [x] ->
        Expr_TApply(FIdent("not_bits", 0), [mul_iters w], std_args [x])
    | "and_bits", 0, [w], [x;y] ->
        Expr_TApply(FIdent("and_bits", 0), [mul_iters w], std_args [x;y])
    | "or_bits", 0, [w], [x;y] ->
        Expr_TApply(FIdent("or_bits", 0),  [mul_iters w], std_args [x;y])
    | "eor_bits", 0, [w], [x;y] ->
        Expr_TApply(FIdent("eor_bits", 0), [mul_iters w], std_args [x;y])

    (* Element-wise Ops *)
    | "add_bits", 0, [w], [x;y] ->
        Expr_TApply(FIdent("add_vec", 0),  [iters; w], vec_args [x; y])
    | "sub_bits", 0, [w], [x;y] ->
        Expr_TApply(FIdent("sub_vec", 0),  [iters; w], vec_args [x; y])
    | "mul_bits", 0, [w], [x;y] ->
        Expr_TApply(FIdent("mul_vec", 0),  [iters; w], vec_args [x; y])
    | "sdiv_bits", 0, [w], [x;y] ->
        Expr_TApply(FIdent("sdiv_vec", 0), [iters; w], vec_args [x; y])
    | "sle_bits", 0, [w], [x;y] ->
        Expr_TApply(FIdent("sle_vec", 0),  [iters; w], vec_args [x; y])
    | "slt_bits", 0, [w], [x;y] ->
        Expr_TApply(FIdent("slt_vec", 0),  [iters; w], vec_args [x; y])
    | "eq_bits", 0, [w], [x;y] ->
        Expr_TApply(FIdent("eq_vec", 0),   [iters; w], vec_args [x; y])

    | "asr_bits", 0, [w;w'], [x;y] when w = w' ->
        Expr_TApply(FIdent("asr_vec", 0),  [iters; w], vec_args [x;y])
    | "asr_bits", 0, [Expr_LitInt w;Expr_LitInt w'], [x;y] when Z.gt (Z.of_string w) (Z.of_string w') ->
        let w = Expr_LitInt w and w' = Expr_LitInt w' in
        let y = Expr_TApply(FIdent("scast_vec", 0), [iters; w; w'], (vec_args [y]) @ [w]) in
        Expr_TApply(FIdent("asr_vec", 0),  [iters; w], [build_vec_expr st x;y;iters])

    | "lsl_bits", 0, [w;w'], [x;y] when w = w' ->
        Expr_TApply(FIdent("lsl_vec", 0),  [iters; w], vec_args [x;y])
    | "lsl_bits", 0, [Expr_LitInt w;Expr_LitInt w'], [x;y] when Z.gt (Z.of_string w) (Z.of_string w') ->
        let w = Expr_LitInt w and w' = Expr_LitInt w' in
        let y = Expr_TApply(FIdent("scast_vec", 0), [iters; w; w'], (vec_args [y]) @ [w]) in
        Expr_TApply(FIdent("lsl_vec", 0),  [iters; w], [build_vec_expr st x;y;iters])

    | "ite", 0, [w], [c;x;y] ->
        Expr_TApply(FIdent("ite_vec", 0), [iters; w], vec_args [c;x;y])

    (* Casts *)
    | "ZeroExtend", 0, [ow;nw], [x;_] ->
        Expr_TApply(FIdent("zcast_vec", 0), [iters; nw; ow], (vec_args [x]) @ [nw])
    | "SignExtend", 0, [ow;nw], [x;_] ->
        Expr_TApply(FIdent("scast_vec", 0), [iters; nw; ow], (vec_args [x]) @ [nw])
    | "slice", 0, [ow;nw;lo], [x] ->
        let shifted =
          match lo with
          | Expr_LitInt "0" -> build_vec_expr st x
          | _ -> Expr_TApply(FIdent("lsr_vec",0), [iters; ow], vec_args [x; Constant (cvt_int_bits lo ow)]) in
        Expr_TApply(FIdent("trunc_vec",0), [iters; nw; ow], [shifted; iters; nw])

    (* Appends *)
    (* Special case for a zero extend, convert into ZeroExtend *)
    | "append_bits", 0, [wx;wy], [Constant (Expr_LitBits i);y] when (parse_bits i).v = Z.zero ->
        let nw = add_int wx wy in
        Expr_TApply(FIdent("zcast_vec", 0), [iters; nw; wy], (vec_args [y]) @ [nw])
    | "append_bits", 0, [wx;wy], [y;Constant (Expr_LitBits i)] when (parse_bits i).v = Z.zero ->
        let nw = add_int wx wy in
        let cast = Expr_TApply(FIdent("zcast_vec", 0), [iters; nw; wx], (vec_args [y]) @ [nw]) in
        let shifts = replicate st.iterations nw (cvt_int_bits wy nw) in
        Expr_TApply(FIdent("lsl_vec", 0), [iters; nw], [cast;shifts;iters])
    (* Append over two bitvectors turns into zip TODO: Extend to support gcd of their widths *)
    | "append_bits", 0, [wx;wy], [x;y] when wx = wy ->
        let input = Expr_TApply(FIdent("append_bits",0), [mul_iters wx; mul_iters wy], std_args [x;y]) in
        let sels = build_sels st.iterations (fun i -> [ i ; add_int st.iterations i ]) in
        let sels = List.fold_left (@) [] sels in
        select_vec (add_int st.iterations st.iterations) wx input sels

    | _ -> failwith @@ "Unsupported conversion: " ^ f ^ " " ^ Utils.pp_list pp_expr tes ^ " " ^ Utils.pp_list pp_abs es

  (*
    Turn an abstract point into an operation.
    In effect, this corresponds to computing the abstract point simultaneously
    for all loop iterations.
  *)
  and build_vec_expr st abs =
    match abs with
    (* Constant should not change, replicate it *)
    | Constant expr ->
        let w = expr_of_int (width_of_expr expr st) in
        replicate st.iterations w expr
    (* Vector Operation *)
    | VecOp(FIdent(f,i), tes, es) ->
        build_vec_prim st f i tes es
    (* Read becomes a select operation, building based on its stride and width *)
    | Read(expr,Index(base,mult),width,expr_width) ->
        let sels = build_sels st.iterations (fun i -> add_int base (mul_int mult i)) in
        let elems = div_int expr_width width in
        select_vec elems width expr sels
    (* Write is a select between a base variable and the overwritten component *)
    | Write(var,Index(base,mult),width,var_width,e) ->
        let elems = div_int var_width width in
        let sels = build_sels elems (fun i ->
          ite_int (eq_int (mod_int (sub_int i base) mult) zero_int)
            (add_int (div_int (sub_int i base) mult) elems) i) in
        let expr = append_bits (mul_int st.iterations width) var_width (build_vec_expr st e) (Expr_Var var) in
        select_vec (add_int elems st.iterations) width expr sels
    | _ -> failwith @@ "Failed to build vector expression for: " ^ pp_abs abs

  (* Identify cases where self-reference is limited to reads of a particular
     position and width. *)
  let rec parallel_write var pos width e =
    match e with
    | VecOp(f, tes, es) ->
        let tes = not (IdentSet.mem var (unionSets (List.map fv_expr tes))) in
        let es = List.map (parallel_write var pos width) es in
        tes && List.for_all (fun s -> s) es
    | Read(Expr_Var v',pos',width',_) when v' = var ->
        pos = pos' && width = width'
    | _ -> not (IdentSet.mem var (deps e))

  (* For a variable and abstract point, produce an expression equivalent to the
     parallel evaluation of the abstract point. *)
  let summarize_assign st var abs =
    match abs with
    (* Result is not dependent on itself in anyway *)
    | a when not (IdentSet.mem var (deps a)) ->
        build_vec_expr st abs
    (* Parallel Write, element is only dependent on itself *)
    | Write(var',pos,width,exprw,e) when var = var' && parallel_write var pos width e ->
        build_vec_expr st abs
    (* Final result for a function of loop index *)
    | BVIndex(Expr_Var base,mul,w) when base = var ->
        let iters = cvt_int_bits st.iterations w in
        let m = mul_bits w mul iters in
        add_bits w (Expr_Var base) m

    (* Reduce Add *)
    | VecOp(FIdent("add_bits", 0), [w], [Constant (Expr_Var var') ; e]) when is_vec_op e && var' = var && not (IdentSet.mem var (deps e)) ->
        let e = build_vec_expr st e in
        Expr_TApply ( FIdent("reduce_add",0), [st.iterations; w], [e ; Expr_Var var])

    | _ -> failwith @@ "Failed to summarize " ^ pprint_ident var ^ " <- " ^ pp_abs abs

  (* Given a successful abstract representation of a loop, reduce its observable
     effects into a series of assignments.
   *)
  let loop_summary st loc =
    Bindings.fold (fun var abs acc ->
      let c = summarize_assign st var abs in
      let s = Stmt_Assign(LExpr_Var var, c, loc) in
      s::acc (* TODO: Need temps for this *)
    ) st.vars []

  (****************************************************************
   * Analysis Entry Point
   ****************************************************************)

  (* Map from inside out *)
  let rec walk s types env =
    List.fold_left (fun acc stmt ->
      match stmt with
      | Stmt_For(var, start, dir, stop, body, loc) ->
          let body = walk body types env in
          let st = init_state var start stop dir types env in
          let st' = fixed_point st body in
          let sum = loop_summary st' loc in
          (acc@sum)
      | Stmt_If(c, t, [], f, loc) ->
          let t = walk t types env in
          let f = walk f types env in
          (acc@[Stmt_If(c, t, [], f, loc)])
      | _ -> (acc@[stmt])) ([]) s

  let parse_sels v =
    let chars = String.length v in
    let elems = chars / 32 in
    let e = List.init elems (fun i -> let bv = parse_bits (String.sub v (i * 32) (32)) in Z.to_int bv.v) in
    List.rev e
  let print_sels sels =
    List.fold_left (fun a s -> (print_bv { n = 32 ; v = Z.of_int s } ^ a)) "" sels

  let check_leq x y =
    match x, y with
    | Expr_LitInt x, Expr_LitInt y -> Z.leq (Z.of_string x) (Z.of_string y)
    | _ -> false

  let check_lt x y =
    match x, y with
    | Expr_LitInt x, Expr_LitInt y -> Z.lt (Z.of_string x) (Z.of_string y)
    | _ -> false

  let is_div x y =
    match x, y with
    | Expr_LitInt x, Expr_LitInt y -> (Z.rem (Z.of_string x) (Z.of_string y)) = Z.zero
    | _ -> false

  let is_const_sels sels =
    List.for_all (fun i -> match i with Expr_LitInt _ -> true | _ -> false) sels
  let force_const_sels sels =
    List.map (fun i -> match i with Expr_LitInt i -> int_of_string i | _ -> failwith "force_const") sels

  let apply_sels bv w sels =
    let ins = (String.length bv) / w in
    let vals = List.init ins (fun i -> String.sub bv (i * w) w) in
    let vals = List.rev vals in
    let res = List.map (fun i -> List.nth vals i) sels in
    let res = List.rev res in
    String.concat "" res

  let rec inc_by s is =
    match is with
    | (Expr_LitInt i)::(Expr_LitInt j)::is when Z.sub (Z.of_string j) (Z.of_string i) = s ->
        inc_by s ((Expr_LitInt j)::is)
    | [Expr_LitInt l] -> Some (Z.of_string l)
    | _ -> None

  let is_slice sels w =
    match sels with
    | [i] -> Some (Slice_LoWd(mul_int i w,w))
    | (Expr_LitInt i)::is ->
        let first = Z.of_string i in
        (match inc_by (Z.one) sels with
        | Some last ->
            let diff = (Z.add (Z.sub last first) Z.one) in
            let width = mul_int (expr_of_Z diff) w in
            let lo = mul_int (expr_of_Z first) w in
            Some (Slice_LoWd(lo, width))
        | _ -> None)
    | _ -> None

  let is_const w =
    match w with Expr_LitInt _ -> true | _ -> false

  let force_const w =
    match w with Expr_LitInt i -> int_of_string i | _ -> failwith ""

  let rec push_select elems w x sels st =
    match x with
    | Expr_TApply (FIdent ("append_bits", 0), [wr;wl], [r;l])
        when List.for_all (fun i -> check_leq (mul_int w (add_int i (Expr_LitInt "1"))) wl) sels &&
          is_div wr w && is_div wl w ->
            let elems = sub_int elems (div_int wr w) in
            push_select elems w l sels st
    | Expr_TApply (FIdent ("append_bits", 0), [wr;wl], [r;l])
        when List.for_all (fun i -> check_leq wl (mul_int w i)) sels && is_div wl w && is_div wr w ->
          let shift = div_int wl w in
          let sels = List.map (fun i -> sub_int i shift) sels in
          let elems = sub_int elems (div_int wl w) in
          push_select elems w r sels st
    | Expr_TApply (FIdent ("append_bits", 0), [wr;wl], [r;l]) when wr = wl ->
        let elems = div_int elems (expr_of_int 2) in
        shuffle_vec elems w r l sels

    (* Comps *)
    | Expr_TApply (FIdent (("sle_vec"|"eq_vec"|"slt_vec") as f, 0), ([_;w] as tes), [l;r;n]) when n = elems ->
        let l = push_select elems w l sels st in
        let r = push_select elems w r sels st in
        Expr_TApply (FIdent (f, 0), tes, [l;r;n])
    (* Binops *)
    | Expr_TApply (FIdent (("add_vec"|"sub_vec"|"mul_vec"|"asr_vec"|"lsr_vec"|"lsl_vec") as f, 0), tes, [l;r;n]) when n = elems ->
        let l = push_select elems w l sels st in
        let r = push_select elems w r sels st in
        Expr_TApply (FIdent (f, 0), tes, [l;r;n])
    (* Casts *)
    | Expr_TApply (FIdent (("trunc_vec"|"zcast_vec"|"scast_vec"), 0), [n;nw;ow], [x;n';nw']) when nw = ow ->
        push_select elems ow x sels st
    | Expr_TApply (FIdent (("trunc_vec"|"zcast_vec"|"scast_vec") as f, 0), [n;nw;ow], [x;n';nw']) when n = elems ->
        let x = push_select elems ow x sels st in
        Expr_TApply (FIdent (f, 0), [n;nw;ow], [x;n';nw'])
    (* Ternary *)
    | Expr_TApply (FIdent ("ite_vec", 0), tes, [c;l;r;n]) when n = elems ->
        let c = push_select elems (expr_of_int 1) c sels st in
        let r = push_select elems w r sels st in
        let l = push_select elems w l sels st in
        Expr_TApply (FIdent ("ite_vec", 0), tes, [c;l;r;n])

    (* Replicate, given same element count no difference in result *)
    | Expr_TApply (FIdent ("replicate_bits", 0), tes, [_;n]) when n = elems ->
        x

    (* Slice from 0 to some width is redundant, just slice full expression directly *)
    | Expr_Slices (x, [Slice_LoWd(lo, wd)]) when is_div lo w ->
        let offset = div_int lo w in
        let sels = List.map (add_int offset) sels in
        let wd = width_of_expr x st in
        let elems = div_int (expr_of_int wd) w in
        push_select elems w x sels st

    (* Nested selects, easy case of matching element widths *)
    | Expr_TApply (FIdent ("select_vec", 0), [ins'; outs'; w'], [x; Expr_LitBits sels']) when is_const_sels sels && w = w' ->
        let sels = force_const_sels sels in
        let sels' = parse_sels sels' in
        let res = List.map (List.nth sels') sels in
        let res = List.map expr_of_int res in
        push_select ins' w x res st

    (* Acceptable result, consider possible slice reduction *)
    | Expr_Var v ->
        (match is_slice sels w with
        | Some s -> Expr_Slices(Expr_Var v, [s])
        | _ -> select_vec elems w x sels)
    (* Evaluate the select given a constant expression *)
    | Expr_LitBits x when is_const_sels sels && is_const w ->
        let sels = force_const_sels sels in
        let w = force_const w in
        Expr_LitBits (apply_sels x w sels)

    (* Failure case, wasn't able to reduce *)
    | _ ->
        (*Printf.printf "push_select: %s\n" (pp_expr x);*)
        select_vec elems w x sels

  class cleanup st = object
    inherit Asl_visitor.nopAslVisitor
    method !vexpr e =
      (match e with
      | Expr_TApply (FIdent ("select_vec", 0), [ins; outs; w], [x;Expr_LitBits sels]) ->
          let sels = parse_sels sels in
          let sels = List.map (fun i -> expr_of_int i) sels in
          ChangeDoChildrenPost(push_select ins w x sels st, fun e -> e)
      | _ -> DoChildren)
  end

  let run (s: stmt list) env : (bool * stmt list) =
    let tys = Dis_tc.LocalVarTypes.run [] [] s in
    let st = { types = tys ; env ; iterations = Expr_LitInt "0" ; ld = Bindings.empty ; vars = Bindings.empty } in
    try
      let res = walk s tys env in
      let res = visit_stmts (new cleanup st) res in
      (true,res)
    with e ->
      (*let m = Printexc.to_string e in
      Printf.printf "\nVec Failure: %s\n" m;*)
      (false,s)

end
