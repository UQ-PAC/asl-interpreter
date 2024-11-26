open Asl_utils
open AST
open Asl_visitor
open Symbolic
open Value

let is_int = function Expr_LitInt _ -> true | _ -> false

(* Operations that are applied bitwise. *)
let bit_ops = [
  ("not_bool", "not_bits");
  ("and_bool", "and_bits");
  ("or_bool",  "or_bits");
  ("not_bits", "not_bits");
  ("and_bits", "and_bits");
  ("or_bits",  "or_bits");
  ("eor_bits", "eor_bits");
]

(* Operations that are applied element wise, with a element
   count argument in the final position. *)
let elem_ops = [
  ("add_bits",  "add_vec");
  ("sub_bits",  "sub_vec");
  ("mul_bits",  "mul_vec");
  ("sdiv_bits", "sdiv_vec");
  ("sle_bits",  "sle_vec");
  ("slt_bits",  "slt_vec");
  ("eq_bits",   "eq_vec");
  ("asr_bits",  "asr_vec");
  ("lsr_bits",  "lsr_vec");
  ("lsl_bits",  "lsl_vec");
  ("ite",       "ite_vec");
  ("BFMul",     "bf_mul_vec");
  ("BFAdd",     "bf_add_vec");
]

(* Operations expecting an additional, final scalar argument. *)
let sv_final_ops = [
  ("FPAdd",       "fp_add_vec");
  ("FPSub",       "fp_sub_vec");
  ("FPMul",       "fp_mul_vec");
  ("FPDiv",       "fp_div_vec");
  ("FPMulAdd",    "fp_mul_add_vec");
  ("FPSqrt",      "fp_sqrt_vec");
  ("FPMax",       "fp_max_vec");
  ("FPMaxNum",    "fp_max_num_vec");
  ("FPMin",       "fp_min_vec");
  ("FPMinNum",    "fp_min_num_vec");
  ("FPMulX",      "fp_mulx_vec");
  ("FPMulAddH",   "fp_mul_addh_vec");
  ("FPCompareEQ", "fp_cmp_eq_vec");
  ("FPCompareGE", "fp_cmp_ge_vec");
  ("FPCompareGT", "fp_cmp_gt_vec");
  ("FPRSqrtEstimate", "fpr_sqrt_est_vec");
  ("ZeroExtend",  "zcast_vec");
  ("SignExtend",  "scast_vec");
  ("trunc",       "trunc_vec");
]

(* Trivial vector operations, with a iteration count as the final argument. *)
let vec_ops = List.map snd elem_ops
(* Subset of vector operations that perform a size cast. *)
let size_cast_vec_ops = ["zcast_vec"; "scast_vec"; "trunc_vec"]
(* Vector operations with an iteration and final scalar argument. *)
let sv_final_vec_ops = (List.map snd sv_final_ops)
(* Vector reduce operations. *)
let reduce_ops = ["reduce_add" ; "reduce_eor"]

(* Normalise for loops, such that:
  - Iterate up from 0 to a fixed value
  - Recognise variables that can be derived from the loop variable
    and rephrase accordingly.

  TODO: Extend to support mod.
*)
module LoopNorm = struct
  let error m =
    failwith ("LoopNorm: " ^ m)

  let log m =
    if false then Printf.printf "LoopNorm: %s\n" m

  (*
    Map all values to a base value and multiples
    of the current loop depth. Otherwise, simply mark as Top.
   *)
  type abs =
    Index of sym * sym list |
    Top

  let is_index = function Index _ -> true | _ -> false
  let is_const = function
    | Index (b,m) -> List.for_all (fun e -> e = sym_of_int 0) m
    | _ -> false
  let is_complex i = is_index i && not (is_const i)

  let pp_bm (b,m) = "(" ^ pp_sym b ^ ", " ^ Utils.pp_list pp_sym m ^ ")"
  let pp_abs a =
    match a with
    | Index (b,m) -> "Index" ^ pp_bm (b,m)
    | Top -> "Top"

  type st = {
    vars: (sym * sym list) Bindings.t;
    next: int;
    iters: sym list;
    ivars: ident list;
  }

  (* Map an abstract point back to an expression *)
  let rec generate_expr base mults ivars loc =
    match mults, ivars with
    | [], [] -> base
    | s::mults, v::ivars ->
        sym_add_int loc (sym_mul_int loc (Exp (Expr_Var v)) s) (generate_expr base mults ivars loc)
    | _ -> error "Mismatched mult and inductive vars"

  let rec get_max base mults iters loc =
    match mults, iters with
    | [], [] -> base
    | s::mults, i::iters ->
        sym_add_int loc (sym_mul_int loc (sym_sub_int loc i (sym_of_int 1)) s) (get_max base mults iters loc)
    | _ -> error "Mismatched mult and iteration count"

  let expr_of_abs st loc b m = sym_expr (generate_expr b m st.ivars loc)

  let distrib_op f l r  =
    match l, r with
    | Index (b,m), Index (b',m') -> Index (f b b', List.map2 f m m')
    | _ -> Top

  let map_op f l =
    match l with
    | Index (b,m) -> Index (f b, List.map f m)
    | _ -> Top

  (* State Variable Operations *)
  let decl st v a =
    match Bindings.find_opt v st.vars with
    | Some _ -> error "Redecl"
    | None ->
        match a with
        | Index(b,m) -> {st with vars = Bindings.add v (b,m) st.vars}
        | _ -> st
  let assign st v a =
    match a with
    | Index(b,m) -> {st with vars = Bindings.add v (b,m) st.vars}
    | _ -> {st with vars = Bindings.remove v st.vars}
  let load st v =
    match Bindings.find_opt v st.vars with
    | Some (b,m) -> Index (b,m)
    | _ -> Top
  let fresh_ivar st =
    let n = Ident ("Loop_" ^ string_of_int st.next) in
    (n, {st with next = st.next + 1})

  let padding st = List.map (fun _ -> sym_of_int 0) st.iters

  (* State Join *)
  let join tst fst =
    let vars = Bindings.merge (fun k v1 v2 ->
      match v1, v2 with
      | Some v1, Some v2 when v1 = v2 -> Some v1
      | _ -> None) tst.vars fst.vars in
    { fst with vars }

  let is_val s =
    match s with Val _ -> true | _ -> false

  (* Loop Entry TF *)
  let enter_loop st var start dir stop loc =
    let start = sym_of_expr start in
    let stop = sym_of_expr stop in
    assert (is_val start && is_val stop);
    (* Create an inductive var *)
    let (ivar,st) = fresh_ivar st in
    let ivars = ivar::st.ivars in
    (* Determine the iterations of this loop *)
    let iter = match dir with
    | Direction_Up   -> sym_add_int loc (sym_sub_int loc stop start) (sym_of_int 1)
    | Direction_Down -> sym_add_int loc (sym_sub_int loc start stop) (sym_of_int 1) in
    let iters = iter::st.iters in
    (* Create a point for the old inductive variable *)
    let abs = match dir with
    | Direction_Up   -> (start, (sym_of_int 1)::(padding st))
    | Direction_Down -> (start, (sym_of_int (-1))::(padding st)) in
    (* Pad out the existing variables and add the old inductive variable *)
    let vars = Bindings.map (fun (b,m) -> (b,(sym_of_int 0)::m)) st.vars in
    let vars = Bindings.add var abs vars in
    (* Generate bounds for the new loop *)
    let stop = sym_expr (sym_sub_int loc iter (sym_of_int 1)) in
    (ivar, stop, { st with vars ; iters ; ivars })

  (* Loop Exit TF *)
  let exit_loop st loc =
    match st.iters, st.ivars with
    | i::iters, _::ivars ->
        let vars = Bindings.map (function
        | (b,m::ms) -> (sym_add_int loc b (sym_mul_int loc i m),ms)
        | _ -> error "Mismatched iteration count and factor in loop exit"
        ) st.vars in
        { st with vars ; iters ; ivars }
    | _ -> error "Mismatched iteraton count and inductive vars in loop exit"

  let div_test loc e s =
    match sym_zrem_int loc e s with
    | Val (VInt i) -> i = Z.zero
    | _ -> false

  (* Expression TF *)
  let tf_prim st f i tes es loc =
    match f, i, tes, es with
    | "add_int", 0, [], [l;r] ->
        distrib_op (sym_add_int loc) l r
    | "sub_int", 0, [], [l;r] ->
        distrib_op (sym_sub_int loc) l r
    | "mul_int", 0, [], [l;(Index(b,_) as r)] when is_const r ->
        map_op (sym_mul_int loc b) l
    | "mul_int", 0, [], [(Index(b,_) as r);l] when is_const r ->
        map_op (sym_mul_int loc b) l
    (* Support zdiv if all values divide perfectly *)
    | "zdiv_int", 0, [], [Index(b,m) as l;(Index(b',_) as r)] when is_const r ->
        if List.for_all (fun i -> div_test loc i b') (b::m) then
          map_op (fun v -> sym_zdiv_int loc v b') l
        else
          Top
    (* Support frem if all values are within bound *)
    | "frem_int", 0, [], [Index(b,m);(Index(b',_) as r)] when is_const r ->
        let max = get_max b m st.iters loc in
        (match sym_lt_int loc max b' with
        | Val (VBool true) -> Index(b,m)
        | _ -> Top)

    (* Expected uses of loop index *)
    | "Elem.set", _, _, _
    | "Elem.read", _, _, _
    (* Shift by index, can't do much with this *)
    | "LSL", _, _, _ -> Top

    | _ ->
        if List.exists is_complex es then log @@ "Precision loss for " ^ f ^ " " ^ Utils.pp_list pp_abs es;
        Top

  let rec tf st loc e =
    match e with
    | Expr_Var v -> load st v
    | Expr_LitInt i -> Index (sym_of_expr e, padding st)
    | Expr_TApply (FIdent (f, i), tes, es) ->
        tf_prim st f i tes (List.map (tf st loc) es) loc
    (* Ignore these *)
    | Expr_LitBits _
    | Expr_Array   _
    | Expr_Field   _
    | Expr_Slices  _ -> Top
    (* Log otherwise *)
    | _ -> log @@ "Unknown expr: " ^ pp_expr e; Top

  class subst st loc = object
    inherit nopAslVisitor
    method! vexpr e =
      match tf st loc e with
      | Index (b,m) -> ChangeTo ( expr_of_abs st loc b m )
      | _ -> DoChildren
  end

  let subst_stmt st loc s = visit_stmt_single (new subst st loc) s
  let subst_expr st loc s = visit_expr (new subst st loc) s

  let rec walk st s =
    List.fold_left (fun (acc,st) stmt ->
      match stmt with
      (* Local variable tracking *)
      | Stmt_VarDecl(ty, v, e, loc)
      | Stmt_ConstDecl(ty, v, e, loc) ->
          let stmt = subst_stmt st loc stmt in
          let st = decl st v (tf st loc e) in
          (acc@[stmt], st)
      | Stmt_Assign(LExpr_Var v, e, loc) ->
          let stmt = subst_stmt st loc stmt in
          let st = assign st v (tf st loc e) in
          (acc@[stmt], st)
      (* Default, state preserving stmt *)
      | Stmt_Assert _
      | Stmt_Assign  _
      | Stmt_VarDeclsNoInit _
      | Stmt_TCall _ ->
          let stmt = subst_stmt st (get_loc stmt) stmt in
          (acc@[stmt], st)
      (* Nested stmts *)
      | Stmt_For(var, start, dir, stop, body, loc) ->
          let (var',stop',st) = enter_loop st var start dir stop loc in
          let (body',st) = fp st body loc in
          let st = exit_loop st loc in
          (acc@[Stmt_For(var',Expr_LitInt "0",Direction_Up,stop',body', loc)], st)
      | Stmt_If(c, t, [], f, loc) ->
          let c = subst_expr st loc c in
          let (t,tst) = walk st t in
          let (f,fst) = walk {st with next = tst.next} f in
          let st = join tst fst in
          (acc@[Stmt_If(c, t, [], f, loc)], st)
      | _ -> error @@ "Unknown stmt: " ^ pp_stmt stmt
    ) ([],st) s

  and fp st s loc =
    log "Performing FP\n";
    (* Do one walk of the loop body *)
    let (s',st') = walk st s in
    (* Perform the join, test if we have a fixed-point *)
    let repeat = ref false in
    let vars = Bindings.merge (fun k v1 v2 ->
      match v1, v2 with
      (* If equal, fixed *)
      | Some v1, Some v2 when v1 = v2 ->
          log @@ "Equivalent " ^ pprint_ident k ^ " - " ^ pp_bm v1;
          Some v1
      (* Given distinct values, consider the loop effects *)
      | Some (b1,m1::ms1), Some (b2,m2::ms2) ->
          (* If mult factors are the same and the value is just offset by
             a single iteration, then this is actually a fixed-point *)
          if b2 = sym_add_int loc b1 m1 && ms1 = ms2 && m1 = m2 then begin
            log @@ "Stable " ^ pprint_ident k;
            v1
          (* If mult factors are the same and the current loop is 0,
             guess a value to produce a 'join'. Guess is the difference
             in base values as the loop mult *)
          end else if m1 = sym_of_int 0 && ms1 = ms2 && m1 = m2 then begin
            log @@ "Repeating, guess for " ^ pprint_ident k;
            repeat := true;
            Some (b1,(sym_sub_int loc b2 b1)::ms1)
          (* Otherwise, can't unify these *)
          end else begin
            log @@ "Repeating, can't unify " ^ pprint_ident k;
            repeat := true;
            None
          end
      (* Value went to top, need to clear it and try again *)
      | Some _, _ ->
          log @@ "Repeating, modified " ^ pprint_ident k;
          repeat := true;
          None
      (* Nothing else makes sense *)
      | _ -> None) st.vars st'.vars in
    (* Try again with the join or return *)
    let st = {st' with vars} in
    if !repeat then fp st s loc
    else (s',st)

  let do_transform s =
    let st = { vars = Bindings.empty ; next = 0 ; iters = [] ; ivars = [] } in
    let (s,_) = walk st s in
    s

end

module Symbol = struct
  type sym = expr

  (****************************************************************
   * Symbolic Helpers
   ****************************************************************)

  let cvt_bool_bv b =
    match b with
    | Expr_Var (Ident "TRUE") -> Expr_LitBits "1"
    | Expr_Var (Ident "FALSE") -> Expr_LitBits "0"
    | _ -> Expr_TApply (FIdent("cvt_bool_bv", 0), [], [b])

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

  let zdiv_int a b =
    match a, b with
    | Expr_LitInt a, Expr_LitInt b -> Expr_LitInt (Z.to_string (Z.div (Z.of_string a) (Z.of_string b)))
    | a, Expr_LitInt "1" -> a
    | a, Expr_LitInt "-1" -> mul_int a b
    | _ -> Expr_TApply(FIdent("zdiv_int",0), [], [a;b])

  let mod_int a b =
    match a, b with
    | Expr_LitInt a, Expr_LitInt b -> Expr_LitInt (Z.to_string (Z.rem (Z.of_string a) (Z.of_string b)))
    | _, Expr_LitInt "1"
    | _, Expr_LitInt "-1" -> Expr_LitInt "0"
    | _ -> Expr_TApply(FIdent("zrem_int",0), [], [a;b])

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

  let concat_bits ls =
    let body = fun (w,x) (yw,y) -> let b = append_bits w yw x y in (add_int w yw,b) in
    match List.rev ls with
    | x::xs -> let (_,r) = List.fold_left body x xs in r
    | _ -> failwith "concat"

  let expr_is_int e i =
    match e with
    | Expr_LitInt s -> int_of_string s = i
    | _ -> false

  let replicate elems elemw x =
    match elems, x with
    | i, _ when expr_is_int i 1 -> x
    | Expr_LitInt i, Expr_LitBits b -> Expr_LitBits (String.concat "" (List.init (int_of_string i) (fun _ -> b)))
    | _ -> Expr_TApply(FIdent("replicate_bits", 0), [elemw; elems], [x; elems])

  let is_factor e f =
    expr_is_int (mod_int e f) 0

end

module LoopOpt = struct
  open Symbol

  let rec triv_sel i is =
    match is with
    | j::is when i = j -> triv_sel (i+1) is
    | [] -> true
    | _ -> false


  let rec select_veci elems sels elemw e sel =
    match e, sel with
    | _, _ when elems = sels && triv_sel 0 sel -> e
    | _, i::is when List.length is > 0 && triv_sel i sel && Z.rem (Z.of_int i) (Z.of_int (List.length sel)) = Z.zero && is_factor elems sels ->
        let elems = zdiv_int elems sels in
        let elemw = mul_int sels elemw in
        let sels = expr_of_int 1 in
        let sel = [i / List.length sel] in
        select_veci elems sels elemw e sel

    | _, i::is when List.length is > 0 && List.for_all (fun j -> i = j) is ->
        let e = select_veci elems (expr_of_int 1) elemw e [i] in
        replicate sels elemw e

    (* Element-wise vector operations *)
    | Expr_TApply(FIdent("ite_vec" as f,0), [iters;w], c::es), _ when is_factor elemw w ->
        let n = zdiv_int elemw w in
        let iters = mul_int n sels in
        let (es,_) = Utils.getlast es in
        let es = List.map (fun e -> select_veci elems sels elemw e sel) es in
        let c = select_veci elems sels n c sel in
        Expr_TApply(FIdent(f,0), [iters;w], c::es@[iters])
    | Expr_TApply(FIdent(f,0), [iters;w], es), _ when List.mem f vec_ops && is_factor iters elems  ->
        let n = zdiv_int iters elems in
        let iters = mul_int n sels in
        let (es,_) = Utils.getlast es in
        let es = List.map (fun e -> select_veci elems sels (mul_int n w) e sel) es in
        Expr_TApply(FIdent(f,0), [iters;w], es@[iters])
    (* Cast operations *)
    | Expr_TApply(FIdent(f,0), elems'::ow::tes, es), _ when List.mem f size_cast_vec_ops && is_factor elems' elems ->
        let subelems = mul_int (zdiv_int elems' elems) sels in
        let elemw = mul_int (zdiv_int elems' elems) ow in
        let (es,_) = Utils.getlast es in
        let (es,l) = Utils.getlast es in
        let es = List.map (fun e -> select_veci elems sels elemw e sel) es in
        Expr_TApply(FIdent(f,0), subelems::ow::tes, es@[l;subelems])

    | Expr_TApply(FIdent("select_vec",0), [elems'; sels'; elemw'], [e; Expr_TApply(FIdent("int_list", 0), [], sel')]), _
        when is_factor elemw elemw' ->
          let n = zdiv_int elemw elemw' in
          let sels = mul_int sels n in
          let sel = List.flatten (List.map (fun s ->
            let n = int_of_expr n in
            Utils.take n (Utils.drop (s * n) sel')
          ) sel) in
          select_vec elems' sels elemw' e sel

    (* Replicate, given same element count no difference in result *)
    | Expr_TApply (FIdent ("replicate_bits", 0), [_; reps], [e;_]), _ when reps = elems ->
        e

    (* Slice from 0 to some width is redundant, just slice full expression directly *)
    (*| Expr_Slices (e, [Slice_LoWd(lo, wd)]), _ when is_factor lo elemw ->
        let offset = zdiv_int lo elemw in
        let sel = List.map (fun e -> add_int offset (expr_of_int e)) sel in
        select_vec elems sels elemw e sel *)

    | Expr_LitBits bv, _ ->
        let w = int_of_expr elemw in
        let ins = (String.length bv) / w in
        let vals = List.init ins (fun i -> String.sub bv (i * w) w) in
        let vals = List.rev vals in
        let res = List.map (fun i -> List.nth vals i) sel in
        let res = List.rev res in
        Expr_LitBits (String.concat "" res)

    | Expr_Slices _, _
    | Expr_Var _, _ ->
        Expr_TApply(FIdent("select_vec",0), [elems; sels; elemw], [e; Expr_TApply (FIdent ("int_list", 0), [], List.map expr_of_int sel)])
    | _ ->
        (*Printf.printf "Selecti: %s %s %s %s %s\n" (pp_expr elems) (pp_expr sels) (pp_expr elemw) (pp_expr e) (Utils.pp_list string_of_int sel);*)
        Expr_TApply(FIdent("select_vec",0), [elems; sels; elemw], [e; Expr_TApply (FIdent ("int_list", 0), [], List.map expr_of_int sel)])

  and select_vec elems sels elemw e sel =
    if List.for_all is_int sel then
      select_veci elems sels elemw e (List.map int_of_expr sel)
    else begin
      (*Printf.printf "Select: %s %s %s %s %s\n" (pp_expr elems) (pp_expr sels) (pp_expr elemw) (pp_expr e) (Utils.pp_list pp_expr sel);*)
      Expr_TApply(FIdent("select_vec",0), [elems; sels; elemw], [e; Expr_TApply (FIdent ("int_list", 0), [], sel)])
    end

  (* For a trivial update:
      - all positions must be integers
      - the original expression must be fully over-written
      - all writes must be unique
  *)
  let trivial_update i is =
    triv_sel i (List.sort (-) is)
  let update_vec elems sels elemw e sel a =
    match sels with
    | _ when elems = sels && List.for_all is_int sel && trivial_update 0 (List.map int_of_expr sel) ->
        select_vec elems sels elemw a sel
    | _ ->
        (*Printf.printf "Update: %s %s %s %s %s %s\n" (pp_expr elems) (pp_expr sels) (pp_expr elemw) (pp_expr e) (Utils.pp_list pp_expr sel) (pp_expr a);*)
        Expr_TApply(FIdent("update_vec",0), [elems; sels; elemw], [e; Expr_TApply (FIdent ("int_list", 0), [], sel);a])

  class opt = object
    inherit nopAslVisitor
    method !vexpr e =
      (match e with
      | Expr_TApply(FIdent("select_vec",0), [elems; sels; elemw], [e;Expr_TApply (FIdent ("int_list", 0), [], is)]) ->
          ChangeDoChildrenPost(select_vec elems sels elemw e is,fun e -> e)
      | Expr_TApply(FIdent("update_vec",0), [elems; sels; elemw], [e;Expr_TApply (FIdent ("int_list", 0), [], is);a]) ->
          ChangeDoChildrenPost(update_vec elems sels elemw e is a,fun e -> e)
      | _ -> DoChildren)
  end

  let do_transform s =
    visit_stmts (new opt) s

end

(*
  A simple pass to sanity check the produced select and update operations.
  Ideally, all selects should operate over a constant position argument and update
  operations should be fully eliminated.
*)
module LoopLower = struct

  class lower = object
    inherit nopAslVisitor
    method !vexpr e =
      match e with
      | Expr_TApply(FIdent("select_vec",0), [elems; sels; elemw], [e'; Expr_TApply (FIdent ("int_list", 0), [], is)]) ->
          if List.for_all is_int is then
            let is = List.map (fun e -> (Primops.({n = 32 ; v = Z.of_int (int_of_expr e)}))) is in
            let bv = List.fold_left Primops.prim_append_bits Primops.empty_bits (List.rev is) in
            let m = Z.format ("%0" ^ string_of_int bv.n ^ "b") bv.v in
            ChangeDoChildrenPost (Expr_TApply(FIdent("select_vec",0), [elems; sels; elemw], [e'; Expr_LitBits m]), fun e -> e)
          else
            failwith @@ "LoopLower: Cannot lower non-constant select_vec position argument " ^ pp_expr e
      | Expr_TApply(FIdent("update_vec",0), _, _) ->
          failwith @@ "LoopLower: update_vec operation left in body " ^ pp_expr e
      | _ -> DoChildren
  end

  let do_transform = visit_stmts (new lower)

end

(*
  Vectorize loops, without much concern for optimal representation.
  Just focus on the correctness of the transform, we can cleanup later.
 *)
module Vectorize = struct
  open Symbol

  let elist i fn =
    List.init (int_of_expr i) (fun i -> fn (expr_of_int i))
  let mk_int_list l =
    Expr_TApply (FIdent("int_list",0), [], l)

  let rec triv_sel i is =
    match is with
    | j::is when expr_is_int j i -> triv_sel (i+1) is
    | [] -> true
    | _ -> false

  let select_vec elems sels elemw e sel =
    match sel with
    | Expr_TApply(FIdent("int_list", 0), [], is) when elems = sels && triv_sel 0 is -> e
    | _ -> Expr_TApply(FIdent("select_vec", 0), [elems; sels; elemw], [e; sel])

  let update_vec elems sels elemw e sel arg =
    Expr_TApply(FIdent("update_vec", 0), [elems; sels; elemw], [e; sel; arg])

  let error m =
    failwith @@ "LoopClassify: " ^ m

  (****************************************************************
   * Abstract Domain
   ****************************************************************)

  type abs =
    (* A single value expression, equivalent across iters *)
    Value of sym |
    (* A parallel write operation *)
    Map of string * sym list * abs list |
    (* A value directly derived from the loop index, as a base and multiplier *)
    Index of (sym * sym) list |
    (* Bot *)
    Undecl

  let rec pp_abs e =
    match e with
    | Value e        -> "Value(" ^ pp_expr e ^ ")"
    | Map(f,tes,ves) -> "Map(" ^ f ^ ", " ^ Utils.pp_list pp_expr tes ^ ", " ^ Utils.pp_list pp_abs ves ^ ")"
    | Index l        -> "Index(" ^ Utils.pp_list (fun (e,m) -> pp_expr e ^ "," ^ pp_expr m) l ^ ")"
    | Undecl         -> "Undecl"

  let rec deps e =
    match e with
    | Value e        -> fv_expr e
    | Map(f,tes,ves) -> IdentSet.union (unionSets (List.map fv_expr tes)) (unionSets (List.map deps ves))
    | Index l     -> unionSets (List.map (fun (b,m) -> IdentSet.union (fv_expr b) (fv_expr m)) l)
    | Undecl         -> IdentSet.empty

  let is_val e =
    match e with
    | Value _ -> true
    | _ -> false

  let force_val e =
    match e with
    | Value e -> e
    | _ -> error @@ "force_val: " ^ pp_abs e

  let is_index e =
    match e with
    | Index _ -> true
    | _ -> false

  let force_index e =
    match e with
    | Index e -> e
    | _ -> error @@ "force_index: " ^ pp_abs e

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
    | Direction_Up -> Index[start, expr_of_Z Z.one]
    | Direction_Down -> Index[start, expr_of_Z (Z.neg Z.one)] in
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

  let type_of_expr st e =
    match Dis_tc.infer_type e st.types st.env with
    | Some t -> t
    | None -> error @@ "type_of_expr: Unknown type " ^ (pp_expr e)

  let width_of_expr st e =
    match type_of_expr st e with
    | Type_Bits e -> e
    | Type_Constructor (Ident "boolean") -> expr_of_int 1
    | Type_Register (w,_) -> expr_of_int (int_of_string w)
    | t -> failwith @@ "width_of_expr: Unknown width " ^ (pp_expr e) ^ " :: " ^ pp_type t

  (****************************************************************
   * Phase 1: Produce a candidate loop summary
   ****************************************************************)

  (* Construct a vector read *)
  let read_vec elems iters elemw e sels =
    Map ("read_vec", [elems; iters; elemw], [e; sels])

  (* Construct a vector write *)
  let write_vec elems iters elemw e sels a =
    match e, sels with
    | Map("write_vec", [elemsi;itersi;elemwi], [e; Index[bi,mi]; ai]), Index[bo,mo]
        when expr_is_int bi 0 && expr_is_int bo 1 && expr_is_int mi 2 && expr_is_int mo 2 &&
          elemsi = elems && elemwi = elemw && itersi = iters ->
            let arg = Map("append_bits", [elemw;elemw], [a;ai]) in
            let elemw = mul_int elemw mi in
            let elems = zdiv_int elems mi in
            let sel = Index[bi,bo] in
            Map ("write_vec", [elems; iters; elemw], [e; sel; arg])
    | _ -> Map("write_vec", [elems; iters; elemw], [e; sels; a])

  (* Construct an ITE expression between a & b, conditional on c.
     Requires a & b to be bvs of width w. *)
  let ite_vec (iters: expr) (w: expr) (c: abs) (a: abs) (b: abs) =
    match c, a, b with
    (* Trivial conditions to collapse an ite *)
    | _, a, b when a = b -> a
    | Value (Expr_Var (Ident "TRUE")), a, b -> a
    | Value (Expr_Var (Ident "FALSE")), a, b -> b
    | c, Value (Expr_Var (Ident "TRUE")), Value (Expr_Var (Ident "FALSE")) -> c
    (* This is a trivial result, constant for all loop iterations *)
    | Value c, Value a, Value b ->
        Value (Expr_TApply(FIdent("ite",0), [w], [c;a;b]))
    (* Vector ite *)
    | _ -> Map ("ite", [w], [c;a;b])

  (* Construct a vector slice *)
  let slice_vec (iters: expr) (ow: expr) (e: abs) (lo: abs) (nw: abs)  =
    match e, lo, nw with
    (* Entirely constant, pass it through *)
    | Value e, Value lo, Value wd when wd = ow && expr_is_int lo 0 ->
        Value e
    | Value e, Value lo, Value wd ->
        Value (Expr_Slices(e, [Slice_LoWd(lo, wd)]))
    (* A truncate operation *)
    | Map _, Value lo, Value nw when expr_is_int lo 0 ->
        Map ("trunc", [ow; nw], [e; Value nw])
    (* A shift and truncate operation *)
    | Map _, Value lo, Value nw  ->
        let lo = cvt_int_bits lo ow in
        let e' = Map("asr_bits", [ow], [e; Value lo]) in
        Map ("trunc", [ow; nw], [e'; Value nw])
    (* Slice that can be converted to Elem.read *)
    | Value e, Index[b,m], Value wd
        when is_factor b wd && is_factor m wd && is_factor ow wd ->
          let elems = zdiv_int ow wd in
          let b = zdiv_int b wd in
          let m = zdiv_int m wd in
          read_vec elems iters wd (Value e) (Index[b,m])
    | a, b, c -> error @@ "slice_vec: " ^ Utils.pp_list pp_abs [a;b;c]

  (* Transfer function for a primitive application *)
  let tf_prim st f i tes es =
    match f, i, tes, es with
    (* Everything is constant, can skip *)
    | f, i, tes, es when List.for_all is_val es ->
        Value (Expr_TApply(FIdent(f,i), tes, List.map force_val es))

    (* Supported operations over Index expressions *)
    | "add_int", 0, [], [Index [base,mul];Value offset]
    | "add_int", 0, [], [Value offset;Index [base,mul]] ->
        Index [add_int base offset, mul]
    | "sub_int", 0, [], [Index [base,mul];Value offset] ->
        Index [sub_int base offset, mul]
    | "sub_int", 0, [], [Value offset;Index [base,mul]] ->
        Index [sub_int offset base, mul_int mul (Expr_LitInt "-1")]
    | "mul_int", 0, [], [Index [base,mul];Value offset]
    | "mul_int", 0, [], [Value offset;Index [base,mul]] ->
        Index [mul_int base offset, mul_int mul offset]
    | "int_list", 0, [], is when List.for_all is_index is ->
        Index (List.flatten (List.map force_index is))
    | "cvt_int_bits", 0, [w], [Index l; _] ->
        Map ("cvt_int_bits", [w], [Index l])

    (* Read Operations *)
    | "Elem.read", 0, [vecw ; elemw], [e; sel; _] when is_factor vecw elemw  ->
        read_vec (zdiv_int vecw elemw) (expr_of_int 1) elemw e sel
    | "select_vec", 0, [elems; sels; elemw], [e; sel] ->
        read_vec elems sels elemw e sel
    | "Elem.set", 0, [vecw ; elemw], [e; sel; _; arg] when is_factor vecw elemw ->
        write_vec (zdiv_int vecw elemw) (expr_of_int 1) elemw e sel arg
    | "update_vec", 0, [elems; sels; elemw], [e; sel; arg] ->
        write_vec elems sels elemw e sel arg
    | "replicate_bits", 0, [w; reps], [e; _] ->
        let sel = elist reps (fun _ -> expr_of_int 0) in
        let sel = mk_int_list sel in
        read_vec (expr_of_int 1) reps w e (Value sel)

    (* TODO: Doesn't seem to fit in any existing generalisation *)
    | "append_bits", 0, tes, es -> Map("append_bits", tes, es)

    (* Boolean Vector Operations *)
    | f, 0, tes, es when List.mem_assoc f bit_ops -> Map(f, tes, es)
    (* Element-wise Vector Operations *)
    | f, 0, tes, es when List.mem_assoc f elem_ops -> Map(f, tes, es)
    (* Element-wise + Scalar Arg Operations *)
    | f, 0, tes, es when List.mem_assoc f sv_final_ops -> Map(f, tes, es)
    (* Vec Ops *)
    | f, 0, tes, es when List.mem f vec_ops -> Map(f, tes, es)
    | f, 0, tes, es when List.mem f sv_final_vec_ops -> Map(f, tes, es)
    | f, 0, tes, es when List.mem f reduce_ops -> Map(f, tes, es)
    | _ -> error @@ "tf_prim: Unknown prim " ^ f ^ " " ^ Utils.pp_list pp_expr tes ^ " " ^ Utils.pp_list pp_abs es

  (* Transfer function for an expression *)
  let rec tf_expr st e =
    let iters = st.iterations in
    match e with
    | Expr_LitBits _ -> Value e
    | Expr_LitInt  _ -> Value e
    | Expr_Var v ->
        (match get_var v st with
        | Some abs -> abs
        | None -> Value e)
    | Expr_Array(e,i) ->
        (match tf_expr st e, tf_expr st i with
        | Value e, Value i -> Value (Expr_Array(e,i))
        | Value e, Index[b,m] -> Map ("array", [], [Value e; Index[b,m]])
        | e, i -> error @@ "tf_expr: Unsupported array op " ^ Utils.pp_list pp_abs [e;i])
    | Expr_TApply(FIdent(f,i), tes, es) ->
        let tes = List.map (tf_expr st) tes in
        if List.for_all is_val tes then
          let es = List.map (tf_expr st) es in
          tf_prim st f i (List.map force_val tes) es
        else
          error @@ "tf_expr: Loop defined type argument " ^ f ^ " " ^ Utils.pp_list pp_abs tes
    | Expr_Slices(e, [Slice_LoWd(lo,wd)]) ->
        let ow = width_of_expr st e in
        let e = tf_expr st e in
        let lo = tf_expr st lo in
        let wd = tf_expr st wd in
        slice_vec iters ow e lo wd
    | _ -> error @@ "tf_expr: Unknown expr " ^ pp_expr e

  (* Join states a & b given the condition cond. *)
  let join_st cond st1 st2 =
    let iters = st1.iterations in
    (* Merge loop defined constructs, assume they are defined
       on both paths. *)
    let ld = Bindings.merge (fun k l r ->
      match l, r with
      (* Same effect *)
      | Some l, Some r when l = r -> Some l
      | Some l, Some r ->
          let w = width_of_expr st1 (Expr_Var k) in
          Some (ite_vec iters w cond l r)
      | _ -> None) st1.ld st2.ld in
    (* Merge external constructs, support conditional effects *)
    let vars = Bindings.merge (fun k l r ->
      match l, r with
      (* Same effect *)
      | Some l, Some r when l = r -> Some l
      (* Conditional write *)
      | Some e, None ->
          let w = width_of_expr st1 (Expr_Var k) in
          Some (ite_vec iters w cond e (Value (Expr_Var k)))
      | None, Some e ->
          let w = width_of_expr st1 (Expr_Var k) in
          Some (ite_vec iters w cond (Value (Expr_Var k)) e)
      (* Conditional write *)
      | _ ->
          failwith @@ "Failed to join vars: " ^ pprint_ident k ^ ":" ^
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
    We attempt to show all externally scoped variables
    are only self-referential, i.e., there is no dependence relation
    between externally scoped variables.
    Once we know variables are at most self-referential, we determine the
    necessary reduction to capture their cumulative effects.
    This occurs in Phase 3.
  *)

  let pp_assign v d =
    pprint_ident v ^ " := " ^ pp_abs d

  (* Determine if the summary is valid:
      1. All constants are actually constant
      2. Modified variables are at most self-referential
   *)
  let validate_summary effects =
    (* Nested iteration to find cases of cross-references *)
    Bindings.iter (fun var def ->
      Bindings.iter (fun var' def' ->
        match var,def,var',def' with
        (* Ignore self *)
        | v,_,v',_ when v = v' -> ()
        (* Outer variable referenced by inner variable *)
        | v,d,v',d' when IdentSet.mem v (deps d') ->
            failwith @@ "Cross-reference: " ^ pp_assign v d ^ " && " ^
              pp_assign v' d'
        | _ -> ()
      ) effects
    ) effects

  (* Run the analysis from an initial state. *)
  let fixed_point init_st body =
    let cand_st = tf_stmts init_st body in
    let _ = validate_summary cand_st.vars in
    cand_st

  (****************************************************************
   * Phase 3: Cycle Reduction
   ****************************************************************)

  (*
    Convert abstract points into expressions that summarize the loop
    effects. Requires pattern matching on any cyclic definitions
    to identify a sound reduction.
  *)

  (*
    This is essentially the concretization function for an
    abstract element, converting it back into a valid expression.
  *)
  let rec unroll st a =
    let iters = st.iterations in
    match a with
    (* Replicated values *)
    | Value e       ->
        (match type_of_expr st e with
        | Type_Bits w -> replicate iters w e
        | t when t = type_bool -> replicate iters (expr_of_int 1) (cvt_bool_bv e)
        | t when t = type_integer -> mk_int_list (elist iters (fun _ -> e))
        | t -> error @@ "unroll: value with unexpected type: " ^ pp_expr e ^ " " ^ pp_type t)

    (* Boolean Vector Operations *)
    | Map(f,[],es) when List.mem_assoc f bit_ops ->
        Expr_TApply(FIdent(List.assoc f bit_ops,0), [iters], List.map (unroll st) es)
    (* Bit-wise Vector Operations *)
    | Map(f,[w],es) when List.mem_assoc f bit_ops ->
        Expr_TApply(FIdent(List.assoc f bit_ops,0), [mul_int iters w], List.map (unroll st) es)
    (* Element-wise Vector Operations *)
    | Map(f,[w],es) when List.mem_assoc f elem_ops ->
        Expr_TApply(FIdent(List.assoc f elem_ops,0), [iters; w], (List.map (unroll st) es)@[iters])
    (* Element-wise + Scalar Arg Operations *)
    | Map(f, tes, es) as abs when List.mem_assoc f sv_final_ops ->
        let (es,l) = Utils.getlast es in
        (match l with
        | Value l ->
            Expr_TApply(FIdent(List.assoc f sv_final_ops,0), iters::tes, (List.map (unroll st) es)@[l;st.iterations])
        | _ -> error @@ "unroll: sv_final_ops with final vector argument: " ^ pp_abs abs )

    (* Element-wise Vector Operations *)
    | Map(f, iters::tes, es) when List.mem f vec_ops ->
        let (es,_) = Utils.getlast es in
        let es = List.map (unroll st) es in
        let iters = mul_int st.iterations iters in
        Expr_TApply (FIdent(f,0), iters::tes, es@[iters])
    (* Element-wise + Scalar Arg Vector Operations *)
    | Map(f, iters::tes, es) as abs when List.mem f sv_final_vec_ops ->
        let (es,_) = Utils.getlast es in
        let (es,l) = Utils.getlast es in
        let es = List.map (unroll st) es in
        let iters = mul_int st.iterations iters in
        (match l with
        | Value l ->
            Expr_TApply (FIdent(f,0), iters::tes, es@[l;iters])
        | _ -> error @@ "unroll: sv_final_vec_ops with vector argument" ^ pp_abs abs)
    (* Vector Reduce Operations *)
    | Map(f, [iters;w], [e;b;_]) when List.mem f reduce_ops ->
        (* Unroll and slice out the parts of e we want *)
        let e = unroll st e in
        let b = unroll st b in
        let ew = mul_int iters w in
        (* One reduce per iteration *)
        let es = elist st.iterations (fun i ->
          let sel = mk_int_list [i] in
          let a = select_vec st.iterations (expr_of_int 1) ew e sel in
          let b = select_vec st.iterations (expr_of_int 1) w b sel in
          Expr_TApply(FIdent(f,0), [iters;w], [a;b;iters])) in
        let es = List.map (fun i -> (w,i)) es in
        concat_bits es

    (* Read Operations *)
    | Map("read_vec", [elems; _; elemw], [Value e; Index l]) ->
        let sel = unroll st (Index l) in
        let iters = mul_int (expr_of_int (List.length l)) iters in
        select_vec elems iters elemw e sel
    | Map("read_vec", [elems; _; elemw], [e; Value (Expr_TApply(FIdent("int_list",0), [], is))]) ->
        let e = unroll st e in
        let sel = elist st.iterations (fun i -> List.map (add_int (mul_int i elems)) is) in
        let sel = (List.flatten sel) in
        let elems = mul_int elems st.iterations in
        let iters = expr_of_int (List.length sel) in
        select_vec elems iters elemw e (mk_int_list sel)

    | Map("append_bits", [w1;w2], [e1;e2]) when w1 = w2 ->
        let e1 = unroll st e1 in
        let e2 = unroll st e2 in
        let w = mul_int st.iterations w1 in
        let e = append_bits w w e1 e2 in
        let sel = List.flatten (elist st.iterations (fun i -> [i; add_int st.iterations i])) in
        let sel = mk_int_list sel in
        let i = mul_int st.iterations (expr_of_int 2) in
        select_vec i i w1 e sel

    (* Array Loads *)
    | Map("array", [], [Value v; Index[b,m]]) ->
        let is = elist st.iterations (fun i -> add_int b (mul_int i m)) in
        let w = width_of_expr st (Expr_Array(v, expr_of_int 0)) in
        let z = List.map (fun i -> (w,Expr_Array(v, i))) is in
        concat_bits z

    (* Index unrolling *)
    | Index l   ->
        let is = elist iters (fun i -> List.map (fun (b,m) -> add_int b (mul_int i m)) l) in
        let is = List.flatten is in
        Expr_TApply(FIdent("int_list",0), [], is)
    | Map ("cvt_int_bits", [w], [Index l]) ->
        let is = elist iters (fun i -> List.map (fun (b,m) -> add_int b (mul_int i m)) l) in
        let is = List.flatten is in
        concat_bits (List.map (fun i -> (w, cvt_int_bits i w)) is)
    | a -> failwith @@ "unroll: " ^ pp_abs a


  let no_fv var abs = not (IdentSet.mem var (deps abs))

  let abs_leq pos pos' =
    match pos, pos' with
    | Index[Expr_LitInt b,Expr_LitInt m], Index[Expr_LitInt b',Expr_LitInt m'] ->
        Z.leq (Z.of_string b) (Z.of_string b') && Z.leq (Z.of_string m) (Z.of_string m')
    | _ -> false

  (* Ensure a vector write does not create a write-read dependency *)
  let rec no_write_read var pos abs =
    match abs with
    | Map("read_vec", _, [Value(Expr_Var var'); pos']) when var = var' -> abs_leq pos pos'
    | Map(f, tes, es) ->
        let tes = not (IdentSet.mem var (unionSets (List.map fv_expr tes))) in
        let es = List.for_all (no_write_read var pos) es in
        tes && es
    | _ -> no_fv var abs

  (* Ensure a vector write does not create a write-write dependency.
     Takes the position argument of an update_vec and ensures all locations
     are distinct.
   *)
  let no_write_write_dep sel =
    match sel with
    | Index l ->
        let fn = function (_,Expr_LitInt i) -> int_of_string i <> 0 | _ -> false in
        List.for_all fn l
    | _ -> false

  (* For a variable and abstract point, produce an expression equivalent to the
     parallel evaluation of the abstract point.
     Assumes we have established at most self reference. *)
  let summarize_assign st var abs =
    match abs with
    (* When not dependent on any loop written vars, simply build the operation. *)
    | Value e when not (IdentSet.mem var (deps abs)) -> e
    | _ when not (IdentSet.mem var (deps abs))->
        let e = unroll st abs in
        let wd = width_of_expr st e in
        let w = zdiv_int wd st.iterations in
        let lo = mul_int (sub_int st.iterations (expr_of_int 1)) w in
        Expr_Slices(e, [Slice_LoWd(lo,w)])
    (* Id *)
    | Value (Expr_Var a) when a = var -> Expr_Var a

    (* Vector update *)
    | Map ("write_vec", [elems; iters; elemw], [Value (Expr_Var var'); sel; arg])
        when var = var' && no_fv var sel && no_write_read var sel arg && no_write_write_dep sel ->
          let sel = unroll st sel in
          let arg = unroll st arg in
          let iters = mul_int iters st.iterations in
          update_vec elems iters elemw (Expr_Var var) sel arg

    (* Reduce Add/EOR *)
    | Map(("add_bits" | "eor_bits") as f, [w], [Value (Expr_Var var') ; e])
        when var' = var && not (IdentSet.mem var (deps e)) ->
          let e = unroll st e in
          let op = if f = "add_bits" then "reduce_add" else "reduce_eor" in
          Expr_TApply (FIdent(op,0), [st.iterations; w], [e ; Expr_Var var; st.iterations])
    | Map("ite", [w], [c; Map("eor_bits" as f, _, [Value (Expr_Var var') ; e]); Value (Expr_Var var'')])
        when var' = var && var'' = var && not (IdentSet.mem var (deps e)) ->
          let z = zeroes (mul_int st.iterations w) in
          let e = unroll st e in
          let c = unroll st c in
          let f = if f = "add_bits" then "reduce_add" else "reduce_eor" in
          let i = Expr_TApply (FIdent("ite_vec", 0), [st.iterations; w], [c ; e ; z ; st.iterations]) in
          Expr_TApply (FIdent(f,0), [st.iterations; w], [i;Expr_Var var;st.iterations])

    (* Signed Min : var <= e ? var : e *)
    | Map("ite", [w], [Map("sle_bits", _, [Value (Expr_Var var'); e]); Value (Expr_Var var''); e'])
        when var' = var'' && var = var' && e = e' && no_fv var e ->
          let e = unroll st e in
          Expr_TApply (FIdent("reduce_smin",0), [st.iterations; w], [e; Expr_Var var])
    (* Signed Max : e <= var ? var : e *)
    | Map("ite", [w], [Map("sle_bits", _, [e; Value (Expr_Var var')]); Value (Expr_Var var''); e'])
        when var' = var'' && var = var' && e = e' && no_fv var e ->
          let e = unroll st e in
          Expr_TApply (FIdent("reduce_smax",0), [st.iterations; w], [e; Expr_Var var])
    (* Unsigned Min : zcast var <= zcast e ? var : e *)
    | Map("ite", [w], [Map("sle_bits", _, [Value (Expr_TApply (FIdent("ZeroExtend", 0), _, [Expr_Var var';_])); Map("ZeroExtend", _, [e;_])]); Value (Expr_Var var''); e'])
        when var' = var'' && var = var' && e = e' && no_fv var e ->
          let e = unroll st e in
          Expr_TApply (FIdent("reduce_smin",0), [st.iterations; w], [e; Expr_Var var])
    (* Unsigned Max : zcast e <= zcast var ? var : e *)
    | Map("ite", [w], [Map("sle_bits", _, [Map("ZeroExtend", _, [e;_]); Value (Expr_TApply (FIdent("ZeroExtend", 0), _, [Expr_Var var';_]))]); Value (Expr_Var var''); e'])
        when var' = var'' && var = var' && e = e' && no_fv var e ->
          let e = unroll st e in
          Expr_TApply (FIdent("reduce_smax",0), [st.iterations; w], [e; Expr_Var var])

    (* Conditional Bit Set *)
    (*| Map("ite", tes, [c;Value t;Value f]) when var = Ident "FPSR" ->
        let ew = width_of_expr st t in
        let c = unroll st c in
        let w = width_of_expr st c in
        let test = Expr_TApply(FIdent("eq_bits", 0), [w], [c; zeroes w]) in
        Expr_TApply(FIdent("ite", 0), [ew], [test; f; t]) *)

    | _ -> error @@ "Failed to summarize " ^ pprint_ident var ^ " <- " ^ pp_abs abs

  (* Given a successful abstract representation of a loop, reduce its observable
     effects into a series of assignments.
   *)
  let loop_summary st loc =
    Bindings.fold (fun var abs acc ->
      let c = summarize_assign st var abs in
      let s = Stmt_Assign(LExpr_Var var, c, loc) in
      s::acc
    ) st.vars []

  (****************************************************************
   * Analysis Entry Point
   ****************************************************************)

  (* Reduce inner loops first *)
  let rec walk s types env : stmt list =
    List.fold_left (fun acc stmt ->
      match stmt with
      | Stmt_For(var, start, dir, stop, body, loc) ->
          let body = walk body types env in
          let st = init_state var start stop dir types env in
          let st' = fixed_point st body in
          let sum = loop_summary st' loc in
          let sum = LoopOpt.do_transform sum in
          acc@sum
      | Stmt_If(c, t, [], f, loc) ->
          let t = walk t types env in
          let f = walk f types env in
          acc@[Stmt_If(c, t, [], f, loc)]
      | _ -> acc@[stmt]) [] s

  let do_transform (s: stmt list) env : stmt list =
    let tys = Dis_tc.LocalVarTypes.run [] [] s in
    walk s tys env

end

let do_transform s env =
  try
    let s = Vectorize.do_transform s env in
    let s = LoopLower.do_transform s in
    (true,s)
  with e ->
    (*Printf.printf "\nVec Failure: %s\n" (Printexc.to_string e);*)
    (false,s)
