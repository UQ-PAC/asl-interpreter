open Asl_utils
open Asl_ast
open Utils

type taint = LiftTime | RunTime

let compare_taint a b =
  match a, b with
  | LiftTime, RunTime -> -1
  | RunTime, LiftTime -> 1
  | _, _ -> 0

let join_taint a b =
  match a, b with
  | LiftTime, LiftTime -> LiftTime
  | _, _ -> RunTime

let pp_taint t =
  match t with
  | LiftTime -> "LiftTime"
  | RunTime -> "RunTime"

let join_taint_l ts = List.fold_left join_taint LiftTime ts

module Sig = struct
  type t = (ident * taint list * taint list)
  let compare (fa,la,sa) (fb,lb,sb) =
    let s = compare fa fb in
    if s <> 0 then s else
    let s = List.compare compare_taint la lb in
    if s <> 0 then s else
    List.compare compare_taint sa sb
end
module SigSet = Set.Make(Sig);;
module SigMap = Map.Make(Sig);;

let pp_sig (f,t,a) =
  Printf.sprintf "%s(%s,%s)" (pprint_ident f) (pp_list pp_taint t) (pp_list pp_taint a)

let ident_of_sig (f,tes,es) =
  if not (List.exists (fun v -> v = RunTime) (tes @ es)) then f
  else
    match f with
    | FIdent(n, i) ->
        let post = List.fold_left (fun acc v -> acc ^ (if v = RunTime then "R" else "L")) "" (tes @ es) in
        FIdent(n ^ post, i)
    | _ -> failwith "ident_of_sig"

type ip_state = ((taint Bindings.t * taint) SigMap.t)

type state = {
  vars       : taint Bindings.t;
  ret        : taint;
  ctx        : taint;
  calls      : SigSet.t;
  changed    : bool;

  env        : Eval.Env.t;
  results    : ip_state;
  globals    : taint Bindings.t;
  prev       : taint Bindings.t;
  log        : bool;
}


let upd_vars f st = {st with vars = f (st.vars)}
let upd_ret f st = {st with ret = f (st.ret)}
let upd_calls f st = {st with calls = f (st.calls)}
let upd_changed f st = {st with changed = f (st.changed)}

let init_state prev globals results env log = {
  vars     = Bindings.empty;
  ret      = LiftTime;
  ctx      = LiftTime;
  calls    = SigSet.empty;
  changed  = false;

  env      = env;
  results  = results;
  globals  = globals;
  prev     = prev;
  log      = log;
}

type 'a stm = (state -> state * 'a)
let (let@) x f = fun s ->
  let (s,r) = x s in
  (f r) s
let (let+) x f = fun s ->
  let (s,r) = x s in
  (s,f r)
let traverse (f: 'a -> 'b stm) (l: 'a list): ('b list) stm =
  fun st -> List.fold_left_map (fun st a -> f a st) st l
let rec traverse2_ (f: 'a -> 'b -> unit stm) (l: 'a list) (l2: 'b list) (st: state): (state * unit) =
  match l, l2 with
  | [], [] -> (st,())
  | x::xs, y::ys ->
      let (st,_) = f x y st in
      traverse2_ f xs ys st
  | _, _ -> invalid_arg "traverse2"
let pure a = fun st -> (st, a)
let with_state f = fun st -> (st, f st)

let get_context st = (st,st.ctx)
let get_return st = (st,st.ret)

(* Get the taint value for a variable *)
let get_var i st =
  let r = match Bindings.find_opt i (st.vars) with
  | Some v -> v
  | None ->
      match Bindings.find_opt i st.globals with
      | Some v -> v
      | None ->
          if st.log then Printf.printf "get_var: missing variable %s, assuming RunTime\n" (pprint_ident i);
          RunTime
      in
      (st,r)

(* register variables with a taint *)
let register_var (v: ident) (t: taint) st =
  match Bindings.find_opt v (st.vars) with
  | Some t' ->
      if st.log then Printf.printf "register_var: redecl of variable: %s\n" (pprint_ident v);
      (upd_vars (Bindings.add v (join_taint t t')) st, ())
  | None ->
      if Bindings.mem v st.globals && st.log then Printf.printf "register_var: global/local collision on %s\n" (pprint_ident v);
      let t = if Bindings.find_opt v st.prev = Some RunTime then RunTime else t in
      (upd_vars (Bindings.add v t) st, ())

(* update an existing variable *)
let update_var (v: ident) (t: taint) st =
  match Bindings.find_opt v (st.vars) with
  | Some t' ->
      if t' = LiftTime && t = RunTime then begin
        let st = upd_changed (fun _ -> true) st in
        let st = upd_vars (Bindings.add v RunTime) st in
        (st,())
      end else
        (upd_vars (Bindings.add v (join_taint t t')) st, ())
  | None ->
      if Bindings.mem v st.globals then (st,())
      else begin
        if st.log then Printf.printf "update_var: missing decl of variable: %s\n" (pprint_ident v);
        (upd_vars (Bindings.add v t) st, ())
      end

(* register return to the current function context *)
let register_return (t: taint) (st: state) =
  (upd_ret (join_taint t) st, ())

(* join two states *)
let join_state (a: state) (b: state): state =
  {
    vars = Bindings.merge (fun k av bv ->
      match av, bv with
      | Some v, Some v' -> Some (join_taint v v')
      | Some v, None
      | None, Some v -> Some v
      | _ -> None) (a.vars) (b.vars);
    ret = join_taint (a.ret) (b.ret);
    calls = SigSet.union (a.calls) (b.calls);
    ctx = join_taint (a.ctx) (b.ctx);
    changed = a.changed || b.changed;

    (* These should not change *)
    env = a.env;
    results = a.results;
    globals = a.globals;
    prev = a.prev;
    log = a.log;
  }

(* Produce a runtime value if any arg is runtime *)
let pure_prims = Symbolic.prims_pure ()

(* Prims that will always produce runtime *)
let impure_prims = Symbolic.prims_impure ()

let prim_ops (f: ident) (targs: taint list) (args: taint list): taint option =
  if List.mem f pure_prims then Some (join_taint_l (targs @ args))
  else if List.mem f impure_prims then Some RunTime
  else None

(* Transfer function for a call, pulling a primop def or looking up registered fn signature.
   If no signature is available, register it for later analysis and assume its result is bot/LiftTime. *)
let call_tf (f: ident) (targs: taint list) (args: taint list) (st: state): (state * taint) =
  match prim_ops f targs args with
  | Some t -> (st,t)
  | None -> failwith @@ "Missing operation: " ^ (name_of_FIdent f)

(* Determine the taint of an expr *)
let rec expr_tf (e: expr): taint stm =
  match e with
  | Expr_If(_, c, t, els, e) ->
      let bodies = (E_Elsif_Cond(c, t) :: els) @ [E_Elsif_Cond(Expr_Var(Ident "TRUE"),e)] in
      let proc = fun (E_Elsif_Cond(c, e)) ->
        let@ c_t = expr_tf c in
        let+ e_t = expr_tf e in
        join_taint c_t e_t
      in
      let+ bodies_t = traverse proc bodies in
      join_taint_l bodies_t
  | Expr_Field(e, f) -> expr_tf e
  | Expr_Slices(e, ss) ->
      let@ e_t = expr_tf e in
      let+ ss_t = traverse slice_tf ss in
      join_taint e_t (join_taint_l ss_t)
  | Expr_Var(v) -> get_var v
  | Expr_Parens(e) -> expr_tf e
  | Expr_TApply(f,tes,es) ->
      let@ tes_t = traverse expr_tf tes in
      let@ es_t = traverse expr_tf es in
      call_tf f tes_t es_t
  | Expr_Tuple(es) ->
      let+ es_t = traverse expr_tf es in
      join_taint_l es_t
  | Expr_Array(a, i) ->
      let@ a_t = expr_tf a in
      let+ i_t = expr_tf i in
      join_taint a_t i_t
  | Expr_Unknown(_)
  | Expr_ImpDef(_,_)
  | Expr_LitInt(_)
  | Expr_LitHex(_)
  | Expr_LitReal(_)
  | Expr_LitBits(_)
  | Expr_LitMask(_)
  | Expr_LitString(_) -> pure (LiftTime)
  | _ -> failwith @@ "expr_tf: Unsupported expr: " ^ (pp_expr e)

and slice_tf (s: slice): taint stm =
  match s with
  | Slice_Single i -> expr_tf i
  | Slice_HiLo(hi,lo) ->
      let@ hi = expr_tf hi in
      let+ lo = expr_tf lo in
      join_taint hi lo
  | Slice_LoWd(lo,wd) ->
      let@ hi = expr_tf lo in
      let+ lo = expr_tf wd in
      join_taint hi lo

(* determine the taint of a type *)
and type_tf (t: ty): taint stm =
  match t with
  | Type_Constructor _ -> pure LiftTime
  | Type_Bits(n) -> expr_tf n
  | Type_Register(n, _) -> pure LiftTime
  | Type_Array(Index_Range(lo,hi),t) ->
      let@ hi = expr_tf hi in
      let@ lo = expr_tf lo in
      let+ t = type_tf t in
      join_taint_l [hi;lo;t]
  | _ -> failwith @@ "type_tf: Unsupported type: " ^ (pp_type t)

(* determine the taint of a pattern *)
and pattern_tf (t: pattern): taint stm =
  match t with
  | Pat_LitInt(_)
  | Pat_LitHex(_)
  | Pat_LitBits(_)
  | Pat_LitMask(_)
  | Pat_Const(_)
  | Pat_Wildcard -> pure LiftTime
  | Pat_Tuple(ps) -> patterns_tf ps
  | Pat_Set(ps) -> patterns_tf ps
  | Pat_Single(e) -> expr_tf e
  | Pat_Range(lo, hi) ->
      let@ hi = expr_tf hi in
      let+ lo = expr_tf lo in
      join_taint hi lo

and patterns_tf (t: pattern list): taint stm =
  let+ t_t = traverse pattern_tf t in
  join_taint_l t_t

and lexpr_tf (l: lexpr) (t: taint): unit stm =
  match l with
  | LExpr_Wildcard -> pure ()
  | LExpr_Var(v) -> update_var v t
  | LExpr_Field(l, f) -> lexpr_mod_tf l (join_taint t)
  | LExpr_Fields(l, fs) -> lexpr_mod_tf l (join_taint t)
  | LExpr_Slices(l, ss) ->
      let@ ss = traverse slice_tf ss in
      let t = join_taint_l (t::ss) in
      lexpr_mod_tf l (join_taint t)
  | LExpr_Tuple(ls) ->
      let+ _ = traverse (fun l -> lexpr_tf l t) ls in ()
  | LExpr_Array(l, i) ->
      let@ i_t = expr_tf i in
      lexpr_mod_tf l (join_taint (join_taint t i_t))
  | _ -> failwith @@ "lexpr_tf: Unsupported lexpr: " ^ (pp_lexpr l)

and lexpr_mod_tf (l: lexpr) (f: taint -> taint): unit stm =
  match l with
  | LExpr_Var(v) ->
      let@ p = get_var v in
      update_var v (f p)
  | LExpr_Field(l, _) -> lexpr_mod_tf l f
  | LExpr_Array(a, i) ->
      let@ i_t = expr_tf i in
      lexpr_mod_tf a (fun p -> join_taint (f p) i_t)
  | _ -> failwith @@ "lexpr_mod_tf: Unsupported lexpr: " ^ (pp_lexpr l)

and branch_tf (c_t: taint) (t: stmt list) (f: stmt list): unit stm =
  (fun st ->
    let stashed = st.ctx in
    let st = {st with ctx = join_taint c_t stashed} in
    let (st1,()) = stmts_tf t st in
    let (st2,()) = stmts_tf f st in
    let st = join_state st1 st2 in
    ({st with ctx = stashed},()))

(* statement transfer function *)
and stmt_tf (s: stmt): unit stm =
  match s with
  | Stmt_VarDeclsNoInit(ty, [v], loc) ->
      let@ ty_t = type_tf ty in
      register_var v LiftTime

  | Stmt_VarDecl(ty, v, e, loc)
  | Stmt_ConstDecl(ty, v, e, loc) ->
      let@ ty_t = type_tf ty in
      let@ e_t = expr_tf e in
      register_var v (join_taint ty_t e_t)

  | Stmt_Assign(l, r, loc) ->
      let@ r_t = expr_tf r in
      let@ ctx = get_context in
      lexpr_tf l (join_taint r_t ctx)

  | Stmt_TCall(f, tes, es, loc) ->
      let@ tes_t = traverse expr_tf tes in
      let@ es_t = traverse expr_tf es in
      let+ _ = call_tf f tes_t es_t in
      ()

  | Stmt_FunReturn(e, loc) ->
      let@ e_t = expr_tf e in
      let@ ctx = get_context in
      register_return (join_taint ctx e_t )

  | Stmt_If(c, t, [], f, loc) ->
      let@ c_t = expr_tf c in
      branch_tf c_t t f

  | Stmt_While(c, b, loc) ->
      let@ c = expr_tf c in
      stmts_tf b

  | Stmt_ProcReturn(_) ->
      let@ ctx = get_context in
      register_return ctx

  | Stmt_Assert _ -> pure ()
  | Stmt_Throw _ -> pure ()

  | _ -> failwith @@ "stmt_tf: Unsupported stmt: " ^ (pp_stmt s)

and stmts_tf (s: stmt list): unit stm =
  let+ _ = traverse stmt_tf s in
  ()

let fun_tf (f: ident) (targs: ident list) (args: ident list) (targs_t: taint list) (args_t: taint list) (body: stmt list): unit stm =
  if body = [] then pure () else
  let@ _ = traverse2_ register_var targs targs_t in
  let@ _ = traverse2_ register_var args args_t in
  stmts_tf body

(* interproc behaviour *)

let add_sig (callers, results, worklist) s st =
  (* Check if interproc sig has changed, reprocess callers if so *)
  let changed = (match SigMap.find_opt s results with
    | Some (_,v) -> (st.ret <> v)
    | None -> st.ret <> LiftTime) in
  let fns = (match SigMap.find_opt s callers with
    | Some fns -> fns
    | _ -> SigSet.empty) in
  let worklist = if changed then SigSet.union fns worklist else worklist in
  (* Register this signature as a caller of any fn calls collected *)
  let callers = SigSet.fold (fun s' callers ->
    match SigMap.find_opt s' callers with
    | Some fns -> SigMap.add s' (SigSet.add s fns) callers
    | None -> SigMap.add s' (SigSet.add s SigSet.empty) callers) (st.calls) callers in
  (* Insert the analysis results *)
  let results = SigMap.add s (st.vars, st.ret) results in
  (callers, results, worklist)

(* Collect new signatures from the analysis *)
let process_missing (callers, results, worklist) st =
  let missing = SigSet.filter (fun s -> not (SigMap.mem s results)) (st.calls) in
  let results = SigSet.fold (fun s results ->
    SigMap.add s (Bindings.empty,LiftTime) results) missing results in
  let worklist = SigSet.union worklist missing in
  (callers, results, worklist)

let build_globals env =
  (* Make constants lifttime, everything else runtime *)
  let globals = Bindings.empty in
  let globals = Bindings.fold (fun k v -> Bindings.add k LiftTime) (Eval.Env.readGlobalConsts env) globals in
  let globals = Bindings.fold (fun k v -> Bindings.add k RunTime) (Eval.Env.readGlobals env) globals in
  let globals = List.fold_right (Bindings.fold (fun k v -> Bindings.add k RunTime)) (Eval.Env.readLocals env) globals in
  globals

(* Interprocedural fixed point *)
let analysis fns (env: Eval.Env.t) =
  let rec fun_fp globals results prev (fn,targs_t,args_t) =
    let st = init_state prev globals results env false in
    match Bindings.find_opt fn fns with
    | Some (_,_,targs,args,_,body) ->
        let (st,_) = fun_tf fn targs args targs_t args_t body st in
        if not st.changed then st
        else fun_fp globals results st.vars (fn,targs_t,args_t)
    | None -> st
  in

  let rec fp globals callers results worklist =
    let (callers, results, worklist) = SigSet.fold (fun s acc ->
      let (_, results, _) = acc in
      (* Process this function *)
      (*Printf.printf "Processing %s\n" (pp_sig s);*)
      let st = fun_fp globals results Bindings.empty s in
      (* Add this analysis result to acc *)
      let acc = add_sig acc s st in
      (* Push new signatures and re-run callers if necessary *)
      let acc = process_missing acc st in
      acc) worklist (callers,results,SigSet.empty)
    in
    if SigSet.cardinal worklist = 0 then (results, callers)
    else fp globals callers results worklist
  in

  let globals = build_globals env in

  (* All functions have initially zero callers *)
  let callers = SigMap.empty in
  (* Map all default signatures to bot/LiftTime *)
  let results = Bindings.fold (fun k (_,_,targs,args,_,_) acc ->
    let targs_t = List.map (fun _ -> LiftTime) targs in
    let args_t = List.map (fun _ -> LiftTime) args in
    let s = (k,targs_t,args_t) in
    SigMap.add s (Bindings.empty,LiftTime) acc) fns SigMap.empty in
  (* Push everything onto the worklist *)
  let worklist = SigMap.fold (fun s _ acc -> SigSet.add s acc) results SigSet.empty in
  fp globals callers results worklist

(*** Fixed Point Analysis Wrappers ***)

let or_all l = List.exists (fun s -> s) l
let is_runtime_var v =
  let+ v_t = get_var v in
  v_t = RunTime
let is_runtime_type ty =
  let+ ty_t = type_tf ty in
  ty_t = RunTime
let is_runtime_expr e: bool stm =
  let+ e_t = expr_tf e in
  e_t = RunTime
let is_runtime_patterns ps =
  let+ p_t = patterns_tf ps in
  p_t = RunTime
let is_runtime_slice s =
  let+ s_t = slice_tf s in
  s_t = RunTime

let rec is_runtime_stmt s: bool stm =
  let@ ctx = get_context in
  if ctx = RunTime then pure true
  else
  match s with
  | Stmt_VarDeclsNoInit(ty, vs, loc) ->
      let@ ty = is_runtime_type ty in
      let+ vs = traverse is_runtime_var vs in
      ty || or_all vs
  | Stmt_VarDecl(ty,v,e,loc)
  | Stmt_ConstDecl(ty,v,e,loc) ->
      let@ ty = is_runtime_type ty in
      let@ v = is_runtime_var v in
      let+ e = is_runtime_expr e in
      ty || v || e
  | Stmt_Assign(l, r, loc) ->
      let@ l = is_runtime_lexpr l in
      let+ r = is_runtime_expr r in
      l || r
  | Stmt_TCall(f, tes, es, loc) ->
      let@ tes = traverse is_runtime_expr tes in
      let+ es = traverse is_runtime_expr es in
      or_all (tes @ es)
  | Stmt_FunReturn(e, loc) ->
      let+ r = get_return in
      r = RunTime
  | Stmt_ProcReturn(loc) -> pure false
  | Stmt_If(c, t, els, f, loc) ->
      let bodies = S_Elsif_Cond(c,t)::els in
      let@ els_t = traverse (fun (S_Elsif_Cond(c,t)) ->
        let@ c = is_runtime_expr c in
        let+ t = is_runtime_stmts t in
        c || t) bodies in
      let+ f = is_runtime_stmts f in
      or_all els_t || f
  | Stmt_Case(c, cas, odefault, loc) ->
      let@ c = is_runtime_expr c in
      let@ cas = traverse (fun (Alt_Alt(p,oc,s)) ->
        let@ p_= is_runtime_patterns p in
        let@ oc = match oc with
          | Some c -> is_runtime_expr c
          | None -> pure false
        in
        let+ s = is_runtime_stmts s in
        c || oc || s) cas in
      let+ d = match odefault with
        | Some v -> is_runtime_stmts v
        | _ -> pure false
      in
      c || or_all cas || d
  | Stmt_For(v, start, dir, stop, b, loc) ->
      let@ start = is_runtime_expr start in
      let@ stop = is_runtime_expr stop in
      let@ v = is_runtime_var v in
      let+ b = is_runtime_stmts b in
      b || start || stop || v
  | Stmt_While(c, b, loc)
  | Stmt_Repeat(b, c, loc) ->
      let@ c = is_runtime_expr c in
      let+ b = is_runtime_stmts b in
      b || c
  | Stmt_Assert(e,loc) -> is_runtime_expr e

  | Stmt_Unpred(_)
  | Stmt_ConstrainedUnpred(_)
  | Stmt_ImpDef(_, _)
  | Stmt_ExceptionTaken(_)
  | Stmt_Dep_Unpred(_)
  | Stmt_Dep_ImpDef(_, _)
  | Stmt_Dep_Undefined(_)
  | Stmt_See(_, _)
  | Stmt_Throw(_, _)
  | Stmt_Undefined(_) -> pure false

  | _ -> failwith @@ "is_runtime_stmt: Unsupported stmt " ^ (pp_stmt s)

and is_runtime_stmts s =
  let+ s = traverse is_runtime_stmt s in
  or_all s

and is_runtime_lexpr l =
  match l with
  | LExpr_Wildcard -> pure false
  | LExpr_Var(v) -> is_runtime_var v
  | LExpr_Field(l, f) -> is_runtime_lexpr l
  | LExpr_Fields(l, fs) -> is_runtime_lexpr l
  | LExpr_Slices(l, ss) ->
      let@ c = is_runtime_lexpr l in
      let+ ss_t = traverse is_runtime_slice ss in
      c || or_all ss_t
  | LExpr_Array(l, i) ->
      let@ i = is_runtime_expr i in
      let+ l = is_runtime_lexpr l in
      i || l
  | LExpr_Write(setter, tes, es) ->
      let@ tes = traverse is_runtime_expr tes in
      let+ es = traverse is_runtime_expr es in
      or_all (tes @ es)
  | LExpr_Tuple(es) ->
      let+ es = traverse is_runtime_lexpr es in
      or_all es
  | LExpr_BitTuple(es) ->
      let+ es = traverse is_runtime_lexpr es in
      or_all es
  | _ -> failwith @@ "is_runtime_lexpr: Unsupported lexpr " ^ (pp_lexpr l)

(*** Lift/Run Time Split ***)

type gen_state = {
  var_count : int;
  res : state;
  env : Eval.Env.t;
  var_type : ty Bindings.t;
  log : bool;
}

let init_gen_state prev globals results env ret types log =
  let res = init_state prev globals results env false in
  let res = {res with ret} in
  let res = {res with vars = prev} in
  {var_count = 0; res; env; var_type = types; log }

type 'a wrm = (gen_state -> (gen_state * stmt list * 'a,string) Either.t)
let (let@) x f = fun s ->
  match x s with
  | Either.Left(s,w,r) ->
      (match f r s with
      | Either.Left(s,w',r) -> Either.Left(s,w@w',r)
      | Either.Right e -> Either.Right e)
  | Either.Right e -> Either.Right e
let (let+) x f = fun s ->
  match x s with
  | Either.Left(s,w,r) -> Either.Left (s,w,f r)
  | Either.Right e -> Either.Right e
let wrap f = fun s ->
  match f s with
  | Either.Left(s,w,r) -> Either.Left (s,[],(w,r))
  | Either.Right e -> Either.Right e
let write l = fun s ->
  Either.Left (s,l,())
let pure v = fun s ->
  Either.Left (s,[],v)
let fail m = fun s ->
  Either.Right m
let test c m =
  if c then fail m else pure ()
let wstate f = fun s ->
  let (s',r) = f s.res in
  Either.Left (s,[],r)
let set_context ctx = fun s ->
  let res = {s.res with ctx} in
  Either.Left ({s with res},[],())
let rec split f l =
  match l with
  | [] -> pure ([], [])
  | x::xs ->
      let@ b = f x in
      let+ (l,r) = split f xs in
      if b then (x::l,r) else (l,x::r)
let rec traverse (f: 'a -> 'b wrm) (l: 'a list): ('b list) wrm =
  match l with
  | [] -> pure []
  | x::xs ->
      let@ x = f x in
      let+ xs = traverse f xs in
      x::xs
let rec traverse2_ (f: 'a -> 'b -> unit wrm) (l: 'a list) (l2: 'b list): unit wrm =
  match l, l2 with
  | [], [] -> pure ()
  | x::xs, y::ys ->
      let@ _ = f x y in
      traverse2_ f xs ys
  | _, _ -> invalid_arg "traverse2_"
let get_env = fun s ->
  Either.Left (s,[],s.env)
let get_types = fun s ->
  Either.Left (s,[],s.var_type)
let get_debug = fun s ->
  Either.Left (s,[],s.log)

let is_rt_var v = wstate (is_runtime_var v)
let is_rt_expr v = wstate (is_runtime_expr v)
let is_rt_stmt v = wstate (is_runtime_stmt v)
let is_rt_slice v = wstate (is_runtime_slice v)



let rt_var_ty   = Type_Constructor (Ident "rt_sym")
let rt_label_ty = Type_Constructor (Ident "rt_label")
let rt_expr_ty = Type_Constructor (Ident "rt_expr")

let rt_decl_bv          = FIdent("decl_bv", 0)         (* string -> int -> sym *)
let rt_decl_bool        = FIdent("decl_bool", 0)       (* string -> sym *)
let rt_gen_bit_lit      = FIdent("gen_bit_lit", 0)     (* bv -> bv rt *)
let rt_gen_bool_lit     = FIdent("gen_bool_lit", 0)    (* bool -> bool rt *)
let rt_gen_int_lit      = FIdent("gen_int_lit", 0)     (* int -> int rt *)
let rt_gen_slice        = FIdent("gen_slice", 0)       (* bv rt -> int -> int -> bv rt *)

let rt_gen_branch       = FIdent("gen_branch", 0)      (* bool rt -> (rt_label, rt_label, rt_label) *)
let rt_switch_context   = FIdent("switch_context", 0)  (* rt_label -> unit *)
let rt_gen_load         = FIdent("gen_load", 0)        (* sym -> 'a rt *)
let rt_gen_store        = FIdent("gen_store", 0)       (* sym -> 'a rt -> unit *)
let rt_gen_assert       = FIdent("gen_assert", 0)      (* bool rt -> unit *)

let rt_gen_array_store  = FIdent("gen_array_store", 0) (* sym -> int -> 'a rt -> unit *)
let rt_gen_array_load   = FIdent("gen_array_load", 0)  (* sym -> int -> 'a rt *)

let arg_of_ident v = Expr_LitString(pprint_ident v)

let get_fresh_name = fun s ->
  let num = s.var_count in
  let s = {s with var_count = num + 1} in
  let i = Ident ("temp" ^ string_of_int num) in
  Either.Left (s,[],i)

(* Declare a variable in the runtime program and return some means to refer to it *)
let gen_var_decl loc ty v =
  let@ e = (match ty with
  | Type_Bits(w) ->
      let@ c = is_rt_expr w in
      if c then fail @@ "gen_var_decl: Runtime variable width " ^ (pp_expr w)
      else pure (Expr_TApply (rt_decl_bv, [], [arg_of_ident v; w]))
  | Type_Constructor(Ident("boolean")) ->
      pure (Expr_TApply (rt_decl_bool, [], [arg_of_ident v]))
  | Type_Constructor(id) ->
      let@ env = get_env in
      (match Eval.Env.getEnum env id with
      | Some l ->
          let len = Expr_LitInt (string_of_int (Z.log2up (Z.of_int (List.length l)))) in
          pure (Expr_TApply (rt_decl_bv, [], [arg_of_ident v; len]))
      | None -> fail @@ "gen_var_decl: Unknown ty " ^ (pp_type ty))
  | _ -> fail @@ "gen_var_decl: Unknown ty " ^ (pp_type ty)) in
  write [Stmt_ConstDecl(rt_var_ty, v, e, loc)]

let gen_lt_var loc ty =
  let@ i = get_fresh_name in
  let+ _ = write[Stmt_VarDeclsNoInit(ty, [i], loc)] in
  i

(* Generate a fresh variable in the runtime program of some type *)
let gen_fresh_var loc ty =
  let@ i = get_fresh_name in
  let+ _ = gen_var_decl loc ty i in
  i

let rt_true_branch = FIdent("true_branch", 0)
let rt_false_branch = FIdent("false_branch", 0)
let rt_merge_branch = FIdent("merge_branch", 0)

(* Generate a branch in the runtime program, with some way to refer to its targets and merge point *)
let gen_branch loc c =
  let@ res = get_fresh_name in
  let v = Expr_Var res in
  let+ _ = write [Stmt_ConstDecl( rt_label_ty, res, Expr_TApply(rt_gen_branch, [], [c]), loc) ] in
  (Expr_TApply(rt_true_branch, [], [v]),Expr_TApply(rt_false_branch,[],[v]),Expr_TApply(rt_merge_branch,[],[v]))

(* Switch the implicit context to one produced by gen_branch *)
let switch_context loc t =
  write [Stmt_TCall(rt_switch_context, [], [t], loc)]

(* Generate a variable store/load *)
let gen_var_store loc v e =
  write [Stmt_TCall(rt_gen_store, [], [Expr_Var v; e], loc)]
let gen_var_load v =
  pure (Expr_TApply(rt_gen_load, [], [Expr_Var v]))

(* Generate a simple field access by collapsing fields *)
let gen_field_store loc l f v =
  match l,f  with
  | LExpr_Var (Ident var), Ident f ->
      let name = Ident (var ^ "." ^ f) in
      gen_var_store loc name v
  | _ -> fail "gen_field_store"
let gen_field_load e f =
  match e, f with
  | Expr_Var (Ident var), Ident f ->
      let name = Ident (var ^ "." ^ f) in
      gen_var_load name
  | _ -> fail "gen_field_load"

(* Generate an array store/load *)
let gen_array_store loc a i e =
  write [Stmt_TCall(rt_gen_array_store, [], [Expr_Var a;i;e], loc)]
let gen_array_load a i =
  pure (Expr_TApply(rt_gen_array_load, [], [Expr_Var a;i]))

(* Generate a slice e[lo:wd] *)
let gen_slice_expr e lo wd =
  pure (Expr_TApply(rt_gen_slice, [], [e;lo;wd]))

(* Generate a literal *)
let gen_lit e =
  let@ env = get_env in
  let@ vars = get_types in
  let t = Dis_tc.infer_type e vars env in
  match t with
  | Some (Type_Bits(w)) -> pure (Expr_TApply (rt_gen_bit_lit, [w], [e]))
  | Some (Type_Constructor(Ident("boolean"))) -> pure (Expr_TApply (rt_gen_bool_lit, [], [e]))
  | Some (Type_Constructor(Ident("integer"))) -> pure (Expr_TApply (rt_gen_int_lit, [], [e]))
  | Some t -> fail @@ "gen_lit: " ^ (pp_expr e) ^ " " ^ (pp_type t)
  | _ -> fail @@ "gen_lit: " ^ (pp_expr e)

let gen_assert loc e =
  write [Stmt_TCall(rt_gen_assert, [], [e], loc)]

(* Generate a prim, where all type arguments are lifttime and standard arguments are runtime*)
let rec gen_prim loc f tes es =
  let@ tes = traverse (lt_expr loc) tes in
  let@ es = traverse (gen_expr loc) es in
  (* Operations over both runtime and lifttime arguments often expose an opportunity for
     simplification at lifttime, by injecting transforms conditional on the lifttime value.
     Ideally this could be done in a later pass with an analysis over the possible lifttime values
     to determine whether the conditional transform is even possible.

     Simple examples:
       rt + lt ~> if lt = 0 then rt else rt + gen_lit lt
       rt * lt ~> if lt = 1 then rt else rt * gen_lit lt
   *)
  match f, tes, es with
  (* If comparing a runtime and lifttime boolean, just pass the runtime through or negate it *)
  | FIdent("eq_enum", 0), [], [(RunTime, e1);(LiftTime, e2)]
  | FIdent("eq_enum", 0), [], [(LiftTime, e2);(RunTime, e1)] ->
      let@ i = gen_lt_var loc rt_expr_ty in
      let ne = Expr_TApply(FIdent("gen_not_bool", 0), [], [e1]) in
      let+ _ = write [Stmt_If(e2,
        [Stmt_Assign(LExpr_Var i, e1, loc)], [],
        [Stmt_Assign(LExpr_Var i, ne, loc)], loc)] in
      Expr_Var i
  | _ ->
    let f = FIdent("gen_" ^ name_of_FIdent f, 0) in
    let@ es = traverse (fun (t,e) -> if t = LiftTime then gen_lit e else pure e) es in
    pure (Expr_TApply(f,tes,es))
and gen_eff loc f tes es =
  let@ tes = traverse (lt_expr loc) tes in
  let@ es = traverse (rt_expr loc) es in
  let f = FIdent("gen_" ^ name_of_FIdent f, 0) in
  write [Stmt_TCall(f, tes, es, loc)]

(* Generate an If, potentially producing a runtime branch if outcome isn't liftime known *)
and gen_if loc (c: expr) (tcase: unit wrm) (fcase: unit wrm) =
  let@ b = is_rt_expr c in
  if b then
    let@ c = rt_expr loc c in
    let@ ctx = wstate get_context in
    let@ _ = set_context RunTime in
    let@ (lt,lf,lm) = gen_branch loc c in
    let@ _ = switch_context loc lt in
    let@ tcase = tcase in
    let@ _ = switch_context loc lf in
    let@ fcase = fcase in
    let@ _ = set_context ctx in
    switch_context loc lm
  else
    let@ (tstmts,tcase) = wrap tcase in
    let@ (fstmts,fcase) = wrap fcase in
    write [Stmt_If(c, tstmts, [], fstmts, loc)]

(* Generate an expression, possibly returning the provided argument if it is lifttime *)
and gen_expr loc e : (taint * expr) wrm =
  let@ c = is_rt_expr e in
  if not c then pure (LiftTime, e)
  else
    let+ r = match e with
      (* Prim application *)
      | Expr_Slices(e, [Slice_LoWd(lo,wd)]) ->
          let@ e = rt_expr loc e in
          let@ lo = lt_expr loc lo in
          let@ wd = lt_expr loc wd in
          gen_slice_expr e lo wd
      | Expr_TApply(f,tes,es) -> 
          gen_prim loc f tes es

      (* State loads *)
      | Expr_Var(v) -> gen_var_load v
      | Expr_Field(e, f) -> gen_field_load e f
      | Expr_Array(Expr_Var a, i) ->
          let@ i = lt_expr loc i in
          gen_array_load a i

      | _ -> fail @@ "gen_expr: unsupported expr " ^ (pp_expr e)
    in (RunTime, r)

(* Generate an expression, fail if it is runtime *)
and lt_expr loc e =
  let@ debug = get_debug in
  if debug then Printf.printf "lt_expr: %s\n" (pp_expr e);
  let@ (t,e) = gen_expr loc e in
  if t = LiftTime then pure e
  else fail @@ "Unexpected runtime expression: " ^ (pp_expr e)

(* Generate an expression, forcing it to be runtime via a cast *)
and rt_expr loc e =
  let@ debug = get_debug in
  if debug then Printf.printf "rt_expr: %s\n" (pp_expr e);
  let@ (t,e) = gen_expr loc e in
  if t = LiftTime then gen_lit e
  else pure e

and gen_stmt s : unit wrm =
  let@ debug = get_debug in
  if debug then Printf.printf "gen_stmt: %s\n" (pp_stmt s);
  let@ c = is_rt_stmt s in
  if not c then write [s]
  else match s with
    (* Runtime decls create symbols for later assignment *)
    | Stmt_VarDeclsNoInit(ty, [v], loc) ->
        gen_var_decl loc ty v

    (* Var/const decls create symbols and introduce an initial assignment *)
    | Stmt_VarDecl(ty, v, e, loc) ->
        let@ _ = gen_var_decl loc ty v in
        let@ e = rt_expr loc e in
        gen_var_store loc v e
    | Stmt_ConstDecl(ty, v, e, loc) ->
        let@ _ = gen_var_decl loc ty v in
        let@ e = rt_expr loc e in
        gen_var_store loc v e

    (* Write the mutable / global var *)
    | Stmt_Assign(l, r, loc) ->
        let@ r = rt_expr loc r in
        rt_lexpr loc l r

    (* Call effectful prim *)
    | Stmt_TCall(f, tes, es, loc) ->
        gen_eff loc f tes es

    (* Build branching structure *)
    | Stmt_If(c, t, [], f, loc) ->
        gen_if loc c (* then *) (gen_stmts t) (* else *) (gen_stmts f)

    (* Generate a runtime exception *)
    | Stmt_Assert(e,loc) ->
        let@ e = rt_expr loc e in
        gen_assert loc e
    | Stmt_Throw(e,loc) ->
        let@ e = gen_lit Symbolic.expr_false in
        gen_assert loc e

    | _ -> fail @@ "gen_stmt: Unsupported stmt " ^ (pp_stmt s)

and gen_stmts s: unit wrm =
  let+ _ = traverse gen_stmt s in ()

and rt_lexpr loc l e =
  match l with
  | LExpr_Wildcard -> pure ()
  | LExpr_Var(v) ->
      gen_var_store loc v e
  | LExpr_Array(LExpr_Var(v),i) ->
      let@ i = lt_expr loc i in
      gen_array_store loc v i e
  | LExpr_Field(l, f) ->
     gen_field_store loc l f e
  | _ -> fail @@ "rt_lexpr: Unsupported lexpr " ^ (pp_lexpr l)

let gen_prog fns results env =
  let globals = build_globals env in

  let sfns = SigMap.filter_map (fun s res ->
    let (fn,_,_) = s in
    let (prev, ret) = SigMap.find s results in
    match Bindings.find_opt fn fns with
    | None -> (None)
    | Some (a,b,c,d,e,body) ->
        let types = Dis_tc.LocalVarTypes.run b c body in
        let st = init_gen_state prev globals results env ret types false in
        match gen_stmts body st with
        | Either.Left (_,w,_) -> Some (a,b,c,d,e,w)
        | Either.Right m -> (Printf.printf "Failed to gen '%s': %s\n" (pp_sig s) m; None)
  ) results in
  SigMap.fold (fun k v acc -> Bindings.add (ident_of_sig k) v acc) sfns Bindings.empty

let run fns env =
  let (taint_res, callers) = analysis fns env in
  gen_prog fns taint_res env

