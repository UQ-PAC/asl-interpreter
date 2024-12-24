open Asl_utils
open Asl_ast

(* Utility functions to match runtime expressions *)
let is_memory_load f =
  f = FIdent ("gen_Mem.read", 0)
let is_var_load f =
  f = Offline_transform.rt_gen_load
let is_var_store f =
  f = Offline_transform.rt_gen_store
let is_array_load f =
  f = Offline_transform.rt_gen_array_load
let is_array_store f =
  f = Offline_transform.rt_gen_array_store
let is_assert f =
  f = Offline_transform.rt_gen_assert
let is_branch f =
  f = Offline_transform.rt_gen_branch
let is_context_switch f =
  f = Offline_transform.rt_switch_context
let is_lit f =
  f = Offline_transform.rt_gen_bool_lit || f = Offline_transform.rt_gen_int_lit || f = Offline_transform.rt_gen_bit_lit
let is_slice f =
  f = FIdent ("gen_slice", 0)

let is_merge_target f2 =
  f2 = Offline_transform.rt_merge_branch

let is_gen_call f =
  let prefix = "gen_" in
  match f with
  | FIdent(f, _) when String.starts_with ~prefix f -> true
  | _ -> false

let is_pure_expr f =
  let prefix = "gen_" in
  match f with
  | FIdent(f, 0) when String.starts_with ~prefix f ->
      let f' = String.sub f 4 (String.length f - 4) in
      List.mem (FIdent(f',0)) Offline_transform.pure_prims
  | _ -> false

let is_var_decl f =
  f = Offline_transform.rt_decl_bv || f = Offline_transform.rt_decl_bool


  (*
module CopyProp = struct
  type clas =
    Declared |
    Defined of IdentSet.t |
    Clobbered |
    Essential

  let pp_clas c =
    match c with
    | Declared -> "Declared"
    | Defined ids -> "Defined (" ^ pp_identset ids ^ ")"
    | Clobbered -> "Clobbered"
    | Essential -> "Essential"

  let merge_clas a b =
    match a, b with
    | Declared, Declared -> Declared

    (* Ignore declared? *)
    | Declared, Defined d
    | Defined d, Declared -> Defined d
    | Declared, Clobbered
    | Clobbered, Declared -> Clobbered

    (* Can't drop essential though - needs to hold once set *)
    | Declared, Essential
    | Essential, Declared -> Essential

    (* Union deps, consider essential even if only conditional *)
    | Defined d, Defined d' -> Defined (IdentSet.union d d')
    | Defined _, Clobbered
    | Clobbered, Defined _ -> Clobbered
    | Defined _, Essential
    | Essential, Defined _ -> Essential

    (* *)
    | Clobbered, Clobbered -> Clobbered
    | Clobbered, Essential
    | Essential, Clobbered
    | Essential, Essential -> Essential

  type state = {
    var_clas : clas Bindings.t;
    ctx : ident list;
  }
  let set_var v k st =
    let var_clas = Bindings.add v k st.var_clas in
    { st with var_clas }
  let clobber_var v st =
    let var_clas = Bindings.map (fun c -> match c with Defined ids when IdentSet.mem v ids -> Clobbered | _ -> c) st.var_clas in
    { st with var_clas }

  let get_var v st = Bindings.find_opt v st.var_clas
  let merge_st a b =
    assert (a.ctx = b.ctx);
    let ctx = a.ctx in
    let var_clas = Bindings.merge (fun k a b ->
      match a, b with
      | Some a, Some b -> Some (merge_clas a b)
      | Some a, None
      | None, Some a -> Some a
      | None, None -> None) a.var_clas b.var_clas in
    { var_clas ; ctx }
  let init_state = { var_clas = Bindings.empty; ctx = [] }
  let push_context m st = { st with ctx = m::st.ctx }
  let peek_context st = match st.ctx with x::xs -> x | _ -> invalid_arg "peek_context"
  let pop_context st = { st with ctx = (match st.ctx with x::xs -> xs | _ -> invalid_arg "pop_context") }
  let has_context st = List.length st.ctx > 0

  let decl_var v st = set_var v Declared st
  let define_var v deps st = set_var v (Defined deps) st

  let read_var v (st,i) =
    match get_var v st with
    (* Reading undeclared generally means a value that is gradually constructed through partial updates *)
    | Some (Declared) ->
        (set_var v Essential st, i)
    (* Reading clobbered implies we cannot reorder *)
    | Some (Clobbered) ->
        (set_var v Essential st, i)
    (* Collect ids for transitive walk given a defined variable *)
    | Some (Defined ids) ->
        (st, IdentSet.union i ids)
    | _ -> (st, i)

  let impure_ident = Ident "CopyProp_impure"

  let read_vars (vs: IdentSet.t) (st: state): state =
    let read_set s st = IdentSet.fold read_var s (st,IdentSet.empty) in
    (* If impure is in the readset, the reads are not pure. Clobber any impure dependencies now. *)
    let st = if IdentSet.mem impure_ident vs then clobber_var impure_ident st else st in
    (* Reading variables after they are clobbered shifts them to essential vars *)
    let rec iter delta seen st =
      let (st,deps) = read_set delta st in
      let seen = IdentSet.union seen delta in
      let delta = IdentSet.diff deps seen in
      if IdentSet.cardinal delta = 0 then st
      else iter delta seen st in
    iter vs IdentSet.empty st

  (* TODO: Updating, check if this has some context dependence *)
  let update_deps v deps st =
    if has_context st then set_var v Essential st
    else
      match get_var v st with
      | Some (Declared) ->
          set_var v (Defined deps) st
      | Some (Defined d') ->
          set_var v (Defined (IdentSet.union deps d')) st
      | _ -> st

  class deps_walker = object (self)
    inherit Asl_visitor.nopAslVisitor
    val mutable deps = IdentSet.empty

    method add_dep i = deps <- IdentSet.add i deps
    method get_deps = deps

    method! vexpr = function
      | Expr_TApply (f, _, _) when is_lit f ->
          SkipChildren
      | Expr_TApply (f, [], [Expr_Var v]) when is_var_load f ->
          self#add_dep v;
          SkipChildren
      | Expr_TApply (f, [], [e;_;_]) when is_slice f ->
          let _ = self#vexpr e in
          SkipChildren
      | Expr_TApply (f, tes, es) when is_pure_expr f ->
          let _ = List.map (self#vexpr) es in
          SkipChildren
      | Expr_TApply (f, [], [Expr_Var a;i]) when is_array_load f ->
          self#add_dep a;
          SkipChildren
      | Expr_TApply(f, _, es) when is_gen_call f ->
          self#add_dep impure_ident;
          let _ = List.map (self#vexpr) es in
          SkipChildren
    | e -> (Printf.printf "Unknown runtime expression: %s\n"  (pp_expr e)); DoChildren
  end

  let get_deps e =
    let v = new deps_walker in
    let _ = Asl_visitor.visit_expr v e in
    v#get_deps

  let pp_state st =
    pp_bindings pp_clas st.var_clas

  let pp_essential st =
    pp_bindings pp_clas (Bindings.filter (fun f v -> v = Essential) st.var_clas)

  let rec walk_stmt s st =
    match s with
    (* Var decl *)
    | Stmt_ConstDecl(t, v, Expr_TApply(f, [], args), loc) when is_var_decl f ->
        decl_var v st

    (* Var assign *)
    | Stmt_TCall(f, [], [Expr_Var v; e], loc) when is_var_store f ->
        (* Collect reads and process them all *)
        let deps = get_deps e in
        let st = read_vars deps st in
        (* Clobber anything dependent on v *)
        let st = clobber_var v st in
        (* Update deps for v *)
        update_deps v deps st

    (* Array assign *)
    | Stmt_TCall(f, [], [Expr_Var a; i; e], loc) when is_array_store f ->
        (* Collect reads and process them all *)
        let deps = get_deps e in
        let st = read_vars deps st in
        (* Clobber anything dependent on a *)
        clobber_var a st

    (* Assert *)
    | Stmt_TCall(f, [], [e], loc) when is_assert f ->
        (* Collect reads and process them all *)
        let deps = get_deps e in
        read_vars deps st

    (* LiftTime branch *)
    | Stmt_If(c, t, [], f, loc) ->
        let tst = walk_stmts t st in
        let fst = walk_stmts f st in
        merge_st tst fst

    (* RunTime branch *)
    | Stmt_ConstDecl(t, v, Expr_TApply(f, [], [c]), loc) when is_branch f ->
        (* Collect reads and process them all *)
        let deps = get_deps c in
        let st = read_vars deps st in
        (* Push the merge point *)
        push_context v st

    (* Context switch *)
    | Stmt_TCall(f, [], [Expr_TApply(f2, [], [Expr_Var i])], loc) when is_context_switch f && is_merge_target f2 ->
        let top = peek_context st in
        if i = top then pop_context st else st

    (* Impure effect *)
    | Stmt_TCall(f, _, es, loc) when is_gen_call f ->
        (* Collect reads and process them all *)
        let st = List.fold_right (fun e st ->
          let deps = get_deps e in
          read_vars deps st) es st in
        (* Clobber everything linked to global state *)
        clobber_var impure_ident st

    | _ -> st

  and walk_stmts s st =
    List.fold_left (fun st s -> walk_stmt s st) st s

  let candidate_var v st =
    match get_var v st with
    | Some Essential -> false
    | None -> false
    | _ -> true

  (* To change this, you'd need to know :
      - The condition under which its safe to copy prop
      - The current reachability

     If you can't establish you are guarded, implies you need to introduce a branch.
     The branch will have the outcomes of both exp reduction and maintaining the current temp.
     Then need to specialise everything downstream for this point based on this introduced branch.

     This means you need to pull the condition out to the front.
     Which means its needs to be fully reduced and in terms of enc.
     BDD approach gives us this flexibility, every single condition in the program in terms of original enc.
     Relatively simple to reduce from that point: eliminate guards based on reachability, etc.

     You can implement constant-prop and dead code in a similar fashion, as long as your notions of conditional
     use / redefinition / loss of constant precision is purely in terms of the original enc.
   *)
  class copyprop_transform st = object
    inherit Asl_visitor.nopAslVisitor
    method! vexpr = function
      (* Transform loads into direct variable accesses *)
      | Expr_TApply(f, [], [Expr_Var v]) when is_var_load f && candidate_var v st ->
          ChangeTo (Expr_Var v)
      | _ -> DoChildren
    method! vstmt = function
      (* Transform runtime variable decls into expression decls *)
      | Stmt_ConstDecl(t, v, Expr_TApply(f, [], args), loc) when is_var_decl f && candidate_var v st ->
          ChangeDoChildrenPost([Stmt_VarDeclsNoInit(Offline_transform.rt_expr_ty, [v], loc)], fun e -> e)
      (* Transform stores into assigns *)
      | Stmt_TCall(f, [], [Expr_Var v; e], loc) when is_var_store f && candidate_var v st ->
          ChangeDoChildrenPost([Stmt_Assign(LExpr_Var v, e, loc)], fun e -> e)
      | _ -> DoChildren
  end

  let run fn body =
    let st = init_state in
    let st = walk_stmts body st in
    (* Printf.printf "%s : %s\n" (pprint_ident fn) (pp_essential st); *)
    (* Printf.printf "%s : %s\n" (pprint_ident fn) (pp_state st); *)
    let v = new copyprop_transform st in
    Asl_visitor.visit_stmts v body

end
*)

module DeadContextSwitch = struct
  (* Backwards walk to reduce consecutive context switches.
     Could be extended to any context switches with no rt gen operations between,
     but this pattern doesn't seem to show up. *)

  let rec walk_stmts s dead =
    List.fold_right (fun s (acc,dead) ->
      match s with
      | Stmt_TCall (f, _, _, _) when is_context_switch f && dead -> (acc,dead)
      | Stmt_TCall (f, _, _, _) when is_context_switch f -> (s::acc,true)
      | Stmt_If(c, t, [], f, loc) ->
          let (t,dead) = walk_stmts t dead in
          let (f,dead') = walk_stmts f dead in
          (Stmt_If(c, t, [], f, loc)::acc, dead && dead')
      | _ -> (s::acc,false)
    ) s ([],dead)

  let run fn body = let (s,_) =  walk_stmts body false in s
end


module RtCopyProp = struct

  let debug_log = false

  type clas =
    Declared |
    Defined of IdentSet.t |
    Clobbered of IdentSet.t |
    Essential

  let pp_clas c =
    match c with
    | Declared -> "Declared"
    | Defined ids -> "Defined (" ^ pp_identset ids ^ ")"
    | Clobbered ids -> "Clobbered (" ^ pp_identset ids ^ ")"
    | Essential -> "Essential"

  let merge_clas a b =
    match a, b with
    | Declared, Declared -> Declared

    (* Ignore declared? *)
    | Declared, Defined d
    | Defined d, Declared -> Defined d
    | Declared, Clobbered c
    | Clobbered c , Declared -> Clobbered c

    (* Can't drop essential though - needs to hold once set *)
    | Declared, Essential
    | Essential, Declared -> Essential

    (* Union deps, consider essential even if only conditional *)
    | Defined d, Defined d' -> Defined (IdentSet.union d d')
    | Defined d, Clobbered d'
    | Clobbered d, Clobbered d' 
    | Clobbered d, Defined d' -> Clobbered (IdentSet.union d d') 
    | Defined _, Essential
    | Essential, Defined _ -> Essential

    (* *)
    | Clobbered _, Essential
    | Essential, Clobbered _
    | Essential, Essential -> Essential



  type state = {
    var_clas : clas Bindings.t;
    ctx : (ident * MLBDD.t) list;
    (* maps idents to the condution under which they are clobbered *)
    cond_clobbered: (MLBDD.t) Bindings.t; (* ident -> clobber condition (any dep updated) *)
    (* maps idents to the condition under which they are read after clobbering *)
    cond_read: (MLBDD.t) Bindings.t; (* ident -> clobber condition (any dep updated) *)

    (*deps: IdentSet.t Bindings.t; (* ident -> ident *) *)

    (* not used; stores dep sets for bindings (and the def reachability) *)
    cond_dep: (MLBDD.t * IdentSet.t) Bindings.t;  (* binding -> condition * deps *)
    (**)
    bdd: Transforms.BDDSimp.state;
  }

  type rt = state
  type olt = MLBDD.t


  let pp_state st =
    (pp_bindings pp_clas st.var_clas) ^ "\n" ^
    "cond read: " ^
    (pp_bindings (fun i -> Printf.sprintf "%s\n" (Transforms.BDDSimp.pp_abs (Val [i]))) st.cond_read) ^
    "\ncond clob: " ^
    (pp_bindings (fun i -> Printf.sprintf "%s\n" (Transforms.BDDSimp.pp_abs (Val [i]))) st.cond_clobbered)

  let pp_essential st =
    pp_bindings pp_clas (Bindings.filter (fun f v -> v = Essential) st.var_clas)

  let set_var v k st =
    let var_clas = Bindings.add v k st.var_clas in
    (* TODO: need to be adapted for new lattice ? *)
    { st with var_clas }


  let cond_merge al bl =  Bindings.merge (fun i a b  -> match a,b  with 
      | Some a, Some b -> Some (MLBDD.dor a b)
      | Some a, _ -> Some a 
      | _ , Some b -> Some b
      | _ -> None) al bl

  let add_cond i c bs = Bindings.add i (match (Bindings.find_opt i bs) with 
    | Some x -> (MLBDD.dor c x)
    | None -> c
  ) bs

  let add_conds is c bs = cond_merge bs (Seq.map (fun i -> i, c) is |>  Bindings.of_seq)


  (* only update deps *)
  let clobber_var v st =
    let var_clas = Bindings.map (fun c -> match c with Defined ids | Clobbered ids when IdentSet.mem v ids -> Clobbered ids | _ -> c) st.var_clas in
    (*let st = {st with cond_clobbered = (add_cond v (st.bdd.ctx) st.cond_clobbered)} in *)
    let st = Seq.fold_left (fun st (i,c) -> 
          match c with 
        | Defined ids 
        | Clobbered ids when IdentSet.mem v ids 
          -> {st with cond_clobbered = (add_cond i (st.bdd.ctx) st.cond_clobbered)}
        | _ -> st
    ) st (Bindings.to_seq var_clas) in
    { st with var_clas }

  let update_clobbers st = 
    (* update everything based on the conditions of their dependencies *)
    let ids = Bindings.to_seq st.cond_clobbered  in
    Seq.fold_left (fun st (iv,cond) -> 
      let var_clas = Bindings.map (fun c -> match c with Defined ids | Clobbered ids when IdentSet.mem iv ids -> Clobbered ids | _ -> c) st.var_clas in
      let st = Seq.fold_left (fun st (ii,c) -> match c with 
          | Defined ids 
          | Clobbered ids when IdentSet.mem ii ids -> {st with cond_clobbered = (add_cond ii cond st.cond_clobbered)}
          | _ -> st
      ) st (Bindings.to_seq var_clas) in
      { st with var_clas }
    )  st ids



  let get_var v st = Bindings.find_opt v st.var_clas

  let merge_st (ts:MLBDD.t) (fs:MLBDD.t) (joined: Transforms.BDDSimp.state) xa xb =
    let merge_cond a b = (MLBDD.dor (MLBDD.dand ts a) (MLBDD.dand fs b)) in
    let merged_bdd = Bindings.merge (fun (k:ident) a b -> match a,b with 
      | Some a, Some b -> Some (merge_cond a b)
      | Some a, None ->  Some (MLBDD.dand ts a)
      | None, Some a -> Some (MLBDD.dand fs a)
      | None, None -> None) in
    let cond_clobbered = merged_bdd xa.cond_clobbered xb.cond_clobbered in
    let cond_read = merged_bdd xa.cond_read xb.cond_read in
    let cond_dep = Bindings.merge (fun k a b -> match a,b with 
        | Some (isa, a), Some (isb, b) -> Option.map (fun x -> x, IdentSet.union a b) (Some (merge_cond isa isb))
        | Some (isa, a), None -> Some (MLBDD.dand ts isa, a)
        | None, Some (isa, a) -> Some (MLBDD.dand fs isa, a)
        | _ -> None
    ) xa.cond_dep xb.cond_dep in
    let var_clas = Bindings.merge (fun k a b ->
      match a, b with
      | Some a, Some b -> Some (merge_clas a b)
      | Some a, None
      | None, Some a -> Some a
      | None, None -> None) xa.var_clas xb.var_clas in
    let st : state = {xa with bdd=joined; var_clas ; cond_clobbered=cond_clobbered;  cond_read=cond_read; cond_dep=cond_dep } in 
    st


  let init_state reachable = {bdd=Transforms.BDDSimp.init_state reachable; 
    var_clas = Bindings.empty; ctx = []; 
    cond_clobbered = Bindings.empty ; 
    cond_read = Bindings.empty ; 
    cond_dep = Bindings.empty}

  let push_context m st = { st with ctx = m::st.ctx }
  let peek_context st = match st.ctx with x::xs -> x | _ -> invalid_arg "peek_context"
  let pop_context st = let (i,c),tl = (match st.ctx with x::xs -> x,xs | _ -> invalid_arg "pop_context") in
    { st with ctx = tl ; bdd = {st.bdd with ctx = c} }

  let has_context st = List.length st.ctx > 0

  let decl_var v st = set_var v Declared st
  let define_var v deps st = 
    let r = set_var v (Defined deps) st in 
    let cond_dep = Bindings.find_opt v st.cond_dep |> 
      Option.map (fun (c,b) -> MLBDD.dor c (st.bdd.ctx), IdentSet.union b deps) |>
    function 
    | Some c -> Bindings.add v c st.cond_dep
    | None -> st.cond_dep
    in
    {r with cond_dep }

  type xform = 
    | Prop 
    | PropCond of MLBDD.t (* encoding whether prop is allowed *)
    | No

  let read_var v (st,i) =
    let st = {st with cond_read = (add_cond v (st.bdd.ctx) st.cond_read )} in
    match get_var v st with
    (* Reading undeclared generally means a value that is gradually constructed through partial updates *)
    | Some (Declared) -> (set_var v Essential st, i)
    (* Reading clobbered implies we cannot reorder *)
    | Some (Clobbered deps) -> (st, IdentSet.union i deps)
        (*if (Transforms.BDDSimp.is_true clobbered st.bdd) then (set_var v Essential st, i) else st, i) *)
    (* Collect ids for transitive walk given a defined variable *)
    | Some (Defined ids) -> (st, IdentSet.union i ids)
    | _ -> (st, i)

  let write_var v (st,i) =
    let st = if has_context st then (set_var v Essential st) else st  in
      (* cannot copy-prop exprs dependent on a run-time branch*)
    let st = clobber_var v st in
    let (st,i) = match get_var v st with
    | Some (Declared) -> (set_var v (Defined i) st, i)
    | Some (Defined ids) -> ((set_var v (Clobbered i) st), i)
    | Some (Clobbered deps) -> (st, i)
    | Some Essential -> (st, i)
      | None -> (st, i)
  in  (st,i)


  let impure_ident = Ident "CopyProp_impure"

  let read_vars (vs: IdentSet.t) (st: state): state =
    let read_set s st = IdentSet.fold read_var s (st,IdentSet.empty) in
    (* If impure is in the readset, the reads are not pure. Clobber any impure dependencies now. *)
    let st = if IdentSet.mem impure_ident vs then clobber_var impure_ident st else st in
    (* Reading variables after they are clobbered shifts them to essential vars *)
    let rec iter delta seen st =
      let (st,deps) = read_set delta st in
      let seen = IdentSet.union seen delta in
      let delta = IdentSet.diff deps seen in
      if IdentSet.cardinal delta = 0 then st
      else iter delta seen st in
    iter vs IdentSet.empty st

  (* TODO: Updating, check if this has some context dependence *)
  let update_deps v deps st =
    if has_context st then (set_var v Essential st) (* cannot copy-prop exprs dependent on a run-time branch*)
    else
      match get_var v st with
      | Some (Declared) ->
          set_var v (Defined deps) st
      | Some (Defined d') ->
          set_var v (Defined (IdentSet.union deps d')) st
      | Some (Clobbered d') ->
          set_var v (Clobbered (IdentSet.union deps d')) st
      | _ -> st

  class deps_walker = object (self)
    inherit Asl_visitor.nopAslVisitor
    val mutable deps = IdentSet.empty

    method add_dep i = deps <- IdentSet.add i deps
    method get_deps = deps

    method! vexpr = function
      | Expr_TApply (f, _, _) when is_lit f ->
          SkipChildren
      | Expr_TApply (f, [], [Expr_Var v]) when is_var_load f ->
          self#add_dep v;
          SkipChildren
      | Expr_TApply (f, [], [e;_;_]) when is_slice f ->
          let _ = self#vexpr e in
          SkipChildren
      | Expr_TApply (f, tes, es) when is_pure_expr f ->
          let _ = List.map (self#vexpr) es in
          SkipChildren
      | Expr_TApply (f, [], [Expr_Var a;i]) when is_array_load f ->
          self#add_dep a;
          SkipChildren
      | Expr_TApply(f, _, es) when is_gen_call f ->
          self#add_dep impure_ident;
          let _ = List.map (self#vexpr) es in
          SkipChildren
      | e -> (if debug_log then Printf.printf "Unknown runtime expression: %s\n"  (pp_expr e)); DoChildren
  end

  let get_deps e =
    let v = new deps_walker in
    let _ = Asl_visitor.visit_expr v e in
    v#get_deps




  let rec walk_stmt s st =
    match s with
    (* Var decl *)
    | Stmt_ConstDecl(t, v, Expr_TApply(f, [], args), loc) when is_var_decl f ->
        decl_var v st 

    (* Var assign *)
    | Stmt_TCall(f, [], [Expr_Var v; e], loc) when is_var_store f ->
        (* Collect reads and process them all *)
        let deps = get_deps e in
        let st = read_vars deps st in
        (* Clobber anything dependent on v *)
        let st,deps = write_var v (st,deps) in
        (* Update deps for v *)
          st
        (*update_deps v deps st*)

    (* Array assign *)
    | Stmt_TCall(f, [], [Expr_Var a; i; e], loc) when is_array_store f ->
        (* Collect reads and process them all *)
        let deps = get_deps e in
        let st = read_vars deps st in
        (* Clobber anything dependent on a *)
        let st,deps = write_var a (st,deps) in
        st

    (* Assert *)
    | Stmt_TCall(f, [], [e], loc) when is_assert f ->
        (* Collect reads and process them all *)
        let deps = get_deps e in
        read_vars deps st

    (* LiftTime branch *)
    | Stmt_If(c, t, [], f, loc) ->  
        (* merge in the bdds as well *)
        let deps = get_deps c in
        read_vars deps st
        (* branches handled by caller splitting, walking children, and joining *)

        (*
        let cond = Transforms.BDDSimp.eval_expr c st.bdd in
        let c = Transforms.BDDSimp.rebuild_expr c cond st.bdd in
        let ncond = Transforms.BDDSimp.not_bool cond in
        let tst:state = walk_stmts t {st with bdd = (Transforms.BDDSimp.restrict_ctx cond {st.bdd with stmts = []})} in
        let fst:state = walk_stmts f {st with bdd = (Transforms.BDDSimp.restrict_ctx ncond {st.bdd with stmts = []})} in

        let condbdd = match cond with 
          | Val [t] -> t
          | _ -> failwith (Printf.sprintf "unable to eval cond branch %s %s %s"   (Transforms.BDDSimp.pp_abs cond) (Transforms.BDDSimp.pp_state st.bdd) (pp_expr c) )
        in

        let st': state  = merge_st cond tst fst in
        let st'= {st' with bdd = Transforms.BDDSimp.writeall st.bdd.stmts st'.bdd} in
        let st' = {st' with bdd = Transforms.BDDSimp.write (Stmt_If (c, tst.bdd.stmts, [], fst.bdd.stmts, loc)) st'.bdd} in
        *)


    (* RunTime branch *)
    | Stmt_ConstDecl(t, v, Expr_TApply(f, [], [c]), loc) when is_branch f ->
        (* Collect reads and process them all *)
        let deps = get_deps c in
        let st = read_vars deps st in
        (* Push the merge point *)
        push_context (v, st.bdd.ctx) st

    (* Context switch *)
    | Stmt_TCall(f, [], [Expr_TApply(f2, [], [Expr_Var i])], loc) when is_context_switch f && is_merge_target f2 ->
        let top = fst (peek_context st) in
        if i = top then ((pop_context st)) else st

    (* Impure effect *)
    | Stmt_TCall(f, _, es, loc) when is_gen_call f ->
        (* Collect reads and process them all *)
        let st = List.fold_right (fun e st ->
          let deps = get_deps e in
          read_vars deps st) es st in
        (* Clobber everything linked to global state *)
        clobber_var impure_ident st

    | v -> st

  and walk_stmts s st : state =
    List.fold_left (fun st s -> walk_stmt s st) st s


  (* To change this, you'd need to know :
      - The condition under which its safe to copy prop
      - The current reachability

     If you can't establish you are guarded, implies you need to introduce a branch.
     The branch will have the outcomes of both exp reduction and maintaining the current temp.
     Then need to specialise everything downstream for this point based on this introduced branch.

     This means you need to pull the condition out to the front.
     Which means its needs to be fully reduced and in terms of enc.
     BDD approach gives us this flexibility, every single condition in the program in terms of original enc.
     Relatively simple to reduce from that point: eliminate guards based on reachability, etc.

     You can implement constant-prop and dead code in a similar fashion, as long as your notions of conditional
     use / redefinition / loss of constant precision is purely in terms of the original enc.

statement s is the only definition of x reaching u on every path from s to u there are no assignments to y 

   *)


  (*
    variable is not clobbered then read
  *)
  let cond_candidate v st rtst = 
    match get_var v st with
    | Some Essential -> No
    | Some Clobbered deps ->
        let c = Bindings.find_opt v st.cond_read in
        let b = Bindings.find_opt v st.cond_clobbered in
        (match c,b with
        | Some read,Some clob -> 
            let cond =  (MLBDD.dand read (MLBDD.dnot clob)) in
          (if (Transforms.BDDSimp.is_true (Val [cond]) rtst) then 
              (
            (*Printf.printf "Condcopyprop prop var %s read => clobbered %s simplifies to FALSE\n" (pprint_ident v) (Transforms.BDDSimp.pp_abs (Val [MLBDD.dand read (MLBDD.dnot clob)])) ; *)
            Prop
            )
          else 
            if (Transforms.BDDSimp.is_false (Val [cond]) rtst) then 
            (
              (* we don't need to generate a condition at read if we know statically *)
              (*Printf.printf "Condcopyprop noprop var %s read => clobbered %s simplifies to TRUE\n" (pprint_ident v) (Transforms.BDDSimp.pp_abs (Val [cond])); *)
            No) 
          else PropCond (cond))
          | Some _, None -> if debug_log then Printf.printf "UNCONCD PROP\n" ; Prop
          | _,_ -> (*Printf.printf "Condcopyprop: Clobbered variable missing cond read %s\n" (pprint_ident v);  *)
            No) (* TODO: clobbered but not subsequently read? *)
    | Some Defined _ -> (*Printf.printf "Condcopyprop ONLY DEFINED %s\n" (pprint_ident v);*) Prop 
    | Some Declared ->  No
    | None ->  No 



  let cp_idents = function 
    | Ident c -> Ident (c) , Ident (c ^ "_copyprop")
    | _ -> failwith "only copyprop vars"

  type cand = {
    typ: ty
  }



  class cond_copyprop_transform cpst = object(self) 
    inherit Asl_visitor.nopAslVisitor
    val mutable rtst = None

    val mutable candidates : cand Bindings.t = Bindings.empty

    method xf_stmt (x:stmt) (st:Transforms.BDDSimp.state) : stmt list = 
      rtst <- Some st; Asl_visitor.visit_stmt self x 

    method candidate v = (Prop = (cond_candidate v cpst (Option.get rtst)))
    method essential v = (No = (cond_candidate v cpst (Option.get rtst)))

    method! vstmt s = ChangeDoChildrenPost ([s], fun s -> List.concat_map self#stmt_xform s)
    method! vexpr e = ChangeDoChildrenPost (e, fun e -> self#expr_xform e)


  (*
    Decl of candidate -> decl of expr ref + decl of tmp (unless its never clobbered)
    Write to candidate -> if !clobbered, write to expr ref, else write to tmp
    Read of candidate -> Wrap whole statement in same test, read from appropriate var
  *)

    (*
    For run-time variables that we have determined we can copyprop, 
    pull them to lift-time variables so they can be conditionally 
    copy-propagated at lift time. 
    *)
    method stmt_xform (s : stmt) : stmt list = 
    let cp_cond c = Option.get (Transforms.BDDSimp.bdd_to_expr (Val [c]) (Option.get rtst)) in
    match s with 
      (* Transform runtime variable decls into expression decls *)
      | Stmt_ConstDecl(t, v, Expr_TApply(f, [], args), loc) when is_var_decl f  ->
          candidates <- Bindings.add v {typ=t} candidates; 
          (match (cond_candidate v cpst (Option.get rtst)) with 
            | No -> if debug_log then Printf.printf "Condcopyprop: NOT PROP at DEFINITION of var %s\n " (pprint_ident v);
                [s] 
            | Prop ->  
                (* move run-time to lift-time *)
                  (*Printf.printf "Condcopyprop: UNCOND prop at DEFINITION of var %s\n " (pprint_ident v); *)
                  [Stmt_VarDeclsNoInit (Offline_transform.rt_expr_ty, [snd (cp_idents v)], Unknown)]  
            | PropCond cond -> 
              let ncp,cp = cp_idents v in
                (* if (cond) lift-time else run-time *)
              if debug_log then Printf.printf "Condcopyprop: CONDITIONAL prop at DEFINITION %s: %s\n " (pprint_ident v) (Transforms.BDDSimp.pp_abs (Val [cond]));
              (*let c = cp_cond cond in *)
              (* lift-time conditionally generates the copy-propagated or non-propagated form *)
              [ 
                Stmt_ConstDecl (Offline_transform.rt_expr_ty, ncp, Expr_TApply(f, [], args), Unknown);
                Stmt_VarDeclsNoInit (Offline_transform.rt_expr_ty, [cp], Unknown);
              ]
          )
      (* Transform stores into assigns *)
      | Stmt_TCall(f, [], [Expr_Var v; e], loc) when is_var_store f  ->
          (match (cond_candidate v cpst (Option.get rtst)) with 
            | No -> (*(Printf.printf "Condcopyprop: UNCOND DISABLE PROP on STORE of var %s\n " (pprint_ident v));*)  [s]
            | Prop -> 
                  (if debug_log then Printf.printf "Condcopyprop: UNCOND RT PROP on STORE of var %s\n " (pprint_ident v);
                  [(Stmt_Assign (LExpr_Var (snd (cp_idents v)), e, loc))])
            | PropCond cond -> let nocp,cp = cp_idents v in
                  if debug_log then Printf.printf "Condcopyprop: CONDITIONAL rt prop on STORE of var %s\n " (pprint_ident v);
              (*
                 - if copy-prop'ed form is reachable then generate a store statement
                 - if non-copyprop'ed form is reachable then generate an assignment statement
              *)
              (* can re-evaluating an expression have side effects? *)

              let gen_store_rt_var = Stmt_TCall(f, [], [Expr_Var nocp; e], loc) in
              let assign_lt_var = Stmt_Assign(LExpr_Var cp, e, loc) in
              (* TODO: could further narrow cases here using bdd*)
              [Stmt_If ( cp_cond cond, [assign_lt_var], [], [gen_store_rt_var], Unknown)]
        )
      | Stmt_TCall(f, _, _, _) when is_var_store f  -> failwith "unhandled store"
      | _ -> [s]

    method expr_xform (e:expr) : expr = match e with
      | Expr_TApply(f, [], [Expr_Var v]) when is_var_load f ->
          (match (cond_candidate v cpst (Option.get rtst)) with 
          | No ->  e
          | Prop ->  Expr_Var (snd (cp_idents v))
          | PropCond cpcond -> let ncp,cp = cp_idents v  in
            let load = Expr_TApply(f, [], [Expr_Var ncp]) in
            let prop = Expr_Var cp in
            let yescpcond = Option.get (Transforms.BDDSimp.bdd_to_expr (Val [cpcond]) (Option.get rtst)) in
            let vt = Bindings.find v candidates in
            (* TODO: might be good to check that yes and no are disjoint here *)
            let e = Expr_If (vt.typ, yescpcond, prop, [] , load) in
          e  
        )

      | Expr_TApply(f, [], [Expr_Var v; e]) when is_var_store f  -> failwith "store expression";
      | _ -> e
  end

  module AnalysisLat = struct 
    let debug_log = false
    type rt = state
    type olt = Transforms.BDDSimp.state
    let xfer_stmt (l:olt) (r:rt) (s:stmt) : rt * stmt list = 
      (*Printf.printf "%s ::\n%s\n" (pp_stmt s) (Transforms.BDDSimp.pp_state l);*) 
      (walk_stmt s r,[s])
    let join (ts:olt) (fs:olt) (js:olt) (rta: rt) (rtb: rt) = if debug_log then Printf.printf "ts %s fs %s" 
      (Transforms.BDDSimp.pp_abs (Val [ts.ctx])) 
      (Transforms.BDDSimp.pp_abs (Val [fs.ctx]))
      ; 
      if debug_log then Printf.printf "\n--------------\n";
      let p s rta = if debug_log then  Printf.printf "%s: %s\n" s (pp_state rta) in 
      p "\nTRUE BRANCH: " rta;  p "\nFALSE BRANCH: " rtb ;  

      let j = merge_st ts.ctx fs.ctx (js:olt) rta rtb in
      p "\nJOIN STATE: " j;
      if debug_log then Printf.printf "\n==============\n"; 
      j

    let init s = init_state s 
  end

  module TransformLat  = struct 
    (* warning: internally mutable because order should not matter etc, join is no-op *)
    type rt = {cpst: cond_copyprop_transform}
    type olt = Transforms.BDDSimp.state
    let xfer_stmt ol ss s =  ss,ss.cpst#xf_stmt s ol
    let join t f j a b = if (a != b) then (failwith "not allowed") else a (* only have one instance of the object so should be fine *)
    let init st = {cpst = new cond_copyprop_transform st} 
  end

  module BDDAnalysis = Transforms.BDDSimp.EvalWithXfer(AnalysisLat)
  module BDDTransform = Transforms.BDDSimp.EvalWithXfer(TransformLat)

  let do_transform reachable copyprop_st stmts = 
    (* apply BDD AI a second time to compare reachability with candidates in analysis pass *)
    let st = Transforms.BDDSimp.init_state reachable in
    let st = Transforms.BDDSimp.set_enc st in 
    let olt,ort = BDDTransform.eval_stmts (TransformLat.init copyprop_st) stmts st in
    olt.stmts

  let run fn reachable  body =
    flush stdout;
    if debug_log then Printf.printf "transforming %s\n" (pprint_ident fn);
    let st : AnalysisLat.rt = init_state reachable in
    let rtst = Transforms.BDDSimp.init_state reachable in
    let rtst = Transforms.BDDSimp.set_enc rtst in 
    (*let st = walk_stmts body st in *)
    let a,b = BDDAnalysis.eval_stmts st body rtst in
    (* Printf.printf "%s : %s\n" (pprint_ident fn) (pp_essential st); *)
    (* Printf.printf "%s : %s\n" (pprint_ident fn) (pp_state st); *)
    do_transform reachable b body

end
