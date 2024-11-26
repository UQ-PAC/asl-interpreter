(****************************************************************
 * ASL dissassembler
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** ASL dissassembler *)

module PP   = Asl_parser_pp
module AST  = Asl_ast
module TC   = Tcheck

open AST
open Asl_utils
open Value

open Symbolic

module StringCmp = struct
    type t = string
    let compare (x: string) (y: string): int = String.compare x y
end
module StringMap = Map.Make(StringCmp)

let debug_level_none = -1
let debug_level = ref debug_level_none
let debug_show_trace = ref false
let no_debug = fun () -> !debug_level <= debug_level_none

(** (name, arg, location) tuple for tracing disassembly calls.
    For example: ("dis_expr", "1+1", loc).
*)
type dis_trace = (string * string * l) list

exception DisTrace of dis_trace * exn
exception DisUnsupported of l * string
exception DisInternalError of l * string

let unsupported (loc: l) (msg: string) =
  raise (DisUnsupported (loc, msg))

let internal_error (loc: l) (msg: string) =
  raise (DisInternalError (loc, msg))

let print_dis_trace (trace: dis_trace) =
    String.concat "\n" @@ List.map (fun (f, e, l) ->
        Printf.sprintf "... at %s: %s --> %s" (pp_loc l) f e)
        (trace)

let () = Printexc.register_printer
    (function
    | DisTrace (trace, exn) ->
        let trace' =
            if !debug_level >= 1 || !debug_show_trace
            then "\n" ^ print_dis_trace trace
            else ""
        in
        Some (Printexc.to_string exn ^ "\n" ^ trace')
    | DisUnsupported (loc, s) ->
        Some ("DisUnsupported: " ^ pp_loc loc ^ ": " ^ s)
    | DisInternalError (loc, s) ->
        Some ("DisInternalError: " ^ pp_loc loc ^ ": " ^ s)
    | Value.Throw (loc, e) ->
        Some ("LibASL.Value.Throw(" ^ Primops.pp_exc e ^ ") at " ^ pp_loc loc)
    | Value.EvalError (loc, e) ->
        Some ("LibASL.Value.EvalError(\"" ^ e ^ "\") at " ^ pp_loc loc)
    | _ -> None)

(* Don't inline these functions, as we assume their behaviours conform to some spec *)
let no_inline = [
  "FPConvert",0;
  "FPRoundInt",0;
  "FPRoundIntN",0;
  "FPToFixed",0;
  "FixedToFP",0;
  "FPCompare",0;
  "FPCompareEQ",0;
  "FPCompareGE",0;
  "FPCompareGT",0;
  "FPToFixedJS_impl",0;
  "FPSqrt",0;
  "FPAdd",0;
  "FPMul",0;
  "FPDiv",0;
  "FPMulAdd",0;
  "FPMulAddH",0;
  "FPMulX",0;
  "FPMax",0;
  "FPMin",0;
  "FPMaxNum",0;
  "FPMinNum",0;
  "FPSub",0;
  "FPRecpX",0;
  "FPRecipStepFused",0;
  "FPRSqrtStepFused",0;
  "FPRoundBase",0;
  "FPConvertBF",0;
  "BFRound",0;
  "BFAdd",0;
  "BFMul",0;
  "FPRecipEstimate",0;
  "FPRSqrtEstimate",0;
  "UnsignedRSqrtEstimate",0;
  "Mem.read",0;
  "Mem.set",0;
  "AtomicStart",0;
  "AtomicEnd",0;
  "AArch64.MemTag.read",0;
  "AArch64.MemTag.set",0;
]

let no_inline_pure () = [
  "LSL",0;
  "LSR",0;
  "ASR",0;
  "SignExtend",0;
  "ZeroExtend",0;
] @ (if !Symbolic.use_vectoriser then [
  "Elem.set",0;
  "Elem.read",0;
] else [])



(** A variable's stack level and original identifier name.
    The "stack level" is how many scopes deep it is.
    For example, globals are level 0 and this increases
    by 1 for each nested function call.  *)
type var = Var of int * string
let pp_var (Var (i,id)) = Printf.sprintf "Var(%d,%s)" i (id)
let var_ident (Var (i,id)) =
  match i,id with
  | 0,s -> Ident s (* special case globals with no suffix. *)
  | _,s -> Ident (s ^ "__" ^ string_of_int i)

(** Returns the variable's name without mangling, suitable for
    disassembling then resolving again.

    WARNING: should only be used when variable is in the inner-most scope. *)
let var_expr_no_suffix_in_local_scope (Var(_,id)) = Expr_Var (Ident id)

(** Returns an expression for the variable with a mangled name,
    suitable for emitting in a generated statement. *)
let var_expr v = Expr_Var (var_ident v)

(** Returns an L-expression for the variable with a mangled name,
    suitable for emitting in a generated statement. *)
let var_lexpr v = LExpr_Var (var_ident v)

(** Returns a sym for the variable with a mangled name,
    suitable for use in a subsequent sym expression.

    WARNING: should only be used when the given variable is
    never re-assigned.
    *)
let var_sym_expr v = Exp (var_expr v)

module LocalEnv = struct
    type t = {
        (* local state, also containing globals at the outer-most level.
           ordered with inner scopes first in list. *)
        (* satisfies invariants that:
           - all values/expressions contained are constant and safe to propagate.
           - a value of VUninitialized indicates that value is unknown.
           - VUninitialized itself is only used for scalar types.
             thus, uninitialized structures must be expanded into structures of uninitialized scalars.
           *)
        locals          : (ty * sym) StringMap.t list;
        returnSymbols   : expr option list;
        numSymbols      : int;
        indent          : int;
        trace           : dis_trace;
    }

    let force i =
      match i with Ident s -> s | _ -> unsupported Unknown ""

    let pp_value_bindings = Utils.pp_list (pp_bindings pp_value)

    let pp_bindings (pp: 'a -> string) (bs: 'a StringMap.t): string =
        String.concat ", " (List.map (fun (k, v) -> k ^"->"^ pp v) (StringMap.bindings bs))

    let pp_sym_bindings (bss: (ty * sym) StringMap.t list) =
        Utils.pp_list (pp_bindings (fun (_,e) -> pp_sym e)) bss

    let init (env: Eval.Env.t) =
        let eval e = val_expr (Eval.eval_expr Unknown env e) in
        let tenv = !Tcheck.env0 in
        let get_global_type id =
            (match Tcheck.GlobalEnv.getGlobalVar tenv id with
            | Some (Type_Bits e) ->
                (Type_Bits (eval e))
            | Some (Type_App (i, es)) ->
                (Type_App (i, List.map eval es))
            | Some t -> (t)
            | _ -> internal_error Unknown @@ "cannot find type for global: " ^ pprint_ident id)
        in

        let globals = Eval.Env.readGlobals env in
        let consts = Eval.Env.readGlobalConsts env in

        let merge_left k l r = Some l in
        let globalsAndConsts = Bindings.union merge_left globals consts
        in
        let globals = Bindings.mapi
            (fun id v -> (get_global_type id, Val v))
            globalsAndConsts in
    let globals = StringMap.of_seq @@ Seq.map ( fun (k,v) -> (force k,v)) @@ Bindings.to_seq globals in
        {
            locals = [StringMap.empty ; globals];
            returnSymbols = [];
            numSymbols = 0;
            indent = 0;
            trace = [];
        }

    let sequence_merge (first: t) (second: t): t =
        {
            first with numSymbols = max first.numSymbols second.numSymbols
        }

    let pp_locals (env: t): string =
        let last = List.length env.locals - 1 in
        let withoutGlobals = List.mapi
            (fun i x -> if i = last then StringMap.empty else x) env.locals in
        Printf.sprintf "locals = %s" (pp_sym_bindings withoutGlobals)
        (* Printf.sprintf "locals = %s" (pp_sym_bindings env.locals) *)

    let getReturnSymbol (loc: l) (env: t): expr =
        match env.returnSymbols with
        | [] -> internal_error loc "attempt to return from outside a function"
        | None :: _ -> internal_error loc "attempt to return a value from inside a procedure"
        | Some e :: rs -> e

    let addReturnSymbol (e: expr option) (env: t): t =
        {env with returnSymbols = e :: env.returnSymbols}

    let removeReturnSymbol (env: t): t =
        match env.returnSymbols with
        | [] -> internal_error Unknown "attempt to remove return symbol but no return symbols exist"
        | (s::ss) -> {env with returnSymbols = ss}

    let getNumSymbols (env: t): int =
        env.numSymbols

    let incNumSymbols (env: t): int * t =
        let env' = {env with numSymbols = env.numSymbols + 1} in
        (env'.numSymbols, env')

    let getLocalPrefix (env: t): string =
        string_of_int (List.length env.locals)

    let getLocalName (x: ident) (env: t): ident =
        Ident (pprint_ident x ^ "__" ^ getLocalPrefix env)

    (** Adds a local scoping level within the current level.  *)
    let addLevel (env: t): t =
        {env with locals = (StringMap.empty)::env.locals}

    (** Pops the innermost scoping level.  *)
    let popLevel (env: t): t =
        match env.locals with
        | [] -> internal_error Unknown "attempt to pop local scope level but none exist"
        | (_::ls) -> {env with locals = ls}

    (** Adds a new local variable to the innermost scope. *)
    let addLocalVar (loc: l) (k: ident) (v: sym) (t: ty) (env: t): var * t =
        let k = force k in
        if !Eval.trace_write then Printf.printf "TRACE: fresh %s = %s\n" (k) (pp_sym v);
        let var = Var (List.length env.locals - 1, k) in
        match env.locals with
        | (bs :: rest) -> var, {env with locals = (StringMap.add k (t,v) bs :: rest)}
        | []        -> internal_error Unknown "attempt to add local var but no local scopes exist"

    let addLocalConst = addLocalVar

    (** Gets the type and value of a resolved variable. *)
    let getVar (loc: l) (x: var) (env: t): (ty * sym) =
        let Var (i,id) = x in
        let n = List.length env.locals - i - 1 in
        match StringMap.find_opt id (List.nth env.locals n) with
        | Some x -> x
        | None -> internal_error loc @@ "failed to get resolved variable: " ^ pp_var x

    (** Resolves then gets the type and value of a resolved variable. *)
    let rec go loc x env i (bs: (ty * sym) StringMap.t list) =
        (match bs with
        | [] -> internal_error loc @@ "cannot resolve undeclared variable: " ^ x ^ "\n\n" ^ pp_locals env
        | b::rest -> match StringMap.find_opt x b with
          | Some v -> (Var (i,x),v)
          | _ -> go loc x env (i - 1) rest)
    let resolveGetVar (loc: l) (x: ident) = fun env ->
        let x = force x in
        let l = List.length env.locals - 1 in
        match env.locals with
        | b::rest -> (match StringMap.find_opt x b with
          | Some v -> (Var (l,x),v)
          | _ -> go loc x env (l - 1) rest)
        | _ -> internal_error loc @@ "cannot resolve undeclared variable: " ^ x ^ "\n\n" ^ pp_locals env

    (** Sets a resolved variable to the given value. *)
    let setVar (loc: l) (x: var) (v: sym) (env: t): t =
        if !Eval.trace_write then Printf.printf "TRACE: write %s = %s\n" (pp_var x) (pp_sym v);
        let Var (i,id) = x in
        let n = List.length env.locals - i - 1 in
        let locals = Utils.nth_modify (
          StringMap.update id (fun e -> match e with
          | Some (t,_) -> Some (t,v)
          | None -> internal_error loc @@ "failed to set resolved variable: " ^ pp_var x)) n env.locals in
        { env with locals }

end

type tree =
    Node of stmt list
  | Branch of tree * tree

let empty = Node []
let single x = Node x
let append x y =
  match x, y with
  | Node [], _ -> y
  | _, Node [] -> x
  | Node [x], Node y -> Node (x::y)
  | _ -> Branch (x, y)

let rec flatten x acc =
  match x with
  | Branch (x,y) ->
      let acc = flatten y acc in
      flatten x acc
  | Node i -> i@acc

type config = {
  eval_env: Eval.Env.t;
  unroll_bound: Z.t;
}

module DisEnv = struct
    include Rws.Make(struct
        type r = config
        type w = tree
        type s = LocalEnv.t
        let mempty = empty
        let mappend = (append)
    end)

    open Let

    let getVar (loc: l) (x: ident): (ty * sym) rws = fun env s ->
        let (_,v) = LocalEnv.resolveGetVar loc x s in
        (v,s,empty)

    let uninit (t: ty) (config): value =
        try
            Eval.mk_uninitialized Unknown config.eval_env t
        with
            e ->
              (* Support bit widths we don't know *)
              match t with
              | Type_Bits _ -> VUninitialized t
              | _ -> unsupported Unknown @@
                "mkUninit: failed to evaluate type " ^ pp_type t ^ " due to " ^
                Printexc.to_string e

    let mkUninit (t: ty): value rws =
        reads (uninit t)

    let merge_bindings env l r: (ty * sym) StringMap.t =
      if l == r then l else
      StringMap.union (fun k (t1,v1) (t2,v2) ->
        if !debug_level > 0 && t2 <> t1 then
            unsupported Unknown @@
              Printf.sprintf "cannot merge locals with different types: %s, %s <> %s."
              (k) (pp_type t1) (pp_type t2);
          let out = Some (t1,match v1 = v2 with
            | false -> Val (uninit t1 env)
            | true -> v1)  in
          out) l r

    let join_locals (l: LocalEnv.t) (r: LocalEnv.t): unit rws = fun env s ->
        assert (l.returnSymbols = r.returnSymbols);
        assert (l.indent = r.indent);
        assert (l.trace = r.trace);
        let locals' = List.map2 (merge_bindings env) l.locals r.locals in
        let s : LocalEnv.t = {
            locals = locals';
            returnSymbols = l.returnSymbols;
            numSymbols = max l.numSymbols r.numSymbols;
            indent = l.indent;
            trace = l.trace;
        } in
        ((),s,empty)


    (** Merge two states, return change flag if RHS must change to merge with LHS.
      * Idea is RHS is the fixed-point state at loop entry, needs to be gradually weakened
      * to include LHS.
      *)
    let merge_bindings_fp env l r: ((ty * sym) StringMap.t * bool) =
      let changed = ref false in
      if l == r then (l,false) else
        let out = (StringMap.union (fun k (t1,v1) (t2,v2) ->
          let out = Some (t1,match v1, v2 with
            | v1, v2 when v1 = v2 -> v1
            | _, Val (VUninitialized _) -> v2
            | _, Val (VArray (ar,v)) when Primops.ImmutableArray.is_empty ar -> v2
            | _ ->
                changed := true;
                Val (uninit t1 env))  in
          out) l r) in (out, !changed)

    (** Same concept as above *)
    let join_locals_fp (l: LocalEnv.t) (r: LocalEnv.t): bool rws = fun env s ->
        assert (l.returnSymbols = r.returnSymbols);
        assert (l.indent = r.indent);
        assert (l.trace = r.trace);
        let (locals') = List.map2 (merge_bindings_fp env) l.locals r.locals in
        let changed = List.mem true (List.map snd locals') in
        let locals' = List.map fst locals' in
        let s : LocalEnv.t = {
            locals = locals';
            returnSymbols = l.returnSymbols;
            numSymbols = max l.numSymbols r.numSymbols;
            indent = l.indent;
            trace = l.trace;
        } in
        (changed,s,empty)

    let getFun (loc: l) (x: ident): Eval.fun_sig option rws =
        reads (fun config -> Eval.Env.getFunOpt loc config.eval_env x)

    let nextVarName (prefix: string): ident rws = fun env s ->
        let num, s = LocalEnv.incNumSymbols s in
        (Ident (prefix ^ string_of_int num),s,empty)

    let indent: string list rws =
        let+ i = gets (fun l -> l.indent) in
        (* when concatenated, produces a string of the form:
                "| I | I | ..." where | and I are
           alternating unicode box-drawing lines *)
        List.init i (fun i -> if i mod 2 == 0 then "\u{2502} " else "\u{250a} ")

    let debug (minLevel: int) (s: string): unit rws =
        if !debug_level >= minLevel then
            let+ i = indent in
            List.iter
              (fun l -> List.iter print_string i; print_endline l)
              (String.split_on_char '\n' s);
            ()
        else
            unit

    let log (s: string): unit rws =
        debug 1 s

    let warn s = debug 0 ("WARNING: " ^ s)

    let write i = fun e x -> ((),x,Node i)

    let scope (loc: l) (name: string) (arg: string) (pp: 'a -> string) (x: 'a rws): 'a rws =
        (* logging header. looks like: +- dis_expr --> 1 + 1. *)
        log (Printf.sprintf "\u{256d}\u{2500} %s --> %s" name arg) >>

        (* add indentation level for logging. *)
        modify (fun l -> {l with indent = l.indent + 1}) >>
        modify (fun l -> {l with trace = (name,arg,loc)::l.trace}) >>
        let* trace = gets (fun l -> l.trace) in

        (* run computation but obtain state and writer to output in debugging. *)
        let* (result,s',w') = locally (catcherror x) in
        let w' = flatten w' [] in
        let x' = (match result with
        | Error ((DisTrace _) as e, bt) -> raise e
        | Error (exn, bt) -> Printexc.raise_with_backtrace (DisTrace (trace, exn)) bt
        | Ok x' -> x') in
        (* restore state and writer. *)
        write w' >>
        put s' >>
        (* remove indentation level. *)
        modify (fun l -> {l with indent = l.indent - 1}) >>
        modify (fun l -> {l with trace = List.tl l.trace}) >>

        (* logging footer. *)
        log (Printf.sprintf "\u{2570}\u{2500} = %s" (pp x')) >>
        let* () = if !debug_level >= 2
            then log (Printf.sprintf "   %s\n" (LocalEnv.pp_locals s'))
            else unit
        and* () = if !debug_level >= 3
            then traverse_ (fun s -> log ("   " ^ pp_stmt s)) w' >> log ""
            else unit
        in
        pure x'

end

type 'a rws = 'a DisEnv.rws

let (let@) x f = fun env s ->
  let (r,s,w) = x env s in
  let (r',s,w') = (f r) env s in
  (r',s,append w w')

let (let+) x f = fun env s ->
  let (r,s,w) = x env s in
  (f r,s,w)

let (>>) x f = fun env s ->
  let (_,s,w) = x env s in
  let (r',s,w') = f env s in
  (r',s,append w w')

let (>>=) x f = fun env s ->
  let (r,s,w) = x env s in
  let (r',s,w') = (f r) env s in
  (r',s,append w w')

(** Convert value to a simple expression containing that value, so we can
    print it or use it symbolically *)
let to_expr = sym_expr

(** Converts a result_or_simplified to a value.
    Raises an exception if an expression is given, as an expression cannot be casted to a value.
    Requires checking beforehand *)
let to_value (v: sym): value =
    match v with
    | Val v' -> v'
    | Exp _ -> raise (EvalError (Unknown, "Unreachable"))

let is_expr (v: sym): bool =
    match v with
    | Val _ -> false
    | Exp _ -> true

let declare_var (loc: l) (t: ty) (i: ident): var rws =
  let@ uninit = DisEnv.mkUninit t in
  let@ var = DisEnv.stateful
    (LocalEnv.addLocalVar loc i (Val uninit) t) in
  let+ () = DisEnv.write [Stmt_VarDeclsNoInit(t, [var_ident var], loc)] in
  var

let declare_assign_var (loc: l) (t: ty) (i: ident) (x: sym): var rws =
  let@ var = DisEnv.stateful
    (LocalEnv.addLocalVar loc i x t) in
  let+ () = DisEnv.write [Stmt_VarDecl(t, var_ident var, sym_expr x, loc)] in
  var

let declare_fresh_named_var (loc: l) (name: string) (t: ty): var rws =
  let@ res = DisEnv.nextVarName name in
  declare_var loc t res

let assign_var (loc: l) (i: var) (x: sym): unit rws =
  DisEnv.modify (LocalEnv.setVar loc i x) >>
  DisEnv.write [Stmt_Assign(LExpr_Var(var_ident i), sym_expr x, loc)]

let declare_const (loc: l) (t: ty) (i: ident) (x: sym): var rws =
  let@ var = DisEnv.stateful
    (LocalEnv.addLocalConst loc i x t) in
  let+ () = DisEnv.write [Stmt_ConstDecl(t, var_ident var, sym_expr x, loc)] in
  var

let declare_fresh_const (loc: l) (t: ty) (name: string) (x: expr): var rws =
  let@ i = DisEnv.nextVarName name in
  declare_const loc t i (Exp x)

(* Captures the given expression and returns a resolved variable to the captured
   name. *)
let capture_expr loc t x: var rws =
  let@ v = declare_fresh_const loc t "Exp" x in
  let@ uninit = DisEnv.mkUninit t in
  let+ () = DisEnv.modify (LocalEnv.setVar loc v (Val uninit)) in
  v

(* Captures the given expression and returns a sym for the captured name.
   Maintains sym invariant of constant pure expression. *)
let capture_expr_sym loc t x: sym rws =
  let+ v = capture_expr loc t x in
  Exp (var_expr v)

(* Captures the given expression into a variable that can be modified.
   Returns a resolved variable reference to the capture. *)
let capture_expr_mutable loc (t: ty) (x: expr): var rws =
  let@ i = DisEnv.nextVarName "Temp" in
  let@ v = declare_assign_var loc t i (Exp x) in
  let@ uninit = DisEnv.mkUninit t in
  let+ () = DisEnv.modify (LocalEnv.setVar loc v (Val uninit)) in
  v

(** Monadic Utilities *)

(** Coerces sym to value, replacing expressions with uninitialised.
    Correctly expands structures to structures of uninit. *)
let sym_val_or_uninit (t: ty) (x: sym): value rws =
  match x with
  | Val v -> DisEnv.pure v
  | Exp e -> DisEnv.mkUninit t

(** Identify constants suitable for the ITE transform *)
let ite_const e =
  match e with
  | Expr_Var(Ident "FALSE") -> Val (VBool false)
  | Expr_Var(Ident "TRUE") ->  Val (VBool true)
  | Expr_LitBits "1" -> Val (VBits {n=1; v=Z.one})
  | Expr_LitBits "0" -> Val (VBits {n=1; v=Z.zero})
  | _ -> Exp e

(** Identify a series of stmts that could be considered pure for the ITE transform *)
let rec ite_body stmts result =
  match stmts with
  | [Stmt_Assign(LExpr_Var tl, te, _)] ->
      if (tl = var_ident result) then Some (ite_const te) else None
  | (Stmt_ConstDecl _ )::es -> ite_body es result
  | _ -> None

(** Symbolic implementation of an if statement that returns an expression
 *)
let rec sym_if (loc: l) (t: ty) (test: sym rws) (tcase: sym rws) (fcase: sym rws): sym rws =
  let@ r = test in
  (match r with
  | Val (VBool (true))  -> tcase
  | Val (VBool (false)) -> fcase
  | Val _ -> failwith ("Split on non-boolean value")
  | Exp e ->
      let@ t = dis_type loc t in
      let@ tmp = declare_fresh_named_var loc "If" t in
      (* Evaluate true branch statements. *)
      let@ (tenv,tstmts) = DisEnv.locally_
          (tcase >>= assign_var loc tmp) in
      let tstmts = flatten tstmts [] in
      (* Propagate incremented counter to env'. *)
      let@ env' = DisEnv.gets (fun env -> LocalEnv.sequence_merge env tenv) in
      (* Execute false branch statements with env'. *)
      let@ (fenv,fstmts) = DisEnv.locally_
          (DisEnv.put env' >> fcase >>= assign_var loc tmp) in
      let@ () = DisEnv.join_locals tenv fenv in
      let fstmts = flatten fstmts [] in
      match ite_body tstmts tmp, ite_body fstmts tmp with
      | Some (Val _ as te), Some fe
      | Some te, Some (Val _ as fe) ->
          let@ () = DisEnv.write (Utils.butlast tstmts) in
          let+ () = DisEnv.write (Utils.butlast fstmts) in
          (match t with
          | Type_Bits _ -> sym_ite_bits loc (Exp e) te fe
          | _ -> sym_ite_bool loc (Exp e) te fe)
      | _ ->
          let+ () = DisEnv.write [Stmt_If(e, tstmts, [], fstmts, loc)] in
          Exp (var_expr tmp))

(** Symbolic implementation of an if statement with no return *)
and unit_if (loc: l) (test: sym rws) (tcase: unit rws) (fcase: unit rws): unit rws =
  let@ r = test in
  (match r with
  | Val (VBool (true))  -> tcase
  | Val (VBool (false)) -> fcase
  | Val _ -> failwith ("Split on non-boolean value")
  | Exp e ->
      let@ (tenv,tstmts) = DisEnv.locally_ tcase in
      let tstmts = flatten tstmts [] in

      let@ env' = DisEnv.gets (fun env -> LocalEnv.sequence_merge env tenv) in
      let@ (fenv,fstmts) = DisEnv.locally_ (DisEnv.put env' >> fcase) in
      let fstmts = flatten fstmts [] in

      let@ () = DisEnv.join_locals tenv fenv in
      DisEnv.write [Stmt_If(e, tstmts, [], fstmts, loc)])

and sym_and (loc: l) (x: sym rws) (y: sym rws): sym rws =
    sym_if loc type_bool x y (DisEnv.pure sym_false)

and sym_or (loc: l) (x: sym rws) (y: sym rws): sym rws =
    sym_if loc type_bool x (DisEnv.pure sym_true) y

(** Symbolic implementation of List.for_all2 *)
and sym_for_all2 p l1 l2 =
  match (l1, l2) with
  | ([], []) -> DisEnv.pure sym_true
  | (a1::l1, a2::l2) -> sym_if Unknown (type_bool) (p a1 a2) (sym_for_all2 p l1 l2) (DisEnv.pure sym_false)
  | (_, _) -> invalid_arg "sym_for_all2"

(** Symbolic implementation of List.exists *)
and sym_exists p = function
  | [] -> DisEnv.pure sym_false
  | [a] -> p a
  | a::l -> sym_or Unknown (p a) (sym_exists p l)

and width_of_type (loc: l) (t: ty): int =
  match t with
  | Type_Bits (Expr_LitInt wd) -> int_of_string wd
  | Type_Register (wd, _) -> int_of_string wd
  | _ -> unsupported loc @@ "Can't get bit width of type: " ^ pp_type t

and width_of_field (loc: l) (t: ty) (f: ident): int =
  let env = !Tcheck.env0 in
  let ft =
    (match Tcheck.typeFields env loc t with
    | FT_Record rfs -> Tcheck.get_recordfield loc rfs f
    | FT_Register rfs -> let (_,t) = Tcheck.get_regfield loc rfs f in t)
  in
  width_of_type loc ft

(** Disassembly Functions *)

(** Determine the type of memory access expression (Var, Array, Field) *)
and type_of_load (loc: l) (x: expr): ty rws =
  let env = !Tcheck.env0 in
  (match x with
  | Expr_Var(id) ->
      let+ (_,(t,_)) = DisEnv.gets (LocalEnv.resolveGetVar loc id) in
      t
  | Expr_Field(e,f) ->
      let@ t = type_of_load loc e in
      (match Tcheck.typeFields env loc t with
      | FT_Record rfs -> dis_type loc @@ Tcheck.get_recordfield loc rfs f
      | FT_Register rfs ->
        let (_,t) = Tcheck.get_regfield loc rfs f in
        dis_type loc t)
  | Expr_Array(a,i) ->
      let@ t = type_of_load loc a in
      (match Tcheck.derefType env t with
      | Type_Array(ixty, elty) -> dis_type loc elty
      | _ -> raise (EvalError (loc, "Can't type expression: " ^ pp_expr a)))
  | _ -> raise (EvalError (loc, "Can't type expression: " ^ pp_expr x)))

and type_access_chain (loc: l) (var: var) (ref: access_chain list): ty rws =
    let Var (_,id) = var in
    type_of_load loc (expr_access_chain (Expr_Var (Ident id)) ref)

(** Disassemble type *)
and dis_type (loc: l) (t: ty): ty rws =
    match t with
    | Type_Bits ex ->
        let+ ex' = dis_expr loc ex in
        (Type_Bits (sym_expr ex'))
    | Type_OfExpr ex ->
        let+ ex' = dis_expr loc ex in
        (Type_OfExpr (sym_expr ex'))
    | Type_Tuple tys ->
        let+ exprs = DisEnv.traverse (dis_type loc) tys in
        (Type_Tuple exprs)
    | t' -> DisEnv.pure t'

(** Disassemble list of expressions *)
and dis_exprs (loc: l) (xs: AST.expr list): sym list rws =
    DisEnv.traverse (dis_expr loc) xs

(** Disassemble a pattern match, mirrors eval_pattern *)
and dis_pattern (loc: l) (v: sym) (x: AST.pattern): sym rws =
    (match x with
    | Pat_LitInt(l)  -> DisEnv.pure (sym_eq_int  loc v (Val (from_intLit l)))
    | Pat_LitHex(l)  -> DisEnv.pure (sym_eq_int  loc v (Val (from_hexLit l)))
    | Pat_LitBits(l) -> DisEnv.pure (sym_eq_bits loc v (Val (from_bitsLit l)))
    | Pat_LitMask(l) -> DisEnv.pure (sym_inmask  loc v (to_mask loc (from_maskLit l)))
    | Pat_Const(c)   ->
            let+ c' = dis_load loc (Expr_Var c) in
            sym_eq loc v c'
    | Pat_Wildcard   -> DisEnv.pure sym_true
    | Pat_Tuple(ps) ->
            let vs = sym_of_tuple loc v in
            assert (List.length vs = List.length ps);
            sym_for_all2 (dis_pattern loc) vs ps
    | Pat_Set(ps) ->
            sym_exists (dis_pattern loc v) ps
    | Pat_Single(e) ->
            let+ v' = dis_expr loc e in
            sym_eq loc v v'
    | Pat_Range(lo, hi) ->
            let@ lo' = dis_expr loc lo in
            let+ hi' = dis_expr loc hi in
            sym_and_bool loc (sym_le_int loc lo' v) (sym_le_int loc v hi')
    )

(** Disassemble bitslice bounds, mirrors eval_slice *)
and dis_slice (loc: l) (x: slice): (sym * sym) rws =
    (match x with
    | Slice_Single(i) ->
            let+ i' = dis_expr loc i in
            (i', Val (VInt Z.one))
    | Slice_HiLo(hi, lo) ->
            let@ hi' = dis_expr loc hi in
            let+ lo' = dis_expr loc lo in
            let wd' = sym_add_int loc (sym_sub_int loc hi' lo') (Val (VInt Z.one)) in
            (lo', wd')
    | Slice_LoWd(lo, wd) ->
            let@ lo' = dis_expr loc lo in
            let+ wd' = dis_expr loc wd in
            (lo', wd')
    )

(**
  Disassemble a variable load, either accessing local or global state, potentially with a chain of
  aggregate structure accesses.

  Locals and globals are expected to all be defined by the symbolic state and assumed
  to never contain symbolic aggregate structures.
  These structures are not supported by the target and must be removed for successful translation.
  TODO: This does not appear to be a problem at the moment, but requires greater testing to be sure.
  *)
and dis_load (loc: l) (x: expr): sym rws =
  let body = (let+ (_,s) = dis_load_chain loc x [] in s) in
  if no_debug() then body
  else DisEnv.scope loc "dis_load" (pp_expr x) pp_sym body

and dis_load_with_type (loc: l) (x: expr): (ty * sym) rws =
  let body = dis_load_chain loc x []  in
  if no_debug() then body
  else DisEnv.scope loc "dis_load_with_type" (pp_expr x) (fun (t,s) -> pp_sym s) body

and dis_load_chain (loc: l) (x: expr) (ref: access_chain list): (ty * sym) rws =
  (match x with
  | Expr_Var(id) ->
      let@ (var,local) = DisEnv.gets (LocalEnv.resolveGetVar loc id) in
      (match local with
      | (t, Val v) ->
          (* we assume that structures in the local state are always maximally
             expanded so this chain can always be evaluated, but may have
             uninitialised values at its base values. *)
          (match (get_access_chain loc v ref) with
          | VUninitialized _ ->
              let expr = expr_access_chain (var_expr var) ref in
              let@ t' = type_access_chain loc var ref in

              let@ var' = capture_expr_sym loc t' expr in
              (* if we are loading a bare symbolic variable,
                 update it to refer to the new captured expression
                 (as a minor optimisation). *)
              let@ () = DisEnv.if_ (ref = [])
                (DisEnv.modify (LocalEnv.setVar loc var var')) in
              DisEnv.pure (t', var')
          | v' -> DisEnv.pure (t, Val v')
          )
      (* Variable is local with a symbolic value, should not expect a structure *)
      | (t, Exp e) ->
          if ref = [] then DisEnv.pure @@ local
          else unsupported loc "Local variable with dynamic structure"
      )
  | Expr_Field(e,f) -> dis_load_chain loc e (Field f::ref)
  | Expr_Array(a,i) ->
      let@ i = dis_expr loc i in
      (match i with
      | Val i -> dis_load_chain loc a (Index i::ref)
      | Exp e -> dis_load_chain loc a (SymIndex e::ref))
  | x -> unsupported loc @@ "Unknown Exp chain: " ^ pp_expr x)

(** Dissassemble expression. This should never return Result VUninitialized *)
and dis_expr loc x =
  let+ r =
    let body = dis_expr' loc x in
    if no_debug() then body
    else DisEnv.scope loc "dis_expr" (pp_expr x) pp_sym (dis_expr' loc x) in
  match r with
  | Val (VUninitialized _) -> internal_error loc @@ "dis_expr returning VUninitialized, invalidating assumption"
  | _ -> r

and dis_expr' (loc: l) (x: AST.expr): sym rws =
    (match x with
    | Expr_If(ty, c, t, els, e) ->
            let rec eval_if xs d : sym rws = match xs with
                | [] -> dis_expr loc d
                | AST.E_Elsif_Cond (c,b)::xs' ->
                    sym_if loc ty (dis_expr loc c) (* then *)
                      (dis_expr loc b)
                    (* else *)
                      (eval_if xs' d)
            in
            eval_if (E_Elsif_Cond(c, t)::els) e
    | Expr_Binop(a, op, b) ->
            raise (EvalError (loc, "binary operation should have been removed in expression "
                   ^ Utils.to_string (PP.pp_expr x)))
    | Expr_Field(_, _) -> dis_load loc x
    | Expr_Fields(e, fs) ->
            let+ vs = DisEnv.traverse (fun f -> dis_load_with_type loc (Expr_Field(e,f))) fs in
            let vs' = List.map (fun (t,x) -> (width_of_type loc t, x)) vs in
            sym_concat loc vs'
    | Expr_Slices(e, [s]) ->
            let@ e' = dis_expr loc e in
            let+ (i,w) = dis_slice loc s in
            sym_extract_bits loc e' i w
    | Expr_Slices(e, ss) ->
            let@ e' = dis_expr loc e in
            let+ ss' = DisEnv.traverse (dis_slice loc) ss in
            let vs = List.map (fun (i,w) -> (int_of_sym w, sym_extract_bits loc e' i w)) ss' in
            sym_concat loc vs
    | Expr_In(e, p) ->
            let@ e' = dis_expr loc e in
            let@ p' = dis_pattern loc e' p in
            (match p' with
            | Val v -> DisEnv.pure (Val v)
            | Exp e -> capture_expr_sym loc type_bool e)
    | Expr_Var(_) -> dis_load loc x
    | Expr_Parens(e) ->
            dis_expr loc e
    | Expr_TApply(f, tes, es) ->
            if name_of_FIdent f = "and_bool" then begin
                (match (tes, es) with
                | ([], [x; y]) ->
                    sym_and loc (dis_expr loc x) (dis_expr loc y)
                | _ ->
                    internal_error loc @@ "malformed and_bool expression "
                       ^ Utils.to_string (PP.pp_expr x)
                )
            end else if name_of_FIdent f = "or_bool" then begin
                (match (tes, es) with
                | ([], [x; y]) ->
                    sym_or loc (dis_expr loc x) (dis_expr loc y)
                | _ ->
                    internal_error loc @@ "malformed or_bool expression "
                       ^ Utils.to_string (PP.pp_expr x)
                )
            end else if name_of_FIdent f = "implies_bool" then begin
                (match (tes, es) with
                | ([], [x; y]) ->
                    sym_if loc (type_bool) (dis_expr loc x) (* then *)
                      (dis_expr loc y)
                    (* else *)
                      (DisEnv.pure sym_true)
                | _ ->
                    internal_error loc @@ "malformed implies_bool expression "
                       ^ Utils.to_string (PP.pp_expr x)
                )
            end else begin
                let@ tvs = dis_exprs loc tes in
                let@ vs  = dis_exprs loc es in
                dis_funcall loc f tvs vs
            end
    | Expr_Tuple(es) ->
            let+ es' = DisEnv.traverse (dis_expr loc) es in
            sym_tuple es'
    | Expr_Unop(op, e) ->
            raise (EvalError (loc, "unary operation should have been removed"))
    | Expr_Unknown(t) -> (* TODO: Is this enough? *)
            let+ t' = dis_type loc t in
            Exp (Expr_Unknown(t'))
    | Expr_ImpDef(t, Some(s)) ->
            DisEnv.reads (fun config -> Val (Eval.Env.getImpdef loc config.eval_env s))
    | Expr_ImpDef(t, None) ->
            raise (EvalError (loc, "unnamed IMPLEMENTATION_DEFINED behavior"))
    | Expr_Array(a,i) ->   dis_load loc x
    | Expr_LitInt(i) ->    DisEnv.pure (Val (from_intLit i))
    | Expr_LitHex(i) ->    DisEnv.pure (Val (from_hexLit i))
    | Expr_LitReal(r) ->   DisEnv.pure (Val (from_realLit r))
    | Expr_LitBits(b) ->   DisEnv.pure (Val (from_bitsLit b))
    | Expr_LitMask(b) ->   DisEnv.pure (Val (from_maskLit b))
    | Expr_LitString(s) -> DisEnv.pure (Val (from_stringLit s))
    )

and no_inline_pure_ids () = List.map (fun (x,y) -> FIdent(x,y))
  (no_inline_pure ())

and no_inline_ids = List.map (fun (x,y) -> FIdent (x,y))
  no_inline

(** Disassemble call to function *)
and dis_funcall (loc: l) (f: ident) (tvs: sym list) (vs: sym list): sym rws =
    if List.mem f (no_inline_pure_ids ()) &&
      ((List.exists (function Exp _ -> true | _ -> false) tvs) ||
        (List.exists (function Exp _ -> true | _ -> false) vs)) then
      let expr = Exp (Expr_TApply (f, List.map sym_expr tvs, List.map sym_expr vs)) in
      DisEnv.pure (match sym_prim_simplify (name_of_FIdent f) tvs vs with
      | Some x -> x
      | None -> expr)
    else
      let+ r = dis_call loc f tvs vs in
      match r with
      | Some x -> x
      | None -> internal_error loc "function call finished without returning a value"

(** Evaluate call to procedure *)
and dis_proccall (loc: l) (f: ident) (tvs: sym list) (vs: sym list): unit rws =
    let+ _ = dis_call loc f tvs vs in ()

(** Disassemble a function call *)
and dis_call (loc: l) (f: ident) (tes: sym list) (es: sym list): sym option rws =
    let body = dis_call' loc f tes es in
    if no_debug() then body
    else DisEnv.scope loc "dis_call"
        (pp_expr (Expr_TApply (f, List.map sym_expr tes, List.map sym_expr es)))
        (Option.fold ~none:"(no return)" ~some:pp_sym)
        body

and dis_call' (loc: l) (f: ident) (tes: sym list) (es: sym list): sym option rws =
    let@ fn = DisEnv.getFun loc f in
    (match fn with
    | Some (rty, _, targs, _, _, _) when List.mem f no_inline_ids ->
        (* impure functions are not visited. *)
        (match sym_prim_simplify (name_of_FIdent f) tes es with
        | Some x -> DisEnv.pure (Some x)
        | None ->
            (match rty with
            | Some rty ->
                let@ () = DisEnv.modify LocalEnv.addLevel in
                let@ () = DisEnv.traverse2_ (fun arg e ->
                    declare_const loc type_integer arg e
                    ) targs tes in

                let@ rty = dis_type loc rty in
                let func = Expr_TApply (f, List.map sym_expr tes, List.map sym_expr es) in
                let@ var = capture_expr loc rty func in
                let@ () = DisEnv.modify LocalEnv.popLevel in
                DisEnv.pure @@ Some (var_sym_expr var)
            | None ->
                let+ () = DisEnv.write [Stmt_TCall (f, List.map sym_expr tes, List.map sym_expr es, loc)] in
                None
            )
        )
    | Some (rty, atys, targs, args, loc, b) ->
        let fname = name_of_FIdent f in

        (* Nest enviroment *)
        let@ () = DisEnv.modify LocalEnv.addLevel in

        assert (List.length targs == List.length tes);

        (* Assign targs := tes *)
        let@ () = DisEnv.traverse2_ (fun arg e ->
            declare_const loc type_integer arg e
            ) targs tes in

        assert (List.length atys == List.length args);
        assert (List.length atys == List.length es);

        (* Assign args := es *)
        let@ () = DisEnv.traverse3_ (fun (ty, _) arg e ->
            let@ ty' = dis_type loc ty in
            declare_const loc ty' arg e
        ) atys args es in

        (* Create return variable (if necessary).
            This is in the inner scope to allow for type parameters. *)
        let@ rv = (match rty with
        | Some (Type_Tuple ts) ->
            let@ ts' = DisEnv.traverse (dis_type loc) ts in
            let+ names = DisEnv.traverse (declare_fresh_named_var loc fname) ts' in
            Some (Expr_Tuple (List.map var_expr_no_suffix_in_local_scope names))
        | Some t ->
            let@ t' = dis_type loc t in
            let+ name = declare_fresh_named_var loc fname t' in
            Some (var_expr_no_suffix_in_local_scope name)
        | None ->
            DisEnv.pure None) in

        let@() = if !debug_level >= 2 then
          let@ env = DisEnv.get in
          DisEnv.log (LocalEnv.pp_locals env ^ "\n")
        else DisEnv.unit in

        (* Evaluate body with new return symbol *)
        let@ () = DisEnv.modify (LocalEnv.addReturnSymbol rv) in
        let@ () = dis_stmts b in
        let@ () = DisEnv.modify (LocalEnv.removeReturnSymbol) in

        (* Disassemble return variable expression and propagate its symbolic value
            into the containing scope. *)
        let@ result = (match rv with
        | Some rv ->
            let+ result = dis_expr loc rv in
            Some result
        | None ->
            DisEnv.pure None) in
        (* Pop enviroment. *)
        let@ () = DisEnv.modify LocalEnv.popLevel in
        DisEnv.pure result
    | None ->
        let+ result = (dis_prim f tes es) in
        Some result
    )

and dis_prim (f: ident) (tes: sym list) (es: sym list): sym rws =
    let name = name_of_FIdent f in
    match sym_prim_simplify name tes es with
    | Some s -> DisEnv.pure s
    | None ->
        match sym_prim f tes es with
        | Exp f' ->
            if List.mem name Value.prims_pure
                then DisEnv.pure (Exp f')
                (* TODO(kl): avoid use of type_unknown by inferring return type of primitive. *)
                else let+ var = capture_expr Unknown type_unknown f' in var_sym_expr var
        | Val v -> DisEnv.pure (Val v)

and dis_lexpr loc x r: unit rws =
    let body = dis_lexpr' loc x r in
    if no_debug() then body
    else DisEnv.scope loc "dis_lexpr" (pp_stmt (Stmt_Assign (x, sym_expr r, Unknown))) Utils.pp_unit body

(** Remove potential effects from an lexpr *)
and resolve_lexpr (loc: l) (x: lexpr): lexpr rws =
  (match x with
  | LExpr_Field(l,f) ->
      let+ l = resolve_lexpr loc l in
      LExpr_Field(l,f)
  | LExpr_Array(l,i) ->
      let@ e = dis_expr loc i in
      let+ l = resolve_lexpr loc l in
      (match e with
      | Val i -> LExpr_Array(l, val_expr i)
      | Exp e -> LExpr_Array(l, e))
  | _ -> DisEnv.pure(x))

(* TODO: Missing ReadWrite LExpr, which introduces some complications for Fields case *)
and dis_lexpr_chain (loc: l) (x: lexpr) (ref: access_chain list) (r: sym): unit rws =
  (match x with
  | LExpr_Field(l, f) -> dis_lexpr_chain loc l (Field f::ref) r
  | LExpr_Array(l, i) ->
      let@ e = dis_expr loc i in
      (match e with
      | Val i -> dis_lexpr_chain loc l (Index i::ref) r
      | Exp e -> dis_lexpr_chain loc l (SymIndex e::ref) r)
  | LExpr_Var(id) ->
      let@ var,local = DisEnv.gets (LocalEnv.resolveGetVar loc id) in
      (match local with
      (* Base variable is local, can update as long as its primitive *)
      | (t,Val (VUninitialized _)) when ref <> [] ->
          (* if we reach here, the assumption that all structures are stored
             fully expanded has failed. that is, we incorrectly have a
             VUnitialized of a structure instead of a structure of uninitialised. *)
          internal_error loc @@
            "attempt to access field/index within invalid uninitialised structure."
      | (t,Val v) ->
          let@ () =
            (match ref with
            | _::_ ->
                (* if accessing inside structure, update local store with
                   new structure value. set to uninitialised if "r" is expression. *)
                let@ t' = type_access_chain loc var ref in
                let@ r' = sym_val_or_uninit t' r in
                let vv' = set_access_chain loc v ref r' in
                (* this loses propagation of pure expressions when they are assigned
                   into structures, but this is unavoidable since the structure value types
                   cannot store expressions. *)

                (* mark all pstate.nrw, pstate.el or pstate.sp writes as unsupported and die when we see them.
                   this basically "fixes" us to EL0 and eliminates a bunch of branches.
                   fun fact - the only instructions i'm aware of that can actually do this don't
                   work anyway *)
                let@ () = (match var, ref with
                | Var(0, ("PSTATE")), ([Field(Ident("EL" | "SP" | "nRW"))]) ->
                    DisEnv.write [Stmt_Assert(expr_false, loc)]
                  (*unsupported loc @@ "Update to PSTATE EL/SP/nRW while disassembling" ^ pp_lexpr x;*)
                | _, _ -> DisEnv.pure ()
                ) in

                DisEnv.modify (LocalEnv.setVar loc var (Val vv'))
            | [] ->
                (match var with
                | Var(0, ("InGuardedPage")) ->
                  unsupported loc @@ "Update to InGuardedPage while disassembling" ^ pp_lexpr x;
                | Var(0, ("SCR_EL3")) ->
                  unsupported loc @@ "Update to SCR_EL3 while disassembling" ^ pp_lexpr x;
                | Var(0, ("SCTLR_EL1")) ->
                  unsupported loc @@ "Update to SCTLR_EL1 while disassembling" ^ pp_lexpr x;

                | _ -> ());
                (* if accessing bare variable, just set its variable in local store. *)
                DisEnv.modify (LocalEnv.setVar loc var r)
          ) in
          (* possible failure if "r" is a record or array since those
             cannot be converted to expressions and assigned directly. *)
          DisEnv.write [Stmt_Assign(
            lexpr_access_chain (var_lexpr var) ref, sym_expr r, loc)]
      | (t,Exp e) ->
          (match ref with
          | _::_ ->
            (* variable contains a symbolic expression. read, modify, then write. *)
            let@ Var(_,tmp) = capture_expr_mutable loc t e in
            let@ () = dis_lexpr_chain loc (LExpr_Var (Ident tmp)) ref r in
            let@ e' = dis_expr loc (Expr_Var (Ident tmp)) in
            assign_var loc var e'
          | [] ->
            assign_var loc var r
          )
      )
  | _ -> unsupported loc @@ "Unknown LExpr modify constructor: " ^ pp_lexpr x)

and dis_lexpr' (loc: l) (x: lexpr) (r: sym): unit rws =
    (match x with
    | LExpr_Wildcard ->
        DisEnv.unit
    | LExpr_Var(v) ->
        dis_lexpr_chain loc x [] r
    | LExpr_Field(_,_) ->
        dis_lexpr_chain loc x [] r
    | LExpr_Fields(l,fs) ->
        let@ l = resolve_lexpr loc l in
        let@ ty = type_of_load loc (lexpr_to_expr loc l) in
        let rec set_fields (i: int) (fs: ident list): unit rws =
            (match fs with
            | [] -> DisEnv.unit
            | (f::fs') ->
                let w = width_of_field loc ty f in
                let y = sym_slice loc r i w in
                let@ () = dis_lexpr_chain loc l [Field f] y in
                set_fields (i + w) fs'
            )
        in
        set_fields 0 (List.rev fs)
    | LExpr_Slices(l, ss) ->
        let e = lexpr_to_expr loc l in
        let@ ty = type_of_load loc e in
        let prev_width = width_of_type loc ty in
        let rec eval (o: sym) (ss': AST.slice list) (prev: sym): sym rws =
            (match ss' with
            | [] -> DisEnv.pure prev
            | (s :: ss) ->
                let@ (i, w) = dis_slice loc s in
                let v       = sym_extract_bits loc r o w in
                eval (sym_add_int loc o w) ss (sym_insert_bits loc prev_width prev i w v)
            )
        in
        let@ old = dis_expr loc e in
        let@ rhs = eval (Val (VInt Z.zero)) ss old in
        dis_lexpr_chain loc l [] rhs
    | LExpr_Tuple(ls) ->
        let rs = sym_of_tuple loc r in
        assert (List.length ls = List.length rs);
        DisEnv.traverse2_ (dis_lexpr loc) ls rs
    | LExpr_Array(_,_) ->
        dis_lexpr_chain loc x [] r
    | LExpr_Write(setter, tes, es) ->
        let@ tvs = dis_exprs loc tes in
        let@ vs = dis_exprs loc es in
        dis_proccall loc setter tvs (vs @ [r])
    | _ -> unsupported loc @@ "Unknown LExpr constructor: " ^ pp_lexpr x)

(** Concatenates two lists of statements, but ensures nothing is
    added after a return statement.  *)
and stmt_append (xs: stmt list) (ys: stmt list): stmt list =
    match xs with
    | [] -> ys

    (* these interrupt control flow so we shouldn't append after them. *)
    | (Stmt_FunReturn _ as x)::xs
    | (Stmt_ProcReturn _ as x)::xs
    | (Stmt_Throw _ as x)::xs
    | (Stmt_Dep_Undefined _ as x)::xs
    | (Stmt_Undefined _ as x)::xs -> [x]

    | x::xs -> x :: stmt_append xs ys

(** When duplicating the body after an If, we may want to stop duplication at
    a particular statement. This function splits the follow-on body into
    a duplicated prefix and preserved suffix. *)
and duplicate_up_to (stmts: AST.stmt list) : (AST.stmt list * AST.stmt list) =
  match stmts with
  (* Don't duplicate AtomicEnd, as they are linked with an AtomicStart *)
  | Stmt_TCall(FIdent("AtomicEnd", 0), _, _, _)::rest ->
      ([], stmts)
  | r::rest -> (match duplicate_up_to rest with (f,s) -> (r::f,s))
  | [] -> ([],[])

(** Dissassemble list of statements. *)
and dis_stmts (stmts: AST.stmt list): unit rws =
    match stmts with
    | [] -> DisEnv.unit
    | (Stmt_If(c, tstmts, elsif, fstmts, loc)::rest) ->
        let (dup,post) = duplicate_up_to rest in
        (* append everything after the if statement into each of its branches. *)
        let tstmts' = stmt_append tstmts dup
        and elsif' = List.map (fun (S_Elsif_Cond(e,ss)) ->
            S_Elsif_Cond(e,stmt_append ss dup)) elsif
        and fstmts' = stmt_append fstmts dup in
        dis_stmt (Stmt_If (c, tstmts', elsif', fstmts', loc)) >> dis_stmts post

    | (Stmt_FunReturn _ | Stmt_ProcReturn _) as ret :: rest ->
        (match rest with
        | [] -> dis_stmt ret
        | _ -> raise (DisUnsupported (stmt_loc ret,
            "unexpected statements after return: " ^
            Utils.pp_list pp_stmt rest)))
    | (s::rest) ->
        dis_stmt s >> dis_stmts rest


(** Disassemble statement *)
and dis_stmt x =
    let body = dis_stmt' x in
    if no_debug() then body
    else DisEnv.scope (stmt_loc x) "dis_stmt" (pp_stmt x) Utils.pp_unit body
and dis_stmt' (x: AST.stmt): unit rws =
    (match x with
    | Stmt_VarDeclsNoInit(ty, vs, loc) ->
        (* If a local prefix exists, add it *)
        let@ ty' = dis_type loc ty in
        DisEnv.traverse_ (declare_var loc ty') vs
    | Stmt_VarDecl(ty, v, e, loc) ->
        (* If a local prefix exists, add it *)
        (* Add the variable *)
        let@ ty' = dis_type loc ty in
        let@ e' = dis_expr loc e in
        let@ _ = declare_assign_var loc ty' v e' in
        DisEnv.unit
    | Stmt_ConstDecl(ty, v, e, loc) ->
        (* If a local prefix exists, add it *)
        let@ ty' = dis_type loc ty in
        let@ e' = dis_expr loc e in
        let@ _ = declare_const loc ty' v e' in
        DisEnv.unit
    | Stmt_Assign(l, r, loc) ->
        let@ r' = dis_expr loc r in
        dis_lexpr loc l r'
    | Stmt_If(c, t, els, e, loc) ->
        let rec eval_if xs d : unit rws = match xs with
        | [] -> dis_stmts d
        | S_Elsif_Cond (c,b)::xs' ->
            unit_if loc (dis_expr loc c)
              (dis_stmts b)
            (* else *)
              (eval_if xs' d)
        in
        eval_if (S_Elsif_Cond(c, t)::els) e
    | Stmt_TCall (f, tes, es, loc) ->
        let@ tes' = dis_exprs loc tes in
        let@ es' = dis_exprs loc es in
        dis_proccall loc f tes' es'
    | Stmt_FunReturn(e, loc) ->
        let@ rv = DisEnv.gets (LocalEnv.getReturnSymbol loc) in
        let@ e' = dis_expr loc e in
        dis_lexpr loc (expr_to_lexpr rv) e'
    | Stmt_ProcReturn(loc) -> DisEnv.unit
    | Stmt_Assert(e, loc) ->
        let@ e' = dis_expr loc e in
        (match e' with
        | Val v ->
            if not (to_bool loc v) then
                (* We don't actually know whether this point is reachable, so we shouldn't error out *)
                DisEnv.write [Stmt_Assert(expr_false, loc)]
                (* raise (EvalError (loc, "assertion failure during symbolic phase")) *)
            else
                DisEnv.unit
        | Exp e'' ->
            DisEnv.write [Stmt_Assert(e'', loc)]
        )
    | Stmt_Case(e, alts, odefault, loc) ->
        let rec dis_alts (alts: alt list) (d: stmt list option) (v: sym): unit rws = (
            let@ () = DisEnv.unit in (* force function to be lazily evaluated when rws is computed. *)
            match alts with
            | [] -> (match d with
                (* cannot throw here because this may be reached by disassembling a
                   case with unknown expressions.
                   should only throw an exception at runtime if does not match. *)
                | None -> DisEnv.write [Stmt_Assert (expr_false, loc)]
                | Some s -> dis_stmts s)
            | Alt_Alt(ps, oc, s) :: alts' ->
                let pat = (sym_exists (dis_pattern loc v) ps) in
                let pat_and_guard =
                    (match oc with
                    | Some c -> sym_and loc pat (dis_expr loc c)
                    | None -> pat)
                in
                (unit_if loc pat_and_guard
                    (dis_stmts s)
                    (dis_alts alts' d v))
        ) in
        let@ e' = dis_expr loc e in
        dis_alts alts odefault e'
    | Stmt_For(var, start, dir, stop, body, loc) ->
        let@ start' = dis_expr loc start in
        let@ stop' = dis_expr loc stop in
        let@ unroll_bound = DisEnv.reads (fun config -> config.unroll_bound) in

        let unrolling =
          (match start', stop', dir with
          | Val (VInt startval), Val (VInt stopval), Direction_Up ->
              Z.lt (Z.sub stopval startval) unroll_bound
          | Val (VInt startval), Val (VInt stopval), Direction_Down ->
              Z.lt (Z.sub startval stopval)  unroll_bound
          | _ -> false) in

        (match unrolling, start', stop' with
        | true, Val startval, Val stopval ->
            let rec dis_for (i: value): unit rws =
                let c = (match dir with
                | Direction_Up -> eval_leq loc i stopval
                | Direction_Down -> eval_leq loc stopval i
                ) in
                if c then
                    let i' = (match dir with
                    | Direction_Up   -> eval_add_int loc i (VInt Z.one)
                    | Direction_Down -> eval_sub_int loc i (VInt Z.one)
                    ) in
                    let@ () = dis_stmts ([Stmt_Assign (LExpr_Var var, val_expr i, loc)] @ body)
                    in
                    dis_for i'
                else
                    DisEnv.unit
            in
            declare_var loc type_integer var >>
            dis_for startval
        | _ ->
            let rec loop v =
              (* Grab the pre-loop state *)
              let@ pre_env = DisEnv.gets (fun env -> env) in
              (* Run the body inside a scope, get its final state *)
              let@ (env,stmts) = DisEnv.locally_ (dis_stmts body) in
              (* Join state after, determining whether anything changed *)
              let@ changed = DisEnv.join_locals_fp env pre_env in
              (* If a change occurred, run again *)

              if changed then loop v else
                let start' = sym_expr start' in
                let stop' = sym_expr stop' in
                DisEnv.write [Stmt_For(var_ident v,start',dir,stop',flatten stmts [],loc)]
              in

            (* Add the loop variable to state, make it unknown *)
            let@ uninit = DisEnv.mkUninit type_integer in
            let@ v = DisEnv.stateful (LocalEnv.addLocalVar loc var (Val uninit) type_integer) in
            loop v)
    | Stmt_Dep_Undefined loc
    | Stmt_Undefined loc
    | Stmt_Unpred loc
    | Stmt_ConstrainedUnpred loc
    | Stmt_ImpDef (_, loc)
    | Stmt_ExceptionTaken loc
    | Stmt_Dep_Unpred loc
    | Stmt_Dep_ImpDef (_, loc)
    | Stmt_See (_, loc)
    | Stmt_Throw (_, loc)
    | Stmt_DecodeExecute (_, _, loc)
    | Stmt_While (_, _, loc)
    | Stmt_Repeat (_, _, loc)
    | Stmt_Try (_, _, _, _, loc) ->
        DisEnv.write [Stmt_Assert(expr_false, loc)]
    )

let dis_encoding (x: encoding) (op: Primops.bigint): bool rws =
    let Encoding_Block (nm, iset, fields, opcode, guard, unpreds, b, loc) = x in
    (* todo: consider checking iset *)
    (* Printf.printf "Checking opcode match %s == %s\n" (Utils.to_string (PP.pp_opcode_value opcode)) (pp_value op); *)
    match Eval.eval_opcode_guard loc opcode op with
    | Some op ->
        if !Eval.trace_instruction then Printf.printf "TRACE: instruction %s\n" (pprint_ident nm);

        let@ () = DisEnv.traverse_ (function (IField_Field (f, lo, wd)) ->
            let v = extract_bits' loc op lo wd in
            if !Eval.trace_instruction then Printf.printf "      %s = %s\n" (pprint_ident f) (pp_value v);
            declare_assign_var Unknown (val_type v) f (Val v)
        ) fields in

        let@ guard' = dis_expr loc guard in
        if to_bool loc (sym_value_unsafe guard') then begin
            List.iter (fun (i, b) ->
                if eval_eq loc (extract_bits' loc op i 1) (from_bitsLit b) then
                    raise (Throw (loc, Exc_Unpredictable))
            ) unpreds;
            (* dis_encoding: we cannot guarantee that these statements are fully evaluated. *)
            let@ () = dis_stmts b in
            DisEnv.pure true
        end else begin
            DisEnv.pure false
        end
    | None -> DisEnv.pure false

let dis_decode_slice (loc: l) (x: decode_slice) (op: Primops.bigint): value rws =
    (match x with
    | DecoderSlice_Slice (lo, wd) ->
        let op = Value.from_bitsInt (lo+wd) op in
        DisEnv.pure @@ extract_bits' loc op lo wd
    | DecoderSlice_FieldName f ->
        (* assumes expression always evaluates to concrete value. *)
        let+ _,f' = DisEnv.getVar loc f in sym_value_unsafe f'
    | DecoderSlice_Concat fs ->
        (* assumes expression always evaluates to concrete value. *)
        let+ fs' = DisEnv.traverse (DisEnv.getVar loc) fs in
        eval_concat loc (List.map (fun (_,s) -> sym_value_unsafe s) fs')
    )

(* Duplicate of eval_decode_case modified to print rather than eval *)
let rec dis_decode_case (loc: AST.l) (x: decode_case) (op: Primops.bigint): string rws =
    let body = dis_decode_case' loc x op in
    if no_debug() then body
    else DisEnv.scope loc "dis_decode_case" (pp_decode_case x) Fun.id body
and dis_decode_case' (loc: AST.l) (x: decode_case) (op: Primops.bigint): string rws =
    (match x with
    | DecoderCase_Case (ss, alts, loc) ->
            let@ vs = DisEnv.traverse (fun s -> dis_decode_slice loc s op) ss in
            let rec dis alts =
                (match alts with
                | (alt :: alts') ->
                    let@ alt' = dis_decode_alt loc alt vs op in
                    (match alt' with
                    | Some x -> DisEnv.pure x
                    | None -> dis alts')
                | [] ->
                        raise (DisInternalError (loc, "unmatched decode pattern"))
                )
            in
            dis alts
    )

(* Duplicate of eval_decode_alt modified to print rather than eval *)
and dis_decode_alt (loc: l) (x: decode_alt) (vs: value list) (op: Primops.bigint): string option rws =
    let body = dis_decode_alt' loc x vs op in
    if no_debug() then body
    else DisEnv.scope loc "dis_decode_alt" (pp_decode_alt x) Option.(fold ~none:"(unmatched)" ~some:Fun.id) body
and dis_decode_alt' (loc: AST.l) (DecoderAlt_Alt (ps, b)) (vs: value list) (op: Primops.bigint): string option rws =
    if List.for_all2 (Eval.eval_decode_pattern loc) ps vs then
        (match b with
        | DecoderBody_UNPRED loc -> raise (Throw (loc, Exc_Unpredictable))
        | DecoderBody_UNALLOC loc -> raise (Throw (loc, Exc_Undefined))
        | DecoderBody_NOP loc -> DisEnv.pure (Some "(NOP)")
        | DecoderBody_Encoding (inst, l) ->
                let@ (enc, opost, cond, exec) = DisEnv.reads (fun config -> Eval.Env.getInstruction loc config.eval_env inst) in
                let@ enc_match = dis_encoding enc op in
                if enc_match then begin
                    (* todo: should evaluate ConditionHolds to decide whether to execute body *)
                    if !debug_level >= 0 then begin
                        Printf.printf "Disasm: %s\n" (pprint_ident inst);
                    end;

                    let@ (lenv',stmts) = DisEnv.locally_ (
                        let@ () = DisEnv.modify (LocalEnv.addLevel) in
                        let@ () = (match opost with
                          | Some post ->
                              if !debug_level >= 2 then begin
                                Printf.printf "also disassembling __postdecode...\n"
                              end;
                              dis_stmts post
                          | None -> DisEnv.unit
                        ) in
                        let@ () = dis_stmts exec in
                        DisEnv.modify (LocalEnv.popLevel)
                    ) in
                    let stmts = flatten stmts [] in

                    if !debug_level >= 2 then begin
                        Printf.printf "-----------\n";
                        List.iter (fun s -> Printf.printf "%s\n" (pp_stmt s)) stmts;
                        Printf.printf "-----------\n";
                    end;

                    let@ () = DisEnv.write stmts in
                    DisEnv.pure (Some (pprint_ident inst))
                end else begin
                    DisEnv.pure None
                end
        | DecoderBody_Decoder (fs, c, loc) ->
                let@ () = DisEnv.modify (LocalEnv.addLevel) in
                let@ () = DisEnv.traverse_ (function (IField_Field (f, lo, wd)) ->
                    let op = Value.from_bitsInt (lo+wd) op in
                    let v = extract_bits' loc op lo wd in
                    declare_assign_var loc (val_type v) f (Val v)
                ) fs
                in
                let@ result = dis_decode_case loc c op in
                let@ () = DisEnv.modify (LocalEnv.popLevel) in
                DisEnv.pure (Some result)
        )
    else
        DisEnv.pure None

type env = (LocalEnv.t * IdentSet.t)


(* Map enum type idents to the width required to represent them, mapping other idents to None *)
let enum_types env i =
  if i = Ident "boolean" then None
  else
    match Eval.Env.getEnum env i with
    | Some l -> Some (Z.log2up (Z.of_int (List.length l)))
    | _ -> None

(* Actually perform dis *)
let dis_core (env: Eval.Env.t) (unroll_bound) ((lenv,globals): env) (decode: decode_case) (op: Primops.bigint): string * stmt list =
    let DecoderCase_Case (_,_,loc) = decode in
    let config = { eval_env = env ; unroll_bound } in

    let (enc,lenv',stmts) = (dis_decode_case loc decode op) config lenv in
    let varentries = List.(concat @@ map (fun vars -> StringMap.(bindings (map fst vars))) lenv.locals) in
    let bindings = Asl_utils.Bindings.of_seq @@ List.to_seq @@ List.map (fun (x,y) -> (Ident x,y)) varentries in
    (* List.iter (fun (v,t) -> Printf.printf ("%s:%s\n") v (pp_type t)) varentries; *)
    let stmts = flatten stmts [] in
    let stmts' = Transforms.RemoveUnused.remove_unused globals @@ stmts in
    let stmts' = Transforms.RedundantSlice.do_transform Bindings.empty stmts' in
    let stmts' = Transforms.FixRedefinitions.run (globals : IdentSet.t) stmts' in
    let stmts' = Transforms.StatefulIntToBits.run (enum_types env) stmts' in
    let stmts' = Transforms.IntToBits.ints_to_bits stmts' in
    let stmts' = Transforms.CommonSubExprElim.do_transform stmts' in
    let stmts' = Transforms.CopyProp.copyProp stmts' in
    let stmts' = Transforms.RedundantSlice.do_transform bindings stmts' in
    let stmts' = Transforms.RemoveUnused.remove_unused globals @@ stmts' in
    let stmts' = Transforms.CaseSimp.do_transform stmts' in
    let stmts' = Transforms.RemoveRegisters.run stmts' in
    let stmts' = Transforms.AppendZeros.run stmts' in
    let stmts' = Transforms.BitITESimp.do_transform stmts' in

    if !debug_level >= 2 then begin
        let stmts' = Asl_visitor.visit_stmts (new Asl_utils.resugarClass (!TC.binop_table)) stmts' in
        Printf.printf "===========\n";
        List.iter (fun s -> Printf.printf "%s\n" (pp_stmt s)) stmts';
        Printf.printf "===========\n";
    end;
    enc, stmts'


(* Wrapper around the core to attempt loop vectorization, reverting back if this fails.
   This is a complete hack, but it is nicer to make the loop unrolling decision during
   partial evaluation, rather than having to unroll after we know vectorization failed.
 *)
let dis_decode_entry_with_inst (env: Eval.Env.t) ((lenv,globals): env) (decode: decode_case) (op: Primops.bigint): string * stmt list =
  let max_upper_bound = Z.of_int64 Int64.max_int in
  match !Symbolic.use_vectoriser with
  | false -> dis_core env max_upper_bound (lenv,globals) decode op
  | true ->
    let enc,stmts' = dis_core env Z.one (lenv,globals) decode op in
    let (res,stmts') = Transforms.LoopClassify.run stmts' env in
    if res then (enc,stmts') else
      dis_core env max_upper_bound (lenv,globals) decode op

let dis_decode_entry (env: Eval.Env.t) ((lenv,globals): env) (decode: decode_case) (op: Primops.bigint): stmt list =
  snd @@ dis_decode_entry_with_inst env (lenv,globals) decode op

let build_env (env: Eval.Env.t): env =
    let env = Eval.Env.freeze env in
    let lenv = LocalEnv.init env in
    let loc = Unknown in

    (* get the pstate, then construct a new pstate where nRW=0, EL=0 & SP=0, then set the pstate *)
    let (_, pstate) = LocalEnv.getVar loc (Var(0, ("PSTATE"))) lenv in
    let pstate = (match pstate with
    | Val(pstate_v) ->
      let pstate_v = set_access_chain loc pstate_v [Field(Ident("EL"))] (VBits({n=2; v=Z.zero;})) in
      let pstate_v = set_access_chain loc pstate_v [Field(Ident("SP"))] (VBits({n=1; v=Z.zero;})) in
      let pstate_v = set_access_chain loc pstate_v [Field(Ident("nRW"))] (VBits({n=1; v=Z.zero;})) in
      pstate_v
    | _ ->
      unsupported loc @@ "Initial env value of PSTATE is not a Value";
    ) in
    let lenv = LocalEnv.setVar loc (Var(0, ("PSTATE"))) (Val(pstate)) lenv in
    let lenv = LocalEnv.setVar loc (Var(0, ("SCR_EL3"))) (Val(VBits({n=64; v=Z.zero;}))) lenv in
    let lenv = LocalEnv.setVar loc (Var(0, ("SCTLR_EL1"))) (Val(VBits({n=64; v=Z.zero;}))) lenv in
    (* set InGuardedPage to false *)
    let lenv = LocalEnv.setVar loc (Var(0, ("InGuardedPage"))) (Val (VBool false)) lenv in
    let globals = IdentSet.of_list @@ List.map fst @@ Bindings.bindings (Eval.Env.readGlobals env) in
    lenv, globals

(** Instruction behaviour may be dependent on its PC. When lifting this information may be statically known.
    If this is the case, we benefit from setting a PC initially and propagating its value through partial evaluation.
    Assumes variable is named _PC and its represented as a bitvector. *)
let setPC (env: Eval.Env.t) (lenv,g: env) (address: Z.t): env =
    let loc = Unknown in
    let pc = "_PC" in
    let width = (match Eval.Env.getVar loc env (Ident pc) with
    | VUninitialized ty -> width_of_type loc ty
    | VBits b -> b.n
    | _ -> unsupported loc @@ "Initial env contains PC with unexpected type") in
    let addr = VBits (Primops.mkBits width address) in
    LocalEnv.setVar loc (Var(0, pc)) (Val addr) lenv,g

let retrieveDisassembly ?(address:string option) (env: Eval.Env.t) (lenv: env) (opcode: string) : stmt list =
    let decoder = Eval.Env.getDecoder env (Ident "A64") in
    let DecoderCase_Case (_,_,loc) = decoder in
    let lenv = match address with
    | Some v -> setPC env lenv (Z.of_string v)
    | None -> lenv in
    dis_decode_entry env lenv decoder (Z.of_string opcode)
