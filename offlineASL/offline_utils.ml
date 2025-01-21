open LibASL
open Asl_ast
open Primops

let mkBits x y = Primops.mkBits (Z.to_int x) y
let from_bitsLit x =
  let x' = Value.drop_chars x ' ' in
  (Primops.mkBits (String.length x') (Z.of_string_base 2 x'))

let frem_int     = Primops.prim_frem_int
let extract_bits = Primops.prim_extract

let f_Elem_set w _w' vec index size x = Primops.prim_insert vec index size x

let f_eq_bits          _ = Primops.prim_eq_bits
let f_ne_bits          _ = Primops.prim_ne_bits
let f_add_bits         _ = Primops.prim_add_bits
let f_sub_bits         _ = Primops.prim_sub_bits
let f_mul_bits         _ = Primops.prim_mul_bits
let f_and_bits         _ = Primops.prim_and_bits
let f_or_bits          _ = Primops.prim_or_bits
let f_eor_bits         _ = Primops.prim_eor_bits
let f_not_bits         _ = Primops.prim_not_bits
let f_slt_bits         _ x y = Primops.prim_lt_int (Primops.prim_cvt_bits_sint x) (Primops.prim_cvt_bits_sint y)
let f_sle_bits         _ x y = Primops.prim_le_int (Primops.prim_cvt_bits_sint x) (Primops.prim_cvt_bits_sint y)
let f_zeros_bits             = Primops.prim_zeros_bits
let f_ones_bits              = Primops.prim_ones_bits
let f_replicate_bits _ _ = Primops.prim_replicate_bits
let f_append_bits    _ _ = Primops.prim_append_bits
let f_ZeroExtend     n m (x : bitvector) _ = { v = x.v ; n = Z.to_int m }
let f_SignExtend     n m (x : bitvector) _ =
  if Z.testbit x.v (Z.to_int (Z.pred n)) then
    Primops.prim_append_bits (Primops.prim_ones_bits (Z.sub m n)) x
  else
    Primops.prim_append_bits (Primops.prim_zeros_bits (Z.sub m n)) x
let f_lsl_bits       w _ (x : bitvector) (y : bitvector) = mkBits w (Z.shift_left x.v (Z.to_int y.v))
let f_lsr_bits       w _ (x : bitvector) (y : bitvector) = mkBits w (Z.shift_right_trunc x.v (Z.to_int y.v))
let f_asr_bits       w _ (x : bitvector) (y : bitvector) = mkBits w (Z.shift_right x.v (Z.to_int y.v))
let f_cvt_bits_uint w bv = Primops.prim_cvt_bits_uint bv

let f_sdiv_int           = Primops.prim_fdiv_int
let f_shl_int            = Primops.prim_shl_int

(****************************************************************
 * Runtime State
 ****************************************************************)

(* Global State *)
let v_PSTATE_C = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "C")
let v_PSTATE_Z = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "Z")
let v_PSTATE_V = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "V")
let v_PSTATE_N = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "N")
let v__PC      = Expr_Var(Ident "_PC")
let v__R       = Expr_Var(Ident "_R")
let v__Z       = Expr_Var(Ident "_Z")
let v_SP_EL0   = Expr_Var(Ident "SP_EL0")
let v_FPSR     = Expr_Var(Ident "FPSR")
let v_FPCR     = Expr_Var(Ident "FPCR")

let v_PSTATE_A         = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "A")
let v_PSTATE_D         = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "D")
let v_PSTATE_DIT       = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "DIT")
let v_PSTATE_F         = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "F")
let v_PSTATE_I         = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "I")
let v_PSTATE_PAN       = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "PAN")
let v_PSTATE_SP        = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "SP")
let v_PSTATE_SSBS      = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "SSBS")
let v_PSTATE_TCO       = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "TCO")
let v_PSTATE_UAO       = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "UAO")
let v_PSTATE_BTYPE     = Expr_Field(Expr_Var(Ident "PSTATE"), Ident "BTYPE")
let v_BTypeCompatible  = Expr_Var (Ident "BTypeCompatible")
let v___BranchTaken    = Expr_Var (Ident "__BranchTaken")
let v_BTypeNext        = Expr_Var (Ident "BTypeNext")
let v___ExclusiveLocal = Expr_Var (Ident "__ExclusiveLocal")

(****************************************************************
 * IR Construction
 ****************************************************************)

let loc = Unknown
let expr_of_z i = Expr_LitInt(Z.to_string i)
let rec to_lexpr = function
  | Expr_Var v -> LExpr_Var v
  | Expr_Field (e,f) -> LExpr_Field (to_lexpr e, f)
  | Expr_Array (e,i) -> LExpr_Array (to_lexpr e, i)
  | _ -> failwith "to_lexpr"

(* Mutable list of blocks, representing the IR as its built *)
let stmts = ref [[]]
(* Block currently being written to *)
let current_pos = ref 0

(* Reset mutable state *)
let reset_ir () =
  stmts := [[]];
  current_pos := 0

(* Add a statement to the end of the current block *)
let push_stmt s =
  stmts := Utils.nth_modify (fun l -> l@[s]) (!current_pos)  !stmts

(* Placeholder function to represent a CFG branch *)
let branch_tmp = FIdent ("branch_tmp", 0)

(* Change the current block *)
let f_switch_context ctx =
  current_pos := ctx

(* Flatten the reachable IR from the provided block ID *)
let rec get_body i =
  let stmts = List.nth !stmts i in
  if List.length stmts = 0 then []
  else
    let (pre,last) = Utils.getlast stmts in
    match last with
    | Stmt_TCall (id, [], [cond; Expr_LitInt t; Expr_LitInt f; Expr_LitInt m], loc) when id = branch_tmp ->
        let tstmts = get_body (int_of_string t) in
        let fstmts = get_body (int_of_string f) in
        let mstmts = get_body (int_of_string m) in
        pre@[Stmt_If (cond, tstmts, [], fstmts, loc)]@mstmts
    | _ -> stmts

(* Flatten the IR from the entry block *)
let get_ir () =
  get_body 0

(* Generate 3 blocks to form a CFG diamond, returning IDs for each new block *)
let f_gen_branch cond =
  let true_branch = List.length !stmts in
  let false_branch = true_branch + 1 in
  let merge = true_branch + 2 in
  stmts := !stmts @ [[]; []; []];
  push_stmt ( Stmt_TCall (branch_tmp, [],
            [cond; Expr_LitInt (string_of_int true_branch);
            Expr_LitInt (string_of_int false_branch);
            Expr_LitInt (string_of_int merge)], loc));
  (true_branch, false_branch, merge)

let f_true_branch (a,_,_) = a
let f_false_branch (_,b,_) = b
let f_merge_branch (_,_,c) = c

let undefined () = Expr_Tuple []

(* Runtime assert *)
let f_gen_assert b =
  push_stmt (Stmt_Assert (b, loc))

(* Convert a lift time bitvector into a runtime bitvector *)
let f_gen_bit_lit w (bv: bitvector) =
  Expr_LitBits (Z.format ("%0" ^ string_of_int bv.n ^ "b") bv.v)
let f_gen_bool_lit b =
  if b then Expr_Var (Ident "TRUE") else Expr_Var (Ident "FALSE")
let f_gen_int_lit i =
  Expr_LitInt (Z.to_string i)

(* Dynamic variable creation *)
let f_decl_bv name width =
  push_stmt (Asl_ast.Stmt_VarDeclsNoInit(Type_Bits(expr_of_z width), [Ident name], Unknown)) ;
  Expr_Var (Ident name)
let f_decl_bool name =
  push_stmt (Asl_ast.Stmt_VarDeclsNoInit(Symbolic.type_bool, [Ident name], Unknown)) ;
  Expr_Var (Ident name)

(* Variable accesses *)
let f_gen_load v = v
let f_gen_store v e = push_stmt (Stmt_Assign(to_lexpr v, e, loc))

(* Array accesses, where the index variable is a liftime bitvector *)
let f_gen_array_load a i =
  Expr_Array(a, expr_of_z i)
let f_gen_array_store a i e =
  push_stmt (Stmt_Assign(LExpr_Array(to_lexpr a, expr_of_z i), e, loc))

(* Vector accesses, with runtime values and indices. *)
let f_gen_Elem_read w w' vec index size =
  (* w' should always == size *)
  Expr_TApply (FIdent ("Elem.read", 0), [expr_of_z w; expr_of_z w'], [vec; index; size])
let f_gen_Elem_set w w' vec index size x =
  (* w' should always == size *)
  Expr_TApply (FIdent ("Elem.set", 0), [expr_of_z w; expr_of_z w'], [vec; index; size; x])

(* Memory ops *)
let f_gen_Mem_set w x _ y z =
  push_stmt (Stmt_TCall (FIdent ("Mem.set", 0), [expr_of_z w], [x; expr_of_z w; y; z], Unknown))
let f_gen_Mem_read w x _ y =
  (Expr_TApply (FIdent ("Mem.read", 0), [expr_of_z w], [x; expr_of_z w; y]))
let f_AtomicStart () =
  push_stmt (Stmt_TCall (FIdent ("AtomicStart", 0), [], [], Unknown))
let f_AtomicEnd () =
  push_stmt (Stmt_TCall (FIdent ("AtomicEnd", 0), [], [], Unknown))
let f_gen_AArch64_MemTag_set x y z: unit =
  failwith "MemTag_set unsupported"
let f_gen_AArch64_MemTag_read x y =
  failwith "MemTag_read unsupported"

(* Prim bool ops *)
let f_gen_and_bool e1 e2 =
  Expr_TApply (FIdent ("and_bool", 0), [], [e1;e2])
let f_gen_or_bool e1 e2 =
  Expr_TApply (FIdent ("or_bool", 0), [], [e1;e2])
let f_gen_not_bool e1 =
  Expr_TApply (FIdent ("not_bool", 0), [], [e1])
let f_gen_eq_enum e1 e2 =
  Expr_TApply (FIdent ("eq_enum", 0), [], [e1;e2])

(* Prim int ops *)
let f_gen_cvt_bits_uint w x =
  Expr_TApply (FIdent ("cvt_bits_uint", 0), [expr_of_z w], [x])

(* Prim bit ops *)
let f_gen_eq_bits w e1 e2 =
  Expr_TApply (FIdent ("eq_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_ne_bits w e1 e2 =
  Expr_TApply (FIdent ("ne_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_not_bits w e1 =
  Expr_TApply (FIdent ("not_bits", 0), [expr_of_z w], [e1])
let f_gen_cvt_bool_bv e =
  Expr_If (Type_Bits (Expr_LitInt "1"), e, Expr_LitBits "1", [], Expr_LitBits "0")
let f_gen_or_bits w e1 e2 =
  Expr_TApply (FIdent ("or_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_eor_bits w e1 e2 =
  Expr_TApply (FIdent ("eor_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_and_bits w e1 e2 =
  Expr_TApply (FIdent ("and_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_add_bits w e1 e2 =
  Expr_TApply (FIdent ("add_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_sub_bits w e1 e2 =
  Expr_TApply (FIdent ("sub_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_sdiv_bits w e1 e2 =
  Expr_TApply (FIdent ("sdiv_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_sle_bits w e1 e2 =
  Expr_TApply (FIdent ("sle_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_slt_bits w e1 e2 =
  Expr_TApply (FIdent ("slt_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_mul_bits w e1 e2 =
  Expr_TApply (FIdent ("mul_bits", 0), [expr_of_z w], [e1;e2])
let f_gen_append_bits xw yw x y =
  Expr_TApply (FIdent ("append_bits", 0), [expr_of_z xw; expr_of_z yw], [x;y])
let f_gen_lsr_bits xw yw x y =
  Expr_TApply (FIdent ("lsr_bits", 0), [expr_of_z xw; expr_of_z yw], [x;y])
let f_gen_lsl_bits xw yw x y =
  Expr_TApply (FIdent ("lsl_bits", 0), [expr_of_z xw; expr_of_z yw], [x;y])
let f_gen_asr_bits xw yw x y =
  Expr_TApply (FIdent ("asr_bits", 0), [expr_of_z xw; expr_of_z yw], [x;y])
let f_gen_replicate_bits xw yw x y =
  Expr_TApply (FIdent ("replicate_bits", 0), [expr_of_z xw; expr_of_z yw], [x; expr_of_z yw])
let f_gen_ZeroExtend xw yw x y =
  Expr_TApply (FIdent ("ZeroExtend", 0), [expr_of_z xw; expr_of_z yw], [x; expr_of_z yw])
let f_gen_SignExtend xw yw x y =
  Expr_TApply (FIdent ("SignExtend", 0), [expr_of_z xw; expr_of_z yw], [x; expr_of_z yw])
let f_gen_slice e lo wd =
  Expr_Slices (e, [Slice_LoWd(expr_of_z lo, expr_of_z wd)])

(* Floating Point *)
let f_gen_FPCompare w x y s t =
  Expr_TApply (FIdent ("FPCompare", 0), [expr_of_z w], [x; y; s; t])
let f_gen_FPCompareEQ w x y r =
  Expr_TApply (FIdent ("FPCompareEQ", 0), [expr_of_z w], [x; y; r])
let f_gen_FPCompareGE w x y r =
  Expr_TApply (FIdent ("FPCompareGE", 0), [expr_of_z w], [x; y; r])
let f_gen_FPCompareGT w x y r =
  Expr_TApply (FIdent ("FPCompareGT", 0), [expr_of_z w], [x; y; r])

let f_gen_FPAdd w x y r =
  Expr_TApply (FIdent ("FPAdd", 0), [expr_of_z w], [x; y; r])
let f_gen_FPSub w x y r =
  Expr_TApply (FIdent ("FPSub", 0), [expr_of_z w], [x; y; r])
let f_gen_FPMulAdd w a x y r =
  Expr_TApply (FIdent ("FPMulAdd", 0), [expr_of_z w], [a; x; y; r])
let f_gen_FPMulAddH w a x y r =
  Expr_TApply (FIdent ("FPMulAddH", 0), [expr_of_z w], [a; x; y; r])
let f_gen_FPMulX w x y r =
  Expr_TApply (FIdent ("FPMulX", 0), [expr_of_z w], [x; y; r])
let f_gen_FPMul w x y r =
  Expr_TApply (FIdent ("FPMul", 0), [expr_of_z w], [x; y; r])
let f_gen_FPDiv w x y r =
  Expr_TApply (FIdent ("FPDiv", 0), [expr_of_z w], [x; y; r])
let f_gen_FPMin w x y r =
  Expr_TApply (FIdent ("FPMin", 0), [expr_of_z w], [x; y; r])
let f_gen_FPMinNum w x y r =
  Expr_TApply (FIdent ("FPMinNum", 0), [expr_of_z w], [x; y; r])
let f_gen_FPMax w x y r =
  Expr_TApply (FIdent ("FPMax", 0), [expr_of_z w], [x; y; r])
let f_gen_FPMaxNum w x y r =
  Expr_TApply (FIdent ("FPMaxNum", 0), [expr_of_z w], [x; y; r])
let f_gen_FPRecpX w x t =
  Expr_TApply (FIdent ("FPRecpX", 0), [expr_of_z w], [x; t])
let f_gen_FPSqrt w x t =
  Expr_TApply (FIdent ("FPSqrt", 0), [expr_of_z w], [x; t])
let f_gen_FPRecipEstimate w x r =
  Expr_TApply (FIdent ("FPRecipEstimate", 0), [expr_of_z w], [x; r])
let f_gen_UnsignedRSqrtEstimate w x =
  Expr_TApply (FIdent ("UnsignedRSqrtEstimate", 0), [expr_of_z w], [x])
let f_gen_FPRSqrtEstimate w x r =
  Expr_TApply (FIdent ("FPRSqrtEstimate", 0), [expr_of_z w], [x; r])

let f_gen_BFAdd x y =
  Expr_TApply (FIdent ("BFAdd", 0), [], [x; y])
let f_gen_BFMul x y =
  Expr_TApply (FIdent ("BFMul", 0), [], [x; y])
let f_gen_FPConvertBF x t r =
  Expr_TApply (FIdent ("FPConvertBF", 0), [], [x; t; r])

let f_gen_FPRecipStepFused w x y =
  Expr_TApply (FIdent ("FPRecipStepFused", 0), [expr_of_z w], [x; y])
let f_gen_FPRSqrtStepFused w x y =
  Expr_TApply (FIdent ("FPRSqrtStepFused", 0), [expr_of_z w], [x; y])

let f_gen_FPToFixed w w' x b u t r =
  Expr_TApply (FIdent ("FPToFixed", 0), [expr_of_z w; expr_of_z w'], [x; b; u; t; r])
let f_gen_FixedToFP w w' x b u t r =
  Expr_TApply (FIdent ("FixedToFP", 0), [expr_of_z w; expr_of_z w'], [x; b; u; t; r])
let f_gen_FPConvert w w' x t r =
  Expr_TApply (FIdent ("FPConvert", 0), [expr_of_z w; expr_of_z w'], [x; t; r])
let f_gen_FPRoundInt w x t r e =
  Expr_TApply (FIdent ("FPRoundInt", 0), [expr_of_z w], [x; t; r; e])
let f_gen_FPRoundIntN w x t r e =
  Expr_TApply (FIdent ("FPRoundIntN", 0), [expr_of_z w], [x; t; r; e])

let f_gen_FPToFixedJS_impl w w' x t s =
  Expr_TApply (FIdent ("FPToFixedJS_impl", 0), [expr_of_z w; expr_of_z w'], [x; t; s])
