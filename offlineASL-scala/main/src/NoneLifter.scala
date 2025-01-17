package main
import lifter._

/**
 * User-provided implementation of the lift-time semantics (e.g. f_eq_bits) and IBI (e.g. f_gen_eq_bits).
 */

sealed trait RExpr 
case class BitVec(val value: BigInt, val size: BigInt) extends RExpr
case class OtherExpr() extends RExpr

class NotImplementedLifter extends LiftState[RExpr, String, BitVec] {
  type BV = BitVec /* Lift-time bitvector representation, must be BV <: RTSym */
  type RTSym = RExpr /* Run-time expression representation */
  type RTLabel = String  /* Block/branch labels for gen_branch */


  /* Lift-time semantics */
  def mkBits(n: BigInt, y: BigInt): BV = throw NotImplementedError()
  def bvextract(e: BV, lo: BigInt, width: BigInt): BV = throw NotImplementedError()
  def f_eq_bits(t: BigInt, x: BV, y: BV): Boolean = throw NotImplementedError()
  def f_ne_bits(t: BigInt, x: BV, y: BV): Boolean = throw NotImplementedError()
  def f_add_bits(t: BigInt, x: BV, y: BV): BV = throw NotImplementedError()
  def f_sub_bits(t: BigInt, x: BV, y: BV): BV = throw NotImplementedError()
  def f_mul_bits(t: BigInt, x: BV, y: BV): BV = throw NotImplementedError()
  def f_and_bits(t: BigInt, x: BV, y: BV): BV = throw NotImplementedError()
  def f_or_bits(t: BigInt, x: BV, y: BV): BV = throw NotImplementedError()
  def f_eor_bits(t: BigInt, x: BV, y: BV): BV = throw NotImplementedError()
  def f_not_bits(t: BigInt, x: BV): BV = throw NotImplementedError()
  def f_slt_bits(t: BigInt, x: BV, y: BV): Boolean = throw NotImplementedError()
  def f_sle_bits(t: BigInt, x: BV, y: BV): Boolean = throw NotImplementedError()
  def f_zeros_bits(w: BigInt): BV = throw NotImplementedError()
  def f_ones_bits(w: BigInt): BV = throw NotImplementedError()
  def f_ZeroExtend(t0: BigInt, t1: BigInt, n: BV, x: BigInt): BV = throw NotImplementedError()
  def f_SignExtend(t0: BigInt, t1: BigInt, n: BV, x: BigInt): BV = throw NotImplementedError()
  def f_asr_bits(targ0: BigInt, targ1: BigInt, arg0: BV, arg1: BV): BV = throw NotImplementedError()
  def f_lsl_bits(targ0: BigInt, targ1: BigInt, arg0: BV, arg1: BV): BV = throw NotImplementedError()
  def f_lsr_bits(targ0: BigInt, targ1: BigInt, arg0: BV, arg1: BV): BV = throw NotImplementedError()
  def f_decl_bool(arg0: String): RTSym = throw NotImplementedError()
  def f_decl_bv(arg0: String, arg1: BigInt): RTSym = throw NotImplementedError()
  def f_AtomicEnd(): RTSym = throw NotImplementedError()
  def f_AtomicStart(): RTSym = throw NotImplementedError()

  def f_replicate_bits(targ0: BigInt, targ1: BigInt, arg0: BV, arg1: BigInt): BV = throw NotImplementedError()
  def f_append_bits(targ0: BigInt, targ1: BigInt, a: BV, b: BV): BV = throw NotImplementedError()

  /** Run-time IR program generation */

  def f_gen_BFAdd(arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_BFMul(arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPAdd(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPCompare(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym, arg3: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPCompareEQ(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPCompareGE(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPCompareGT(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPConvert(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPConvertBF(arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPDiv(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPMax(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPMaxNum(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPMin(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPMinNum(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPMul(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPMulAdd(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym, arg3: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPMulAddH(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym, arg3: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPMulX(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPRSqrtStepFused(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPRecipEstimate(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_UnsignedRSqrtEstimate(targ0: BigInt, arg0: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPRSqrtEstimate(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPRecipStepFused(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPRecpX(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPRoundInt(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym, arg3: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPRoundIntN(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym, arg3: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPSqrt(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPSub(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPToFixed(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym, arg3: RTSym, arg4: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FPToFixedJS_impl(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_FixedToFP(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym, arg3: RTSym, arg4: RTSym): RTSym = throw NotImplementedError()
  def f_gen_bit_lit(targ0: BigInt, arg0: BV): RTSym = throw NotImplementedError()
  def f_gen_bool_lit(arg0: Boolean): RTSym = throw NotImplementedError()
  def f_gen_branch(arg0: RTSym): RTLabel = throw NotImplementedError()
  def f_cvt_bits_uint(targ0: BigInt, arg0: BV): BigInt = throw NotImplementedError()
  def f_gen_cvt_bits_uint(targ0: BigInt, arg0: RTSym): RTSym = throw NotImplementedError()
  def f_gen_cvt_bool_bv(arg0: RTSym): RTSym = throw NotImplementedError()
  def f_gen_eor_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_eq_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_eq_enum(arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_int_lit(arg0: BigInt): BV = throw NotImplementedError()
  def f_gen_store(lval: RTSym, e: RTSym): Unit = throw NotImplementedError()
  def f_gen_load(e: RTSym): RTSym = throw NotImplementedError()
  def f_gen_SignExtend(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: BV): RTSym = throw NotImplementedError()
  def f_gen_ZeroExtend(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: BV): RTSym = throw NotImplementedError()
  def f_gen_add_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_and_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_and_bool(arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_asr_bits(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_lsl_bits(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_lsr_bits(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_mul_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_ne_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_not_bits(targ0: BigInt, arg0: RTSym): RTSym = throw NotImplementedError()
  def f_gen_not_bool(arg0: RTSym): RTSym = throw NotImplementedError()
  def f_gen_or_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_or_bool(arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_sdiv_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_sle_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_slt_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_sub_bits(targ0: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_AArch64_MemTag_set(arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_AArch64_MemTag_read(arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_Mem_read(targ0: BigInt, arg0: RTSym, arg1: RTSym, arg2: RTSym): RTSym = throw NotImplementedError()
  def f_gen_slice(e: RTSym, lo: BigInt, wd: BigInt): RTSym = throw NotImplementedError()
  def f_gen_replicate_bits(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: BV): RTSym = throw NotImplementedError()
  def f_gen_append_bits(targ0: BigInt, targ1: BigInt, arg0: RTSym, arg1: RTSym): RTSym = throw NotImplementedError()
  def f_gen_array_load(arg0: RTSym, arg1: BigInt): RTSym = throw NotImplementedError()
  def f_gen_array_store(arg0: RTSym, arg1: BigInt, arg2: RTSym): Unit = throw NotImplementedError()
  def f_gen_Mem_set(sz: BigInt, ptr: RTSym, width: BV, acctype: RTSym, value: RTSym): Unit = throw NotImplementedError()
  def f_gen_assert(arg0: RTSym): Unit = throw NotImplementedError()

  def f_switch_context(arg0: RTLabel): Unit = throw NotImplementedError()
  def f_true_branch(arg0: RTLabel): RTLabel = throw NotImplementedError()
  def f_false_branch(arg0: RTLabel): RTLabel = throw NotImplementedError()
  def f_merge_branch(arg0: RTLabel): RTLabel = throw NotImplementedError()


  /** Global variable definitions * */

  def rTLabelDefault : RTLabel = throw NotImplementedError()
  def rTSymDefault : RTSym = throw NotImplementedError()
  def rTExprDefault : RTSym = throw NotImplementedError()

  def v_PSTATE_UAO: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_PAN: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_DIT: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_SSBS: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_G: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_A: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_I: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_F: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_D: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_C: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_Z: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_V: Mutable[RTSym] = throw NotImplementedError()
  def v_PSTATE_N: Mutable[RTSym] = throw NotImplementedError()
  def v__PC: Mutable[RTSym] = throw NotImplementedError()
  def v__R: Mutable[RTSym] = throw NotImplementedError()
  def v__Z: Mutable[RTSym] = throw NotImplementedError()
  def v_SP_EL0: Mutable[RTSym] = throw NotImplementedError()
  def v_FPSR: Mutable[RTSym] = throw NotImplementedError()
  def v_FPCR: Mutable[RTSym] = throw NotImplementedError()

  def v_PSTATE_BTYPE: Mutable[RTSym] = throw NotImplementedError()
  def v_BTypeCompatible: Mutable[RTSym] = throw NotImplementedError()
  def v___BranchTaken: Mutable[RTSym] = throw NotImplementedError()
  def v_BTypeNext: Mutable[RTSym] = throw NotImplementedError()
  def v___ExclusiveLocal: Mutable[RTSym] = throw NotImplementedError()

}


object Lifter {

  def liftOpcode(op: BigInt, sp: BigInt) = {
    var liftState = NotImplementedLifter()
    /* Invoking the lifter */
    val dec = f_A64_decoder[RExpr, String, BitVec](liftState, BitVec(op, 32), BitVec(sp, 64))
  }


  def liftOpcode(op: BigInt) = {
    var liftState = NotImplementedLifter()
    /* Invoking the lifter */
    val dec = f_A64_decoder[RExpr, String, BitVec](liftState, BitVec(op, 32), BitVec(0, 64))
  }

}
