#pragma once

#include <string_view>

namespace aslp {

template <typename T>
concept lifter_traits = requires(T) {
  typename T::bits;
  typename T::bigint;
  typename T::rt_expr;
  typename T::rt_lexpr;
  typename T::rt_label;
};

template <typename Traits> class lifter_interface : public Traits {
public:
  // bits which are known at lift-time
  using typename Traits::bits;
  // bigints which are known at lift-time
  using typename Traits::bigint;

  // runtime-expression type, i.e. the type of values produced by the semantics
  using typename Traits::rt_expr;
  using typename Traits::rt_lexpr;
  // runtime-label, supports switching blocks during semantics generation
  using typename Traits::rt_label;

  // TODO: split lift-time interface from run-time interface
  // TODO: more flexible method of adding const-lvalue qualifiers
public:
  virtual ~lifter_interface() = default;

  virtual rt_lexpr v_PSTATE_C() = 0;
  virtual rt_lexpr v_PSTATE_Z() = 0;
  virtual rt_lexpr v_PSTATE_V() = 0;
  virtual rt_lexpr v_PSTATE_N() = 0;
  virtual rt_lexpr v__PC() = 0;
  virtual rt_lexpr v__R() = 0;
  virtual rt_lexpr v__Z() = 0;
  virtual rt_lexpr v_SP_EL0() = 0;
  virtual rt_lexpr v_FPSR() = 0;
  virtual rt_lexpr v_FPCR() = 0;
  virtual rt_lexpr v_PSTATE_UAO() = 0;
  virtual rt_lexpr v_PSTATE_PAN() = 0;
  virtual rt_lexpr v_PSTATE_DIT() = 0;
  virtual rt_lexpr v_PSTATE_SSBS() = 0;
  virtual rt_lexpr v_PSTATE_G() = 0;
  virtual rt_lexpr v_PSTATE_A() = 0;
  virtual rt_lexpr v_PSTATE_I() = 0;
  virtual rt_lexpr v_PSTATE_F() = 0;
  virtual rt_lexpr v_PSTATE_D() = 0;

  virtual rt_lexpr v_PSTATE_BTYPE() = 0;
  virtual rt_lexpr v_BTypeCompatible() = 0;
  virtual rt_lexpr v___BranchTaken() = 0;
  virtual rt_lexpr v_BTypeNext() = 0;
  virtual rt_lexpr v___ExclusiveLocal() = 0;

  virtual bits bits_lit(unsigned width, std::string_view str) = 0;
  virtual bits bits_zero(unsigned width) = 0;
  virtual bigint bigint_lit(std::string_view str) = 0;
  virtual bigint bigint_zero() = 0;
  virtual bits extract_bits(const bits &val, bigint lo, bigint wd) = 0;

  virtual bool f_eq_bits(const bits &x, const bits &y) = 0;
  virtual bool f_ne_bits(const bits &x, const bits &y) = 0;
  virtual bits f_add_bits(const bits &x, const bits &y) = 0;
  virtual bits f_sub_bits(const bits &x, const bits &y) = 0;
  virtual bits f_mul_bits(const bits &x, const bits &y) = 0;
  virtual bits f_and_bits(const bits &x, const bits &y) = 0;
  virtual bits f_or_bits(const bits &x, const bits &y) = 0;
  virtual bits f_eor_bits(const bits &x, const bits &y) = 0;
  virtual bits f_not_bits(const bits &x) = 0;
  virtual bool f_slt_bits(const bits &x, const bits &y) = 0;
  virtual bool f_sle_bits(const bits &x, const bits &y) = 0;
  virtual bits f_zeros_bits(bigint n) = 0;
  virtual bits f_ones_bits(bigint n) = 0;
  virtual bits f_replicate_bits(const bits &x, bigint n) = 0;
  virtual bits f_append_bits(const bits &x, const bits &y) = 0;
  virtual bits f_ZeroExtend(const bits &x, bigint wd) = 0;
  virtual bits f_SignExtend(const bits &x, bigint wd) = 0;
  virtual bits f_lsl_bits(const bits &x, const bits &y) = 0;
  virtual bits f_lsr_bits(const bits &x, const bits &y) = 0;
  virtual bits f_asr_bits(const bits &x, const bits &y) = 0;
  virtual bigint f_cvt_bits_uint(const bits &x) = 0;

  virtual rt_lexpr f_decl_bv(std::string_view name, bigint width) = 0;
  virtual rt_lexpr f_decl_bool(std::string_view name) = 0;

  virtual void f_switch_context(rt_label label) = 0;
  virtual rt_label f_true_branch(std::tuple<rt_label, rt_label, rt_label>) = 0;
  virtual rt_label f_false_branch(std::tuple<rt_label, rt_label, rt_label>) = 0;
  virtual rt_label f_merge_branch(std::tuple<rt_label, rt_label, rt_label>) = 0;
  virtual std::tuple<rt_label, rt_label, rt_label>
  f_gen_branch(rt_expr cond) = 0;

  virtual void f_gen_assert(rt_expr cond) = 0;
  virtual rt_expr f_gen_bit_lit(bits bits) = 0;
  virtual rt_expr f_gen_bool_lit(bool b) = 0;
  virtual rt_expr f_gen_int_lit(bigint i) = 0;
  virtual rt_expr f_gen_load(rt_lexpr ptr) = 0;
  virtual void f_gen_store(rt_lexpr var, rt_expr exp) = 0;
  virtual rt_expr
  f_gen_array_load(rt_lexpr array,
                   bigint index) = 0; // XXX unsure of array ptr type.
  virtual void f_gen_array_store(rt_lexpr array, bigint index, rt_expr exp) = 0;
  virtual void f_gen_Mem_set(rt_expr ptr, rt_expr width, rt_expr acctype,
                             rt_expr exp) = 0;
  virtual rt_expr f_gen_Mem_read(rt_expr ptr, rt_expr width,
                                 rt_expr acctype) = 0;
  virtual void f_gen_AArch64_MemTag_set(rt_expr address, rt_expr acctype,
                                        rt_expr value) = 0;
  virtual rt_expr f_gen_AArch64_MemTag_read(rt_expr address, rt_expr acctype) = 0;

  virtual void f_AtomicStart() = 0;
  virtual void f_AtomicEnd() = 0;

  virtual rt_expr f_gen_cvt_bits_uint(rt_expr bits) = 0;
  virtual rt_expr f_gen_cvt_bool_bv(rt_expr e) = 0;

  virtual rt_expr f_gen_not_bool(rt_expr e) = 0;
  virtual rt_expr f_gen_and_bool(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_or_bool(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_eq_enum(rt_expr x, rt_expr y) = 0;

  virtual rt_expr f_gen_not_bits(rt_expr x) = 0;
  virtual rt_expr f_gen_eq_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_ne_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_or_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_eor_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_and_bits(rt_expr x, rt_expr y) = 0;

  virtual rt_expr f_gen_add_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_sub_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_sdiv_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_sle_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_slt_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_mul_bits(rt_expr x, rt_expr y) = 0;

  virtual rt_expr f_gen_append_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_lsr_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_lsl_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_asr_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_replicate_bits(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_ZeroExtend(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_SignExtend(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_slice(rt_expr e, bigint lo, bigint wd) = 0;

  virtual rt_expr f_gen_FPCompare(rt_expr x, rt_expr y, rt_expr signalnan,
                                  rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPCompareEQ(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPCompareGE(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPCompareGT(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPAdd(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPSub(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPMulAdd(rt_expr addend, rt_expr x, rt_expr y,
                                 rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPMulAddH(rt_expr addend, rt_expr x, rt_expr y,
                                  rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPMulX(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPMul(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPDiv(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPMin(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPMinNum(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPMax(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPMaxNum(rt_expr x, rt_expr y, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPRecpX(rt_expr x, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPSqrt(rt_expr x, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_FPRecipEstimate(rt_expr x, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_UnsignedRSqrtEstimate(rt_expr x) = 0;
  virtual rt_expr f_gen_FPRSqrtEstimate(rt_expr x, rt_expr fpcr) = 0;
  virtual rt_expr f_gen_BFAdd(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_BFMul(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_FPConvertBF(rt_expr x, rt_expr fpcr,
                                    rt_expr rounding) = 0;
  virtual rt_expr f_gen_FPRecipStepFused(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_FPRSqrtStepFused(rt_expr x, rt_expr y) = 0;
  virtual rt_expr f_gen_FPToFixed(rt_expr x, rt_expr fbits, rt_expr isunsigned,
                                  rt_expr fpcr, rt_expr rounding) = 0;
  virtual rt_expr f_gen_FixedToFP(rt_expr x, rt_expr fbits, rt_expr isunsigned,
                                  rt_expr fpcr, rt_expr rounding) = 0;
  virtual rt_expr f_gen_FPConvert(rt_expr x, rt_expr fpcr,
                                  rt_expr rounding) = 0;
  virtual rt_expr f_gen_FPRoundInt(rt_expr x, rt_expr fpcr, rt_expr rounding,
                                   rt_expr isexact) = 0;
  virtual rt_expr f_gen_FPRoundIntN(rt_expr x, rt_expr fpcr, rt_expr rounding,
                                    rt_expr intsize) = 0;
  virtual rt_expr f_gen_FPToFixedJS_impl(rt_expr x, rt_expr fpcr,
                                         rt_expr is64) = 0; // from override.asl
};

} // namespace aslp
