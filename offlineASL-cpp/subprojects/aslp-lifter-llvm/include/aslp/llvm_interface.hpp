#pragma once
#include <charconv>
#include <llvm/ADT/APInt.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IRBuilder.h>

#include <stdexcept>
#include <string>
#include <type_traits>
#include <memory>
#include <variant>

#include <aslp/interface.hpp>
#include "llvm_lifter_traits.hpp"

namespace aslp {

class llvm_lift_time_interface : virtual public lifter_interface<llvm_lifter_traits> {
public:
  bits bits_lit(unsigned width, std::string_view str) override {
    return llvm::APInt{width, str, (char)2};
  }
  bits bits_zero(unsigned width) override {
    return llvm::APInt::getZero(width);
  }
  bigint bigint_lit(std::string_view str) override {
    bigint x;
    auto result = std::from_chars(str.cbegin(), str.cend(), x);

    if (result.ec == std::errc{} && result.ptr == str.cend()) {
     return x;
    } else {
      throw std::invalid_argument{"invalid bigint literal: " + std::string{str}};
    }
  }
  bigint bigint_zero() override {
    return 0LL;
  }

  bits extract_bits(const bits &val, bigint lo, bigint wd) override {
    return val.extractBits(wd, lo);
  }
  bool f_eq_bits(const bits &x, const bits &y) override {
    return x == y;
  }
  bool f_ne_bits(const bits &x, const bits &y) override {
    return x != y;
  }
  bits f_add_bits(const bits &x, const bits &y) override {
    return x + y;
  }
  bits f_sub_bits(const bits &x, const bits &y) override {
    return x - y;
  }
  bits f_mul_bits(const bits &x, const bits &y) override {
    return x * y;
  }
  bits f_and_bits(const bits &x, const bits &y) override {
    return x & y;
  }
  bits f_or_bits(const bits &x, const bits &y) override {
    return x | y;
  }
  bits f_eor_bits(const bits &x, const bits &y) override {
    return x ^ y;
  }
  bits f_not_bits(const bits &x) override {
    return ~x;
  }
  bool f_slt_bits(const bits &x, const bits &y) override {
    return x.slt(y);
  }
  bool f_sle_bits(const bits &x, const bits &y) override {
    return x.sle(y);
  }
  bits f_zeros_bits(bigint n) override {
    return llvm::APInt::getZero(n);
  }
  bits f_ones_bits(bigint n) override {
    return llvm::APInt::getAllOnes(n);
  }
  bits f_replicate_bits(const bits &x, bigint n) override {
    assert(n >= 1);
    bits original = x;
    unsigned wd = x.getBitWidth();
    auto ret = x.zextOrTrunc(wd * n);
    for (unsigned i = 1; i < n; i++) {
     ret <<= wd;
     ret |= original;
    }
   return ret;
  }
  bits f_append_bits(const bits &x, const bits &y) override {
    auto wd = x.getBitWidth() + y.getBitWidth();
    auto ret = x.zext(wd);
    ret <<= y.getBitWidth();
    ret |= y.zext(wd);
    return ret;
  }
  bits f_ZeroExtend(const bits &x, bigint wd) override {
    return x.zextOrTrunc(wd);
  }
  bits f_SignExtend(const bits &x, bigint wd) override {
    return x.sextOrTrunc(wd);
  }
  bits f_lsl_bits(const bits &x, const bits &y) override {
    return x << y;
  }
  bits f_lsr_bits(const bits &x, const bits &y) override {
    return x.lshr(y);
  }
  bits f_asr_bits(const bits &x, const bits &y) override {
    return x.ashr(y);
  }
  bigint f_cvt_bits_uint(const bits &x) override {
    return x.getZExtValue();
  }

};


class llvm_run_time_interface : virtual public lifter_interface<llvm_lifter_traits> {
protected:
  llvm::Function &function;
  llvm::LLVMContext &context{function.getContext()};
  llvm::Module &module{*function.getParent()};

  rt_label builder{std::make_shared<llvm::IRBuilder<>>(&function.getEntryBlock())};

  llvm::Function &assertDecl{createAssertDecl(module)};

  static llvm::Function& createAssertDecl(llvm::Module &module) {
    auto& context = module.getContext();
    auto funTy = llvm::FunctionType::get(llvm::Type::getVoidTy(context), {llvm::Type::getInt1Ty(context)}, false);
    auto fun = module.getOrInsertFunction("llvm.assert", funTy);
    return *llvm::cast<llvm::Function>(fun.getCallee());
  }

  rt_global getOrInsertGlobal(unsigned count, llvm::Type *type, const std::string_view basename) {
    if (count == 0) return {};

    rt_global ret{std::make_shared<rt_global::element_type>(count)};
    for (unsigned i = 0; i < count; i++) {
      std::string name{basename};
      if (count > 1)
        name += std::to_string(i);

      ret->at(i) = llvm::cast<llvm::GlobalVariable>(module.getOrInsertGlobal(name, type));
    }
    assert(ret->size() == count);
    return ret;
  }

  llvm::Type* intty(unsigned width) {
    return llvm::Type::getIntNTy(context, width);
  }

  bigint int_expr(rt_expr x) {
    return llvm::cast<llvm::ConstantInt>(x)->getSExtValue();
  }
  rt_expr int_const(unsigned wd, bigint x) {
    return llvm::ConstantInt::get(intty(wd), x);
  }


public:
  llvm_run_time_interface(llvm::Function &f) : function{f} {}

  rt_lexpr v_PSTATE_UAO() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "UAO")};
    return x;
  }
  rt_lexpr v_PSTATE_PAN() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "PAN")};
    return x;
  }
  rt_lexpr v_PSTATE_DIT() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "DIT")};
    return x;
  }
  rt_lexpr v_PSTATE_SSBS() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "SSBS")};
    return x;
  }
  rt_lexpr v_PSTATE_G() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "G")};
    return x;
  }
  rt_lexpr v_PSTATE_A() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "A")};
    return x;
  }
  rt_lexpr v_PSTATE_I() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "I")};
    return x;
  }
  rt_lexpr v_PSTATE_F() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "F")};
    return x;
  }
  rt_lexpr v_PSTATE_D() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "D")};
    return x;
  }


  rt_lexpr v_PSTATE_C() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "C")};
    return x;
  };
  rt_lexpr v_PSTATE_Z() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "Z")};
    return x;
  };
  rt_lexpr v_PSTATE_V() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "V")};
    return x;
  };
  rt_lexpr v_PSTATE_N() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(1), "N")};
    return x;
  };
  rt_lexpr v__PC() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(64), "PC")};
    return x;
  };
  rt_lexpr v__R() override {
    // XXX redirect some of these to FP/LR
    static rt_lexpr x{getOrInsertGlobal(31, intty(64), "R")};
    return x;
  };
  rt_lexpr v__Z() override {
    static rt_lexpr x{getOrInsertGlobal(32, intty(128), "Z")};
    return x;
  };
  rt_lexpr v_SP_EL0() override {
    static rt_lexpr x{getOrInsertGlobal(1, intty(64), "SP")};
    return x;
  };
  rt_lexpr v_FPSR() override { assert(0); };
  rt_lexpr v_FPCR() override { assert(0); };

  rt_lexpr v_PSTATE_BTYPE() override { assert(0); };
  rt_lexpr v_BTypeCompatible() override { assert(0); };
  rt_lexpr v___BranchTaken() override { assert(0); };
  rt_lexpr v_BTypeNext() override { assert(0); };
  rt_lexpr v___ExclusiveLocal() override { assert(0); };


  rt_lexpr f_decl_bv(std::string_view name, bigint width) override {
    return builder->CreateAlloca(intty(width), /*addrspace*/0, /*arraysize*/nullptr, name);
  }
  rt_lexpr f_decl_bool(std::string_view name) override {
    return f_decl_bv(name, 1);
  }

  void f_switch_context(rt_label label) override { builder.swap(label); }

  std::tuple<rt_label, rt_label, rt_label> f_gen_branch(rt_expr cond) override {
    auto tcase = llvm::BasicBlock::Create(context, "true", &function);
    auto fcase = llvm::BasicBlock::Create(context, "false", &function);
    auto join = llvm::BasicBlock::Create(context, "join", &function);

    builder->CreateCondBr(cond, tcase, fcase);

    rt_label tlabel = std::make_shared<llvm::IRBuilder<>>(llvm::BranchInst::Create(join, tcase));
    rt_label flabel = std::make_shared<llvm::IRBuilder<>>(llvm::BranchInst::Create(join, fcase));
    rt_label jlabel = std::make_shared<llvm::IRBuilder<>>(join);

    return std::make_tuple(std::move(tlabel), std::move(flabel), std::move(jlabel));
  }

  rt_label f_true_branch(std::tuple<rt_label, rt_label, rt_label> x) override {
    return std::get<0>(x);
  }
  rt_label f_false_branch(std::tuple<rt_label, rt_label, rt_label> x) override {
    return std::get<1>(x);
  }
  rt_label f_merge_branch(std::tuple<rt_label, rt_label, rt_label> x) override {
    return std::get<2>(x);
  }

  void f_gen_assert(rt_expr cond) override {
    builder->CreateCall(assertDecl.getFunctionType(), &assertDecl, {cond});
  }
  rt_expr f_gen_bit_lit(bits bits) override {
    return llvm::ConstantInt::get(intty(bits.getBitWidth()), bits);
  }
  rt_expr f_gen_bool_lit(bool b) override {
    return f_gen_bit_lit(b ? llvm::APInt::getAllOnes(1) : llvm::APInt::getZero(1));
  }
  rt_expr f_gen_int_lit(bigint i) override {
    return llvm::ConstantInt::get(intty(111), i); // XXX hopefully this is never needed
  }

  rt_expr f_gen_load(rt_lexpr ptr) override {
    return f_gen_array_load(ptr, 0);
  }
  void f_gen_store(rt_lexpr ptr, rt_expr exp) override {
    return f_gen_array_store(ptr, 0, exp);
  }
 
  rt_expr f_gen_array_load(rt_lexpr var, bigint index) override {
    llvm::Value* ptr{};
    llvm::Type* ty{};

    if (auto global = std::get_if<rt_global>(&var); global) {
      auto glob = global[0]->at(index);
      ptr = glob;
      ty = glob->getValueType();
    } else if (auto local = std::get_if<rt_local>(&var); local) {
      assert(index == 0 && "non-zero index into rt_local");
      ptr = *local;
      ty = local[0]->getAllocatedType();
    }
    assert(ptr && ty);
    return builder->CreateLoad(ty, ptr);
  }

  void f_gen_array_store(rt_lexpr var, bigint index, rt_expr exp) override {
    llvm::Value* ptr{};

    if (auto global = std::get_if<rt_global>(&var); global) {
      auto glob = global[0]->at(index);
      ptr = glob;
    } else if (auto local = std::get_if<rt_local>(&var); local) {
      assert(index == 0 && "non-zero index into rt_local");
      ptr = *local;
    }
    assert(ptr);
    builder->CreateStore(exp, ptr);
  }
  void f_gen_Mem_set(rt_expr addr, rt_expr width, rt_expr acctype, rt_expr exp) override {
    auto ptr = builder->CreateIntToPtr(addr, llvm::PointerType::get(context, 0));
    builder->CreateStore(exp, ptr);
  }
  rt_expr f_gen_Mem_read(rt_expr addr, rt_expr width, rt_expr acctype) override {
    auto ptr = builder->CreateIntToPtr(addr, llvm::PointerType::get(context, 0));
    return builder->CreateLoad(intty(int_expr(width)), ptr);
  }
  void f_gen_AArch64_MemTag_set(rt_expr address, rt_expr acctype, rt_expr value) override { assert(0); }
  rt_expr f_gen_AArch64_MemTag_read(rt_expr address, rt_expr acctype) override { assert(0); }

  void f_AtomicStart() override { assert(0); }
  void f_AtomicEnd() override { assert(0); }

  rt_expr f_gen_cvt_bits_uint(rt_expr bits) override {
    return bits;
  }
  rt_expr f_gen_cvt_bool_bv(rt_expr e) override {
    assert(e->getType()->getIntegerBitWidth() == 1 && "f_gen_cvt_bool_bv given non-bv1 expression");
    return e;
  }

  rt_expr f_gen_not_bool(rt_expr e) override {
    return f_gen_not_bits(e);
  }
  rt_expr f_gen_and_bool(rt_expr x, rt_expr y) override {
    return f_gen_and_bits(x, y);
  }
  rt_expr f_gen_or_bool(rt_expr x, rt_expr y) override {
    return f_gen_or_bits(x, y);
  }
  rt_expr f_gen_eq_enum(rt_expr x, rt_expr y) override {
    return f_gen_eq_bits(x, y);
  }

  rt_expr f_gen_not_bits(rt_expr x) override {
    return builder->CreateNot(x);
  }
  rt_expr f_gen_eq_bits(rt_expr x, rt_expr y) override {
    return builder->CreateICmpEQ(x, y);
  }
  rt_expr f_gen_ne_bits(rt_expr x, rt_expr y) override {
    return builder->CreateICmpNE(x, y);
  }
  rt_expr f_gen_or_bits(rt_expr x, rt_expr y) override {
    return builder->CreateOr(x, y);
  }
  rt_expr f_gen_eor_bits(rt_expr x, rt_expr y) override {
    return builder->CreateXor(x, y);
  }
  rt_expr f_gen_and_bits(rt_expr x, rt_expr y) override {
    return builder->CreateAnd(x, y);
  }

  rt_expr f_gen_add_bits(rt_expr x, rt_expr y) override {
    return builder->CreateAdd(x, y);
  }
  rt_expr f_gen_sub_bits(rt_expr x, rt_expr y) override {
    return builder->CreateSub(x, y);
  }
  rt_expr f_gen_sdiv_bits(rt_expr x, rt_expr y) override {
    return builder->CreateSDiv(x, y);
  }
  rt_expr f_gen_sle_bits(rt_expr x, rt_expr y) override {
    return builder->CreateICmpSLE(x, y);
  }
  rt_expr f_gen_slt_bits(rt_expr x, rt_expr y) override {
    return builder->CreateICmpSLT(x, y);
  }
  rt_expr f_gen_mul_bits(rt_expr x, rt_expr y) override {
    return builder->CreateMul(x, y);
  }

  rt_expr f_gen_append_bits(rt_expr x, rt_expr y) override {
    unsigned xwd = x->getType()->getIntegerBitWidth();
    unsigned wd = xwd + y->getType()->getIntegerBitWidth();
    // shift lhs
    x = builder->CreateZExtOrBitCast(x, intty(wd));
    x = builder->CreateShl(x, int_const(wd, xwd));
    // union with rhs
    y = builder->CreateZExtOrBitCast(y, intty(wd));
    return builder->CreateOr(x, y);
  }
  rt_expr f_gen_lsr_bits(rt_expr x, rt_expr y) override {
    // assert(x->getType() == y->getType());
    auto wd = x->getType()->getIntegerBitWidth();
    auto max = llvm::ConstantInt::get(x->getType(), wd-1);
    auto ok = builder->CreateICmpULE(y, max);
    auto shift = builder->CreateLShr(x, y);
    auto zero = int_const(wd, 0);
    return builder->CreateSelect(ok, shift, zero);
  }

  rt_expr f_gen_lsl_bits(rt_expr x, rt_expr y) override {
    // assert(x->getType() == y->getType());
    auto wd = x->getType()->getIntegerBitWidth();
    auto max = llvm::ConstantInt::get(x->getType(), wd-1);
    auto ok = builder->CreateICmpULE(y, max);
    auto shift = builder->CreateShl(x, y);
    auto zero = int_const(wd, 0);
    return builder->CreateSelect(ok, shift, zero);
  }

  rt_expr f_gen_asr_bits(rt_expr x, rt_expr y) override {
    assert(x->getType() == y->getType());
    auto wd = x->getType()->getIntegerBitWidth();
    auto max = llvm::ConstantInt::get(x->getType(), wd-1);
    auto ok = builder->CreateICmpULE(y, max);
    auto shift = builder->CreateAShr(x, y);
    auto zero = int_const(wd, 0);
    return builder->CreateSelect(ok, shift, zero);
  }

  rt_expr f_gen_replicate_bits(rt_expr x, rt_expr y) override {
    auto count = int_expr(y);
    auto basewd = x->getType()->getIntegerBitWidth() ;
    auto finalwd = basewd * count;
    auto finalty = intty(finalwd);

    auto base = builder->CreateZExtOrBitCast(x, finalty);
    auto ret = base;
    for (unsigned i = 1; i < count; i++) {
      auto shifted = builder->CreateShl(base, int_const(finalwd, basewd * i));
      ret = builder->CreateOr(ret, shifted);
    }
    return ret;
  }

  rt_expr f_gen_ZeroExtend(rt_expr x, rt_expr y) override {
    return builder->CreateZExtOrBitCast(x, intty(int_expr(y)));
  }
  rt_expr f_gen_SignExtend(rt_expr x, rt_expr y) override {
    return builder->CreateSExtOrBitCast(x, intty(int_expr(y)));
  }

  rt_expr f_gen_slice(rt_expr e, bigint lo, bigint wd) override {
    auto shifted = lo != 0 ? builder->CreateLShr(e, llvm::ConstantInt::get(e->getType(), lo)) : e;
    return builder->CreateTruncOrBitCast(shifted, intty(wd));
  }

  rt_expr f_gen_FPCompare(rt_expr x, rt_expr y, rt_expr signalnan, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPCompareEQ(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPCompareGE(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPCompareGT(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPAdd(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPSub(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPMulAdd(rt_expr addend, rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPMulAddH(rt_expr addend, rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPMulX(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPMul(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPDiv(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPMin(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPMinNum(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPMax(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPMaxNum(rt_expr x, rt_expr y, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPRecpX(rt_expr x, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPSqrt(rt_expr x, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_FPRecipEstimate(rt_expr x, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_UnsignedRSqrtEstimate(rt_expr x) override { assert(0); }
  rt_expr f_gen_FPRSqrtEstimate(rt_expr x, rt_expr fpcr) override { assert(0); }
  rt_expr f_gen_BFAdd(rt_expr x, rt_expr y) override { assert(0); }
  rt_expr f_gen_BFMul(rt_expr x, rt_expr y) override { assert(0); }
  rt_expr f_gen_FPConvertBF(rt_expr x, rt_expr fpcr, rt_expr rounding) override { assert(0); }
  rt_expr f_gen_FPRecipStepFused(rt_expr x, rt_expr y) override { assert(0); }
  rt_expr f_gen_FPRSqrtStepFused(rt_expr x, rt_expr y) override { assert(0); }
  rt_expr f_gen_FPToFixed(rt_expr x, rt_expr fbits, rt_expr isunsigned, rt_expr fpcr, rt_expr rounding) override { assert(0); }
  rt_expr f_gen_FixedToFP(rt_expr x, rt_expr fbits, rt_expr isunsigned, rt_expr fpcr, rt_expr rounding) override { assert(0); }
  rt_expr f_gen_FPConvert(rt_expr x, rt_expr fpcr, rt_expr rounding) override { assert(0); }
  rt_expr f_gen_FPRoundInt(rt_expr x, rt_expr fpcr, rt_expr rounding, rt_expr isexact) override { assert(0); }
  rt_expr f_gen_FPRoundIntN(rt_expr x, rt_expr fpcr, rt_expr rounding, rt_expr intsize) override { assert(0); }
  rt_expr f_gen_FPToFixedJS_impl(rt_expr x, rt_expr fpcr, rt_expr is64) override { assert(0); } // from override.asl
};


class llvm_lifter_interface : public llvm_lift_time_interface, public llvm_run_time_interface {
public:
  llvm_lifter_interface(llvm::Function &f) : llvm_run_time_interface(f) { };
};

static_assert(!std::is_abstract_v<llvm_lifter_interface>);

} // namespace aslp
