adds x1, x2, x3:
  $ echo 0xab030041 >> input

sub sp, sp, #32:
  $ echo 0xd10083ff >> input

ucvtf d0, w2:
  $ echo 0x1e630040 >> input

mrs x0, nzcv:
  $ echo 0xd53b4200 >> input

tbl v0.8b, {v0.16b}, v0.8b:
  $ echo 0x0e000000 >> input

note: concatenate all commands to avoid aslp startup overhead
  $ for op in $(cat input); do printf '%s\n' "\"\n$op\n\"" ":sem A64 $op" '""' ":ast A64 $op"; done > commands

  $ asli < commands
  "
  0xab030041
  "
  Decoding instruction A64 ab030041
  constant bits ( 64 ) Cse0__5 = add_bits.0 {{ 64 }} ( __array _R [ 2 ],__array _R [ 3 ] ) ;
  PSTATE . V = not_bits.0 {{ 1 }} ( cvt_bool_bv.0 {{  }} ( eq_bits.0 {{ 65 }} ( SignExtend.0 {{ 64,65 }} ( Cse0__5,65 ),add_bits.0 {{ 65 }} ( SignExtend.0 {{ 64,65 }} ( __array _R [ 2 ],65 ),SignExtend.0 {{ 64,65 }} ( __array _R [ 3 ],65 ) ) ) ) ) ;
  PSTATE . C = not_bits.0 {{ 1 }} ( cvt_bool_bv.0 {{  }} ( eq_bits.0 {{ 65 }} ( ZeroExtend.0 {{ 64,65 }} ( Cse0__5,65 ),add_bits.0 {{ 65 }} ( ZeroExtend.0 {{ 64,65 }} ( __array _R [ 2 ],65 ),ZeroExtend.0 {{ 64,65 }} ( __array _R [ 3 ],65 ) ) ) ) ) ;
  PSTATE . Z = cvt_bool_bv.0 {{  }} ( eq_bits.0 {{ 64 }} ( Cse0__5,'0000000000000000000000000000000000000000000000000000000000000000' ) ) ;
  PSTATE . N = Cse0__5 [ 63 +: 1 ] ;
  __array _R [ 1 ] = Cse0__5 ;
  ""
  Stmt_ConstDecl(Type_Bits(Expr_LitInt("64")),"Cse0__5",Expr_TApply("add_bits.0",[(Expr_LitInt("64"))],[(Expr_Array(Expr_Var("_R"),Expr_LitInt("2")));(Expr_Array(Expr_Var("_R"),Expr_LitInt("3")))]))
  Stmt_Assign(LExpr_Field(LExpr_Var("PSTATE"),V),Expr_TApply("not_bits.0",[(Expr_LitInt("1"))],[(Expr_TApply("cvt_bool_bv.0",[],[(Expr_TApply("eq_bits.0",[(Expr_LitInt("65"))],[(Expr_TApply("SignExtend.0",[(Expr_LitInt("64"));(Expr_LitInt("65"))],[(Expr_Var("Cse0__5"));(Expr_LitInt("65"))]));(Expr_TApply("add_bits.0",[(Expr_LitInt("65"))],[(Expr_TApply("SignExtend.0",[(Expr_LitInt("64"));(Expr_LitInt("65"))],[(Expr_Array(Expr_Var("_R"),Expr_LitInt("2")));(Expr_LitInt("65"))]));(Expr_TApply("SignExtend.0",[(Expr_LitInt("64"));(Expr_LitInt("65"))],[(Expr_Array(Expr_Var("_R"),Expr_LitInt("3")));(Expr_LitInt("65"))]))]))]))]))]))
  Stmt_Assign(LExpr_Field(LExpr_Var("PSTATE"),C),Expr_TApply("not_bits.0",[(Expr_LitInt("1"))],[(Expr_TApply("cvt_bool_bv.0",[],[(Expr_TApply("eq_bits.0",[(Expr_LitInt("65"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("64"));(Expr_LitInt("65"))],[(Expr_Var("Cse0__5"));(Expr_LitInt("65"))]));(Expr_TApply("add_bits.0",[(Expr_LitInt("65"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("64"));(Expr_LitInt("65"))],[(Expr_Array(Expr_Var("_R"),Expr_LitInt("2")));(Expr_LitInt("65"))]));(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("64"));(Expr_LitInt("65"))],[(Expr_Array(Expr_Var("_R"),Expr_LitInt("3")));(Expr_LitInt("65"))]))]))]))]))]))
  Stmt_Assign(LExpr_Field(LExpr_Var("PSTATE"),Z),Expr_TApply("cvt_bool_bv.0",[],[(Expr_TApply("eq_bits.0",[(Expr_LitInt("64"))],[(Expr_Var("Cse0__5"));(Expr_LitBits("0000000000000000000000000000000000000000000000000000000000000000"))]))]))
  Stmt_Assign(LExpr_Field(LExpr_Var("PSTATE"),N),Expr_Slices(Expr_Var("Cse0__5"),[(Slice_LoWd(Expr_LitInt("63"),Expr_LitInt("1")))]))
  Stmt_Assign(LExpr_Array(LExpr_Var("_R"),Expr_LitInt("1")),Expr_Var("Cse0__5"))
  "
  0xd10083ff
  "
  Decoding instruction A64 d10083ff
  SP_EL0 = add_bits.0 {{ 64 }} ( SP_EL0,'1111111111111111111111111111111111111111111111111111111111100000' ) ;
  ""
  Stmt_Assign(LExpr_Var("SP_EL0"),Expr_TApply("add_bits.0",[(Expr_LitInt("64"))],[(Expr_Var("SP_EL0"));(Expr_LitBits("1111111111111111111111111111111111111111111111111111111111100000"))]))
  "
  0x1e630040
  "
  Decoding instruction A64 1e630040
  bits ( 3 ) FPDecodeRounding5__5 ;
  FPDecodeRounding5__5 = ZeroExtend.0 {{ 2,3 }} ( FPCR [ 22 +: 2 ],3 ) ;
  constant bits ( 64 ) Exp9__5 = FixedToFP.0 {{ 32,64 }} ( __array _R [ 2 ] [ 0 +: 32 ],0,TRUE,FPCR,cvt_bits_uint.0 {{ 3 }} ( FPDecodeRounding5__5 ) ) ;
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( Exp9__5,128 ) ;
  ""
  Stmt_VarDeclsNoInit(Type_Bits(Expr_LitInt("3")),[("FPDecodeRounding5__5")])
  Stmt_Assign(LExpr_Var("FPDecodeRounding5__5"),Expr_TApply("ZeroExtend.0",[(Expr_LitInt("2"));(Expr_LitInt("3"))],[(Expr_Slices(Expr_Var("FPCR"),[(Slice_LoWd(Expr_LitInt("22"),Expr_LitInt("2")))]));(Expr_LitInt("3"))]))
  Stmt_ConstDecl(Type_Bits(Expr_LitInt("64")),"Exp9__5",Expr_TApply("FixedToFP.0",[(Expr_LitInt("32"));(Expr_LitInt("64"))],[(Expr_Slices(Expr_Array(Expr_Var("_R"),Expr_LitInt("2")),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("32")))]));(Expr_LitInt("0"));(Expr_Var("TRUE"));(Expr_Var("FPCR"));(Expr_TApply("cvt_bits_uint.0",[(Expr_LitInt("3"))],[(Expr_Var("FPDecodeRounding5__5"))]))]))
  Stmt_Assign(LExpr_Array(LExpr_Var("_Z"),Expr_LitInt("0")),Expr_TApply("ZeroExtend.0",[(Expr_LitInt("64"));(Expr_LitInt("128"))],[(Expr_Var("Exp9__5"));(Expr_LitInt("128"))]))
  "
  0xd53b4200
  "
  Decoding instruction A64 d53b4200
  __array _R [ 0 ] = append_bits.0 {{ 36,28 }} ( append_bits.0 {{ 32,4 }} ( '00000000000000000000000000000000',append_bits.0 {{ 3,1 }} ( append_bits.0 {{ 2,1 }} ( append_bits.0 {{ 1,1 }} ( PSTATE . N,PSTATE . Z ),PSTATE . C ),PSTATE . V ) ),'0000000000000000000000000000' ) ;
  ""
  Stmt_Assign(LExpr_Array(LExpr_Var("_R"),Expr_LitInt("0")),Expr_TApply("append_bits.0",[(Expr_LitInt("36"));(Expr_LitInt("28"))],[(Expr_TApply("append_bits.0",[(Expr_LitInt("32"));(Expr_LitInt("4"))],[(Expr_LitBits("00000000000000000000000000000000"));(Expr_TApply("append_bits.0",[(Expr_LitInt("3"));(Expr_LitInt("1"))],[(Expr_TApply("append_bits.0",[(Expr_LitInt("2"));(Expr_LitInt("1"))],[(Expr_TApply("append_bits.0",[(Expr_LitInt("1"));(Expr_LitInt("1"))],[(Expr_Field(Expr_Var("PSTATE"),N));(Expr_Field(Expr_Var("PSTATE"),Z))]));(Expr_Field(Expr_Var("PSTATE"),C))]));(Expr_Field(Expr_Var("PSTATE"),V))]))]));(Expr_LitBits("0000000000000000000000000000"))]))
  "
  0x0e000000
  "
  Decoding instruction A64 e000000
  constant bits ( 9 ) Cse7__5 = ZeroExtend.0 {{ 8,9 }} ( __array _Z [ 0 ] [ 0 +: 8 ],9 ) ;
  constant bits ( 9 ) Cse6__5 = ZeroExtend.0 {{ 8,9 }} ( __array _Z [ 0 ] [ 8 +: 8 ],9 ) ;
  constant bits ( 9 ) Cse5__5 = ZeroExtend.0 {{ 8,9 }} ( __array _Z [ 0 ] [ 16 +: 8 ],9 ) ;
  constant bits ( 9 ) Cse4__5 = ZeroExtend.0 {{ 8,9 }} ( __array _Z [ 0 ] [ 24 +: 8 ],9 ) ;
  constant bits ( 9 ) Cse3__5 = ZeroExtend.0 {{ 8,9 }} ( __array _Z [ 0 ] [ 32 +: 8 ],9 ) ;
  constant bits ( 9 ) Cse2__5 = ZeroExtend.0 {{ 8,9 }} ( __array _Z [ 0 ] [ 40 +: 8 ],9 ) ;
  constant bits ( 9 ) Cse1__5 = ZeroExtend.0 {{ 8,9 }} ( __array _Z [ 0 ] [ 48 +: 8 ],9 ) ;
  constant bits ( 9 ) Cse0__5 = ZeroExtend.0 {{ 8,9 }} ( __array _Z [ 0 ] [ 56 +: 8 ],9 ) ;
  bits ( 64 ) result__4 ;
  result__4 = '0000000000000000000000000000000000000000000000000000000000000000' ;
  if slt_bits.0 {{ 9 }} ( Cse7__5,'000010000' ) then {
  assert and_bool.0 {{  }} ( sle_bits.0 {{ 9 }} ( '000000000',Cse7__5 ),sle_bits.0 {{ 13 }} ( ZeroExtend.0 {{ 12,13 }} ( mul_bits.0 {{ 12 }} ( ZeroExtend.0 {{ 9,12 }} ( add_bits.0 {{ 9 }} ( Cse7__5,'000000001' ),12 ),'000000001000' ),13 ),'0000010000000' ) ) ;
  result__4 = append_bits.0 {{ 56,8 }} ( '00000000000000000000000000000000000000000000000000000000',lsr_bits.0 {{ 128,12 }} ( __array _Z [ 0 ],ZeroExtend.0 {{ 11,12 }} ( mul_bits.0 {{ 11 }} ( ZeroExtend.0 {{ 8,11 }} ( __array _Z [ 0 ] [ 0 +: 8 ],11 ),'00000001000' ),12 ) ) [ 0 +: 8 ] ) ;
  }
  if slt_bits.0 {{ 9 }} ( Cse6__5,'000010000' ) then {
  assert and_bool.0 {{  }} ( sle_bits.0 {{ 9 }} ( '000000000',Cse6__5 ),sle_bits.0 {{ 13 }} ( ZeroExtend.0 {{ 12,13 }} ( mul_bits.0 {{ 12 }} ( ZeroExtend.0 {{ 9,12 }} ( add_bits.0 {{ 9 }} ( Cse6__5,'000000001' ),12 ),'000000001000' ),13 ),'0000010000000' ) ) ;
  result__4 = append_bits.0 {{ 48,16 }} ( result__4 [ 16 +: 48 ],append_bits.0 {{ 8,8 }} ( lsr_bits.0 {{ 128,12 }} ( __array _Z [ 0 ],ZeroExtend.0 {{ 11,12 }} ( mul_bits.0 {{ 11 }} ( ZeroExtend.0 {{ 8,11 }} ( __array _Z [ 0 ] [ 8 +: 8 ],11 ),'00000001000' ),12 ) ) [ 0 +: 8 ],result__4 [ 0 +: 8 ] ) ) ;
  }
  if slt_bits.0 {{ 9 }} ( Cse5__5,'000010000' ) then {
  assert and_bool.0 {{  }} ( sle_bits.0 {{ 9 }} ( '000000000',Cse5__5 ),sle_bits.0 {{ 13 }} ( ZeroExtend.0 {{ 12,13 }} ( mul_bits.0 {{ 12 }} ( ZeroExtend.0 {{ 9,12 }} ( add_bits.0 {{ 9 }} ( Cse5__5,'000000001' ),12 ),'000000001000' ),13 ),'0000010000000' ) ) ;
  result__4 = append_bits.0 {{ 40,24 }} ( result__4 [ 24 +: 40 ],append_bits.0 {{ 8,16 }} ( lsr_bits.0 {{ 128,12 }} ( __array _Z [ 0 ],ZeroExtend.0 {{ 11,12 }} ( mul_bits.0 {{ 11 }} ( ZeroExtend.0 {{ 8,11 }} ( __array _Z [ 0 ] [ 16 +: 8 ],11 ),'00000001000' ),12 ) ) [ 0 +: 8 ],result__4 [ 0 +: 16 ] ) ) ;
  }
  if slt_bits.0 {{ 9 }} ( Cse4__5,'000010000' ) then {
  assert and_bool.0 {{  }} ( sle_bits.0 {{ 9 }} ( '000000000',Cse4__5 ),sle_bits.0 {{ 13 }} ( ZeroExtend.0 {{ 12,13 }} ( mul_bits.0 {{ 12 }} ( ZeroExtend.0 {{ 9,12 }} ( add_bits.0 {{ 9 }} ( Cse4__5,'000000001' ),12 ),'000000001000' ),13 ),'0000010000000' ) ) ;
  result__4 = append_bits.0 {{ 32,32 }} ( result__4 [ 32 +: 32 ],append_bits.0 {{ 8,24 }} ( lsr_bits.0 {{ 128,12 }} ( __array _Z [ 0 ],ZeroExtend.0 {{ 11,12 }} ( mul_bits.0 {{ 11 }} ( ZeroExtend.0 {{ 8,11 }} ( __array _Z [ 0 ] [ 24 +: 8 ],11 ),'00000001000' ),12 ) ) [ 0 +: 8 ],result__4 [ 0 +: 24 ] ) ) ;
  }
  if slt_bits.0 {{ 9 }} ( Cse3__5,'000010000' ) then {
  assert and_bool.0 {{  }} ( sle_bits.0 {{ 9 }} ( '000000000',Cse3__5 ),sle_bits.0 {{ 13 }} ( ZeroExtend.0 {{ 12,13 }} ( mul_bits.0 {{ 12 }} ( ZeroExtend.0 {{ 9,12 }} ( add_bits.0 {{ 9 }} ( Cse3__5,'000000001' ),12 ),'000000001000' ),13 ),'0000010000000' ) ) ;
  result__4 = append_bits.0 {{ 24,40 }} ( result__4 [ 40 +: 24 ],append_bits.0 {{ 8,32 }} ( lsr_bits.0 {{ 128,12 }} ( __array _Z [ 0 ],ZeroExtend.0 {{ 11,12 }} ( mul_bits.0 {{ 11 }} ( ZeroExtend.0 {{ 8,11 }} ( __array _Z [ 0 ] [ 32 +: 8 ],11 ),'00000001000' ),12 ) ) [ 0 +: 8 ],result__4 [ 0 +: 32 ] ) ) ;
  }
  if slt_bits.0 {{ 9 }} ( Cse2__5,'000010000' ) then {
  assert and_bool.0 {{  }} ( sle_bits.0 {{ 9 }} ( '000000000',Cse2__5 ),sle_bits.0 {{ 13 }} ( ZeroExtend.0 {{ 12,13 }} ( mul_bits.0 {{ 12 }} ( ZeroExtend.0 {{ 9,12 }} ( add_bits.0 {{ 9 }} ( Cse2__5,'000000001' ),12 ),'000000001000' ),13 ),'0000010000000' ) ) ;
  result__4 = append_bits.0 {{ 16,48 }} ( result__4 [ 48 +: 16 ],append_bits.0 {{ 8,40 }} ( lsr_bits.0 {{ 128,12 }} ( __array _Z [ 0 ],ZeroExtend.0 {{ 11,12 }} ( mul_bits.0 {{ 11 }} ( ZeroExtend.0 {{ 8,11 }} ( __array _Z [ 0 ] [ 40 +: 8 ],11 ),'00000001000' ),12 ) ) [ 0 +: 8 ],result__4 [ 0 +: 40 ] ) ) ;
  }
  if slt_bits.0 {{ 9 }} ( Cse1__5,'000010000' ) then {
  assert and_bool.0 {{  }} ( sle_bits.0 {{ 9 }} ( '000000000',Cse1__5 ),sle_bits.0 {{ 13 }} ( ZeroExtend.0 {{ 12,13 }} ( mul_bits.0 {{ 12 }} ( ZeroExtend.0 {{ 9,12 }} ( add_bits.0 {{ 9 }} ( Cse1__5,'000000001' ),12 ),'000000001000' ),13 ),'0000010000000' ) ) ;
  result__4 = append_bits.0 {{ 8,56 }} ( result__4 [ 56 +: 8 ],append_bits.0 {{ 8,48 }} ( lsr_bits.0 {{ 128,12 }} ( __array _Z [ 0 ],ZeroExtend.0 {{ 11,12 }} ( mul_bits.0 {{ 11 }} ( ZeroExtend.0 {{ 8,11 }} ( __array _Z [ 0 ] [ 48 +: 8 ],11 ),'00000001000' ),12 ) ) [ 0 +: 8 ],result__4 [ 0 +: 48 ] ) ) ;
  }
  if slt_bits.0 {{ 9 }} ( Cse0__5,'000010000' ) then {
  assert and_bool.0 {{  }} ( sle_bits.0 {{ 9 }} ( '000000000',Cse0__5 ),sle_bits.0 {{ 13 }} ( ZeroExtend.0 {{ 12,13 }} ( mul_bits.0 {{ 12 }} ( ZeroExtend.0 {{ 9,12 }} ( add_bits.0 {{ 9 }} ( Cse0__5,'000000001' ),12 ),'000000001000' ),13 ),'0000010000000' ) ) ;
  result__4 = append_bits.0 {{ 8,56 }} ( lsr_bits.0 {{ 128,12 }} ( __array _Z [ 0 ],ZeroExtend.0 {{ 11,12 }} ( mul_bits.0 {{ 11 }} ( ZeroExtend.0 {{ 8,11 }} ( __array _Z [ 0 ] [ 56 +: 8 ],11 ),'00000001000' ),12 ) ) [ 0 +: 8 ],result__4 [ 0 +: 56 ] ) ;
  }
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  ""
  Stmt_ConstDecl(Type_Bits(Expr_LitInt("9")),"Cse7__5",Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("9"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]));(Expr_LitInt("9"))]))
  Stmt_ConstDecl(Type_Bits(Expr_LitInt("9")),"Cse6__5",Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("9"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("8"),Expr_LitInt("8")))]));(Expr_LitInt("9"))]))
  Stmt_ConstDecl(Type_Bits(Expr_LitInt("9")),"Cse5__5",Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("9"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("16"),Expr_LitInt("8")))]));(Expr_LitInt("9"))]))
  Stmt_ConstDecl(Type_Bits(Expr_LitInt("9")),"Cse4__5",Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("9"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("24"),Expr_LitInt("8")))]));(Expr_LitInt("9"))]))
  Stmt_ConstDecl(Type_Bits(Expr_LitInt("9")),"Cse3__5",Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("9"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("32"),Expr_LitInt("8")))]));(Expr_LitInt("9"))]))
  Stmt_ConstDecl(Type_Bits(Expr_LitInt("9")),"Cse2__5",Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("9"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("40"),Expr_LitInt("8")))]));(Expr_LitInt("9"))]))
  Stmt_ConstDecl(Type_Bits(Expr_LitInt("9")),"Cse1__5",Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("9"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("48"),Expr_LitInt("8")))]));(Expr_LitInt("9"))]))
  Stmt_ConstDecl(Type_Bits(Expr_LitInt("9")),"Cse0__5",Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("9"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("56"),Expr_LitInt("8")))]));(Expr_LitInt("9"))]))
  Stmt_VarDeclsNoInit(Type_Bits(Expr_LitInt("64")),[("result__4")])
  Stmt_Assign(LExpr_Var("result__4"),Expr_LitBits("0000000000000000000000000000000000000000000000000000000000000000"))
  Stmt_If(Expr_TApply("slt_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse7__5"));(Expr_LitBits("000010000"))]),[
  Stmt_Assert(Expr_TApply("and_bool.0",[],[(Expr_TApply("sle_bits.0",[(Expr_LitInt("9"))],[(Expr_LitBits("000000000"));(Expr_Var("Cse7__5"))]));(Expr_TApply("sle_bits.0",[(Expr_LitInt("13"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("12"));(Expr_LitInt("13"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("12"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("9"));(Expr_LitInt("12"))],[(Expr_TApply("add_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse7__5"));(Expr_LitBits("000000001"))]));(Expr_LitInt("12"))]));(Expr_LitBits("000000001000"))]));(Expr_LitInt("13"))]));(Expr_LitBits("0000010000000"))]))]))
  Stmt_Assign(LExpr_Var("result__4"),Expr_TApply("append_bits.0",[(Expr_LitInt("56"));(Expr_LitInt("8"))],[(Expr_LitBits("00000000000000000000000000000000000000000000000000000000"));(Expr_Slices(Expr_TApply("lsr_bits.0",[(Expr_LitInt("128"));(Expr_LitInt("12"))],[(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")));(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("11"));(Expr_LitInt("12"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("11"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("11"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]));(Expr_LitInt("11"))]));(Expr_LitBits("00000001000"))]));(Expr_LitInt("12"))]))]),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]))]))
  ],[],[])
  Stmt_If(Expr_TApply("slt_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse6__5"));(Expr_LitBits("000010000"))]),[
  Stmt_Assert(Expr_TApply("and_bool.0",[],[(Expr_TApply("sle_bits.0",[(Expr_LitInt("9"))],[(Expr_LitBits("000000000"));(Expr_Var("Cse6__5"))]));(Expr_TApply("sle_bits.0",[(Expr_LitInt("13"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("12"));(Expr_LitInt("13"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("12"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("9"));(Expr_LitInt("12"))],[(Expr_TApply("add_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse6__5"));(Expr_LitBits("000000001"))]));(Expr_LitInt("12"))]));(Expr_LitBits("000000001000"))]));(Expr_LitInt("13"))]));(Expr_LitBits("0000010000000"))]))]))
  Stmt_Assign(LExpr_Var("result__4"),Expr_TApply("append_bits.0",[(Expr_LitInt("48"));(Expr_LitInt("16"))],[(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("16"),Expr_LitInt("48")))]));(Expr_TApply("append_bits.0",[(Expr_LitInt("8"));(Expr_LitInt("8"))],[(Expr_Slices(Expr_TApply("lsr_bits.0",[(Expr_LitInt("128"));(Expr_LitInt("12"))],[(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")));(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("11"));(Expr_LitInt("12"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("11"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("11"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("8"),Expr_LitInt("8")))]));(Expr_LitInt("11"))]));(Expr_LitBits("00000001000"))]));(Expr_LitInt("12"))]))]),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]));(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]))]))]))
  ],[],[])
  Stmt_If(Expr_TApply("slt_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse5__5"));(Expr_LitBits("000010000"))]),[
  Stmt_Assert(Expr_TApply("and_bool.0",[],[(Expr_TApply("sle_bits.0",[(Expr_LitInt("9"))],[(Expr_LitBits("000000000"));(Expr_Var("Cse5__5"))]));(Expr_TApply("sle_bits.0",[(Expr_LitInt("13"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("12"));(Expr_LitInt("13"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("12"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("9"));(Expr_LitInt("12"))],[(Expr_TApply("add_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse5__5"));(Expr_LitBits("000000001"))]));(Expr_LitInt("12"))]));(Expr_LitBits("000000001000"))]));(Expr_LitInt("13"))]));(Expr_LitBits("0000010000000"))]))]))
  Stmt_Assign(LExpr_Var("result__4"),Expr_TApply("append_bits.0",[(Expr_LitInt("40"));(Expr_LitInt("24"))],[(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("24"),Expr_LitInt("40")))]));(Expr_TApply("append_bits.0",[(Expr_LitInt("8"));(Expr_LitInt("16"))],[(Expr_Slices(Expr_TApply("lsr_bits.0",[(Expr_LitInt("128"));(Expr_LitInt("12"))],[(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")));(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("11"));(Expr_LitInt("12"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("11"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("11"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("16"),Expr_LitInt("8")))]));(Expr_LitInt("11"))]));(Expr_LitBits("00000001000"))]));(Expr_LitInt("12"))]))]),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]));(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("16")))]))]))]))
  ],[],[])
  Stmt_If(Expr_TApply("slt_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse4__5"));(Expr_LitBits("000010000"))]),[
  Stmt_Assert(Expr_TApply("and_bool.0",[],[(Expr_TApply("sle_bits.0",[(Expr_LitInt("9"))],[(Expr_LitBits("000000000"));(Expr_Var("Cse4__5"))]));(Expr_TApply("sle_bits.0",[(Expr_LitInt("13"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("12"));(Expr_LitInt("13"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("12"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("9"));(Expr_LitInt("12"))],[(Expr_TApply("add_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse4__5"));(Expr_LitBits("000000001"))]));(Expr_LitInt("12"))]));(Expr_LitBits("000000001000"))]));(Expr_LitInt("13"))]));(Expr_LitBits("0000010000000"))]))]))
  Stmt_Assign(LExpr_Var("result__4"),Expr_TApply("append_bits.0",[(Expr_LitInt("32"));(Expr_LitInt("32"))],[(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("32"),Expr_LitInt("32")))]));(Expr_TApply("append_bits.0",[(Expr_LitInt("8"));(Expr_LitInt("24"))],[(Expr_Slices(Expr_TApply("lsr_bits.0",[(Expr_LitInt("128"));(Expr_LitInt("12"))],[(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")));(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("11"));(Expr_LitInt("12"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("11"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("11"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("24"),Expr_LitInt("8")))]));(Expr_LitInt("11"))]));(Expr_LitBits("00000001000"))]));(Expr_LitInt("12"))]))]),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]));(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("24")))]))]))]))
  ],[],[])
  Stmt_If(Expr_TApply("slt_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse3__5"));(Expr_LitBits("000010000"))]),[
  Stmt_Assert(Expr_TApply("and_bool.0",[],[(Expr_TApply("sle_bits.0",[(Expr_LitInt("9"))],[(Expr_LitBits("000000000"));(Expr_Var("Cse3__5"))]));(Expr_TApply("sle_bits.0",[(Expr_LitInt("13"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("12"));(Expr_LitInt("13"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("12"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("9"));(Expr_LitInt("12"))],[(Expr_TApply("add_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse3__5"));(Expr_LitBits("000000001"))]));(Expr_LitInt("12"))]));(Expr_LitBits("000000001000"))]));(Expr_LitInt("13"))]));(Expr_LitBits("0000010000000"))]))]))
  Stmt_Assign(LExpr_Var("result__4"),Expr_TApply("append_bits.0",[(Expr_LitInt("24"));(Expr_LitInt("40"))],[(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("40"),Expr_LitInt("24")))]));(Expr_TApply("append_bits.0",[(Expr_LitInt("8"));(Expr_LitInt("32"))],[(Expr_Slices(Expr_TApply("lsr_bits.0",[(Expr_LitInt("128"));(Expr_LitInt("12"))],[(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")));(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("11"));(Expr_LitInt("12"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("11"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("11"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("32"),Expr_LitInt("8")))]));(Expr_LitInt("11"))]));(Expr_LitBits("00000001000"))]));(Expr_LitInt("12"))]))]),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]));(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("32")))]))]))]))
  ],[],[])
  Stmt_If(Expr_TApply("slt_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse2__5"));(Expr_LitBits("000010000"))]),[
  Stmt_Assert(Expr_TApply("and_bool.0",[],[(Expr_TApply("sle_bits.0",[(Expr_LitInt("9"))],[(Expr_LitBits("000000000"));(Expr_Var("Cse2__5"))]));(Expr_TApply("sle_bits.0",[(Expr_LitInt("13"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("12"));(Expr_LitInt("13"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("12"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("9"));(Expr_LitInt("12"))],[(Expr_TApply("add_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse2__5"));(Expr_LitBits("000000001"))]));(Expr_LitInt("12"))]));(Expr_LitBits("000000001000"))]));(Expr_LitInt("13"))]));(Expr_LitBits("0000010000000"))]))]))
  Stmt_Assign(LExpr_Var("result__4"),Expr_TApply("append_bits.0",[(Expr_LitInt("16"));(Expr_LitInt("48"))],[(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("48"),Expr_LitInt("16")))]));(Expr_TApply("append_bits.0",[(Expr_LitInt("8"));(Expr_LitInt("40"))],[(Expr_Slices(Expr_TApply("lsr_bits.0",[(Expr_LitInt("128"));(Expr_LitInt("12"))],[(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")));(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("11"));(Expr_LitInt("12"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("11"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("11"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("40"),Expr_LitInt("8")))]));(Expr_LitInt("11"))]));(Expr_LitBits("00000001000"))]));(Expr_LitInt("12"))]))]),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]));(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("40")))]))]))]))
  ],[],[])
  Stmt_If(Expr_TApply("slt_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse1__5"));(Expr_LitBits("000010000"))]),[
  Stmt_Assert(Expr_TApply("and_bool.0",[],[(Expr_TApply("sle_bits.0",[(Expr_LitInt("9"))],[(Expr_LitBits("000000000"));(Expr_Var("Cse1__5"))]));(Expr_TApply("sle_bits.0",[(Expr_LitInt("13"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("12"));(Expr_LitInt("13"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("12"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("9"));(Expr_LitInt("12"))],[(Expr_TApply("add_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse1__5"));(Expr_LitBits("000000001"))]));(Expr_LitInt("12"))]));(Expr_LitBits("000000001000"))]));(Expr_LitInt("13"))]));(Expr_LitBits("0000010000000"))]))]))
  Stmt_Assign(LExpr_Var("result__4"),Expr_TApply("append_bits.0",[(Expr_LitInt("8"));(Expr_LitInt("56"))],[(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("56"),Expr_LitInt("8")))]));(Expr_TApply("append_bits.0",[(Expr_LitInt("8"));(Expr_LitInt("48"))],[(Expr_Slices(Expr_TApply("lsr_bits.0",[(Expr_LitInt("128"));(Expr_LitInt("12"))],[(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")));(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("11"));(Expr_LitInt("12"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("11"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("11"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("48"),Expr_LitInt("8")))]));(Expr_LitInt("11"))]));(Expr_LitBits("00000001000"))]));(Expr_LitInt("12"))]))]),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]));(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("48")))]))]))]))
  ],[],[])
  Stmt_If(Expr_TApply("slt_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse0__5"));(Expr_LitBits("000010000"))]),[
  Stmt_Assert(Expr_TApply("and_bool.0",[],[(Expr_TApply("sle_bits.0",[(Expr_LitInt("9"))],[(Expr_LitBits("000000000"));(Expr_Var("Cse0__5"))]));(Expr_TApply("sle_bits.0",[(Expr_LitInt("13"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("12"));(Expr_LitInt("13"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("12"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("9"));(Expr_LitInt("12"))],[(Expr_TApply("add_bits.0",[(Expr_LitInt("9"))],[(Expr_Var("Cse0__5"));(Expr_LitBits("000000001"))]));(Expr_LitInt("12"))]));(Expr_LitBits("000000001000"))]));(Expr_LitInt("13"))]));(Expr_LitBits("0000010000000"))]))]))
  Stmt_Assign(LExpr_Var("result__4"),Expr_TApply("append_bits.0",[(Expr_LitInt("8"));(Expr_LitInt("56"))],[(Expr_Slices(Expr_TApply("lsr_bits.0",[(Expr_LitInt("128"));(Expr_LitInt("12"))],[(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")));(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("11"));(Expr_LitInt("12"))],[(Expr_TApply("mul_bits.0",[(Expr_LitInt("11"))],[(Expr_TApply("ZeroExtend.0",[(Expr_LitInt("8"));(Expr_LitInt("11"))],[(Expr_Slices(Expr_Array(Expr_Var("_Z"),Expr_LitInt("0")),[(Slice_LoWd(Expr_LitInt("56"),Expr_LitInt("8")))]));(Expr_LitInt("11"))]));(Expr_LitBits("00000001000"))]));(Expr_LitInt("12"))]))]),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("8")))]));(Expr_Slices(Expr_Var("result__4"),[(Slice_LoWd(Expr_LitInt("0"),Expr_LitInt("56")))]))]))
  ],[],[])
  Stmt_Assign(LExpr_Array(LExpr_Var("_Z"),Expr_LitInt("0")),Expr_TApply("ZeroExtend.0",[(Expr_LitInt("64"));(Expr_LitInt("128"))],[(Expr_Var("result__4"));(Expr_LitInt("128"))]))

