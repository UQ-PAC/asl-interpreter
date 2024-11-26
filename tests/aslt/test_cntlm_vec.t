
  $ echo ':set +dis:vectors' > commands
  $ for op in $(grep '^0x' ./cntlm-vec-ops.txt); do printf '%s\n' "\"$op\"" ":sem A64 $op"; done >> commands

  $ asli < commands > stmts

  $ cat stmts
  "0x0e011800"
  Decoding instruction A64 e011800
  constant bits ( 128 ) Exp8__5 = __array _Z [ 0 ] ;
  constant bits ( 128 ) Exp10__5 = __array _Z [ 1 ] ;
  bits ( 64 ) result__4 ;
  result__4 = select_vec.0 {{ 16,8,8 }} ( append_bits.0 {{ 64,64 }} ( Exp10__5 [ 0 +: 64 ],Exp8__5 [ 0 +: 64 ] ),'0000000000000000000000000000111000000000000000000000000000001100000000000000000000000000000010100000000000000000000000000000100000000000000000000000000000000110000000000000000000000000000001000000000000000000000000000000001000000000000000000000000000000000' ) ;
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x0e040ea8"
  Decoding instruction A64 e040ea8
  constant bits ( 64 ) Exp6__5 = __array _R [ 21 ] ;
  bits ( 64 ) result__4 ;
  result__4 = replicate_bits.0 {{ 32,2 }} ( Exp6__5 [ 0 +: 32 ],2 ) ;
  __array _Z [ 8 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x0e211c00"
  Decoding instruction A64 e211c00
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( and_bits.0 {{ 64 }} ( __array _Z [ 0 ] [ 0 +: 64 ],__array _Z [ 1 ] [ 0 +: 64 ] ),128 ) ;
  "0x0ea00800"
  Decoding instruction A64 ea00800
  constant bits ( 128 ) Exp8__5 = __array _Z [ 0 ] ;
  bits ( 64 ) result__4 ;
  result__4 = select_vec.0 {{ 2,2,32 }} ( Exp8__5 [ 0 +: 64 ],'0000000000000000000000000000000000000000000000000000000000000001' ) ;
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x0ea00801"
  Decoding instruction A64 ea00801
  constant bits ( 128 ) Exp8__5 = __array _Z [ 0 ] ;
  bits ( 64 ) result__4 ;
  result__4 = select_vec.0 {{ 2,2,32 }} ( Exp8__5 [ 0 +: 64 ],'0000000000000000000000000000000000000000000000000000000000000001' ) ;
  __array _Z [ 1 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x0ea03020"
  Decoding instruction A64 ea03020
  constant bits ( 128 ) Exp8__5 = __array _Z [ 1 ] ;
  constant bits ( 128 ) Exp11__6 = __array _Z [ 0 ] ;
  bits ( 128 ) result__4 ;
  result__4 = sub_vec.0 {{ 2,64 }} ( trunc_vec.0 {{ 2,128,64 }} ( scast_vec.0 {{ 2,64,128 }} ( Exp8__5,128,2 ),64,2 ),trunc_vec.0 {{ 2,128,64 }} ( scast_vec.0 {{ 2,32,128 }} ( Exp11__6 [ 0 +: 64 ],128,2 ),64,2 ),2 ) ;
  __array _Z [ 0 ] = result__4 ;
  "0x0ea18508"
  Decoding instruction A64 ea18508
  constant bits ( 128 ) Exp7__5 = __array _Z [ 8 ] ;
  constant bits ( 128 ) Exp9__5 = __array _Z [ 1 ] ;
  bits ( 64 ) result__4 ;
  result__4 = add_vec.0 {{ 2,32 }} ( Exp7__5 [ 0 +: 64 ],Exp9__5 [ 0 +: 64 ],2 ) ;
  __array _Z [ 8 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x0ea48400"
  Decoding instruction A64 ea48400
  constant bits ( 128 ) Exp7__5 = __array _Z [ 0 ] ;
  constant bits ( 128 ) Exp9__5 = __array _Z [ 4 ] ;
  bits ( 64 ) result__4 ;
  result__4 = add_vec.0 {{ 2,32 }} ( Exp7__5 [ 0 +: 64 ],Exp9__5 [ 0 +: 64 ],2 ) ;
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x0f000420"
  Decoding instruction A64 f000420
  __array _Z [ 0 ] = '00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001' ;
  "0x0f000428"
  Decoding instruction A64 f000428
  __array _Z [ 8 ] = '00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001' ;
  "0x0f07e7c1"
  Decoding instruction A64 f07e7c1
  __array _Z [ 1 ] = '00000000000000000000000000000000000000000000000000000000000000001111111011111110111111101111111011111110111111101111111011111110' ;
  "0x0f20a402"
  Decoding instruction A64 f20a402
  constant bits ( 128 ) Exp9__6 = __array _Z [ 0 ] ;
  bits ( 128 ) result__4 ;
  result__4 = scast_vec.0 {{ 2,32,64 }} ( Exp9__6 [ 0 +: 64 ],64,2 ) ;
  __array _Z [ 2 ] = result__4 ;
  "0x0f20a423"
  Decoding instruction A64 f20a423
  constant bits ( 128 ) Exp9__6 = __array _Z [ 1 ] ;
  bits ( 128 ) result__4 ;
  result__4 = scast_vec.0 {{ 2,32,64 }} ( Exp9__6 [ 0 +: 64 ],64,2 ) ;
  __array _Z [ 3 ] = result__4 ;
  "0x2e200800"
  Decoding instruction A64 2e200800
  constant bits ( 128 ) Exp8__5 = __array _Z [ 0 ] ;
  bits ( 64 ) result__4 ;
  result__4 = select_vec.0 {{ 8,8,8 }} ( Exp8__5 [ 0 +: 64 ],'0000000000000000000000000000010000000000000000000000000000000101000000000000000000000000000001100000000000000000000000000000011100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000001000000000000000000000000000000011' ) ;
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x2e200820"
  Decoding instruction A64 2e200820
  constant bits ( 128 ) Exp8__5 = __array _Z [ 1 ] ;
  bits ( 64 ) result__4 ;
  result__4 = select_vec.0 {{ 8,8,8 }} ( Exp8__5 [ 0 +: 64 ],'0000000000000000000000000000010000000000000000000000000000000101000000000000000000000000000001100000000000000000000000000000011100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000001000000000000000000000000000000011' ) ;
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x2e211c00"
  Decoding instruction A64 2e211c00
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( eor_bits.0 {{ 64 }} ( __array _Z [ 1 ] [ 0 +: 64 ],eor_bits.0 {{ 64 }} ( '0000000000000000000000000000000000000000000000000000000000000000',__array _Z [ 0 ] [ 0 +: 64 ] ) ),128 ) ;
  "0x2f000400"
  Decoding instruction A64 2f000400
  __array _Z [ 0 ] = '00000000000000000000000000000000000000000000000000000000000000001111111111111111111111111111111111111111111111111111111111111111' ;
  "0x2f03d7e0"
  Decoding instruction A64 2f03d7e0
  __array _Z [ 0 ] = '00000000000000000000000000000000000000000000000000000000000000001111111110000000000000000000000011111111100000000000000000000000' ;
  "0x2f044400"
  Decoding instruction A64 2f044400
  __array _Z [ 0 ] = '00000000000000000000000000000000000000000000000000000000000000001111111101111111111111111111111111111111011111111111111111111111' ;
  "0x2f280400"
  Decoding instruction A64 2f280400
  constant bits ( 128 ) Exp7__5 = __array _Z [ 0 ] ;
  bits ( 64 ) result__4 ;
  result__4 = add_vec.0 {{ 2,32 }} ( '0000000000000000000000000000000000000000000000000000000000000000',lsr_vec.0 {{ 2,32 }} ( Exp7__5 [ 0 +: 64 ],'0000000000000000000000000001100000000000000000000000000000011000',2 ),2 ) ;
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x2f280424"
  Decoding instruction A64 2f280424
  constant bits ( 128 ) Exp7__5 = __array _Z [ 1 ] ;
  bits ( 64 ) result__4 ;
  result__4 = add_vec.0 {{ 2,32 }} ( '0000000000000000000000000000000000000000000000000000000000000000',lsr_vec.0 {{ 2,32 }} ( Exp7__5 [ 0 +: 64 ],'0000000000000000000000000001100000000000000000000000000000011000',2 ),2 ) ;
  __array _Z [ 4 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x2f300423"
  Decoding instruction A64 2f300423
  constant bits ( 128 ) Exp7__5 = __array _Z [ 1 ] ;
  bits ( 64 ) result__4 ;
  result__4 = add_vec.0 {{ 2,32 }} ( '0000000000000000000000000000000000000000000000000000000000000000',lsr_vec.0 {{ 2,32 }} ( Exp7__5 [ 0 +: 64 ],'0000000000000000000000000001000000000000000000000000000000010000',2 ),2 ) ;
  __array _Z [ 3 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x2f300446"
  Decoding instruction A64 2f300446
  constant bits ( 128 ) Exp7__5 = __array _Z [ 2 ] ;
  bits ( 64 ) result__4 ;
  result__4 = add_vec.0 {{ 2,32 }} ( '0000000000000000000000000000000000000000000000000000000000000000',lsr_vec.0 {{ 2,32 }} ( Exp7__5 [ 0 +: 64 ],'0000000000000000000000000001000000000000000000000000000000010000',2 ),2 ) ;
  __array _Z [ 6 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x2f380422"
  Decoding instruction A64 2f380422
  constant bits ( 128 ) Exp7__5 = __array _Z [ 1 ] ;
  bits ( 64 ) result__4 ;
  result__4 = add_vec.0 {{ 2,32 }} ( '0000000000000000000000000000000000000000000000000000000000000000',lsr_vec.0 {{ 2,32 }} ( Exp7__5 [ 0 +: 64 ],'0000000000000000000000000000100000000000000000000000000000001000',2 ),2 ) ;
  __array _Z [ 2 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x2f380445"
  Decoding instruction A64 2f380445
  constant bits ( 128 ) Exp7__5 = __array _Z [ 2 ] ;
  bits ( 64 ) result__4 ;
  result__4 = add_vec.0 {{ 2,32 }} ( '0000000000000000000000000000000000000000000000000000000000000000',lsr_vec.0 {{ 2,32 }} ( Exp7__5 [ 0 +: 64 ],'0000000000000000000000000000100000000000000000000000000000001000',2 ),2 ) ;
  __array _Z [ 5 ] = ZeroExtend.0 {{ 64,128 }} ( result__4,128 ) ;
  "0x4cdf0860"
  Decoding instruction A64 4cdf0860
  __array _Z [ 0 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 0 ],0,32,Mem.read.0 {{ 4 }} ( __array _R [ 3 ],4,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 1 ],0,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000000100' ),4,1 ) ) ;
  __array _Z [ 2 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 2 ],0,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000001000' ),4,1 ) ) ;
  __array _Z [ 3 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 3 ],0,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000001100' ),4,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 0 ],1,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000010000' ),4,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 1 ],1,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000010100' ),4,1 ) ) ;
  __array _Z [ 2 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 2 ],1,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000011000' ),4,1 ) ) ;
  __array _Z [ 3 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 3 ],1,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000011100' ),4,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 0 ],2,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000100000' ),4,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 1 ],2,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000100100' ),4,1 ) ) ;
  __array _Z [ 2 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 2 ],2,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000101000' ),4,1 ) ) ;
  __array _Z [ 3 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 3 ],2,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000101100' ),4,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 0 ],3,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000110000' ),4,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 1 ],3,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000110100' ),4,1 ) ) ;
  __array _Z [ 2 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 2 ],3,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000111000' ),4,1 ) ) ;
  __array _Z [ 3 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 3 ],3,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000000111100' ),4,1 ) ) ;
  __array _R [ 3 ] = add_bits.0 {{ 64 }} ( __array _R [ 3 ],'0000000000000000000000000000000000000000000000000000000001000000' ) ;
  "0x4cdf8000"
  Decoding instruction A64 4cdf8000
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],0,8,Mem.read.0 {{ 1 }} ( __array _R [ 0 ],1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],0,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000000001' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],1,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000000010' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],1,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000000011' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],2,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000000100' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],2,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000000101' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],3,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000000110' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],3,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000000111' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],4,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000001000' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],4,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000001001' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],5,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000001010' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],5,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000001011' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],6,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000001100' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],6,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000001101' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],7,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000001110' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],7,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000001111' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],8,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000010000' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],8,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000010001' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],9,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000010010' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],9,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000010011' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],10,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000010100' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],10,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000010101' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],11,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000010110' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],11,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000010111' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],12,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000011000' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],12,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000011001' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],13,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000011010' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],13,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000011011' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],14,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000011100' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],14,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000011101' ),1,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],15,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000011110' ),1,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 1 ],15,8,Mem.read.0 {{ 1 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000011111' ),1,1 ) ) ;
  __array _R [ 0 ] = add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000100000' ) ;
  "0x4cdf8800"
  Decoding instruction A64 4cdf8800
  __array _Z [ 0 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 0 ],0,32,Mem.read.0 {{ 4 }} ( __array _R [ 0 ],4,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 1 ],0,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000000100' ),4,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 0 ],1,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000001000' ),4,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 1 ],1,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000001100' ),4,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 0 ],2,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000010000' ),4,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 1 ],2,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000010100' ),4,1 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 0 ],3,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000011000' ),4,1 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,32 }} ( __array _Z [ 1 ],3,32,Mem.read.0 {{ 4 }} ( add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000011100' ),4,1 ) ) ;
  __array _R [ 0 ] = add_bits.0 {{ 64 }} ( __array _R [ 0 ],'0000000000000000000000000000000000000000000000000000000000100000' ) ;
  "0x4d408660"
  Decoding instruction A64 4d408660
  __array _Z [ 0 ] = Elem.set.0 {{ 128,64 }} ( __array _Z [ 0 ],1,64,Mem.read.0 {{ 8 }} ( __array _R [ 19 ],8,1 ) ) ;
  "0x4e031c40"
  Decoding instruction A64 4e031c40
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],1,8,__array _R [ 2 ] [ 0 +: 8 ] ) ;
  "0x4e040ea0"
  Decoding instruction A64 4e040ea0
  constant bits ( 64 ) Exp6__5 = __array _R [ 21 ] ;
  bits ( 128 ) result__4 ;
  result__4 = replicate_bits.0 {{ 32,4 }} ( Exp6__5 [ 0 +: 32 ],4 ) ;
  __array _Z [ 0 ] = result__4 ;
  "0x4e051ce0"
  Decoding instruction A64 4e051ce0
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],2,8,__array _R [ 7 ] [ 0 +: 8 ] ) ;
  "0x4e052042"
  Decoding instruction A64 4e052042
  bits ( 128 ) result__4 ;
  constant bits ( 256 ) Cse0__5 = append_bits.0 {{ 128,128 }} ( __array _Z [ 3 ],__array _Z [ 2 ] ) ;
  result__4 = '00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000' ;
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],0,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( '00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000',0,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],0,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],1,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,1,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],1,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],2,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,2,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],2,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],3,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,3,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],3,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],4,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,4,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],4,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],5,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,5,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],5,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],6,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,6,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],6,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],7,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,7,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],7,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],8,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,8,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],8,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],9,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,9,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],9,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],10,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,10,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],10,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],11,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,11,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],11,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],12,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,12,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],12,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],13,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,13,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],13,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],14,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,14,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],14,8 ) ),8 ) ) ;
  }
  if slt_bits.0 {{ 16 }} ( ZeroExtend.0 {{ 8,16 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],15,8 ),16 ),'0000000000100000' ) then {
  result__4 = Elem.set.0 {{ 128,8 }} ( result__4,15,8,Elem.read.0 {{ 256,8 }} ( Cse0__5,cvt_bits_uint.0 {{ 8 }} ( Elem.read.0 {{ 128,8 }} ( __array _Z [ 5 ],15,8 ) ),8 ) ) ;
  }
  __array _Z [ 2 ] = result__4 ;
  "0x4e071c00"
  Decoding instruction A64 4e071c00
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],3,8,__array _R [ 0 ] [ 0 +: 8 ] ) ;
  "0x4e071cc0"
  Decoding instruction A64 4e071cc0
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],3,8,__array _R [ 6 ] [ 0 +: 8 ] ) ;
  "0x4e080401"
  Decoding instruction A64 4e080401
  constant bits ( 128 ) Exp7__5 = __array _Z [ 0 ] ;
  bits ( 128 ) result__4 ;
  result__4 = replicate_bits.0 {{ 64,2 }} ( Elem.read.0 {{ 64,64 }} ( Exp7__5 [ 0 +: 64 ],0,64 ),2 ) ;
  __array _Z [ 1 ] = result__4 ;
  "0x4e091ca0"
  Decoding instruction A64 4e091ca0
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],4,8,__array _R [ 5 ] [ 0 +: 8 ] ) ;
  "0x4e0b1c80"
  Decoding instruction A64 4e0b1c80
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],5,8,__array _R [ 4 ] [ 0 +: 8 ] ) ;
  "0x4e0d1c40"
  Decoding instruction A64 4e0d1c40
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],6,8,__array _R [ 2 ] [ 0 +: 8 ] ) ;
  "0x4e0f1c60"
  Decoding instruction A64 4e0f1c60
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],7,8,__array _R [ 3 ] [ 0 +: 8 ] ) ;
  "0x4e211ca1"
  Decoding instruction A64 4e211ca1
  __array _Z [ 1 ] = and_bits.0 {{ 128 }} ( __array _Z [ 5 ],__array _Z [ 1 ] ) ;
  "0x4e61d800"
  Decoding instruction A64 4e61d800
  bits ( 128 ) result__4 ;
  bits ( 4 ) FPDecodeRounding9__6 ;
  FPDecodeRounding9__6 = ZeroExtend.0 {{ 2,4 }} ( FPCR [ 22 +: 2 ],4 ) ;
  constant bits ( 64 ) Exp12__5 = FixedToFP.0 {{ 64,64 }} ( Elem.read.0 {{ 128,64 }} ( __array _Z [ 0 ],0,64 ),0,FALSE,FPCR,cvt_bits_uint.0 {{ 4 }} ( FPDecodeRounding9__6 ) ) ;
  constant bits ( 64 ) Exp13__5 = FixedToFP.0 {{ 64,64 }} ( Elem.read.0 {{ 128,64 }} ( __array _Z [ 0 ],1,64 ),0,FALSE,FPCR,cvt_bits_uint.0 {{ 4 }} ( FPDecodeRounding9__6 ) ) ;
  __array _Z [ 0 ] = Elem.set.0 {{ 128,64 }} ( Elem.set.0 {{ 128,64 }} ( result__4,0,64,Exp12__5 ),1,64,Exp13__5 ) ;
  "0x4e61d821"
  Decoding instruction A64 4e61d821
  bits ( 128 ) result__4 ;
  bits ( 4 ) FPDecodeRounding9__6 ;
  FPDecodeRounding9__6 = ZeroExtend.0 {{ 2,4 }} ( FPCR [ 22 +: 2 ],4 ) ;
  constant bits ( 64 ) Exp12__5 = FixedToFP.0 {{ 64,64 }} ( Elem.read.0 {{ 128,64 }} ( __array _Z [ 1 ],0,64 ),0,FALSE,FPCR,cvt_bits_uint.0 {{ 4 }} ( FPDecodeRounding9__6 ) ) ;
  constant bits ( 64 ) Exp13__5 = FixedToFP.0 {{ 64,64 }} ( Elem.read.0 {{ 128,64 }} ( __array _Z [ 1 ],1,64 ),0,FALSE,FPCR,cvt_bits_uint.0 {{ 4 }} ( FPDecodeRounding9__6 ) ) ;
  __array _Z [ 1 ] = Elem.set.0 {{ 128,64 }} ( Elem.set.0 {{ 128,64 }} ( result__4,0,64,Exp12__5 ),1,64,Exp13__5 ) ;
  "0x4e61d842"
  Decoding instruction A64 4e61d842
  bits ( 128 ) result__4 ;
  bits ( 4 ) FPDecodeRounding9__6 ;
  FPDecodeRounding9__6 = ZeroExtend.0 {{ 2,4 }} ( FPCR [ 22 +: 2 ],4 ) ;
  constant bits ( 64 ) Exp12__5 = FixedToFP.0 {{ 64,64 }} ( Elem.read.0 {{ 128,64 }} ( __array _Z [ 2 ],0,64 ),0,FALSE,FPCR,cvt_bits_uint.0 {{ 4 }} ( FPDecodeRounding9__6 ) ) ;
  constant bits ( 64 ) Exp13__5 = FixedToFP.0 {{ 64,64 }} ( Elem.read.0 {{ 128,64 }} ( __array _Z [ 2 ],1,64 ),0,FALSE,FPCR,cvt_bits_uint.0 {{ 4 }} ( FPDecodeRounding9__6 ) ) ;
  __array _Z [ 2 ] = Elem.set.0 {{ 128,64 }} ( Elem.set.0 {{ 128,64 }} ( result__4,0,64,Exp12__5 ),1,64,Exp13__5 ) ;
  "0x4e61d863"
  Decoding instruction A64 4e61d863
  bits ( 128 ) result__4 ;
  bits ( 4 ) FPDecodeRounding9__6 ;
  FPDecodeRounding9__6 = ZeroExtend.0 {{ 2,4 }} ( FPCR [ 22 +: 2 ],4 ) ;
  constant bits ( 64 ) Exp12__5 = FixedToFP.0 {{ 64,64 }} ( Elem.read.0 {{ 128,64 }} ( __array _Z [ 3 ],0,64 ),0,FALSE,FPCR,cvt_bits_uint.0 {{ 4 }} ( FPDecodeRounding9__6 ) ) ;
  constant bits ( 64 ) Exp13__5 = FixedToFP.0 {{ 64,64 }} ( Elem.read.0 {{ 128,64 }} ( __array _Z [ 3 ],1,64 ),0,FALSE,FPCR,cvt_bits_uint.0 {{ 4 }} ( FPDecodeRounding9__6 ) ) ;
  __array _Z [ 3 ] = Elem.set.0 {{ 128,64 }} ( Elem.set.0 {{ 128,64 }} ( result__4,0,64,Exp12__5 ),1,64,Exp13__5 ) ;
  "0x4ea11c23"
  Decoding instruction A64 4ea11c23
  __array _Z [ 3 ] = or_bits.0 {{ 128 }} ( __array _Z [ 1 ],__array _Z [ 1 ] ) ;
  "0x4ea28400"
  Decoding instruction A64 4ea28400
  constant bits ( 128 ) Exp7__5 = __array _Z [ 0 ] ;
  constant bits ( 128 ) Exp9__5 = __array _Z [ 2 ] ;
  bits ( 128 ) result__4 ;
  result__4 = add_vec.0 {{ 4,32 }} ( Exp7__5,Exp9__5,4 ) ;
  __array _Z [ 0 ] = result__4 ;
  "0x4ee08484"
  Decoding instruction A64 4ee08484
  constant bits ( 128 ) Exp7__5 = __array _Z [ 4 ] ;
  constant bits ( 128 ) Exp9__5 = __array _Z [ 0 ] ;
  bits ( 128 ) result__4 ;
  result__4 = add_vec.0 {{ 2,64 }} ( Exp7__5,Exp9__5,2 ) ;
  __array _Z [ 4 ] = result__4 ;
  "0x4ee08c00"
  Decoding instruction A64 4ee08c00
  constant bits ( 128 ) Exp7__5 = __array _Z [ 0 ] ;
  constant bits ( 128 ) Exp9__5 = __array _Z [ 0 ] ;
  bits ( 128 ) result__4 ;
  result__4 = ite_vec.0 {{ 2,64 }} ( not_bits.0 {{ 2 }} ( eq_vec.0 {{ 2,64 }} ( and_bits.0 {{ 128 }} ( Exp7__5,Exp9__5 ),'00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000',2 ) ),'11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111','00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000',2 ) ;
  __array _Z [ 0 ] = result__4 ;
  "0x4ee28420"
  Decoding instruction A64 4ee28420
  constant bits ( 128 ) Exp7__5 = __array _Z [ 1 ] ;
  constant bits ( 128 ) Exp9__5 = __array _Z [ 2 ] ;
  bits ( 128 ) result__4 ;
  result__4 = add_vec.0 {{ 2,64 }} ( Exp7__5,Exp9__5,2 ) ;
  __array _Z [ 0 ] = result__4 ;
  "0x4f000400"
  Decoding instruction A64 4f000400
  __array _Z [ 0 ] = '00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000' ;
  "0x4f000401"
  Decoding instruction A64 4f000401
  __array _Z [ 1 ] = '00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000' ;
  "0x4f000404"
  Decoding instruction A64 4f000404
  __array _Z [ 4 ] = '00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000' ;
  "0x4f0004e6"
  Decoding instruction A64 4f0004e6
  __array _Z [ 6 ] = '00000000000000000000000000000111000000000000000000000000000001110000000000000000000000000000011100000000000000000000000000000111' ;
  "0x4f01e6c0"
  Decoding instruction A64 4f01e6c0
  __array _Z [ 0 ] = '00110110001101100011011000110110001101100011011000110110001101100011011000110110001101100011011000110110001101100011011000110110' ;
  "0x4f02e780"
  Decoding instruction A64 4f02e780
  __array _Z [ 0 ] = '01011100010111000101110001011100010111000101110001011100010111000101110001011100010111000101110001011100010111000101110001011100' ;
  "0x4f20a400"
  Decoding instruction A64 4f20a400
  constant bits ( 128 ) Exp9__6 = __array _Z [ 0 ] ;
  bits ( 128 ) result__4 ;
  result__4 = scast_vec.0 {{ 2,32,64 }} ( Exp9__6 [ 64 +: 64 ],64,2 ) ;
  __array _Z [ 0 ] = result__4 ;
  "0x4f20a401"
  Decoding instruction A64 4f20a401
  constant bits ( 128 ) Exp9__6 = __array _Z [ 0 ] ;
  bits ( 128 ) result__4 ;
  result__4 = scast_vec.0 {{ 2,32,64 }} ( Exp9__6 [ 64 +: 64 ],64,2 ) ;
  __array _Z [ 1 ] = result__4 ;
  "0x4f20a421"
  Decoding instruction A64 4f20a421
  constant bits ( 128 ) Exp9__6 = __array _Z [ 1 ] ;
  bits ( 128 ) result__4 ;
  result__4 = scast_vec.0 {{ 2,32,64 }} ( Exp9__6 [ 64 +: 64 ],64,2 ) ;
  __array _Z [ 1 ] = result__4 ;
  "0x5ef1b820"
  Decoding instruction A64 5ef1b820
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( add_bits.0 {{ 64 }} ( __array _Z [ 1 ] [ 0 +: 64 ],__array _Z [ 1 ] [ 64 +: 64 ] ),128 ) ;
  "0x5ef1b880"
  Decoding instruction A64 5ef1b880
  __array _Z [ 0 ] = ZeroExtend.0 {{ 64,128 }} ( add_bits.0 {{ 64 }} ( __array _Z [ 4 ] [ 0 +: 64 ],__array _Z [ 4 ] [ 64 +: 64 ] ),128 ) ;
  "0x6e030460"
  Decoding instruction A64 6e030460
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],1,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 3 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e0304c0"
  Decoding instruction A64 6e0304c0
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],1,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 6 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e050440"
  Decoding instruction A64 6e050440
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],2,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 2 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e0504a0"
  Decoding instruction A64 6e0504a0
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],2,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 5 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e070420"
  Decoding instruction A64 6e070420
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],3,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 1 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e090480"
  Decoding instruction A64 6e090480
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],4,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 4 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e090680"
  Decoding instruction A64 6e090680
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],4,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 20 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e0b0460"
  Decoding instruction A64 6e0b0460
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],5,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 3 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e0b0660"
  Decoding instruction A64 6e0b0660
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],5,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 19 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e0d0440"
  Decoding instruction A64 6e0d0440
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],6,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 2 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e0d0640"
  Decoding instruction A64 6e0d0640
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],6,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 18 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e0f0420"
  Decoding instruction A64 6e0f0420
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],7,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 1 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e0f0620"
  Decoding instruction A64 6e0f0620
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],7,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 17 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e110600"
  Decoding instruction A64 6e110600
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],8,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 16 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e1304e0"
  Decoding instruction A64 6e1304e0
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],9,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 7 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e1504c0"
  Decoding instruction A64 6e1504c0
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],10,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 6 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e1704a0"
  Decoding instruction A64 6e1704a0
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],11,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 5 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e190480"
  Decoding instruction A64 6e190480
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],12,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 4 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e1b0460"
  Decoding instruction A64 6e1b0460
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],13,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 3 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e1d0440"
  Decoding instruction A64 6e1d0440
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],14,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 2 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e1f0420"
  Decoding instruction A64 6e1f0420
  __array _Z [ 0 ] = Elem.set.0 {{ 128,8 }} ( __array _Z [ 0 ],15,8,Elem.read.0 {{ 64,8 }} ( __array _Z [ 1 ] [ 0 +: 64 ],0,8 ) ) ;
  "0x6e200800"
  Decoding instruction A64 6e200800
  constant bits ( 128 ) Exp8__5 = __array _Z [ 0 ] ;
  bits ( 128 ) result__4 ;
  result__4 = select_vec.0 {{ 16,16,8 }} ( Exp8__5,'00000000000000000000000000001100000000000000000000000000000011010000000000000000000000000000111000000000000000000000000000001111000000000000000000000000000010000000000000000000000000000000100100000000000000000000000000001010000000000000000000000000000010110000000000000000000000000000010000000000000000000000000000000101000000000000000000000000000001100000000000000000000000000000011100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000001000000000000000000000000000000011' ) ;
  __array _Z [ 0 ] = result__4 ;
  "0x6e205800"
  Decoding instruction A64 6e205800
  constant bits ( 128 ) Exp4__5 = __array _Z [ 0 ] ;
  bits ( 128 ) result__4 ;
  result__4 = not_bits.0 {{ 128 }} ( Exp4__5 ) ;
  __array _Z [ 0 ] = result__4 ;
  "0x6e211c00"
  Decoding instruction A64 6e211c00
  __array _Z [ 0 ] = eor_bits.0 {{ 128 }} ( __array _Z [ 1 ],eor_bits.0 {{ 128 }} ( '00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000',__array _Z [ 0 ] ) ) ;
  "0x6ea68c00"
  Decoding instruction A64 6ea68c00
  constant bits ( 128 ) Exp7__5 = __array _Z [ 0 ] ;
  constant bits ( 128 ) Exp9__5 = __array _Z [ 6 ] ;
  bits ( 128 ) result__4 ;
  result__4 = ite_vec.0 {{ 4,32 }} ( eq_vec.0 {{ 4,32 }} ( Exp7__5,Exp9__5,4 ),'11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111','00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000',4 ) ;
  __array _Z [ 0 ] = result__4 ;
  "0x6ee08421"
  Decoding instruction A64 6ee08421
  constant bits ( 128 ) Exp7__5 = __array _Z [ 1 ] ;
  constant bits ( 128 ) Exp9__5 = __array _Z [ 0 ] ;
  bits ( 128 ) result__4 ;
  result__4 = sub_vec.0 {{ 2,64 }} ( Exp7__5,Exp9__5,2 ) ;
  __array _Z [ 1 ] = result__4 ;
  "0x6f000400"
  Decoding instruction A64 6f000400
  __array _Z [ 0 ] = '11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111' ;
