AtomicStart()
  return;

AtomicEnd()
  return;

bits(64) AArch64.BranchAddr(bits(64) vaddress)
    return vaddress;

AArch64.CheckFPAdvSIMDEnabled()
    return;

integer ImplementedSVEVectorLength(integer nbits)
    return 128;

boolean IsSVEEnabled(bits(2) el)
    return FALSE;

boolean HaveMTEExt()
    return FALSE;

boolean sle_bits(bits(N) x, bits(N) y)
    integer xn = SInt(x);
    integer yn = SInt(y);
    return xn <= yn;

boolean slt_bits(bits(N) x, bits(N) y)
    integer xn = SInt(x);
    integer yn = SInt(y);
    return xn < yn;

bits(N) neg_bits(bits(N) x)
    return (NOT x) + ZeroExtend('1', N);

bits(N) sdiv_bits(bits(N) x, bits(N) y)
    integer xn = SInt(x);
    integer yn = SInt(y);
    return RoundTowardsZero(Real(xn) / Real (yn))[N-1:0];

bits(N) lsl_bits(bits(N) x, bits(N) y)
    integer yn = UInt(y);
    return LSL(x, yn);

bits(N) lsr_bits(bits(N) x, bits(N) y)
    integer yn = UInt(y);
    return LSR(x, yn);

bits(N) asr_bits(bits(N) x, bits(N) y)
    integer yn = UInt(y);
    return ASR(x, yn);

bits(N) ror_bits(bits(N) x, bits(N) y)
    integer yn = UInt(y);
    return ROR(x, yn);

integer HighestSetBit(bits(N) x)
    assert 0 < N && N <= 64;
    if (63 < N && x[63] == '1') then
        return 63;
    elsif (62 < N && x[62] == '1') then
        return 62;
    elsif (61 < N && x[61] == '1') then
        return 61;
    elsif (60 < N && x[60] == '1') then
        return 60;
    elsif (59 < N && x[59] == '1') then
        return 59;
    elsif (58 < N && x[58] == '1') then
        return 58;
    elsif (57 < N && x[57] == '1') then
        return 57;
    elsif (56 < N && x[56] == '1') then
        return 56;
    elsif (55 < N && x[55] == '1') then
        return 55;
    elsif (54 < N && x[54] == '1') then
        return 54;
    elsif (53 < N && x[53] == '1') then
        return 53;
    elsif (52 < N && x[52] == '1') then
        return 52;
    elsif (51 < N && x[51] == '1') then
        return 51;
    elsif (50 < N && x[50] == '1') then
        return 50;
    elsif (49 < N && x[49] == '1') then
        return 49;
    elsif (48 < N && x[48] == '1') then
        return 48;
    elsif (47 < N && x[47] == '1') then
        return 47;
    elsif (46 < N && x[46] == '1') then
        return 46;
    elsif (45 < N && x[45] == '1') then
        return 45;
    elsif (44 < N && x[44] == '1') then
        return 44;
    elsif (43 < N && x[43] == '1') then
        return 43;
    elsif (42 < N && x[42] == '1') then
        return 42;
    elsif (41 < N && x[41] == '1') then
        return 41;
    elsif (40 < N && x[40] == '1') then
        return 40;
    elsif (39 < N && x[39] == '1') then
        return 39;
    elsif (38 < N && x[38] == '1') then
        return 38;
    elsif (37 < N && x[37] == '1') then
        return 37;
    elsif (36 < N && x[36] == '1') then
        return 36;
    elsif (35 < N && x[35] == '1') then
        return 35;
    elsif (34 < N && x[34] == '1') then
        return 34;
    elsif (33 < N && x[33] == '1') then
        return 33;
    elsif (32 < N && x[32] == '1') then
        return 32;
    elsif (31 < N && x[31] == '1') then
        return 31;
    elsif (30 < N && x[30] == '1') then
        return 30;
    elsif (29 < N && x[29] == '1') then
        return 29;
    elsif (28 < N && x[28] == '1') then
        return 28;
    elsif (27 < N && x[27] == '1') then
        return 27;
    elsif (26 < N && x[26] == '1') then
        return 26;
    elsif (25 < N && x[25] == '1') then
        return 25;
    elsif (24 < N && x[24] == '1') then
        return 24;
    elsif (23 < N && x[23] == '1') then
        return 23;
    elsif (22 < N && x[22] == '1') then
        return 22;
    elsif (21 < N && x[21] == '1') then
        return 21;
    elsif (20 < N && x[20] == '1') then
        return 20;
    elsif (19 < N && x[19] == '1') then
        return 19;
    elsif (18 < N && x[18] == '1') then
        return 18;
    elsif (17 < N && x[17] == '1') then
        return 17;
    elsif (16 < N && x[16] == '1') then
        return 16;
    elsif (15 < N && x[15] == '1') then
        return 15;
    elsif (14 < N && x[14] == '1') then
        return 14;
    elsif (13 < N && x[13] == '1') then
        return 13;
    elsif (12 < N && x[12] == '1') then
        return 12;
    elsif (11 < N && x[11] == '1') then
        return 11;
    elsif (10 < N && x[10] == '1') then
        return 10;
    elsif (9 < N && x[9] == '1') then
        return 9;
    elsif (8 < N && x[8] == '1') then
        return 8;
    elsif (7 < N && x[7] == '1') then
        return 7;
    elsif (6 < N && x[6] == '1') then
        return 6;
    elsif (5 < N && x[5] == '1') then
        return 5;
    elsif (4 < N && x[4] == '1') then
        return 4;
    elsif (3 < N && x[3] == '1') then
        return 3;
    elsif (2 < N && x[2] == '1') then
        return 2;
    elsif (1 < N && x[1] == '1') then
        return 1;
    elsif (0 < N && x[0] == '1') then
        return 0;
    else
        return -1;

boolean AArch64.CheckAlignment(bits(64) address, integer alignment, AccType acctype,
                               boolean iswrite)
    return TRUE;

CheckSPAlignment()
    return;

AArch64.SoftwareBreakpoint(bits(16) immediate)
    assert FALSE;

integer LowestSetBit(bits(N) x)
    assert 0 < N && N <= 64;
    if (0 < N && x[0] == '1') then
        return 0;
    elsif (1 < N && x[1] == '1') then
        return 1;
    elsif (2 < N && x[2] == '1') then
        return 2;
    elsif (3 < N && x[3] == '1') then
        return 3;
    elsif (4 < N && x[4] == '1') then
        return 4;
    elsif (5 < N && x[5] == '1') then
        return 5;
    elsif (6 < N && x[6] == '1') then
        return 6;
    elsif (7 < N && x[7] == '1') then
        return 7;
    elsif (8 < N && x[8] == '1') then
        return 8;
    elsif (9 < N && x[9] == '1') then
        return 9;
    elsif (10 < N && x[10] == '1') then
        return 10;
    elsif (11 < N && x[11] == '1') then
        return 11;
    elsif (12 < N && x[12] == '1') then
        return 12;
    elsif (13 < N && x[13] == '1') then
        return 13;
    elsif (14 < N && x[14] == '1') then
        return 14;
    elsif (15 < N && x[15] == '1') then
        return 15;
    elsif (16 < N && x[16] == '1') then
        return 16;
    elsif (17 < N && x[17] == '1') then
        return 17;
    elsif (18 < N && x[18] == '1') then
        return 18;
    elsif (19 < N && x[19] == '1') then
        return 19;
    elsif (20 < N && x[20] == '1') then
        return 20;
    elsif (21 < N && x[21] == '1') then
        return 21;
    elsif (22 < N && x[22] == '1') then
        return 22;
    elsif (23 < N && x[23] == '1') then
        return 23;
    elsif (24 < N && x[24] == '1') then
        return 24;
    elsif (25 < N && x[25] == '1') then
        return 25;
    elsif (26 < N && x[26] == '1') then
        return 26;
    elsif (27 < N && x[27] == '1') then
        return 27;
    elsif (28 < N && x[28] == '1') then
        return 28;
    elsif (29 < N && x[29] == '1') then
        return 29;
    elsif (30 < N && x[30] == '1') then
        return 30;
    elsif (31 < N && x[31] == '1') then
        return 31;
    elsif (32 < N && x[32] == '1') then
        return 32;
    elsif (33 < N && x[33] == '1') then
        return 33;
    elsif (34 < N && x[34] == '1') then
        return 34;
    elsif (35 < N && x[35] == '1') then
        return 35;
    elsif (36 < N && x[36] == '1') then
        return 36;
    elsif (37 < N && x[37] == '1') then
        return 37;
    elsif (38 < N && x[38] == '1') then
        return 38;
    elsif (39 < N && x[39] == '1') then
        return 39;
    elsif (40 < N && x[40] == '1') then
        return 40;
    elsif (41 < N && x[41] == '1') then
        return 41;
    elsif (42 < N && x[42] == '1') then
        return 42;
    elsif (43 < N && x[43] == '1') then
        return 43;
    elsif (44 < N && x[44] == '1') then
        return 44;
    elsif (45 < N && x[45] == '1') then
        return 45;
    elsif (46 < N && x[46] == '1') then
        return 46;
    elsif (47 < N && x[47] == '1') then
        return 47;
    elsif (48 < N && x[48] == '1') then
        return 48;
    elsif (49 < N && x[49] == '1') then
        return 49;
    elsif (50 < N && x[50] == '1') then
        return 50;
    elsif (51 < N && x[51] == '1') then
        return 51;
    elsif (52 < N && x[52] == '1') then
        return 52;
    elsif (53 < N && x[53] == '1') then
        return 53;
    elsif (54 < N && x[54] == '1') then
        return 54;
    elsif (55 < N && x[55] == '1') then
        return 55;
    elsif (56 < N && x[56] == '1') then
        return 56;
    elsif (57 < N && x[57] == '1') then
        return 57;
    elsif (58 < N && x[58] == '1') then
        return 58;
    elsif (59 < N && x[59] == '1') then
        return 59;
    elsif (60 < N && x[60] == '1') then
        return 60;
    elsif (61 < N && x[61] == '1') then
        return 61;
    elsif (62 < N && x[62] == '1') then
        return 62;
    elsif (63 < N && x[63] == '1') then
        return 63;
    else
        return N;

bits(W) ite(boolean c, bits(W) x, bits(W) y)
  return if c then x else y;

// Vector Operations

bits(W * N) add_vec(bits(W * N) x, bits(W * N) y, integer N)
  bits(W * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, W] = Elem[x, i, W] + Elem[y, i, W];
  return result;

bits(W * N) sub_vec(bits(W * N) x, bits(W * N) y, integer N)
  bits(W * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, W] = Elem[x, i, W] - Elem[y, i, W];
  return result;

bits(W * N) mul_vec(bits(W * N) x, bits(W * N) y, integer N)
  bits(W * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, W] = Elem[x, i, W] * Elem[y, i, W];
  return result;

bits(W * N) sdiv_vec(bits(W * N) x, bits(W * N) y, integer N)
  bits(W * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, W] = sdiv_bits(Elem[x, i, W], Elem[y, i, W]);
  return result;

bits(W * N) lsr_vec(bits(W * N) x, bits(W * N) y, integer N)
  bits(W * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, W] = lsr_bits(Elem[x, i, W], Elem[y, i, W]);
  return result;

bits(W * N) asr_vec(bits(W * N) x, bits(W * N) y, integer N)
  bits(W * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, W] = asr_bits(Elem[x, i, W], Elem[y, i, W]);
  return result;

bits(W * N) lsl_vec(bits(W * N) x, bits(W * N) y, integer N)
  bits(W * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, W] = lsl_bits(Elem[x, i, W], Elem[y, i, W]);
  return result;

bits(W * N) ite_vec(bits(N) c, bits(W * N) x, bits(W * N) y, integer N)
  bits(W * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, W] = if c[i] == '1' then Elem[x, i, W] else Elem[y, i, W];
  return result;

bits(N) sle_vec(bits(W * N) x, bits(W * N) y, integer N)
  bits(N) result;
  for i = 0 to (N - 1)
    Elem[result, i, 1] = if sle_bits(Elem[x, i, W],Elem[y, i, W]) then '1' else '0';
  return result;

bits(N) slt_vec(bits(W * N) x, bits(W * N) y, integer N)
  bits(N) result;
  for i = 0 to (N - 1)
    Elem[result, i, 1] = if slt_bits(Elem[x, i, W], Elem[y, i, W]) then '1' else '0';
  return result;

bits(N) eq_vec(bits(W * N) x, bits(W * N) y, integer N)
  bits(N) result;
  for i = 0 to (N - 1)
    Elem[result, i, 1] = if (Elem[x, i, W] == Elem[y, i, W]) then '1' else '0';
  return result;

bits(NW * N) zcast_vec(bits(W * N) x, integer N, integer NW)
  bits(NW * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, NW] = ZeroExtend(Elem[x, i, W], NW);
  return result;

bits(NW * N) scast_vec(bits(W * N) x, integer N, integer NW)
  bits(NW * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, NW] = SignExtend(Elem[x, i, W], NW);
  return result;

bits(NW * N) trunc_vec(bits(W * N) x, integer N, integer NW)
  bits(NW * N) result;
  for i = 0 to (N - 1)
    Elem[result, i, NW] = (Elem[x, i, W])[ 0 +: NW ];
  return result;

bits(W * N) select_vec(bits(W * M) x, bits(32 * N) sel)
  bits(W * N) result;
  for i = 0 to (N - 1)
    integer pos = UInt(Elem[sel,i,32]);
    Elem[result, i, W] = Elem[x,pos,W];
  return result;

bits(W * N) shuffle_vec(bits(W * M) x, bits(W * M) y, bits(32 * N) sel)
  bits(W * N) result;
  bits(W * M * 2) input = x:y;
  for i = 0 to (N - 1)
    integer pos = UInt(Elem[sel,i,32]);
    Elem[result, i, W] = Elem[input,pos,W];
  return result;

bits(W) reduce_add(bits(W * N) x, bits(W) init)
  bits(W) result = init;
  for i = 0 to (N - 1)
    result = result + Elem[x,i,W];
  return result;

// bits(8*size) _Mem[AddressDescriptor desc, integer size, AccessDescriptor accdesc];
// _Mem[AddressDescriptor desc, integer size, AccessDescriptor accdesc] = bits(8*size) value;

// very basic replacements for memory load operations.
// SKIPS address translation, alignment check, non-atomicity, and much more.
bits(size*8) AArch64.MemSingle[bits(64) vaddress, integer size, AccType acctype, boolean wasaligned]
    AccessDescriptor access;
    access.acctype = acctype;
    //access.mpam = GenMPAMcurEL(acctype IN {AccType_IFETCH, AccType_IC});
    access.page_table_walk = FALSE;

    AddressDescriptor address;
    address.paddress.address = Align(vaddress[51:0], size);
    address.paddress.NS = '1';

    return _Mem[address, size, access];


AArch64.MemSingle[bits(64) vaddress, integer size, AccType acctype, boolean wasaligned] = bits(size*8) value
    AccessDescriptor access;
    access.acctype = acctype;
    //access.mpam = GenMPAMcurEL(acctype IN {AccType_IFETCH, AccType_IC});
    access.page_table_walk = FALSE;

    AddressDescriptor address;
    address.paddress.address = Align(vaddress[51:0], size);
    address.paddress.NS = '1';

    _Mem[address, size, access] = value;

bits(size) MemAtomic(bits(64) address, MemAtomicOp op, bits(size) value, AccType ldacctype, AccType stacctype)
    bits(size) newvalue;
    //memaddrdesc = AArch64.TranslateAddressForAtomicAccess(address, size);
    //ldaccdesc = CreateAccessDescriptor(ldacctype);
    //staccdesc = CreateAccessDescriptor(stacctype);

    AtomicStart();

    // All observers in the shareability domain observe the
    // following load and store atomically.
    oldvalue = Mem[address, size DIV 8, ldacctype];
    if BigEndian() then
        oldvalue = BigEndianReverse(oldvalue);

    case op of
        when MemAtomicOp_ADD   newvalue = oldvalue + value;
        when MemAtomicOp_BIC   newvalue = oldvalue AND NOT(value);
        when MemAtomicOp_EOR   newvalue = oldvalue EOR value;
        when MemAtomicOp_ORR   newvalue = oldvalue OR value;
        when MemAtomicOp_SMAX  newvalue = if SInt(oldvalue) > SInt(value) then oldvalue else value;
        when MemAtomicOp_SMIN  newvalue = if SInt(oldvalue) > SInt(value) then value else oldvalue;
        when MemAtomicOp_UMAX  newvalue = if UInt(oldvalue) > UInt(value) then oldvalue else value;
        when MemAtomicOp_UMIN  newvalue = if UInt(oldvalue) > UInt(value) then value else oldvalue;
        when MemAtomicOp_SWP   newvalue = value;

    if BigEndian() then
        newvalue = BigEndianReverse(newvalue);
    Mem[address, size DIV 8, stacctype] = newvalue;

    AtomicEnd();

    // Load operations return the old (pre-operation) value
    return oldvalue;

bits(size) MemAtomicCompareAndSwap(bits(64) address, bits(size) expectedvalue,
                                   bits(size) newvalue, AccType ldacctype, AccType stacctype)
    AtomicStart();
    bits(size) oldvalue = Mem[address, size DIV 8, ldacctype];
    if BigEndian() then
        oldvalue = BigEndianReverse(oldvalue);

    if oldvalue == expectedvalue then
        if BigEndian() then
            newvalue = BigEndianReverse(newvalue);
        Mem[address, size DIV 8, stacctype] = newvalue;
    AtomicEnd();
    return oldvalue;

// Stub this out, beyond the bounds of the model
CheckSVEEnabled()
  return;

// Beyond bounds
bits(64) AuthIA(bits(64) X, bits(64) Y, boolean is_combined)
  return X;

bits(64) AuthIB(bits(64) X, bits(64) Y, boolean is_combined)
  return X;

// Exactly the same as the real impl, but current dis does not support an ITE that returns a tuple
(bits(N), boolean) SatQ(integer i, integer N, boolean unsigned)
    if unsigned then
        return UnsignedSatQ(i, N);
    else
        return SignedSatQ(i, N);

// Avoid tuple return
bits(N) FPToFixedJS_impl(bits(M) op, FPCRType fpcr, boolean Is64)

    assert M == 64 && N == 33;

    // Unpack using fpcr to determine if subnormals are flushed-to-zero
    (fptype,sign,value) = FPUnpack(op, fpcr);

    Z = '1';
    // If NaN, set cumulative flag or take exception
    if fptype == FPType_SNaN || fptype == FPType_QNaN then
        FPProcessException(FPExc_InvalidOp, fpcr);
        Z = '0';

    int_result = RoundDown(value);
    error = value - Real(int_result);

    // Determine whether supplied rounding mode requires an increment

    round_it_up = (error != 0.0 && int_result < 0);
    if round_it_up then int_result = int_result + 1;

    if int_result < 0 then
        result = int_result - 2^32*RoundUp(Real(int_result)/Real(2^32));
    else
        result = int_result - 2^32*RoundDown(Real(int_result)/Real(2^32));

    // Generate exceptions
    if int_result < -(2^31) || int_result > (2^31)-1 then
        FPProcessException(FPExc_InvalidOp, fpcr);
        Z = '0';
    elsif error != 0.0 then
        FPProcessException(FPExc_Inexact, fpcr);
        Z = '0';
    elsif sign == '1' && value == 0.0 then
        Z = '0';
    elsif sign == '0' && value == 0.0 && !IsZero(op[51:0]) then
        Z = '0';

    if fptype == FPType_Infinity then result = 0;

    return result[N-2:0]:Z;

(bits(N), bit) FPToFixedJS(bits(M) op, FPCRType fpcr, boolean Is64)
    bits(N + 1) res = FPToFixedJS_impl(op, fpcr, Is64);
    return (res[N:1], res[0]);
