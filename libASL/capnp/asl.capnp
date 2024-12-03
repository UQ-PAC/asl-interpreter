@0xfb2c121f1031930d;

# schema for reduced asl, based off offline lifter's output

struct X { num @0 :UInt32; }
struct V { num @0 :UInt32; }

struct PSTATE {
  union {
    n @0 :Void;
    z @1 :Void;
    c @2 :Void;
    v @3 :Void;
  }
}

struct LExpr {
  union {
    x @0 :X;
    v @1 :V;
    pstate @2 :PSTATE;
    pc @3 :Void;
    sp @4 :Void;

    fpsr @5 :Void;
    fpcr @6 :Void;

    btype @7 :Void;
    btypecompatible @8 :Void;
    branchtaken @9 :Void;
    btypenext @10 :Void;
    exclusivelocal @11 :Void;
  }
}

using Width = UInt32;

struct IntExpr {

}

struct BinaryBitsPred {
  union {
    eq  @0 :Void;
    ne  @1 :Void;
    slt @2 :Void;
    sle @3 :Void;
  }
}
struct BinaryBitsPred {
  union {
    eq  @0 :Void;
    ne  @1 :Void;
    slt @2 :Void;
    sle @3 :Void;
  }
}

struct BinaryBitsOp {
  union {
    add @0 :Void;
    sub @1 :Void;
    mul @2 :Void;
    and @3 :Void;
    or  @4 :Void;
    eor @5 :Void;
    not @6 :Void;
    lsl @7 :Void;
    lsr @8 :Void;
    asr @9 :Void;
  }
}

struct BitsExpr {
  union {
    literal :group {
      width @0 :Width;
      str @1 :Text;
    }
    zero :group {
      width @2 :Width;
    }
    extract :group {
      base @3 :BitsExpr;
      lo @4 :IntExpr;
      wd @5 :IntExpr;
    }
    binop :group {
      op @6 :BinaryBitsOp;
      x @7 :BitsExpr;
      y @8 :BitsExpr;
    }
  }

}

struct BoolExpr {
  union {
    binbits :group {
      pred @0 :BinaryBitsPred;
      x @1 :BitsExpr;
      y @2 :BitsExpr;
    }
    binop :group {
      op @3 :BinaryBoolOp;
      x @4 :BitsExpr;
      y @5 :BitsExpr;
    }
  }

}





