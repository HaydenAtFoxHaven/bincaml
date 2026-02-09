var $Global_131088_131096: bv64;
var $Global_131112_131120: bv64;
var $Global_131120_131128: bv64;
declare-fun $__VERIFIER_nondet_uint : () -> bv32;
declare-fun $__VERIFIER_nondet_char : () -> bv8;

prog entry @main_1856;

proc @main_1856
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R1_out:bv64, R29_out:bv64, R3_out:bv64, _PC_out:bv64)
  { .name = "main"; .address = 0x740; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x740; .originalLabel = "7zXyKF5BQ9unwmYzZHvR0A=="} [
    var Stack_n48_n40: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n40_n32: bv64 := R30_in:bv64 { .label = "1856_2" };
    var Stack_n32_n24: bv64 := R19_in:bv64 { .label = "1864_1" };
    var Stack_n24_n16: bv64 := R20_in:bv64 { .label = "1864_2" };
    var Stack_n16_n8: bv64 := R21_in:bv64 { .label = "1868_0" };
    var load9_1: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv32 := $__VERIFIER_nondet_uint();
    var R20_2: bv64 := zero_extend(32, R0_2:bv32) { .label = "1876_0" };
    var load2_1: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv64 := zero_extend(56, $__VERIFIER_nondet_char());
    var R21_2: bv64 := zero_extend(32, extract(32, 0, R0_4:bv64)) { .label = "1884_0" };
    var load9_2: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_6: bv32 := $__VERIFIER_nondet_uint();
    var R19_2: bv64 := zero_extend(32, R0_6:bv32) { .label = "1892_0" };
    var load2_2: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv64 := zero_extend(56, $__VERIFIER_nondet_char());
    var R3_2: bv64 := zero_extend(32, extract(32, 0, R0_8:bv64)) { .label = "1900_0" };
    goto(%phi_15, %phi_16);
  ];
  block %main_14 {.address = 0x798; .originalLabel = "CUWJhlw/SRSR7tnVHCqT9A=="} [
    var (R0_17:bv64, R1_7:bv64, R29_23:bv64, R2_24:bv64, R3_15:bv64, R4_22:bv64)
        := call @addflt_2656 (zero_extend(32, extract(32, 0, R20_14:bv64)), zero_extend(32, extract(32, 0, R19_16:bv64)), bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), 0x74c:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_2:bv64, R4_in:bv64);
    goto(%main_14_retval_inline);
  ];
  block %main_24 {.address = 0x784; .originalLabel = "QIafpHesRhaQVkpv17kXdQ=="} [
    goto(%phi_22, %phi_23);
  ];
  block %phi_15 {.originalLabel = "cZzFYbHyS6KS2iiAPs8hYw=="} [
    guard eq(extract(32, 0, R20_2:bv64), 0x0:bv32);
    var R20_14: bv64 := R20_2:bv64 { .label = "phiback" };
    var R2_16: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%main_24);
  ];
  block %phi_16 {.originalLabel = "cZzFYbHyS6KS2iiAPs8hYw=="} [
    guard boolnot(eq(extract(32, 0, R20_2:bv64), 0x0:bv32));
    var (R0_11:bv64, R1_3:bv64, R2_12:bv64) := call @base2flt.part.0_2368 (zero_extend(32, extract(32, 0, R20_2:bv64)), zero_extend(32, sign_extend(24, extract(8, 0, R21_2:bv64))));
    goto(%phi_16_retval_inline);
  ];
  block %phi_22 {.originalLabel = "QIafpHesRhaQVkpv17kXdQ=="} [
    guard eq(extract(32, 0, R19_2:bv64), 0x0:bv32);
    var R19_16: bv64 := R19_2:bv64 { .label = "phiback" };
    var R2_23: bv64 := R2_16:bv64 { .label = "phiback" };
    goto(%main_14);
  ];
  block %phi_23 {.originalLabel = "QIafpHesRhaQVkpv17kXdQ=="} [
    guard boolnot(eq(extract(32, 0, R19_2:bv64), 0x0:bv32));
    var (R0_14:bv64, R1_5:bv64, R2_19:bv64) := call @base2flt.part.0_2368 (zero_extend(32, extract(32, 0, R19_2:bv64)), zero_extend(32, sign_extend(24, extract(8, 0, R3_2:bv64))));
    goto(%phi_23_retval_inline);
  ];
  block %phi_31 {.originalLabel = "9JF7g5kwQAC2eL0nn9nILQ=="} [
    guard boolnot(eq(extract(32, 0, R21_19:bv64), extract(32, 0, R0_20:bv64)));
    var (R0_retval_inlined_6:bv64, R17_24:bv64, R1_retval_inlined_10:bv64, R2_retval_inlined_14:bv64, R3_retval_inlined_16:bv64) := call @reach_error_2472 (R29_25:bv64, 0x744:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64)) { .label = "2000_2" };
    goto(%phi_31_retval_inline);
  ];
  block %phi_32 {.originalLabel = "9JF7g5kwQAC2eL0nn9nILQ=="} [
    guard eq(extract(32, 0, R21_19:bv64), extract(32, 0, R0_20:bv64));
    var load13_1: bv64 := Stack_n16_n8:bv64 { .label = "1980_0_0" };
    var load14_1: bv64 := Stack_n32_n24:bv64 { .label = "1988_1_0" };
    var load15_1: bv64 := Stack_n24_n16:bv64 { .label = "1988_2_0" };
    var load16_1: bv64 := Stack_n48_n40:bv64 { .label = "1992_0_0" };
    var load17_1: bv64 := Stack_n40_n32:bv64 { .label = "1992_1_0" };
    var R29_33: bv64 := load16_1:bv64 { .label = "phiback" };
    var R31_30: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_30: bv64 := 0x20010:bv64 { .label = "phiback" };
    var R1_16: bv64 := R1_9:bv64 { .label = "phiback" };
    var R3_24: bv64 := R3_17:bv64 { .label = "phiback" };
    var R17_26: bv64 := load2_2:bv64 { .label = "phiback" };
    var R0_28: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_18: bv64 := load17_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_31_retval_inline [
    var R29_33: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffc0:bv64) { .label = "phiback" };
    var R31_30: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64) { .label = "phiback" };
    var R16_30: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R1_16: bv64 := 0xbb0:bv64 { .label = "phiback" };
    var R3_24: bv64 := 0xba0:bv64 { .label = "phiback" };
    var R17_26: bv64 := R17_24:bv64 { .label = "phiback" };
    var R0_28: bv64 := 0xbc8:bv64 { .label = "phiback" };
    var R30_18: bv64 := 0x744:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_16_retval_inline [
    var R20_14: bv64 := zero_extend(32, extract(32, 0, R0_11:bv64)) { .label = "phiback" };
    var R2_16: bv64 := R2_12:bv64 { .label = "phiback" };
    goto(%main_24);
  ];
  block %phi_23_retval_inline [
    var R19_16: bv64 := zero_extend(32, extract(32, 0, R0_14:bv64)) { .label = "phiback" };
    var R2_23: bv64 := R2_19:bv64 { .label = "phiback" };
    goto(%main_14);
  ];
  block %main_14_retval_inline [
    var _PC_24: bv64 := _PC_in:bv64 { .label = "inlineret" };
    var R21_19: bv64 := zero_extend(32, extract(32, 0, R0_17:bv64)) { .label = "1956_0" };
    var (R0_20:bv64, R1_9:bv64, R29_25:bv64, R2_26:bv64, R3_17:bv64, R4_24:bv64)
        := call @addflt_2656 (zero_extend(32, extract(32, 0, R19_16:bv64)), zero_extend(32, extract(32, 0, R20_14:bv64)), R29_23:bv64, 0x750:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_15:bv64, R4_22:bv64);
    goto(%phi_29_retval_inline);
  ];
  block %phi_29_retval_inline [
    var _PC_26: bv64 := _PC_24:bv64 { .label = "inlineret" };
    goto(%phi_31, %phi_32);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_18:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_30:bv64) { .comment = "R31 preserved across calls" };
    return (R0_28:bv64, R16_30:bv64, R17_26:bv64, R1_16:bv64, R29_33:bv64, R3_24:bv64, _PC_26:bv64);
  ]
];


proc @reach_error_2472
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x9a8; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x9a8; .originalLabel = "FsWsRXG1SLGflaXcncMhcA=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2472_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2472_2" };
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 = R30_in" };
    var load27_1: bv64 := $Global_131112_131120:bv64 { .label = "1796_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0xbc8:bv64, load27_1:bv64, 0xbb0:bv64, 0x3:bv64, 0xba0:bv64);
  ]
];


proc @addflt_2656
  (R0_in:bv64, R1_in:bv64, R29_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64)
    -> (R0_out:bv64, R1_out:bv64, R29_out:bv64, R2_out:bv64, R3_out:bv64, R4_out:bv64)
  { .name = "addflt"; .address = 0xa60; .returnBlock = "addflt_return" }
[
  block %addflt_entry {.address = 0xa60; .originalLabel = "eNHeFvijQIKu+D8BA6oMTQ=="} [
    goto(%phi_3, %phi_4);
  ];
  block %addflt_4 {.address = 0xad0; .originalLabel = "cNKtPYNUSxy1PQ6cBK5Vsw=="} [
    goto(%phi_44);
  ];
  block %addflt_8 {.address = 0xaec; .originalLabel = "c3n1AnynTuKdCAk3veacgQ=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2796_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2796_2" };
    assert eq(R30_in:bv64, 0x74c:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_7:bv64, R17_28:bv64, R1_retval_inlined_11:bv64, R2_retval_inlined_15:bv64, R3_retval_inlined_17:bv64) := call @reach_error_2472 (bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), 0x74c:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .label = "2804_2" };
    goto(%addflt_8_retval_inline);
  ];
  block %addflt_54 [
    var R0_9: bv64 := zero_extend(32, extract(32, 0, R2_6:bv64)) { .label = "2668_0" };
    goto(%phi_15, %phi_16);
  ];
  block %addflt_60 [
    goto(%phi_9, %phi_10);
  ];
  block %phi_3 {.originalLabel = "eNHeFvijQIKu+D8BA6oMTQ=="} [
    guard bvult(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R2_6: bv64 := zero_extend(32, extract(32, 0, R1_in:bv64)) { .label = "phiback" };
    goto(%addflt_60);
  ];
  block %phi_4 {.originalLabel = "eNHeFvijQIKu+D8BA6oMTQ=="} [
    guard bvuge(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R2_6: bv64 := zero_extend(32, extract(32, 0, R0_in:bv64)) { .label = "phiback" };
    goto(%addflt_60);
  ];
  block %phi_9 [
    guard bvult(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R1_13: bv64 := zero_extend(32, extract(32, 0, R0_in:bv64)) { .label = "phiback" };
    goto(%addflt_54);
  ];
  block %phi_10 [
    guard bvuge(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R1_13: bv64 := zero_extend(32, extract(32, 0, R1_in:bv64)) { .label = "phiback" };
    goto(%addflt_54);
  ];
  block %phi_15 [
    guard eq(extract(32, 0, R1_13:bv64), 0x0:bv32);
    var R1_42: bv64 := R1_13:bv64 { .label = "phiback" };
    var R4_38: bv64 := R4_in:bv64 { .label = "phiback" };
    var R0_35: bv64 := R0_9:bv64 { .label = "phiback" };
    var R3_39: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_43: bv64 := R2_6:bv64 { .label = "phiback" };
    goto(%addflt_4);
  ];
  block %phi_16 [
    guard boolnot(eq(extract(32, 0, R1_13:bv64), 0x0:bv32));
    var R4_14: bv64 := zero_extend(56, extract(32, 24, R2_6:bv64)) { .label = "2676_0" };
    var R3_14: bv64 := zero_extend(56, extract(32, 24, R1_13:bv64)) { .label = "2680_0" };
    goto(%phi_17, %phi_18);
  ];
  block %phi_17 [
    guard bvslt(extract(32, 0, R4_14:bv64), extract(32, 0, R3_14:bv64));
    var R1_38: bv64 := R1_13:bv64 { .label = "phiback" };
    var R3_35: bv64 := R3_14:bv64 { .label = "phiback" };
    var R2_39: bv64 := R2_6:bv64 { .label = "phiback" };
    var R0_31: bv64 := R0_9:bv64 { .label = "phiback" };
    goto(%addflt_8);
  ];
  block %phi_18 [
    guard bvsge(extract(32, 0, R4_14:bv64), extract(32, 0, R3_14:bv64));
    var R3_17: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_14:bv64), bvneg(extract(32, 0, R3_14:bv64)))) { .label = "2692_0" };
    goto(%phi_19, %phi_20);
  ];
  block %phi_19 [
    guard bvsgt(extract(32, 0, R3_17:bv64), 0x1f:bv32);
    var R1_38: bv64 := R1_13:bv64 { .label = "phiback" };
    var R3_35: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_39: bv64 := R2_6:bv64 { .label = "phiback" };
    var R0_31: bv64 := R0_9:bv64 { .label = "phiback" };
    goto(%addflt_8);
  ];
  block %phi_20 [
    guard bvsle(extract(32, 0, R3_17:bv64), 0x1f:bv32);
    var R1_21: bv32 := bvor(zero_extend(8, extract(24, 0, R1_13:bv64)), 0x1000000:bv32) { .label = "2708_0" };
    var R1_22: bv64 := zero_extend(32, bvlshr(R1_21:bv32, zero_extend(27, extract(5, 0, R3_17:bv64)))) { .label = "2712_0" };
    goto(%phi_21, %phi_22);
  ];
  block %phi_21 [
    guard eq(extract(32, 0, R1_22:bv64), 0x0:bv32);
    var R1_42: bv64 := R1_22:bv64 { .label = "phiback" };
    var R4_38: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_35: bv64 := R0_9:bv64 { .label = "phiback" };
    var R3_39: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_43: bv64 := R2_6:bv64 { .label = "phiback" };
    goto(%addflt_4);
  ];
  block %phi_22 [
    guard boolnot(eq(extract(32, 0, R1_22:bv64), 0x0:bv32));
    var R2_21: bv32 := bvor(zero_extend(8, extract(24, 0, R2_6:bv64)), 0x1000000:bv32) { .label = "2724_0" };
    var R2_22: bv64 := zero_extend(32, bvadd(R2_21:bv32, extract(32, 0, R1_22:bv64))) { .label = "2728_0" };
    goto(%phi_23, %phi_24);
  ];
  block %phi_23 [
    guard boolnot(eq(extract(26, 25, R2_22:bv64), 0x1:bv1));
    goto(%phi_29, %phi_30);
  ];
  block %phi_24 [
    guard eq(extract(26, 25, R2_22:bv64), 0x1:bv1);
    goto(%phi_25, %phi_26);
  ];
  block %phi_25 [
    guard eq(extract(32, 0, R4_14:bv64), 0xff:bv32);
    var R1_42: bv64 := R1_22:bv64 { .label = "phiback" };
    var R4_38: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_35: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    var R3_39: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_43: bv64 := R2_22:bv64 { .label = "phiback" };
    goto(%addflt_4);
  ];
  block %phi_26 [
    guard boolnot(eq(extract(32, 0, R4_14:bv64), 0xff:bv32));
    var R4_25: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_14:bv64), 0x1:bv32)) { .label = "2744_0" };
    var R0_18: bv64 := zero_extend(32, bvor(zero_extend(8, extract(25, 1, R2_22:bv64)), bvshl(zero_extend(24, extract(8, 0, R4_25:bv64)), 0x18:bv32))) { .label = "2756_0" };
    var R29_40: bv64 := R29_in:bv64 { .label = "phiback" };
    var R31_39: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_44: bv64 := R1_22:bv64 { .label = "phiback" };
    var R4_40: bv64 := R4_25:bv64 { .label = "phiback" };
    var R0_37: bv64 := R0_18:bv64 { .label = "phiback" };
    var R3_41: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_45: bv64 := zero_extend(40, extract(25, 1, R2_22:bv64)) { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %phi_29 [
    guard bvugt(extract(32, 0, R2_22:bv64), 0x1ffffff:bv32);
    var R1_38: bv64 := R1_22:bv64 { .label = "phiback" };
    var R3_35: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_39: bv64 := R2_22:bv64 { .label = "phiback" };
    var R0_31: bv64 := 0x1ffffff:bv64 { .label = "phiback" };
    goto(%addflt_8);
  ];
  block %phi_30 [
    guard bvule(extract(32, 0, R2_22:bv64), 0x1ffffff:bv32);
    var R0_25: bv64 := zero_extend(32, bvor(zero_extend(8, extract(24, 0, R2_22:bv64)), bvshl(zero_extend(24, extract(8, 0, R4_14:bv64)), 0x18:bv32))) { .label = "2788_0" };
    var R29_40: bv64 := R29_in:bv64 { .label = "phiback" };
    var R31_39: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_44: bv64 := R1_22:bv64 { .label = "phiback" };
    var R4_40: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_37: bv64 := R0_25:bv64 { .label = "phiback" };
    var R3_41: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_45: bv64 := zero_extend(40, extract(24, 0, R2_22:bv64)) { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %phi_44 {.originalLabel = "cNKtPYNUSxy1PQ6cBK5Vsw=="} [
    var R29_40: bv64 := R29_in:bv64 { .label = "phiback" };
    var R31_39: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_44: bv64 := R1_42:bv64 { .label = "phiback" };
    var R4_40: bv64 := R4_38:bv64 { .label = "phiback" };
    var R0_37: bv64 := R0_35:bv64 { .label = "phiback" };
    var R3_41: bv64 := R3_39:bv64 { .label = "phiback" };
    var R2_45: bv64 := R2_43:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %addflt_8_retval_inline [
    var R29_40: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R31_39: bv64 := bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64) { .label = "phiback" };
    var R1_44: bv64 := 0xbb0:bv64 { .label = "phiback" };
    var R4_40: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_37: bv64 := 0xbc8:bv64 { .label = "phiback" };
    var R3_41: bv64 := 0xba0:bv64 { .label = "phiback" };
    var R2_45: bv64 := 0x3:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %addflt_return [
    assert eq(R31_in:bv64, R31_39:bv64) { .comment = "R31 preserved across calls" };
    return (R0_37:bv64, R1_44:bv64, R29_40:bv64, R2_45:bv64, R3_41:bv64, R4_40:bv64);
  ]
];


proc @base2flt.part.0_2368 (R0_in:bv64, R1_in:bv64) -> (R0_out:bv64, R1_out:bv64, R2_out:bv64)
  { .name = "base2flt.part.0"; .address = 0x940; .returnBlock = "base2flt.part.0_return" }
[
  block %base2flt.part.0_entry {.address = 0x940; .originalLabel = "BQgixXwmRGSurl8tK67TwQ=="} [
    goto(%phi_3, %phi_4);
  ];
  block %base2flt.part.0_4 {.address = 0x958; .originalLabel = "0o1hmwY/TBKTa3mTsNnS5g=="} [
    var R1_24: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_23:bv64), 0x80:bv32)) { .label = "2392_0" };
    var R0_26: bv32 := bvand(extract(32, 0, R0_25:bv64), 0xfeffffff:bv32) { .label = "2396_0" };
    var R0_27: bv64 := zero_extend(32, bvor(R0_26:bv32, bvshl(zero_extend(24, extract(8, 0, R1_24:bv64)), 0x18:bv32))) { .label = "2400_0" };
    var R1_26: bv64 := R1_24:bv64 { .label = "phiback" };
    var R0_29: bv64 := R0_27:bv64 { .label = "phiback" };
    var R2_25: bv64 := R2_23:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_return);
  ];
  block %base2flt.part.0_loop1_18 {.address = 0x978; .originalLabel = "B8eml3FwRE2NgNjsucIRXg=="} [
    goto(%phi_17, %phi_18);
  ];
  block %base2flt.part.0_loop2_34 {.address = 0x998; .originalLabel = "OosCMvcbSK+UwlFX6CuSMg=="} [
    goto(%phi_9, %phi_10);
  ];
  block %phi_3 {.originalLabel = "BQgixXwmRGSurl8tK67TwQ=="} [
    guard bvule(extract(32, 0, R0_in:bv64), 0xffffff:bv32);
    ( var R1_15: bv64 := R1_in:bv64,
      var R0_16: bv64 := R0_in:bv64 );
    goto(%base2flt.part.0_loop1_18);
  ];
  block %phi_4 {.originalLabel = "BQgixXwmRGSurl8tK67TwQ=="} [
    guard bvugt(extract(32, 0, R0_in:bv64), 0xffffff:bv32);
    goto(%phi_5, %phi_6);
  ];
  block %phi_5 [
    guard bvugt(extract(32, 0, R0_in:bv64), 0x1ffffff:bv32);
    ( var R1_7: bv64 := R1_in:bv64,
      var R0_7: bv64 := R0_in:bv64 );
    goto(%base2flt.part.0_loop2_34);
  ];
  block %phi_6 [
    guard bvule(extract(32, 0, R0_in:bv64), 0x1ffffff:bv32);
    var R1_23: bv64 := R1_in:bv64 { .label = "phiback" };
    var R0_25: bv64 := R0_in:bv64 { .label = "phiback" };
    var R2_23: bv64 := 0x1ffffff:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_4);
  ];
  block %phi_9 {.originalLabel = "OosCMvcbSK+UwlFX6CuSMg=="} [
    guard bvsle(extract(32, 0, R1_7:bv64), 0x7e:bv32);
    var R0_12: bv64 := zero_extend(33, extract(32, 1, R0_7:bv64)) { .label = "2440_0" };
    var R1_11: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_7:bv64), 0x1:bv32)) { .label = "2444_0" };
    goto(%phi_12, %phi_13);
  ];
  block %phi_10 {.originalLabel = "OosCMvcbSK+UwlFX6CuSMg=="} [
    guard bvsgt(extract(32, 0, R1_7:bv64), 0x7e:bv32);
    var R1_26: bv64 := R1_7:bv64 { .label = "phiback" };
    var R0_29: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    var R2_25: bv64 := 0x1ffffff:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_return);
  ];
  block %phi_12 [
    guard bvule(extract(32, 0, R0_12:bv64), 0x1ffffff:bv32);
    var R1_23: bv64 := R1_11:bv64 { .label = "phiback" };
    var R0_25: bv64 := R0_12:bv64 { .label = "phiback" };
    var R2_23: bv64 := 0x1ffffff:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_4);
  ];
  block %phi_13 [
    guard bvugt(extract(32, 0, R0_12:bv64), 0x1ffffff:bv32);
    ( var R1_7: bv64 := R1_11:bv64,
      var R0_7: bv64 := R0_12:bv64 );
    goto(%base2flt.part.0_loop2_34);
  ];
  block %phi_17 {.originalLabel = "B8eml3FwRE2NgNjsucIRXg=="} [
    guard bvsge(extract(32, 0, R1_15:bv64), 0xffffff81:bv32);
    var R0_21: bv64 := zero_extend(32, bvshl(zero_extend(1, extract(31, 0, R0_16:bv64)), 0x1:bv32)) { .label = "2408_0" };
    var R1_19: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_15:bv64), 0xffffffff:bv32)) { .label = "2412_0" };
    goto(%phi_20, %phi_21);
  ];
  block %phi_18 {.originalLabel = "B8eml3FwRE2NgNjsucIRXg=="} [
    guard bvslt(extract(32, 0, R1_15:bv64), 0xffffff81:bv32);
    var R1_26: bv64 := R1_15:bv64 { .label = "phiback" };
    var R0_29: bv64 := 0x0:bv64 { .label = "phiback" };
    var R2_25: bv64 := 0xffffff:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_return);
  ];
  block %phi_20 [
    guard bvugt(extract(32, 0, R0_21:bv64), 0xffffff:bv32);
    var R1_23: bv64 := R1_19:bv64 { .label = "phiback" };
    var R0_25: bv64 := R0_21:bv64 { .label = "phiback" };
    var R2_23: bv64 := 0xffffff:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_4);
  ];
  block %phi_21 [
    guard bvule(extract(32, 0, R0_21:bv64), 0xffffff:bv32);
    ( var R1_15: bv64 := R1_19:bv64,
      var R0_16: bv64 := R0_21:bv64 );
    goto(%base2flt.part.0_loop1_18);
  ];
  block %base2flt.part.0_return [
    return (R0_29:bv64, R1_26:bv64, R2_25:bv64);
  ]
];




prog entry @main_1856 {
  .symbols = {
    .externalFunctions = [
      { .name = "_ITM_deregisterTMCloneTable"; .offset = 0x1ffc0 };
      { .name = "_ITM_registerTMCloneTable"; .offset = 0x1ffe0 };
      { .name = "__VERIFIER_nondet_char"; .offset = 0x20010 };
      { .name = "__VERIFIER_nondet_uint"; .offset = 0x20030 };
      { .name = "__assert_fail"; .offset = 0x20028 };
      { .name = "__cxa_finalize"; .offset = 0x1ffc8 };
      { .name = "__cxa_finalize"; .offset = 0x20008 };
      { .name = "__gmon_start__"; .offset = 0x1ffd0 };
      { .name = "__gmon_start__"; .offset = 0x20018 };
      { .name = "__libc_start_main@GLIBC_2.34"; .offset = 0x20000 };
      { .name = "abort"; .offset = 0x20020 }
    ];
    .globals = [
      { .name = "_DYNAMIC"; .address = 0x1fdc8; .size = 0x0 };
      { .name = "_GLOBAL_OFFSET_TABLE_"; .address = 0x1ffb8; .size = 0x0 };
      { .name = "_IO_stdin_used"; .address = 0xb98; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xd70; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xd74; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20048; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x9d0; .size = 0xa0 };
      { .name = "_start"; .address = 0x800; .size = 0x1a0 };
      { .name = "addflt"; .address = 0xa60; .size = 0x4c0 };
      { .name = "base2flt"; .address = 0x9e4; .size = 0x380 };
      { .name = "main"; .address = 0x740; .size = 0x4a0 };
      { .name = "mulflt"; .address = 0xb00; .size = 0x420 };
      { .name = "reach_error"; .address = 0x9a8; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x920 ]; [ 0x1fdc0; 0x8cc ]; [ 0x1ffd8; 0x740 ]; [ 0x20040; 0x20040 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2X4ftTnSF9Q6Xkmj7iPZ9cqF5T6R/cCALYFe48kAAAA" ]
  };
  {
    .name = ".interp";
    .address = 0x294;
    .size = 0x1b;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/9PPyUzSz0nRzcnMK63QTUwsSs4wM9ErztczZAAA7nBxrxsAAAA=" ]
  };
  {
    .name = ".gnu.hash";
    .address = 0x2b0;
    .size = 0x1c;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NkYGBghGJ0AACV1IdlHAAAAA==" ]
  };
  {
    .name = ".dynsym";
    .address = 0x2d0;
    .size = 0x120;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2NgwA2YGbgYKtiwiYszWDAwoYg1AbEQFjMYgVgBi/gUIFbCIh6LwxxZHOYsxqFeB4f6Ehzq3XCIAwAzFX1Y";
      "IAEAAA=="
    ]
  };
  {
    .name = ".dynstr";
    .address = 0x3f0;
    .size = 0xd8;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3WNywrCQAxF80MWfKB7pcqA3ZTiNqTTtAamGZgZQfx6o4grXeXew+EG0HUNDpx4klw4dc0hROWO+sCAOM1R";
      "MRdKBRHe6h/xUrfu6OoWNerABW+i5Qf2V0qGKWe2yZEkWAvS+8+TmUSN+DvhKEpBHgzUx1TAJNtY2EiucnxVb7fawuns9gdc";
      "VcvdN6438ARG3ace2AAAAA=="
    ]
  };
  {
    .name = ".gnu.version";
    .address = 0x4c8;
    .size = 0x18;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgAAEmBkYGZiCGkCAMAFF4Bk4YAAAA" ]
  };
  {
    .name = ".gnu.version_r";
    .address = 0x4e0;
    .size = 0x30;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NkYGLYwcDAIMAAAdMnTmNjYGBmOAQV2wLmMzGchcoDAA4AW9AwAAAA" ]
  };
  {
    .name = ".rela.dyn";
    .address = 0x510;
    .size = 0xc0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/9vxl5EBBJhZwBSDAieEPoAmfoYDQt/4jyruwA6lGZhQxaH8A1D1jEBxqBQYnEASZ0USv4Akzo4k/gBJnBNJ";
      "HAAMldD9wAAAAA=="
    ]
  };
  {
    .name = ".rela.plt";
    .address = 0x5d0;
    .size = 0xa8;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/03IKw4AIAxEwU35NWCQSCSS+5+OVPFGjmQKlqWkz/EFP/EVv/ANv/GOP/iOv/iBf1RxYNCoAAAA"
    ]
  };
  {
    .name = ".init";
    .address = 0x678;
    .size = 0x18;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBNzGBim/K0+uOIAc/w1AC1CiMQYAAAA" ]
  };
  {
    .name = ".plt";
    .address = 0x690;
    .size = 0x90;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA//tQvX/lBwaGD4L/3H8KPLKfqMAkf01egfkqDAswMkwQZHL4KcDEAJYD89mAfCUkPheQ74TE5wPyk5D4QkB+";
      "ExJfDMhfhMSXAvIPQfgAxvOha5AAAAA="
    ]
  };
  {
    .name = ".text";
    .address = 0x740;
    .size = 0x444;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/5VSPWhTURT+7rsFC+nSpKAUbfLSDjZCbUtQOvXlIWQQh5oMCkLTdjM6pIMUEkhKOyg6NCg4KLTdkqJQtKs2";
      "2qXgZrGgiCT1B6EdgjHggxfjd19IbYMKDodzz/3OOff7zrm15LN8TSJbiYh81QOrXK/f/y4R+EBfpd+jr9C/o/9IvwYEi7Ir";
      "sNwDTwK4p3KfOneewMRxeK7xTuWXGKu8VcZVJ+4KqJxHjNc1xF8A0arHsIDMxUoklK8lN3IFOb59g7jXJ9/8j51A5nUP7bPE";
      "Skka1k4vsl+oqQiUsRe2JLE22jI1rNKc+69hywDWcvX6UfXu33pDYAE+kRX0Ov0osFsg9xJ76MWwNcEeZSlWoHm3VZ/WfB14";
      "5bfTW6GO2du6HbpL3Ws7rDXLYWvSqdX2a2vJ541duGB5WB/zh0YMgbMO309hK8P8Rn/DmqaOtzQf5xfzi5GKy7BqyZe5Vi3v";
      "qe9fs9OK624vtPgtgahWaJxPaojq0Doxc8SNmAg4uma8Eb0NYw5er0dHbTF0lV7tz8FTQuGdCu//SfyHSFxv4O6GtvW8BBYE";
      "TWkE/VRmIKsXBrLwnc5Oss8F6uFOgs18lfdN7Usg2OTZr/3muck9dAJdB9/OU0fr2we551jTyr1V66EZQcT9g5luMTjbXZRa";
      "QEgEz6WORXppi5DxuER0DvJ8OoVEB8/6Fbh1tA/rfRvdy+RtMjYZmxAuU2yeWbRlQv2fefI1yVvhRqytMeMmX+obB+I3mXcQ";
      "b87kMWfyJ35KT4j8+shN9ZqPma65JTmWtkXiDuem8DS0oVM8+xQvGhxu7cOlKeOJmVp6YNiXtthzN8+3VR3/XnTuoRwz7Mtb";
      "U/tzkof4/gLiX4CgRAQAAA=="
    ]
  };
  {
    .name = ".fini";
    .address = 0xb84;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0xb98;
    .size = 0x32;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML84P60kPi0nP7Ek3kTXOFEvWS85M0cvmcGAAQCM8wNwMgAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xbcc;
    .size = 0x6c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrbOYGBg4AHikt///1cwMjCY/Pn/vwHInwKkpwDpI0B6BZBm+Pv//x4gFQKkH4DUA+kvQPoOkOYA6mP5";
      "9/+/ApCWANIWQHoKkPYBmff///8UIA0Aq9ub1mwAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xc38;
    .size = 0x13c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiNf8/v/fBCTpyC4HEtMB4h9AMQOoHpCYAxCL/Pn/3wYqpgDEIUBsAxTz";
      "AOvlU5jLMo/ZaTKT3727l/lg+iqAOAeohgXJrB6QOFAsAyomAsQLgPgMUEwDYpbAXKZ5jCDxHUB8BygOYjM4Q8RBZlwA4htA";
      "8QIkM56A3Pn3//8ZIIEUhNo/QHwCKN4CVQuyQ4CRgeHLz///p0DsM5jLNo/VeTLLFOapTPFc9+5evXyFj8GRG6IeAPz+Y6s8";
      "AQAA"
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xd74;
    .size = 0x20;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAGJGIHb3C2UAAWYgZmeAAAA9kbzyIAAAAA==" ]
  };
  {
    .name = ".init_array";
    .address = 0x1fdb8;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/1PgZAADAOz4zAkIAAAA" ]
  };
  {
    .name = ".fini_array";
    .address = 0x1fdc0;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/zvDwQAGAHbDxHsIAAAA" ]
  };
  {
    .name = ".dynamic";
    .address = 0x1fdc8;
    .size = 0x1f0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/7WQqw7CQBBFp9DlTYKgoTz+EcsH8DHgkMhKJBJZiaxBNE27hNyzYusZc3Ln7s6d3cRUV5jAO1zA00hcos9z";
      "cRvOt7q5R0/gDhb4h57/6fzxx9tA2tGvhiKx9sSfoV+QNSyHmcXFGHt75TPGLnANx3AT8lzcX7l47wJOe/mN13vC0Q5dpmp6";
      "dPjnCv3Ar9Gp/ae++eb76/ABAAA="
    ]
  };
  {
    .name = ".got";
    .address = 0x1ffb8;
    .size = 0x30;
    .readOnly = true;
    .bytes = [ "H4sIAAAAAAAA/zvxl5EBH3BgR+UDAATSJGQwAAAA" ]
  };
  {
    .name = ".got.plt";
    .address = 0x1ffe8;
    .size = 0x50;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgwA4msJFHAwB0hWLRUAAAAA==" ]
  };
  {
    .name = ".data";
    .address = 0x20038;
    .size = 0x10;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NggAAHBiYwDQCzKO6IEAAAAA==" ]
  };
  {
    .name = ".bss";
    .address = 0x20048;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NggAAAad8iZQgAAAA=" ]
  }
]
} ;
