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
  block %main_entry {.address = 0x740; .originalLabel = "KVTcNAXuRjC5pU9guBleEQ=="} [
    var Stack_n48_n40: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n40_n32: bv64 := R30_in:bv64 { .label = "1856_2" };
    var Stack_n32_n24: bv64 := R19_in:bv64 { .label = "1864_1" };
    var Stack_n24_n16: bv64 := R20_in:bv64 { .label = "1864_2" };
    var Stack_n16_n8: bv64 := R21_in:bv64 { .label = "1868_0" };
    var load3_1: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv32 := $__VERIFIER_nondet_uint();
    var R20_2: bv64 := zero_extend(32, R0_2:bv32) { .label = "1876_0" };
    var load22_1: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv64 := zero_extend(56, $__VERIFIER_nondet_char());
    var R21_2: bv64 := zero_extend(32, extract(32, 0, R0_4:bv64)) { .label = "1884_0" };
    var load3_2: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_6: bv32 := $__VERIFIER_nondet_uint();
    var R19_2: bv64 := zero_extend(32, R0_6:bv32) { .label = "1892_0" };
    var load22_2: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv64 := zero_extend(56, $__VERIFIER_nondet_char());
    var R3_2: bv64 := zero_extend(32, extract(32, 0, R0_8:bv64)) { .label = "1900_0" };
    goto(%phi_15, %phi_16);
  ];
  block %main_14 {.address = 0x798; .originalLabel = "NK5R5WbtSEey0HAD6FKEVQ=="} [
    var (R0_17:bv64, R1_7:bv64, R29_23:bv64, R2_24:bv64, R3_15:bv64, R4_22:bv64)
        := call @addflt_2656 (zero_extend(32, extract(32, 0, R20_14:bv64)), zero_extend(32, extract(32, 0, R19_16:bv64)), bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), 0x74c:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_2:bv64, R4_in:bv64);
    goto(%main_14_retval_inline);
  ];
  block %main_24 {.address = 0x784; .originalLabel = "HYA8Oc6pT82U+tsPxRmYzw=="} [
    goto(%phi_22, %phi_23);
  ];
  block %phi_15 {.originalLabel = "TUjUFiEVQAOeqcEwr6vhmw=="} [
    guard eq(extract(32, 0, R20_2:bv64), 0x0:bv32);
    var R20_14: bv64 := R20_2:bv64 { .label = "phiback" };
    var R2_16: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%main_24);
  ];
  block %phi_16 {.originalLabel = "TUjUFiEVQAOeqcEwr6vhmw=="} [
    guard boolnot(eq(extract(32, 0, R20_2:bv64), 0x0:bv32));
    var (R0_11:bv64, R1_3:bv64, R2_12:bv64) := call @base2flt.part.0_2368 (zero_extend(32, extract(32, 0, R20_2:bv64)), zero_extend(32, sign_extend(24, extract(8, 0, R21_2:bv64))));
    goto(%phi_16_retval_inline);
  ];
  block %phi_22 {.originalLabel = "HYA8Oc6pT82U+tsPxRmYzw=="} [
    guard eq(extract(32, 0, R19_2:bv64), 0x0:bv32);
    var R19_16: bv64 := R19_2:bv64 { .label = "phiback" };
    var R2_23: bv64 := R2_16:bv64 { .label = "phiback" };
    goto(%main_14);
  ];
  block %phi_23 {.originalLabel = "HYA8Oc6pT82U+tsPxRmYzw=="} [
    guard boolnot(eq(extract(32, 0, R19_2:bv64), 0x0:bv32));
    var (R0_14:bv64, R1_5:bv64, R2_19:bv64) := call @base2flt.part.0_2368 (zero_extend(32, extract(32, 0, R19_2:bv64)), zero_extend(32, sign_extend(24, extract(8, 0, R3_2:bv64))));
    goto(%phi_23_retval_inline);
  ];
  block %phi_31 {.originalLabel = "FiNGMFTHR0uwrTb+gUtqQQ=="} [
    guard boolnot(eq(extract(32, 0, R21_19:bv64), extract(32, 0, R0_20:bv64)));
    var (R0_retval_inlined_7:bv64, R17_24:bv64, R1_retval_inlined_11:bv64, R2_retval_inlined_15:bv64, R3_retval_inlined_17:bv64) := call @reach_error_2472 (R29_25:bv64, 0x744:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64)) { .label = "2000_2" };
    goto(%phi_31_retval_inline);
  ];
  block %phi_32 {.originalLabel = "FiNGMFTHR0uwrTb+gUtqQQ=="} [
    guard eq(extract(32, 0, R21_19:bv64), extract(32, 0, R0_20:bv64));
    var load5_1: bv64 := Stack_n16_n8:bv64 { .label = "1980_0_0" };
    var load6_1: bv64 := Stack_n32_n24:bv64 { .label = "1988_1_0" };
    var load7_1: bv64 := Stack_n24_n16:bv64 { .label = "1988_2_0" };
    var load8_1: bv64 := Stack_n48_n40:bv64 { .label = "1992_0_0" };
    var load9_1: bv64 := Stack_n40_n32:bv64 { .label = "1992_1_0" };
    var R29_33: bv64 := load8_1:bv64 { .label = "phiback" };
    var R31_30: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_30: bv64 := 0x20010:bv64 { .label = "phiback" };
    var R1_16: bv64 := R1_9:bv64 { .label = "phiback" };
    var R3_24: bv64 := R3_17:bv64 { .label = "phiback" };
    var R17_26: bv64 := load22_2:bv64 { .label = "phiback" };
    var R0_28: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_18: bv64 := load9_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_31_retval_inline [
    var R29_33: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffc0:bv64) { .label = "phiback" };
    var R31_30: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64) { .label = "phiback" };
    var R16_30: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R1_16: bv64 := 0xba0:bv64 { .label = "phiback" };
    var R3_24: bv64 := 0xb90:bv64 { .label = "phiback" };
    var R17_26: bv64 := R17_24:bv64 { .label = "phiback" };
    var R0_28: bv64 := 0xbb8:bv64 { .label = "phiback" };
    var R30_18: bv64 := 0x744:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_23_retval_inline [
    var R19_16: bv64 := zero_extend(32, extract(32, 0, R0_14:bv64)) { .label = "phiback" };
    var R2_23: bv64 := R2_19:bv64 { .label = "phiback" };
    goto(%main_14);
  ];
  block %phi_16_retval_inline [
    var R20_14: bv64 := zero_extend(32, extract(32, 0, R0_11:bv64)) { .label = "phiback" };
    var R2_16: bv64 := R2_12:bv64 { .label = "phiback" };
    goto(%main_24);
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
  block %reach_error_entry {.address = 0x9a8; .originalLabel = "vL4Ypkk9SCuZ/bRB8Fg+jA=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2472_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2472_2" };
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 = R30_in" };
    var load21_1: bv64 := $Global_131112_131120:bv64 { .label = "1796_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0xbb8:bv64, load21_1:bv64, 0xba0:bv64, 0x3:bv64, 0xb90:bv64);
  ]
];


proc @addflt_2656
  (R0_in:bv64, R1_in:bv64, R29_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64)
    -> (R0_out:bv64, R1_out:bv64, R29_out:bv64, R2_out:bv64, R3_out:bv64, R4_out:bv64)
  { .name = "addflt"; .address = 0xa60; .returnBlock = "addflt_return" }
[
  block %addflt_entry {.address = 0xa60; .originalLabel = "pLt1Mb7JTYKZ3EhAIKgjpA=="} [
    goto(%phi_3, %phi_4);
  ];
  block %addflt_4 {.address = 0xac8; .originalLabel = "DUy43F+1RzKnNrGggcNvqQ=="} [
    goto(%phi_40);
  ];
  block %addflt_8 {.address = 0xae4; .originalLabel = "etgDn+CSSz6IDs/cFuemVg=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2788_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2788_2" };
    assert eq(R30_in:bv64, 0x74c:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_6:bv64, R17_25:bv64, R1_retval_inlined_10:bv64, R2_retval_inlined_14:bv64, R3_retval_inlined_16:bv64) := call @reach_error_2472 (bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), 0x74c:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .label = "2796_2" };
    goto(%addflt_8_retval_inline);
  ];
  block %addflt_48 [
    var R0_9: bv64 := zero_extend(32, extract(32, 0, R2_6:bv64)) { .label = "2668_0" };
    goto(%phi_15, %phi_16);
  ];
  block %addflt_54 [
    goto(%phi_9, %phi_10);
  ];
  block %phi_3 {.originalLabel = "pLt1Mb7JTYKZ3EhAIKgjpA=="} [
    guard bvult(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R2_6: bv64 := zero_extend(32, extract(32, 0, R1_in:bv64)) { .label = "phiback" };
    goto(%addflt_54);
  ];
  block %phi_4 {.originalLabel = "pLt1Mb7JTYKZ3EhAIKgjpA=="} [
    guard bvuge(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R2_6: bv64 := zero_extend(32, extract(32, 0, R0_in:bv64)) { .label = "phiback" };
    goto(%addflt_54);
  ];
  block %phi_9 [
    guard bvult(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R1_13: bv64 := zero_extend(32, extract(32, 0, R0_in:bv64)) { .label = "phiback" };
    goto(%addflt_48);
  ];
  block %phi_10 [
    guard bvuge(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R1_13: bv64 := zero_extend(32, extract(32, 0, R1_in:bv64)) { .label = "phiback" };
    goto(%addflt_48);
  ];
  block %phi_15 [
    guard eq(extract(32, 0, R1_13:bv64), 0x0:bv32);
    var R1_39: bv64 := R1_13:bv64 { .label = "phiback" };
    var R4_35: bv64 := R4_in:bv64 { .label = "phiback" };
    var R0_32: bv64 := R0_9:bv64 { .label = "phiback" };
    var R3_36: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_40: bv64 := R2_6:bv64 { .label = "phiback" };
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
    var R1_35: bv64 := R1_13:bv64 { .label = "phiback" };
    var R3_32: bv64 := R3_14:bv64 { .label = "phiback" };
    var R2_36: bv64 := R2_6:bv64 { .label = "phiback" };
    var R0_28: bv64 := R0_9:bv64 { .label = "phiback" };
    goto(%addflt_8);
  ];
  block %phi_18 [
    guard bvsge(extract(32, 0, R4_14:bv64), extract(32, 0, R3_14:bv64));
    var R3_17: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_14:bv64), bvneg(extract(32, 0, R3_14:bv64)))) { .label = "2696_0" };
    var R1_19: bv32 := bvor(zero_extend(8, extract(24, 0, R1_13:bv64)), 0x1000000:bv32) { .label = "2700_0" };
    var R1_20: bv64 := zero_extend(32, bvlshr(R1_19:bv32, zero_extend(27, extract(5, 0, R3_17:bv64)))) { .label = "2704_0" };
    goto(%phi_19, %phi_20);
  ];
  block %phi_19 [
    guard eq(extract(32, 0, R1_20:bv64), 0x0:bv32);
    var R1_39: bv64 := R1_20:bv64 { .label = "phiback" };
    var R4_35: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_32: bv64 := R0_9:bv64 { .label = "phiback" };
    var R3_36: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_40: bv64 := R2_6:bv64 { .label = "phiback" };
    goto(%addflt_4);
  ];
  block %phi_20 [
    guard boolnot(eq(extract(32, 0, R1_20:bv64), 0x0:bv32));
    var R2_19: bv32 := bvor(zero_extend(8, extract(24, 0, R2_6:bv64)), 0x1000000:bv32) { .label = "2716_0" };
    var R2_20: bv64 := zero_extend(32, bvadd(R2_19:bv32, extract(32, 0, R1_20:bv64))) { .label = "2720_0" };
    goto(%phi_21, %phi_22);
  ];
  block %phi_21 [
    guard boolnot(eq(extract(26, 25, R2_20:bv64), 0x1:bv1));
    goto(%phi_27, %phi_28);
  ];
  block %phi_22 [
    guard eq(extract(26, 25, R2_20:bv64), 0x1:bv1);
    goto(%phi_23, %phi_24);
  ];
  block %phi_23 [
    guard eq(extract(32, 0, R4_14:bv64), 0xff:bv32);
    var R1_39: bv64 := R1_20:bv64 { .label = "phiback" };
    var R4_35: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_32: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    var R3_36: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_40: bv64 := R2_20:bv64 { .label = "phiback" };
    goto(%addflt_4);
  ];
  block %phi_24 [
    guard boolnot(eq(extract(32, 0, R4_14:bv64), 0xff:bv32));
    var R4_23: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_14:bv64), 0x1:bv32)) { .label = "2736_0" };
    var R0_16: bv64 := zero_extend(32, bvor(zero_extend(8, extract(25, 1, R2_20:bv64)), bvshl(zero_extend(24, extract(8, 0, R4_23:bv64)), 0x18:bv32))) { .label = "2748_0" };
    var R29_37: bv64 := R29_in:bv64 { .label = "phiback" };
    var R31_36: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_41: bv64 := R1_20:bv64 { .label = "phiback" };
    var R4_37: bv64 := R4_23:bv64 { .label = "phiback" };
    var R0_34: bv64 := R0_16:bv64 { .label = "phiback" };
    var R3_38: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_42: bv64 := zero_extend(40, extract(25, 1, R2_20:bv64)) { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %phi_27 [
    guard bvugt(extract(32, 0, R2_20:bv64), 0x1ffffff:bv32);
    var R1_35: bv64 := R1_20:bv64 { .label = "phiback" };
    var R3_32: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_36: bv64 := R2_20:bv64 { .label = "phiback" };
    var R0_28: bv64 := 0x1ffffff:bv64 { .label = "phiback" };
    goto(%addflt_8);
  ];
  block %phi_28 [
    guard bvule(extract(32, 0, R2_20:bv64), 0x1ffffff:bv32);
    var R0_23: bv64 := zero_extend(32, bvor(zero_extend(8, extract(24, 0, R2_20:bv64)), bvshl(zero_extend(24, extract(8, 0, R4_14:bv64)), 0x18:bv32))) { .label = "2780_0" };
    var R29_37: bv64 := R29_in:bv64 { .label = "phiback" };
    var R31_36: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_41: bv64 := R1_20:bv64 { .label = "phiback" };
    var R4_37: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_34: bv64 := R0_23:bv64 { .label = "phiback" };
    var R3_38: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_42: bv64 := zero_extend(40, extract(24, 0, R2_20:bv64)) { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %phi_40 {.originalLabel = "DUy43F+1RzKnNrGggcNvqQ=="} [
    var R29_37: bv64 := R29_in:bv64 { .label = "phiback" };
    var R31_36: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_41: bv64 := R1_39:bv64 { .label = "phiback" };
    var R4_37: bv64 := R4_35:bv64 { .label = "phiback" };
    var R0_34: bv64 := R0_32:bv64 { .label = "phiback" };
    var R3_38: bv64 := R3_36:bv64 { .label = "phiback" };
    var R2_42: bv64 := R2_40:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %addflt_8_retval_inline [
    var R29_37: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R31_36: bv64 := bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64) { .label = "phiback" };
    var R1_41: bv64 := 0xba0:bv64 { .label = "phiback" };
    var R4_37: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_34: bv64 := 0xbb8:bv64 { .label = "phiback" };
    var R3_38: bv64 := 0xb90:bv64 { .label = "phiback" };
    var R2_42: bv64 := 0x3:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %addflt_return [
    assert eq(R31_in:bv64, R31_36:bv64) { .comment = "R31 preserved across calls" };
    return (R0_34:bv64, R1_41:bv64, R29_37:bv64, R2_42:bv64, R3_38:bv64, R4_37:bv64);
  ]
];


proc @base2flt.part.0_2368 (R0_in:bv64, R1_in:bv64) -> (R0_out:bv64, R1_out:bv64, R2_out:bv64)
  { .name = "base2flt.part.0"; .address = 0x940; .returnBlock = "base2flt.part.0_return" }
[
  block %base2flt.part.0_entry {.address = 0x940; .originalLabel = "FRsNQuSQSu2arwE2AY/ZXA=="} [
    goto(%phi_3, %phi_4);
  ];
  block %base2flt.part.0_4 {.address = 0x958; .originalLabel = "LL+txp/gRwWePGSVPEoUhA=="} [
    var R1_24: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_23:bv64), 0x80:bv32)) { .label = "2392_0" };
    var R0_26: bv32 := bvand(extract(32, 0, R0_25:bv64), 0xfeffffff:bv32) { .label = "2396_0" };
    var R0_27: bv64 := zero_extend(32, bvor(R0_26:bv32, bvshl(zero_extend(24, extract(8, 0, R1_24:bv64)), 0x18:bv32))) { .label = "2400_0" };
    var R1_26: bv64 := R1_24:bv64 { .label = "phiback" };
    var R0_29: bv64 := R0_27:bv64 { .label = "phiback" };
    var R2_25: bv64 := R2_23:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_return);
  ];
  block %base2flt.part.0_loop1_18 {.address = 0x978; .originalLabel = "r/4uorm7Sgq5LyDX9u77vA=="} [
    goto(%phi_17, %phi_18);
  ];
  block %base2flt.part.0_loop2_34 {.address = 0x998; .originalLabel = "XS7eW9qST6WqiW1AMSXFJg=="} [
    goto(%phi_9, %phi_10);
  ];
  block %phi_3 {.originalLabel = "FRsNQuSQSu2arwE2AY/ZXA=="} [
    guard bvule(extract(32, 0, R0_in:bv64), 0xffffff:bv32);
    ( var R1_15: bv64 := R1_in:bv64,
      var R0_16: bv64 := R0_in:bv64 );
    goto(%base2flt.part.0_loop1_18);
  ];
  block %phi_4 {.originalLabel = "FRsNQuSQSu2arwE2AY/ZXA=="} [
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
  block %phi_9 {.originalLabel = "XS7eW9qST6WqiW1AMSXFJg=="} [
    guard bvsle(extract(32, 0, R1_7:bv64), 0x7e:bv32);
    var R0_12: bv64 := zero_extend(33, extract(32, 1, R0_7:bv64)) { .label = "2440_0" };
    var R1_11: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_7:bv64), 0x1:bv32)) { .label = "2444_0" };
    goto(%phi_12, %phi_13);
  ];
  block %phi_10 {.originalLabel = "XS7eW9qST6WqiW1AMSXFJg=="} [
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
  block %phi_17 {.originalLabel = "r/4uorm7Sgq5LyDX9u77vA=="} [
    guard bvsge(extract(32, 0, R1_15:bv64), 0xffffff81:bv32);
    var R0_21: bv64 := zero_extend(32, bvshl(zero_extend(1, extract(31, 0, R0_16:bv64)), 0x1:bv32)) { .label = "2408_0" };
    var R1_19: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_15:bv64), 0xffffffff:bv32)) { .label = "2412_0" };
    goto(%phi_20, %phi_21);
  ];
  block %phi_18 {.originalLabel = "r/4uorm7Sgq5LyDX9u77vA=="} [
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
      { .name = "_IO_stdin_used"; .address = 0xb88; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xd60; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xd64; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20048; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x9d0; .size = 0xa0 };
      { .name = "_start"; .address = 0x800; .size = 0x1a0 };
      { .name = "addflt"; .address = 0xa60; .size = 0x480 };
      { .name = "base2flt"; .address = 0x9e4; .size = 0x380 };
      { .name = "main"; .address = 0x740; .size = 0x4a0 };
      { .name = "mulflt"; .address = 0xaf0; .size = 0x420 };
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
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2XgK6mdOF+oV2OKOGvA9tBjnKse3ikEAAe2Ce0kAAAA" ]
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
    .size = 0x434;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/5VSPWhTURg9992Chbg0KShBm7y0g02htCUonfryEDKIQ0wGBaFpuxkd4iCFFJrSDooODQoOCm23pAgWzapt";
      "7VJws1hQRJL6g9AOwRjwwYvx3BdS04CCw8d53z3f991zvvtq6Rf5mkS2EhP5qgdWuV5/+EMi+JFYJR4QK8T3xE/EAhAqyu7g";
      "Sg88KeCBqn3unHmCE6fguc4zVV9irurWmFedvDuoap4wX9eQ3ATiVY9hAZlLlVg4X0tv5Tbk+O4t8j6/fPs/cRqZNz2MLxKr";
      "JWlYe73IfqWnIlDGQcSS5DoYK/SwxnDOv0UsAyjk6vUT6t6/zYbAIvwiK4g6cQzY36D2EmfoxYg1wRllKVah+XbVnPZ6HXgd";
      "sGd3wsfn7up2+D59F/bYa5Yj1qTTqx321tIvG2/hguVhfyIQHjUEzjl6P0esDOsb8w3rJn28Y/i5v0RAjFZchlVLv8q1e/lA";
      "f//anVZcd/ugJe8IxLWNxvcZDXEdWhemj7mREEHH17Qvpncg6vD1enzMFsPXiOr9HH5GKL5L8f2/yP8UqRsN3t3wtp6XwKJg";
      "KI8gThmDWT0zmEVxMDvJORfph28Sataruu/qvQRCTZ392h+d23yHLqC79e48fbTf3ao9x5527e1ej+wIIhkYynjF0Jy3KLXg";
      "pobQ+ZmTsV7GEmRyQHJXV+Geh7ygo3NE79vyrlCvyTOTuQnhMsX22SVbptR/s0CdJvUq3kh0NHbb1Elf40DyNuta+eYunnIX";
      "rXqU/rBEqI9a1IyFhOmaX5bRWVuk7nFPip+FNjzAb7/Sw4CjqXOkNGU8M2eWHxn25R3O3M/zTtXHfy0+/1hGDfvKztThXuQR";
      "nb8BiqyaLTQEAAA="
    ]
  };
  {
    .name = ".fini";
    .address = 0xb74;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0xb88;
    .size = 0x32;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML84P60kPi0nP7Ek3kTXUC9ZLzkzRy+ZgcGAAQDzDnUDMgAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xbbc;
    .size = 0x6c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrbOYGBg4AHilt///1cwMjC4/Pn/vwHIXwKkpwDpK0B6BZAW+Pv//x4gnQKkH4DUA+kvQPoNkOYA6hP5";
      "9/+/ApDWANIWQHoJkPYB0ib///9PAdIA7UMV1GwAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xc28;
    .size = 0x13c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiPf8/v/fBCTpyC4HEtMBYo4///8bQPWAxByAWAUoZgMVUwDiECD2AYp5";
      "gPXyKcxlmcfsNJnJ797dy3wwfRVAXANUw4JkVg8QdwDFMqBiIkC8AIjvAMU0IGYJzGWaxwgS3wHEb4DiIDaDM0QcZMYFIH4B";
      "FC9AMuMJEAf8/f9/AkggCaH2DxCfAIq3QNWC7BBgZGBg+fX//xSIfQZz2eaxOk9mmcI8lSme697dq5ev8DE4ckPUAwDjT38z";
      "PAEAAA=="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xd64;
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
      "H4sIAAAAAAAA/7WQqxLCMBBFt9DwZgZBh/L4RwyCTwKHRFYikchKZA2i02nDMPdEpJ41Z+7eZO8miamuMIF3uIDnkbhEn+bi";
      "NpxvdXOPnsAdLPAPPf/T+eOPt4G0o18NRWLtiT9DvyBrWA4zi4sx9vbKZ4xd4BqO4Sbkubi/cvHeBZz28huv94SjHbpM1fTo";
      "8M8V+oFfo1P7T30BE9yhpPABAAA="
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
