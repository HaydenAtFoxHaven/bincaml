var $Global_131088_131096: bv64;
var $Global_131104_131112: bv64;
var $Global_131112_131120: bv64;
var $Global_131120_131128: bv64;
declare-fun $__VERIFIER_nondet_uint : () -> bv32;
declare-fun $__VERIFIER_nondet_char : () -> bv8;

prog entry @main_1856;

proc @main_1856
  (R0_in:bv64, R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R16_in:bv64, R17_in:bv64, R18_in:bv64, R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R1_out:bv64, R29_out:bv64, R3_out:bv64, _PC_out:bv64)
  { .name = "main"; .address = 0x740; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x740; .originalLabel = "DAKDt32TRmCIAhR9+SJVqQ=="} [
    var Stack_n48_n40: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n40_n32: bv64 := R30_in:bv64 { .label = "1856_2" };
    var Stack_n32_n24: bv64 := R19_in:bv64 { .label = "1864_1" };
    var Stack_n24_n16: bv64 := R20_in:bv64 { .label = "1864_2" };
    var Stack_n16_n8: bv64 := R21_in:bv64 { .label = "1868_0" };
    var load24_1: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv32 := $__VERIFIER_nondet_uint();
    var R19_2: bv64 := zero_extend(32, R0_2:bv32) { .label = "1876_0" };
    var load25_1: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv64 := zero_extend(56, $__VERIFIER_nondet_char());
    var R21_2: bv64 := zero_extend(32, extract(32, 0, R0_4:bv64)) { .label = "1884_0" };
    var load24_2: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_6: bv32 := $__VERIFIER_nondet_uint();
    var R20_2: bv64 := zero_extend(32, R0_6:bv32) { .label = "1892_0" };
    var load25_2: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv8 := $__VERIFIER_nondet_char();
    var R3_2: bv64 := zero_extend(32, sign_extend(24, R0_8:bv8)) { .label = "1900_0" };
    goto(%phi_15, %phi_16);
  ];
  block %main_4 {.address = 0x7bc; .originalLabel = "aYsuYNHLRFyvZLU2WIvV9A=="} [
    var load14_1: bv64 := Stack_n16_n8:bv64 { .label = "1980_0_0" };
    var load15_1: bv64 := Stack_n32_n24:bv64 { .label = "1988_1_0" };
    var load16_1: bv64 := Stack_n24_n16:bv64 { .label = "1988_2_0" };
    var load17_1: bv64 := Stack_n48_n40:bv64 { .label = "1992_0_0" };
    var load18_1: bv64 := Stack_n40_n32:bv64 { .label = "1992_1_0" };
    var _PC_59: bv64 := _PC_57:bv64 { .label = "phiback" };
    var R29_54: bv64 := load17_1:bv64 { .label = "phiback" };
    var R31_54: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_54: bv64 := 0x20010:bv64 { .label = "phiback" };
    var R1_39: bv64 := R1_37:bv64 { .label = "phiback" };
    var R3_49: bv64 := R3_47:bv64 { .label = "phiback" };
    var R17_50: bv64 := load25_2:bv64 { .label = "phiback" };
    var R0_51: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_20: bv64 := load18_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_10 {.address = 0x7f4; .originalLabel = "haoRJIT+S7eP4irNxFaR5A=="} [
    var R30_16: bv64 := 0x744:bv64 { .label = "2036_0" };
    var (R0_retval_inlined_7:bv64, R17_44:bv64, R1_retval_inlined_11:bv64, R2_retval_inlined_15:bv64, R3_retval_inlined_17:bv64) := call @reach_error_2536 (R29_49:bv64, 0x744:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64)) { .label = "2036_2" };
    goto(%main_10_retval_inline);
  ];
  block %main_18 {.address = 0x7e4; .originalLabel = "Xtx9NpPbQOywVx7ITDJIMA=="} [
    goto(%phi_51, %phi_52);
  ];
  block %main_20 {.address = 0x7d4; .originalLabel = "nc1b0wjWQOiT9s1DrXzW5g=="} [
    var R20_26: bv64 := 0x0:bv64 { .label = "2004_0" };
    var (R0_38:bv64, R1_24:bv64, R29_41:bv64, R2_43:bv64, R3_34:bv64, R4_30:bv64, R5_30:bv64, R6_30:bv64, R7_30:bv64)
        := call @addflt_2736 (zero_extend(32, extract(32, 0, R19_38:bv64)), R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R18_in:bv64, 0x0:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), 0x750:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_2:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64);
    goto(%main_20_retval_inline);
  ];
  block %phi_15 {.originalLabel = "s2YTgsA9Sz2HJERo2dotig=="} [
    guard eq(extract(32, 0, R19_2:bv64), 0x0:bv32);
    goto(%phi_35, %phi_36);
  ];
  block %phi_16 {.originalLabel = "s2YTgsA9Sz2HJERo2dotig=="} [
    guard boolnot(eq(extract(32, 0, R19_2:bv64), 0x0:bv32));
    var (R0_11:bv64, R1_3:bv64, R2_12:bv64) := call @base2flt.part.0_2432 (zero_extend(32, extract(32, 0, R19_2:bv64)), zero_extend(32, sign_extend(24, extract(8, 0, R21_2:bv64))));
    goto(%phi_16_retval_inline);
  ];
  block %phi_18 {.originalLabel = "0VP9ZeN0Q3KA8+dfnaIK6g=="} [
    guard eq(extract(32, 0, R20_2:bv64), 0x0:bv32);
    var R19_38: bv64 := R19_11:bv64 { .label = "phiback" };
    var R2_42: bv64 := R2_12:bv64 { .label = "phiback" };
    goto(%main_20);
  ];
  block %phi_19 {.originalLabel = "0VP9ZeN0Q3KA8+dfnaIK6g=="} [
    guard boolnot(eq(extract(32, 0, R20_2:bv64), 0x0:bv32));
    var (R0_14:bv64, R1_5:bv64, R2_16:bv64) := call @base2flt.part.0_2432 (zero_extend(32, extract(32, 0, R20_2:bv64)), zero_extend(32, extract(32, 0, R3_2:bv64)));
    goto(%phi_19_retval_inline);
  ];
  block %phi_21 {.originalLabel = "cuUJg6HgRM2pxbig3AVVdw=="} [
    guard eq(extract(32, 0, R0_14:bv64), 0x0:bv32);
    var R19_38: bv64 := R19_11:bv64 { .label = "phiback" };
    var R2_42: bv64 := R2_16:bv64 { .label = "phiback" };
    goto(%main_20);
  ];
  block %phi_22 {.originalLabel = "cuUJg6HgRM2pxbig3AVVdw=="} [
    guard boolnot(eq(extract(32, 0, R0_14:bv64), 0x0:bv32));
    var (R0_19:bv64, R1_7:bv64, R29_19:bv64, R2_20:bv64, R3_11:bv64, R4_18:bv64, R5_18:bv64, R6_18:bv64, R7_18:bv64)
        := call @addflt_2736 (zero_extend(32, extract(32, 0, R19_11:bv64)), R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R18_in:bv64, zero_extend(32, extract(32, 0, R0_14:bv64)), bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), 0x74c:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_2:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64);
    goto(%phi_22_retval_inline);
  ];
  block %phi_23 [
    guard eq(extract(32, 0, R19_11:bv64), 0x0:bv32);
    var _PC_46: bv64 := _PC_20:bv64 { .label = "phiback" };
    var R29_43: bv64 := R29_19:bv64 { .label = "phiback" };
    var R20_28: bv64 := R20_10:bv64 { .label = "phiback" };
    var R0_40: bv64 := R0_19:bv64 { .label = "phiback" };
    var R1_26: bv64 := R1_7:bv64 { .label = "phiback" };
    var R19_40: bv64 := R19_11:bv64 { .label = "phiback" };
    var R3_36: bv64 := R3_11:bv64 { .label = "phiback" };
    var R2_45: bv64 := R2_20:bv64 { .label = "phiback" };
    goto(%main_18);
  ];
  block %phi_24 [
    guard boolnot(eq(extract(32, 0, R19_11:bv64), 0x0:bv32));
    goto(%phi_25, %phi_26);
  ];
  block %phi_25 [
    guard bvugt(extract(32, 0, R19_11:bv64), extract(32, 0, R0_19:bv64));
    var _PC_52: bv64 := _PC_20:bv64 { .label = "phiback" };
    var R29_49: bv64 := R29_19:bv64 { .label = "phiback" };
    var R20_34: bv64 := R20_10:bv64 { .label = "phiback" };
    var R0_46: bv64 := R0_19:bv64 { .label = "phiback" };
    var R1_32: bv64 := R1_7:bv64 { .label = "phiback" };
    var R19_46: bv64 := R19_11:bv64 { .label = "phiback" };
    var R3_42: bv64 := R3_11:bv64 { .label = "phiback" };
    var R2_51: bv64 := R2_20:bv64 { .label = "phiback" };
    goto(%main_10);
  ];
  block %phi_26 [
    guard bvule(extract(32, 0, R19_11:bv64), extract(32, 0, R0_19:bv64));
    goto(%phi_27, %phi_28);
  ];
  block %phi_27 [
    guard bvugt(extract(32, 0, R20_10:bv64), extract(32, 0, R0_19:bv64));
    var _PC_52: bv64 := _PC_20:bv64 { .label = "phiback" };
    var R29_49: bv64 := R29_19:bv64 { .label = "phiback" };
    var R20_34: bv64 := R20_10:bv64 { .label = "phiback" };
    var R0_46: bv64 := R0_19:bv64 { .label = "phiback" };
    var R1_32: bv64 := R1_7:bv64 { .label = "phiback" };
    var R19_46: bv64 := R19_11:bv64 { .label = "phiback" };
    var R3_42: bv64 := R3_11:bv64 { .label = "phiback" };
    var R2_51: bv64 := R2_20:bv64 { .label = "phiback" };
    goto(%main_10);
  ];
  block %phi_28 [
    guard bvule(extract(32, 0, R20_10:bv64), extract(32, 0, R0_19:bv64));
    var _PC_57: bv64 := _PC_20:bv64 { .label = "phiback" };
    var R1_37: bv64 := R1_7:bv64 { .label = "phiback" };
    var R3_47: bv64 := R3_11:bv64 { .label = "phiback" };
    goto(%main_4);
  ];
  block %phi_35 [
    guard eq(extract(32, 0, R20_2:bv64), 0x0:bv32);
    var R19_38: bv64 := 0x0:bv64 { .label = "phiback" };
    var R2_42: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%main_20);
  ];
  block %phi_36 [
    guard boolnot(eq(extract(32, 0, R20_2:bv64), 0x0:bv32));
    var (R0_30:bv64, R1_19:bv64, R2_34:bv64) := call @base2flt.part.0_2432 (zero_extend(32, extract(32, 0, R20_2:bv64)), zero_extend(32, extract(32, 0, R3_2:bv64)));
    goto(%phi_36_retval_inline);
  ];
  block %phi_38 {.originalLabel = "IAAtoEDnRb+bXePBUSX1Pg=="} [
    guard eq(extract(32, 0, R0_30:bv64), 0x0:bv32);
    var R19_38: bv64 := R19_30:bv64 { .label = "phiback" };
    var R2_42: bv64 := R2_34:bv64 { .label = "phiback" };
    goto(%main_20);
  ];
  block %phi_39 {.originalLabel = "IAAtoEDnRb+bXePBUSX1Pg=="} [
    guard boolnot(eq(extract(32, 0, R0_30:bv64), 0x0:bv32));
    var R20_24: bv64 := zero_extend(32, extract(32, 0, R19_30:bv64)) { .label = "2068_0" };
    var (R0_35:bv64, R1_21:bv64, R29_36:bv64, R2_38:bv64, R3_29:bv64, R4_26:bv64, R5_26:bv64, R6_26:bv64, R7_26:bv64)
        := call @addflt_2736 (0x0:bv64, R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R18_in:bv64, zero_extend(32, extract(32, 0, R0_30:bv64)), bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), 0x754:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_2:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64);
    goto(%phi_39_retval_inline);
  ];
  block %phi_51 {.originalLabel = "Xtx9NpPbQOywVx7ITDJIMA=="} [
    guard eq(extract(32, 0, R19_40:bv64), extract(32, 0, R0_40:bv64));
    var _PC_57: bv64 := _PC_46:bv64 { .label = "phiback" };
    var R1_37: bv64 := R1_26:bv64 { .label = "phiback" };
    var R3_47: bv64 := R3_36:bv64 { .label = "phiback" };
    goto(%main_4);
  ];
  block %phi_52 {.originalLabel = "Xtx9NpPbQOywVx7ITDJIMA=="} [
    guard boolnot(eq(extract(32, 0, R19_40:bv64), extract(32, 0, R0_40:bv64)));
    goto(%phi_53, %phi_54);
  ];
  block %phi_53 [
    guard eq(extract(32, 0, R0_40:bv64), extract(32, 0, R20_28:bv64));
    var _PC_57: bv64 := _PC_46:bv64 { .label = "phiback" };
    var R1_37: bv64 := R1_26:bv64 { .label = "phiback" };
    var R3_47: bv64 := R3_36:bv64 { .label = "phiback" };
    goto(%main_4);
  ];
  block %phi_54 [
    guard boolnot(eq(extract(32, 0, R0_40:bv64), extract(32, 0, R20_28:bv64)));
    var _PC_52: bv64 := _PC_46:bv64 { .label = "phiback" };
    var R29_49: bv64 := R29_43:bv64 { .label = "phiback" };
    var R20_34: bv64 := R20_28:bv64 { .label = "phiback" };
    var R0_46: bv64 := R0_40:bv64 { .label = "phiback" };
    var R1_32: bv64 := R1_26:bv64 { .label = "phiback" };
    var R19_46: bv64 := R19_40:bv64 { .label = "phiback" };
    var R3_42: bv64 := R3_36:bv64 { .label = "phiback" };
    var R2_51: bv64 := R2_45:bv64 { .label = "phiback" };
    goto(%main_10);
  ];
  block %main_10_retval_inline [
    var _PC_59: bv64 := _PC_52:bv64 { .label = "phiback" };
    var R29_54: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffc0:bv64) { .label = "phiback" };
    var R31_54: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64) { .label = "phiback" };
    var R16_54: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R1_39: bv64 := 0xc10:bv64 { .label = "phiback" };
    var R3_49: bv64 := 0xc00:bv64 { .label = "phiback" };
    var R17_50: bv64 := R17_44:bv64 { .label = "phiback" };
    var R0_51: bv64 := 0xc28:bv64 { .label = "phiback" };
    var R30_20: bv64 := R30_16:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_36_retval_inline [
    var R19_30: bv64 := zero_extend(32, extract(32, 0, R0_30:bv64)) { .label = "2056_0" };
    goto(%phi_38, %phi_39);
  ];
  block %phi_19_retval_inline [
    var R20_10: bv64 := zero_extend(32, extract(32, 0, R0_14:bv64)) { .label = "1940_0" };
    goto(%phi_21, %phi_22);
  ];
  block %phi_16_retval_inline [
    var R19_11: bv64 := zero_extend(32, extract(32, 0, R0_11:bv64)) { .label = "1920_0" };
    goto(%phi_18, %phi_19);
  ];
  block %main_20_retval_inline [
    var _PC_44: bv64 := _PC_in:bv64 { .label = "inlineret" };
    var _PC_46: bv64 := _PC_44:bv64 { .label = "phiback" };
    var R29_43: bv64 := R29_41:bv64 { .label = "phiback" };
    var R20_28: bv64 := R20_26:bv64 { .label = "phiback" };
    var R0_40: bv64 := R0_38:bv64 { .label = "phiback" };
    var R1_26: bv64 := R1_24:bv64 { .label = "phiback" };
    var R19_40: bv64 := R19_38:bv64 { .label = "phiback" };
    var R3_36: bv64 := R3_34:bv64 { .label = "phiback" };
    var R2_45: bv64 := R2_43:bv64 { .label = "phiback" };
    goto(%main_18);
  ];
  block %phi_39_retval_inline [
    var _PC_39: bv64 := _PC_in:bv64 { .label = "inlineret" };
    var _PC_46: bv64 := _PC_39:bv64 { .label = "phiback" };
    var R29_43: bv64 := R29_36:bv64 { .label = "phiback" };
    var R20_28: bv64 := R20_24:bv64 { .label = "phiback" };
    var R0_40: bv64 := R0_35:bv64 { .label = "phiback" };
    var R1_26: bv64 := R1_21:bv64 { .label = "phiback" };
    var R19_40: bv64 := 0x0:bv64 { .label = "phiback" };
    var R3_36: bv64 := R3_29:bv64 { .label = "phiback" };
    var R2_45: bv64 := R2_38:bv64 { .label = "phiback" };
    goto(%main_18);
  ];
  block %phi_22_retval_inline [
    var _PC_20: bv64 := _PC_in:bv64 { .label = "inlineret" };
    goto(%phi_23, %phi_24);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_20:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_54:bv64) { .comment = "R31 preserved across calls" };
    return (R0_51:bv64, R16_54:bv64, R17_50:bv64, R1_39:bv64, R29_54:bv64, R3_49:bv64, _PC_59:bv64);
  ]
];


proc @reach_error_2536
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x9e8; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x9e8; .originalLabel = "xHfJSKuoRjSBxDu6qTz6BQ=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2536_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2536_2" };
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 = R30_in" };
    var load27_1: bv64 := $Global_131112_131120:bv64 { .label = "1796_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0xc28:bv64, load27_1:bv64, 0xc10:bv64, 0x3:bv64, 0xc00:bv64);
  ]
];


proc @addflt_2736
  (R0_in:bv64, R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R18_in:bv64, R1_in:bv64, R29_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64)
    -> (R0_out:bv64, R1_out:bv64, R29_out:bv64, R2_out:bv64, R3_out:bv64, R4_out:bv64, R5_out:bv64, R6_out:bv64, R7_out:bv64)
  { .name = "addflt"; .address = 0xab0; .returnBlock = "addflt_return" }
[
  block %addflt_entry {.address = 0xab0; .originalLabel = "iLUYipHRTM+Q2aRIBdwidg=="} [
    goto(%phi_4, %phi_5);
  ];
  block %addflt_8 {.address = 0xb50; .originalLabel = "4EkwHFDjQeqssZnv/aTrZg=="} [
    assert eq(R30_in:bv64, 0x744:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_6:bv64, R17_29:bv64, R1_retval_inlined_10:bv64, R2_retval_inlined_14:bv64, R3_retval_inlined_16:bv64) := call @reach_error_2536 (bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), 0x744:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .label = "2896_2" };
    goto(%addflt_8_retval_inline);
  ];
  block %addflt_20 {.address = 0xb20; .originalLabel = "lurT7pfjSKa6PPrDgxAgZQ=="} [
    var load28_1: bv64 := Stack_n16_n8:bv64 { .label = "2848_0_0" };
    var load29_1: bv64 := Stack_n8_0:bv64 { .label = "2848_1_0" };
    var R29_38: bv64 := load28_1:bv64 { .label = "phiback" };
    var R31_42: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_46: bv64 := R1_22:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_33:bv64 { .label = "phiback" };
    var R0_39: bv64 := R0_29:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_in:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_in:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_in:bv64 { .label = "phiback" };
    var R3_43: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_47: bv64 := R2_37:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %addflt_62 [
    var R0_9: bv64 := zero_extend(32, extract(32, 0, R2_6:bv64)) { .label = "2748_0" };
    goto(%phi_16, %phi_17);
  ];
  block %addflt_68 [
    goto(%phi_10, %phi_11);
  ];
  block %phi_4 {.originalLabel = "iLUYipHRTM+Q2aRIBdwidg=="} [
    guard bvult(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R2_6: bv64 := zero_extend(32, extract(32, 0, R1_in:bv64)) { .label = "phiback" };
    goto(%addflt_68);
  ];
  block %phi_5 {.originalLabel = "iLUYipHRTM+Q2aRIBdwidg=="} [
    guard bvuge(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R2_6: bv64 := zero_extend(32, extract(32, 0, R0_in:bv64)) { .label = "phiback" };
    goto(%addflt_68);
  ];
  block %phi_10 [
    guard bvult(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R1_13: bv64 := zero_extend(32, extract(32, 0, R0_in:bv64)) { .label = "phiback" };
    goto(%addflt_62);
  ];
  block %phi_11 [
    guard bvuge(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R1_13: bv64 := zero_extend(32, extract(32, 0, R1_in:bv64)) { .label = "phiback" };
    goto(%addflt_62);
  ];
  block %phi_16 [
    guard eq(extract(32, 0, R1_13:bv64), 0x0:bv32);
    var R29_38: bv64 := R29_in:bv64 { .label = "phiback" };
    var R31_42: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_46: bv64 := R1_13:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_in:bv64 { .label = "phiback" };
    var R0_39: bv64 := R0_9:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_in:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_in:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_in:bv64 { .label = "phiback" };
    var R3_43: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_47: bv64 := R2_6:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %phi_17 [
    guard boolnot(eq(extract(32, 0, R1_13:bv64), 0x0:bv32));
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2756_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2756_2" };
    var R4_14: bv64 := zero_extend(56, extract(32, 24, R2_6:bv64)) { .label = "2760_0" };
    var R3_14: bv64 := zero_extend(56, extract(32, 24, R1_13:bv64)) { .label = "2764_0" };
    goto(%phi_18, %phi_19);
  ];
  block %phi_18 [
    guard bvslt(extract(32, 0, R4_14:bv64), extract(32, 0, R3_14:bv64));
    var R0_35: bv64 := R0_9:bv64 { .label = "phiback" };
    var R1_42: bv64 := R1_13:bv64 { .label = "phiback" };
    var R3_39: bv64 := R3_14:bv64 { .label = "phiback" };
    var R2_43: bv64 := R2_6:bv64 { .label = "phiback" };
    goto(%addflt_8);
  ];
  block %phi_19 [
    guard bvsge(extract(32, 0, R4_14:bv64), extract(32, 0, R3_14:bv64));
    var R3_17: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_14:bv64), bvneg(extract(32, 0, R3_14:bv64)))) { .label = "2784_0" };
    var R1_19: bv64 := zero_extend(32, bvor(zero_extend(8, extract(24, 0, R1_13:bv64)), 0x1000000:bv32)) { .label = "2788_0" };
    goto(%phi_20, %phi_21);
  ];
  block %phi_20 [
    guard bvsgt(extract(32, 0, R3_17:bv64), 0x1f:bv32);
    assert eq(R30_in:bv64, 0x744:bv64) { .comment = "R30 = R30_in" };
    var load8_1: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "abort" };
    goto(%phi_40);
  ];
  block %phi_21 [
    guard bvsle(extract(32, 0, R3_17:bv64), 0x1f:bv32);
    var R1_22: bv64 := zero_extend(32, bvlshr(extract(32, 0, R1_19:bv64), zero_extend(27, extract(5, 0, R3_17:bv64)))) { .label = "2800_0" };
    goto(%phi_22, %phi_23);
  ];
  block %phi_22 [
    guard eq(extract(32, 0, R1_22:bv64), 0x0:bv32);
    var R4_33: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_29: bv64 := R0_9:bv64 { .label = "phiback" };
    var R2_37: bv64 := R2_6:bv64 { .label = "phiback" };
    goto(%addflt_20);
  ];
  block %phi_23 [
    guard boolnot(eq(extract(32, 0, R1_22:bv64), 0x0:bv32));
    var R2_21: bv32 := bvor(zero_extend(8, extract(24, 0, R2_6:bv64)), 0x1000000:bv32) { .label = "2812_0" };
    var R2_22: bv64 := zero_extend(32, bvadd(R2_21:bv32, extract(32, 0, R1_22:bv64))) { .label = "2816_0" };
    goto(%phi_24, %phi_25);
  ];
  block %phi_24 [
    guard boolnot(eq(extract(26, 25, R2_22:bv64), 0x1:bv1));
    goto(%phi_30, %phi_31);
  ];
  block %phi_25 [
    guard eq(extract(26, 25, R2_22:bv64), 0x1:bv1);
    goto(%phi_26, %phi_27);
  ];
  block %phi_26 [
    guard eq(extract(32, 0, R4_14:bv64), 0xff:bv32);
    var R4_33: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_29: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    var R2_37: bv64 := R2_22:bv64 { .label = "phiback" };
    goto(%addflt_20);
  ];
  block %phi_27 [
    guard boolnot(eq(extract(32, 0, R4_14:bv64), 0xff:bv32));
    var R4_25: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_14:bv64), 0x1:bv32)) { .label = "2836_0" };
    var R0_18: bv64 := zero_extend(32, bvor(zero_extend(8, extract(25, 1, R2_22:bv64)), bvshl(zero_extend(24, extract(8, 0, R4_25:bv64)), 0x18:bv32))) { .label = "2844_0" };
    var R4_33: bv64 := R4_25:bv64 { .label = "phiback" };
    var R0_29: bv64 := R0_18:bv64 { .label = "phiback" };
    var R2_37: bv64 := zero_extend(40, extract(25, 1, R2_22:bv64)) { .label = "phiback" };
    goto(%addflt_20);
  ];
  block %phi_30 [
    guard bvugt(extract(32, 0, R2_22:bv64), 0x1ffffff:bv32);
    var R0_35: bv64 := 0x1ffffff:bv64 { .label = "phiback" };
    var R1_42: bv64 := R1_22:bv64 { .label = "phiback" };
    var R3_39: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_43: bv64 := R2_22:bv64 { .label = "phiback" };
    goto(%addflt_8);
  ];
  block %phi_31 [
    guard bvule(extract(32, 0, R2_22:bv64), 0x1ffffff:bv32);
    var R0_25: bv64 := zero_extend(32, bvor(zero_extend(8, extract(24, 0, R2_22:bv64)), bvshl(zero_extend(24, extract(8, 0, R4_14:bv64)), 0x18:bv32))) { .label = "2876_0" };
    var load30_1: bv64 := Stack_n16_n8:bv64 { .label = "2880_0_0" };
    var load31_1: bv64 := Stack_n8_0:bv64 { .label = "2880_1_0" };
    var R29_38: bv64 := load30_1:bv64 { .label = "phiback" };
    var R31_42: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_46: bv64 := R1_22:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_39: bv64 := R0_25:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_in:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_in:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_in:bv64 { .label = "phiback" };
    var R3_43: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_47: bv64 := zero_extend(40, extract(24, 0, R2_22:bv64)) { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %phi_40 [
    var R29_38: bv64 := R29_31:bv64 { .label = "phiback" };
    var R31_42: bv64 := bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64) { .label = "phiback" };
    var R1_46: bv64 := R1_39:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_36:bv64 { .label = "phiback" };
    var R0_39: bv64 := R0_32:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_34:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_34:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_34:bv64 { .label = "phiback" };
    var R3_43: bv64 := R3_36:bv64 { .label = "phiback" };
    var R2_47: bv64 := R2_40:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %addflt_8_retval_inline [
    var R29_38: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R31_42: bv64 := bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64) { .label = "phiback" };
    var R1_46: bv64 := 0xc10:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_39: bv64 := 0xc28:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_in:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_in:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_in:bv64 { .label = "phiback" };
    var R3_43: bv64 := 0xc00:bv64 { .label = "phiback" };
    var R2_47: bv64 := 0x3:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %addflt_return [
    assert eq(R31_in:bv64, R31_42:bv64) { .comment = "R31 preserved across calls" };
    return (R0_39:bv64, R1_46:bv64, R29_38:bv64, R2_47:bv64, R3_43:bv64, R4_42:bv64, R5_40:bv64, R6_40:bv64, R7_40:bv64);
  ]
];


proc @base2flt.part.0_2432 (R0_in:bv64, R1_in:bv64) -> (R0_out:bv64, R1_out:bv64, R2_out:bv64)
  { .name = "base2flt.part.0"; .address = 0x980; .returnBlock = "base2flt.part.0_return" }
[
  block %base2flt.part.0_entry {.address = 0x980; .originalLabel = "MXoB8TkjRfKA2SN31rz8Dw=="} [
    goto(%phi_3, %phi_4);
  ];
  block %base2flt.part.0_4 {.address = 0x998; .originalLabel = "75hrFjapQsCxIhQJKjetCg=="} [
    var R1_24: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_23:bv64), 0x80:bv32)) { .label = "2456_0" };
    var R0_26: bv32 := bvand(extract(32, 0, R0_25:bv64), 0xfeffffff:bv32) { .label = "2460_0" };
    var R0_27: bv64 := zero_extend(32, bvor(R0_26:bv32, bvshl(zero_extend(24, extract(8, 0, R1_24:bv64)), 0x18:bv32))) { .label = "2464_0" };
    var R1_26: bv64 := R1_24:bv64 { .label = "phiback" };
    var R0_29: bv64 := R0_27:bv64 { .label = "phiback" };
    var R2_25: bv64 := R2_23:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_return);
  ];
  block %base2flt.part.0_loop1_18 {.address = 0x9b8; .originalLabel = "f0Wm2olES1a2uJHxCeSmCQ=="} [
    goto(%phi_17, %phi_18);
  ];
  block %base2flt.part.0_loop2_34 {.address = 0x9d8; .originalLabel = "VBzOM9ZlTqKmv0+LeCL/EQ=="} [
    goto(%phi_9, %phi_10);
  ];
  block %phi_3 {.originalLabel = "MXoB8TkjRfKA2SN31rz8Dw=="} [
    guard bvule(extract(32, 0, R0_in:bv64), 0xffffff:bv32);
    ( var R1_15: bv64 := R1_in:bv64,
      var R0_16: bv64 := R0_in:bv64 );
    goto(%base2flt.part.0_loop1_18);
  ];
  block %phi_4 {.originalLabel = "MXoB8TkjRfKA2SN31rz8Dw=="} [
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
  block %phi_9 {.originalLabel = "VBzOM9ZlTqKmv0+LeCL/EQ=="} [
    guard bvsle(extract(32, 0, R1_7:bv64), 0x7e:bv32);
    var R0_12: bv64 := zero_extend(33, extract(32, 1, R0_7:bv64)) { .label = "2504_0" };
    var R1_11: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_7:bv64), 0x1:bv32)) { .label = "2508_0" };
    goto(%phi_12, %phi_13);
  ];
  block %phi_10 {.originalLabel = "VBzOM9ZlTqKmv0+LeCL/EQ=="} [
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
  block %phi_17 {.originalLabel = "f0Wm2olES1a2uJHxCeSmCQ=="} [
    guard bvsge(extract(32, 0, R1_15:bv64), 0xffffff81:bv32);
    var R0_21: bv64 := zero_extend(32, bvshl(zero_extend(1, extract(31, 0, R0_16:bv64)), 0x1:bv32)) { .label = "2472_0" };
    var R1_19: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_15:bv64), 0xffffffff:bv32)) { .label = "2476_0" };
    goto(%phi_20, %phi_21);
  ];
  block %phi_18 {.originalLabel = "f0Wm2olES1a2uJHxCeSmCQ=="} [
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
      { .name = "_IO_stdin_used"; .address = 0xbf8; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xe04; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xe08; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20048; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0xa24; .size = 0xa0 };
      { .name = "_start"; .address = 0x840; .size = 0x1a0 };
      { .name = "addflt"; .address = 0xab0; .size = 0x540 };
      { .name = "assume_abort_if_not"; .address = 0xa10; .size = 0xa0 };
      { .name = "base2flt"; .address = 0xa40; .size = 0x380 };
      { .name = "main"; .address = 0x740; .size = 0x740 };
      { .name = "mulflt"; .address = 0xb60; .size = 0x420 };
      { .name = "reach_error"; .address = 0x9e8; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x960 ]; [ 0x1fdc0; 0x90c ]; [ 0x1ffd8; 0x740 ]; [ 0x20040; 0x20040 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2VY8tDcdgbnNrGmc3ulWad9bTfqzz8DAHLpo1gkAAAA" ]
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
      "H4sIAAAAAAAA/9vxl5EBBJhZwBRDAieEPoAmzgMVv/EfVdyBHUozMKGKQ/kHoOoZgeJQKTA4gSTOiiR+AUmcHUn8AZI4J5I4";
      "AAi+cZLAAAAA"
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
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBNrGBim/K0+uOIAc/w1ANGvkMgYAAAA" ]
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
    .size = 0x4a4;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/4VTTWgTYRCdb7+AQrw0G1CKNtm0B7te0hKUHqSbRchBLzV7UBCatjeDh9wKiSSlvYgeulhQUGgEkaZH6VXb";
      "2kuhN6sFRSQp/hRaIZAGXNg0vtmYtgSLh+Fl583MvjezaWTflBqS7FpSlOoqOdVm80lNkv4VWAfuAfeBn4HyPKlJH8XKUtVf";
      "9JA6RTTHtXMK54J6RUo9hxzXlwXFKoyoXeM6POcVSl9UyJoH7giy6qrhEBVu1pLxUiO7trAiR7dUPAcR3CeAS+jlvuJB0wpR";
      "MJ0C3kfuw0Ezxu/j947+1WF4OdL30ctzedZLcPB0NhSWH0+KC1R434P4LmmxIg1nu5fsH9hJmahKewlHgvMhbOygiPDyOwnH";
      "IFp6itms+6TZJGiWwsIWQA04TLS7QmRVMEMrJ5wxzKhKsUhKaIvndNZrRBsRN78ZPzP1UHPjj1dRv41es5pwxr1e5bC3kX3b";
      "uqWfHBX9qUh8yBB0xdP7LeEUUN+abzjj8PEJEcaOUhExVPMbTiP7bqHTy5f/7E4pLwdCpKQf4J7KSus331gjpYsmTwUoJXTP";
      "12QoqfloxOObTWvYFQN3gXwnj88J5ruY78eNh3+LzL0WH2h5Wy5JolmBYI8EnKCorRlRm4pRexxzrsIPbhJr13Nd7B+5X8i1";
      "9fN32vbQrxx5WMeNuoiCx3WV4LFT13FfC+jp9NW5hxCJdCRa6BbRqe6yVPS4pBjrupY7l+xFsL55kukNiR3eocA0yesanR7M";
      "5yhzg3N9a91j0GyCM5E3SfhNsX553pUZeLFM6J2BXuaNlE9vZFe9m3pa4Q3/lfQOdHby7KeOW7/Cbn4eHO3nuF72xHr7oJPr";
      "Z1Kmf7ooR/KuyDzC7pjPkzJwCb/DrA9BnsbTg5UJ47WZKz4z3FubmLlbggbuw7dpTT+XI4Z7e3PicFdSb2ti/AOXFXaBpAQA";
      "AA=="
    ]
  };
  {
    .name = ".fini";
    .address = 0xbe4;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0xbf8;
    .size = 0x32;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML84P60kPi0nP7Ek3lDXSC9ZLzkzRy+ZgcGAAQC23DiNMgAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xc2c;
    .size = 0x74;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrYuYGBg4AVikd///69hBNJ//v/vAPJLgPQcIL0ESG8A0g+A9BEgbfL3//8XQDoESP8B0nuAtABQ3xMg";
      "rQGkfwBpB5A5//7/jwDSLUA6B0ib/P//fwaQBgAflo0ndAAAAA=="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xca0;
    .size = 0x168;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiFt+//9vApJ0ZJcDiekA8QWgmAFUD0jMAYjfAMVsoGIKQBwCxCJ//v/3";
      "AOvlU5jLMo/ZaTKT3727l/lg+iqA2AWohgXJrB4gDgCKZUDFRIB4ARAvAYppQMwSmMs0jxEkvgOItwDFQWwGZ4T4BSDegCYO";
      "MvsFVH0B1GyQeX9A9v79/38FSMANojb83l0+BicI240LxHHkBunXYGRgmAJU24Kk3wYolvDz//8XELcZzGWbx+o8mWUK81Sm";
      "eKDWq5evgHRD1AMAe28hcWgBAAA="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xe08;
    .size = 0x20;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAGJGIHb3C2UAAWYgZmeAAAA9kbzyIAAAAA==" ]
  };
  {
    .name = ".init_array";
    .address = 0x1fdb8;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/0vgZAADAAE6USAIAAAA" ]
  };
  {
    .name = ".fini_array";
    .address = 0x1fdc0;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/+PhZAADAPWPFacIAAAA" ]
  };
  {
    .name = ".dynamic";
    .address = 0x1fdc8;
    .size = 0x1f0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/7WQqxLCMBBFt9DwZgZBh/L4RyyfBA6JrEQikYgKZA2i02nDMPdEpJ41Z+7eZO8miakuMIE3uICnkbhEl3Nx";
      "G863urlHT+AOFviHnv/p/PHH60Da0a+GIrH2wJ+hn5A1LIeZxcUYe3vlM8bOcA3HcBPyXNxfuXjvAk57+Y3Xe8LRDv1K1fTo";
      "8M8V+o5fo1P7T30BAqqlcfABAAA="
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
