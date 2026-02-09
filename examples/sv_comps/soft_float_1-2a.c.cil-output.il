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
  block %main_entry {.address = 0x740; .originalLabel = "6G/5W043QneFQqBBUD349Q=="} [
    var Stack_n48_n40: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n40_n32: bv64 := R30_in:bv64 { .label = "1856_2" };
    var Stack_n32_n24: bv64 := R19_in:bv64 { .label = "1864_1" };
    var Stack_n24_n16: bv64 := R20_in:bv64 { .label = "1864_2" };
    var Stack_n16_n8: bv64 := R21_in:bv64 { .label = "1868_0" };
    var load27_1: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv32 := $__VERIFIER_nondet_uint();
    var R19_2: bv64 := zero_extend(32, R0_2:bv32) { .label = "1876_0" };
    var load13_1: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv64 := zero_extend(56, $__VERIFIER_nondet_char());
    var R21_2: bv64 := zero_extend(32, extract(32, 0, R0_4:bv64)) { .label = "1884_0" };
    var load27_2: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_6: bv32 := $__VERIFIER_nondet_uint();
    var R20_2: bv64 := zero_extend(32, R0_6:bv32) { .label = "1892_0" };
    var load13_2: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv8 := $__VERIFIER_nondet_char();
    var R3_2: bv64 := zero_extend(32, sign_extend(24, R0_8:bv8)) { .label = "1900_0" };
    goto(%phi_15, %phi_16);
  ];
  block %main_4 {.address = 0x7bc; .originalLabel = "hie6o1McROmnSe+6MpffqA=="} [
    var load6_1: bv64 := Stack_n16_n8:bv64 { .label = "1980_0_0" };
    var load7_1: bv64 := Stack_n32_n24:bv64 { .label = "1988_1_0" };
    var load8_1: bv64 := Stack_n24_n16:bv64 { .label = "1988_2_0" };
    var load9_1: bv64 := Stack_n48_n40:bv64 { .label = "1992_0_0" };
    var load10_1: bv64 := Stack_n40_n32:bv64 { .label = "1992_1_0" };
    var _PC_59: bv64 := _PC_57:bv64 { .label = "phiback" };
    var R29_54: bv64 := load9_1:bv64 { .label = "phiback" };
    var R31_54: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_54: bv64 := 0x20010:bv64 { .label = "phiback" };
    var R1_39: bv64 := R1_37:bv64 { .label = "phiback" };
    var R3_49: bv64 := R3_47:bv64 { .label = "phiback" };
    var R17_50: bv64 := load13_2:bv64 { .label = "phiback" };
    var R0_51: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_20: bv64 := load10_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_10 {.address = 0x7f4; .originalLabel = "sCQ6TeHhTKa4+W09Sf81sA=="} [
    var R30_16: bv64 := 0x744:bv64 { .label = "2036_0" };
    var (R0_retval_inlined_7:bv64, R17_44:bv64, R1_retval_inlined_11:bv64, R2_retval_inlined_15:bv64, R3_retval_inlined_17:bv64) := call @reach_error_2536 (R29_49:bv64, 0x744:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64)) { .label = "2036_2" };
    goto(%main_10_retval_inline);
  ];
  block %main_18 {.address = 0x7e4; .originalLabel = "Z96i/e/nR2qRlIKYqw3klg=="} [
    goto(%phi_51, %phi_52);
  ];
  block %main_20 {.address = 0x7d4; .originalLabel = "6sQgRYdeS4+ccQArJVYKSg=="} [
    var R20_26: bv64 := 0x0:bv64 { .label = "2004_0" };
    var (R0_38:bv64, R1_24:bv64, R29_41:bv64, R2_43:bv64, R3_34:bv64, R4_30:bv64, R5_30:bv64, R6_30:bv64, R7_30:bv64)
        := call @addflt_2720 (zero_extend(32, extract(32, 0, R19_38:bv64)), R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R18_in:bv64, 0x0:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), 0x750:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_2:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64);
    goto(%main_20_retval_inline);
  ];
  block %phi_15 {.originalLabel = "YYhuiMBfStulYtMJqiG6/w=="} [
    guard eq(extract(32, 0, R19_2:bv64), 0x0:bv32);
    goto(%phi_35, %phi_36);
  ];
  block %phi_16 {.originalLabel = "YYhuiMBfStulYtMJqiG6/w=="} [
    guard boolnot(eq(extract(32, 0, R19_2:bv64), 0x0:bv32));
    var (R0_11:bv64, R1_3:bv64, R2_12:bv64) := call @base2flt.part.0_2432 (zero_extend(32, extract(32, 0, R19_2:bv64)), zero_extend(32, sign_extend(24, extract(8, 0, R21_2:bv64))));
    goto(%phi_16_retval_inline);
  ];
  block %phi_18 {.originalLabel = "VVSUknqqTgW03SsJ99ip7Q=="} [
    guard eq(extract(32, 0, R20_2:bv64), 0x0:bv32);
    var R19_38: bv64 := R19_11:bv64 { .label = "phiback" };
    var R2_42: bv64 := R2_12:bv64 { .label = "phiback" };
    goto(%main_20);
  ];
  block %phi_19 {.originalLabel = "VVSUknqqTgW03SsJ99ip7Q=="} [
    guard boolnot(eq(extract(32, 0, R20_2:bv64), 0x0:bv32));
    var (R0_14:bv64, R1_5:bv64, R2_16:bv64) := call @base2flt.part.0_2432 (zero_extend(32, extract(32, 0, R20_2:bv64)), zero_extend(32, extract(32, 0, R3_2:bv64)));
    goto(%phi_19_retval_inline);
  ];
  block %phi_21 {.originalLabel = "zRhrESLXTRSi8uOX3OSuxA=="} [
    guard eq(extract(32, 0, R0_14:bv64), 0x0:bv32);
    var R19_38: bv64 := R19_11:bv64 { .label = "phiback" };
    var R2_42: bv64 := R2_16:bv64 { .label = "phiback" };
    goto(%main_20);
  ];
  block %phi_22 {.originalLabel = "zRhrESLXTRSi8uOX3OSuxA=="} [
    guard boolnot(eq(extract(32, 0, R0_14:bv64), 0x0:bv32));
    var (R0_19:bv64, R1_7:bv64, R29_19:bv64, R2_20:bv64, R3_11:bv64, R4_18:bv64, R5_18:bv64, R6_18:bv64, R7_18:bv64)
        := call @addflt_2720 (zero_extend(32, extract(32, 0, R19_11:bv64)), R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R18_in:bv64, zero_extend(32, extract(32, 0, R0_14:bv64)), bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), 0x74c:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_2:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64);
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
  block %phi_38 {.originalLabel = "m0/oHJpdRyeb/45RQPRitA=="} [
    guard eq(extract(32, 0, R0_30:bv64), 0x0:bv32);
    var R19_38: bv64 := R19_30:bv64 { .label = "phiback" };
    var R2_42: bv64 := R2_34:bv64 { .label = "phiback" };
    goto(%main_20);
  ];
  block %phi_39 {.originalLabel = "m0/oHJpdRyeb/45RQPRitA=="} [
    guard boolnot(eq(extract(32, 0, R0_30:bv64), 0x0:bv32));
    var R20_24: bv64 := zero_extend(32, extract(32, 0, R19_30:bv64)) { .label = "2068_0" };
    var (R0_35:bv64, R1_21:bv64, R29_36:bv64, R2_38:bv64, R3_29:bv64, R4_26:bv64, R5_26:bv64, R6_26:bv64, R7_26:bv64)
        := call @addflt_2720 (0x0:bv64, R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R18_in:bv64, zero_extend(32, extract(32, 0, R0_30:bv64)), bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), 0x754:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_2:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64);
    goto(%phi_39_retval_inline);
  ];
  block %phi_51 {.originalLabel = "Z96i/e/nR2qRlIKYqw3klg=="} [
    guard eq(extract(32, 0, R19_40:bv64), extract(32, 0, R0_40:bv64));
    var _PC_57: bv64 := _PC_46:bv64 { .label = "phiback" };
    var R1_37: bv64 := R1_26:bv64 { .label = "phiback" };
    var R3_47: bv64 := R3_36:bv64 { .label = "phiback" };
    goto(%main_4);
  ];
  block %phi_52 {.originalLabel = "Z96i/e/nR2qRlIKYqw3klg=="} [
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
    var R1_39: bv64 := 0xbf8:bv64 { .label = "phiback" };
    var R3_49: bv64 := 0xbe8:bv64 { .label = "phiback" };
    var R17_50: bv64 := R17_44:bv64 { .label = "phiback" };
    var R0_51: bv64 := 0xc10:bv64 { .label = "phiback" };
    var R30_20: bv64 := R30_16:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_16_retval_inline [
    var R19_11: bv64 := zero_extend(32, extract(32, 0, R0_11:bv64)) { .label = "1920_0" };
    goto(%phi_18, %phi_19);
  ];
  block %phi_36_retval_inline [
    var R19_30: bv64 := zero_extend(32, extract(32, 0, R0_30:bv64)) { .label = "2056_0" };
    goto(%phi_38, %phi_39);
  ];
  block %phi_19_retval_inline [
    var R20_10: bv64 := zero_extend(32, extract(32, 0, R0_14:bv64)) { .label = "1940_0" };
    goto(%phi_21, %phi_22);
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
  block %reach_error_entry {.address = 0x9e8; .originalLabel = "pSSjd0J7TU6mj84tSX1H9A=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2536_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2536_2" };
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 = R30_in" };
    var load14_1: bv64 := $Global_131112_131120:bv64 { .label = "1796_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0xc10:bv64, load14_1:bv64, 0xbf8:bv64, 0x3:bv64, 0xbe8:bv64);
  ]
];


proc @addflt_2720
  (R0_in:bv64, R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R18_in:bv64, R1_in:bv64, R29_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64)
    -> (R0_out:bv64, R1_out:bv64, R29_out:bv64, R2_out:bv64, R3_out:bv64, R4_out:bv64, R5_out:bv64, R6_out:bv64, R7_out:bv64)
  { .name = "addflt"; .address = 0xaa0; .returnBlock = "addflt_return" }
[
  block %addflt_entry {.address = 0xaa0; .originalLabel = "r+rWzGw4TWW5Z+Jdt3e74g=="} [
    goto(%phi_4, %phi_5);
  ];
  block %addflt_8 {.address = 0xb40; .originalLabel = "xTLlpwXDSsSYErEyhpr3Nw=="} [
    assert eq(R30_in:bv64, 0x744:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_6:bv64, R17_29:bv64, R1_retval_inlined_10:bv64, R2_retval_inlined_14:bv64, R3_retval_inlined_16:bv64) := call @reach_error_2536 (bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), 0x744:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .label = "2880_2" };
    goto(%addflt_8_retval_inline);
  ];
  block %addflt_20 {.address = 0xb10; .originalLabel = "9kFkT7V3RsCZ18H0hrAA8A=="} [
    var load30_1: bv64 := Stack_n16_n8:bv64 { .label = "2832_0_0" };
    var load31_1: bv64 := Stack_n8_0:bv64 { .label = "2832_1_0" };
    var R29_38: bv64 := load30_1:bv64 { .label = "phiback" };
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
    var R0_9: bv64 := zero_extend(32, extract(32, 0, R2_6:bv64)) { .label = "2732_0" };
    goto(%phi_16, %phi_17);
  ];
  block %addflt_68 [
    goto(%phi_10, %phi_11);
  ];
  block %phi_4 {.originalLabel = "r+rWzGw4TWW5Z+Jdt3e74g=="} [
    guard bvult(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R2_6: bv64 := zero_extend(32, extract(32, 0, R1_in:bv64)) { .label = "phiback" };
    goto(%addflt_68);
  ];
  block %phi_5 {.originalLabel = "r+rWzGw4TWW5Z+Jdt3e74g=="} [
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
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2740_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2740_2" };
    var R4_14: bv64 := zero_extend(56, extract(32, 24, R2_6:bv64)) { .label = "2744_0" };
    var R3_14: bv64 := zero_extend(56, extract(32, 24, R1_13:bv64)) { .label = "2748_0" };
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
    var R3_17: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_14:bv64), bvneg(extract(32, 0, R3_14:bv64)))) { .label = "2768_0" };
    var R1_19: bv64 := zero_extend(32, bvor(zero_extend(8, extract(24, 0, R1_13:bv64)), 0x1000000:bv32)) { .label = "2772_0" };
    goto(%phi_20, %phi_21);
  ];
  block %phi_20 [
    guard bvsgt(extract(32, 0, R3_17:bv64), 0x1f:bv32);
    assert eq(R30_in:bv64, 0x744:bv64) { .comment = "R30 = R30_in" };
    var load23_1: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "abort" };
    goto(%phi_40);
  ];
  block %phi_21 [
    guard bvsle(extract(32, 0, R3_17:bv64), 0x1f:bv32);
    var R1_22: bv64 := zero_extend(32, bvlshr(extract(32, 0, R1_19:bv64), zero_extend(27, extract(5, 0, R3_17:bv64)))) { .label = "2784_0" };
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
    var R2_21: bv32 := bvor(zero_extend(8, extract(24, 0, R2_6:bv64)), 0x1000000:bv32) { .label = "2796_0" };
    var R2_22: bv64 := zero_extend(32, bvadd(R2_21:bv32, extract(32, 0, R1_22:bv64))) { .label = "2800_0" };
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
    var R4_25: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_14:bv64), 0x1:bv32)) { .label = "2820_0" };
    var R0_18: bv64 := zero_extend(32, bvor(zero_extend(8, extract(25, 1, R2_22:bv64)), bvshl(zero_extend(24, extract(8, 0, R4_25:bv64)), 0x18:bv32))) { .label = "2828_0" };
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
    var R0_25: bv64 := zero_extend(32, bvor(zero_extend(8, extract(24, 0, R2_22:bv64)), bvshl(zero_extend(24, extract(8, 0, R4_14:bv64)), 0x18:bv32))) { .label = "2860_0" };
    var load28_1: bv64 := Stack_n16_n8:bv64 { .label = "2864_0_0" };
    var load29_1: bv64 := Stack_n8_0:bv64 { .label = "2864_1_0" };
    var R29_38: bv64 := load28_1:bv64 { .label = "phiback" };
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
    var R1_46: bv64 := 0xbf8:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_14:bv64 { .label = "phiback" };
    var R0_39: bv64 := 0xc10:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_in:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_in:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_in:bv64 { .label = "phiback" };
    var R3_43: bv64 := 0xbe8:bv64 { .label = "phiback" };
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
  block %base2flt.part.0_entry {.address = 0x980; .originalLabel = "7mGhQtHCRJaqlrmtSJOUkQ=="} [
    goto(%phi_3, %phi_4);
  ];
  block %base2flt.part.0_4 {.address = 0x998; .originalLabel = "1DsJcV9jQrKQiw6+01HesQ=="} [
    var R1_24: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_23:bv64), 0x80:bv32)) { .label = "2456_0" };
    var R0_26: bv32 := bvand(extract(32, 0, R0_25:bv64), 0xfeffffff:bv32) { .label = "2460_0" };
    var R0_27: bv64 := zero_extend(32, bvor(R0_26:bv32, bvshl(zero_extend(24, extract(8, 0, R1_24:bv64)), 0x18:bv32))) { .label = "2464_0" };
    var R1_26: bv64 := R1_24:bv64 { .label = "phiback" };
    var R0_29: bv64 := R0_27:bv64 { .label = "phiback" };
    var R2_25: bv64 := R2_23:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_return);
  ];
  block %base2flt.part.0_loop1_18 {.address = 0x9b8; .originalLabel = "iSGqWftgSQKUjxsoExBWuQ=="} [
    goto(%phi_17, %phi_18);
  ];
  block %base2flt.part.0_loop2_34 {.address = 0x9d8; .originalLabel = "7kGDkD9PTUu99FHCIXHvZw=="} [
    goto(%phi_9, %phi_10);
  ];
  block %phi_3 {.originalLabel = "7mGhQtHCRJaqlrmtSJOUkQ=="} [
    guard bvule(extract(32, 0, R0_in:bv64), 0xffffff:bv32);
    ( var R1_15: bv64 := R1_in:bv64,
      var R0_16: bv64 := R0_in:bv64 );
    goto(%base2flt.part.0_loop1_18);
  ];
  block %phi_4 {.originalLabel = "7mGhQtHCRJaqlrmtSJOUkQ=="} [
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
  block %phi_9 {.originalLabel = "7kGDkD9PTUu99FHCIXHvZw=="} [
    guard bvsle(extract(32, 0, R1_7:bv64), 0x7e:bv32);
    var R0_12: bv64 := zero_extend(33, extract(32, 1, R0_7:bv64)) { .label = "2504_0" };
    var R1_11: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_7:bv64), 0x1:bv32)) { .label = "2508_0" };
    goto(%phi_12, %phi_13);
  ];
  block %phi_10 {.originalLabel = "7kGDkD9PTUu99FHCIXHvZw=="} [
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
  block %phi_17 {.originalLabel = "iSGqWftgSQKUjxsoExBWuQ=="} [
    guard bvsge(extract(32, 0, R1_15:bv64), 0xffffff81:bv32);
    var R0_21: bv64 := zero_extend(32, bvshl(zero_extend(1, extract(31, 0, R0_16:bv64)), 0x1:bv32)) { .label = "2472_0" };
    var R1_19: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_15:bv64), 0xffffffff:bv32)) { .label = "2476_0" };
    goto(%phi_20, %phi_21);
  ];
  block %phi_18 {.originalLabel = "iSGqWftgSQKUjxsoExBWuQ=="} [
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
      { .name = "_IO_stdin_used"; .address = 0xbe0; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xdcc; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xdd0; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20048; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0xa10; .size = 0xa0 };
      { .name = "_start"; .address = 0x840; .size = 0x1a0 };
      { .name = "addflt"; .address = 0xaa0; .size = 0x540 };
      { .name = "base2flt"; .address = 0xa24; .size = 0x380 };
      { .name = "main"; .address = 0x740; .size = 0x740 };
      { .name = "mulflt"; .address = 0xb48; .size = 0x420 };
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
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2VY0bv9102/lDv+klGLbfIf6rX+mcAGANvn36QkAAAA" ]
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
    .size = 0x48c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/4VTP2gTcRR+v/sFLMSlSUAp2uTSDvYc+oegdJBeDiGDLjU3KAhN283gkK2QSFLaRXToYaGCQuPWdBJx1bZ2";
      "KXSzWlBELkWl0A7BNODBpef3LrbWQHF4fHfv7/e9d9fMv6k0JVn1tKg0wuTUPG+hLkn7CmwA94EHwM9AeYHC6QAlbBnWXnRT";
      "eJponnPnFfZFtKqUWgE+zrcFJaqMyF3hPLwXFcpeUshcBO4KMhth3SEq3aqnk5Vmfn1pVY5th/EegXGdAL5ELdeVDz0zSpFs";
      "BvgAvg+HXoLn8dyxPzx030faAWq5L/cqIwZN56Ix+fE0u0il992w75KWq1J3dnrI+oGd2EQ12k85ErEAzMIOyjDfv5tydKLX";
      "T9GbeZ/WmwTNUUxYAqgCR4j2VonMKnqodsoZR4+aFMukRLe5T3u+SrQZd4tbybPTj1Q3+WQN+TuoNWopZ8KvVY5rm/m3rVsG";
      "yQmjPhNPDuuCrvp8v6WcEvJb/XVnAjo+wWLYUSYuhutB3Wnm3y21a/nyn90p9kooSkr2Ie6prLae+cYqKZ00dSZEGaH5uqai";
      "aTVAo37c88wRVwzeA/Kd/HhBcLyT43248cgvkbvfioda2lYqkmhOwFgjASfL/ZZq91ukD1gT6HMNenCTxFE+5/3ke+HbO+LZ";
      "p/zluYE7dBJFTs6uQEf77JPcl1DTzr1d6z87IpGND5S6xMB0ly0VLSkpwdyuF86ne2DMcZFkdlNiZ3cpNEPyhkodQ8UC5W6y";
      "r3e9axz8DcQM+A0SQUNsXFl0ZQ66TAPcZ8Gd43omoDXza/4Nfd7QiX8juwvO7XHW1sBtl7GfvUNv4SRP1sU8e8GP82YzRnCm";
      "LEeLrsg9xv44XiRl8DKeY8wLRj63jqHqpP7KKJSf6e7tLfTcq2A21+EbNGeey1HdvbM1ebwvqR1xYfwNv807D4wEAAA="
    ]
  };
  {
    .name = ".fini";
    .address = 0xbcc;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0xbe0;
    .size = 0x32;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML84P60kPi0nP7Ek3lDXKFEvWS85M0cvmcGAAQCClBKeMgAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xc14;
    .size = 0x6c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrbOYGBg4AFind////cwAuk///83APk9QHoKkN4DpFcA6R9Aeg+Q9vn7//8DIJ0DpL8A6StAmgOo7w+Q";
      "VgDSAv/+/7cA0j1A2gdIm/z//78CSAMACdfB0mwAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xc80;
    .size = 0x150;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiJf8/v/fBCTpyC4HEtMB4g9AMQOoHpCYAxDz/Pn/3wYqpgDEIUBsAhTz";
      "AOvlU5jLMo/ZaTKT3727l/lg+iqAOAWohgXJrB4gLgCKZUDFRIB4ARAfAYppQMwSmMs0jxEkvgOIrwDFQWwGZ4g4yIwLIAwU";
      "L4CaAdL3BIgt/v7/vwIk4AZRG37vLh+DE4TtxgXiOHKD9AswMjBsAaptQdKvAhSb8fP//xcQNxjMZZvH6jyZZQrzVKZ4oNar";
      "l6+AdEPUAwCzGq2QUAEAAA=="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xdd0;
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
      "H4sIAAAAAAAA/7WQqxLCMBBFt9DwZgZBh/L4RyyfBA6JrEQgkMhKZA2i02nDMPdEpJ41Z+7eZO8miakuMIE3uICnkbhEP+bi";
      "NpxvdXOPnsAdLPAPPf/T+eOP14G0o18NRWLtiT9DvyBrWA4zi4sx9vbKZ4yd4RqO4Sbkubi/cvHeBZz28huv94SjHbpM1fTo";
      "8M8V+o5fo1P7T30B0V7BbPABAAA="
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
