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
  block %main_entry {.address = 0x740; .originalLabel = "rTboommFQYKaOJjS0arpOQ=="} [
    var Stack_n48_n40: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n40_n32: bv64 := R30_in:bv64 { .label = "1856_2" };
    var Stack_n32_n24: bv64 := R19_in:bv64 { .label = "1864_1" };
    var Stack_n24_n16: bv64 := R20_in:bv64 { .label = "1864_2" };
    var Stack_n16_n8: bv64 := R21_in:bv64 { .label = "1868_0" };
    var load14_1: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv32 := $__VERIFIER_nondet_uint();
    var R20_2: bv64 := zero_extend(32, R0_2:bv32) { .label = "1876_0" };
    var load23_1: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv64 := zero_extend(56, $__VERIFIER_nondet_char());
    var R21_2: bv64 := zero_extend(32, extract(32, 0, R0_4:bv64)) { .label = "1884_0" };
    var load14_2: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_6: bv32 := $__VERIFIER_nondet_uint();
    var R19_2: bv64 := zero_extend(32, R0_6:bv32) { .label = "1892_0" };
    var load23_2: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv64 := zero_extend(56, $__VERIFIER_nondet_char());
    var R3_2: bv64 := zero_extend(32, extract(32, 0, R0_8:bv64)) { .label = "1900_0" };
    goto(%phi_15, %phi_16);
  ];
  block %main_14 {.address = 0x798; .originalLabel = "QQJPuTSoQmibzu+VzySx0Q=="} [
    var (R0_17:bv64, R10_22:bv64, R11_22:bv64, R12_22:bv64, R13_22:bv64, R14_22:bv64, R15_22:bv64, R18_22:bv64, R1_7:bv64, R29_23:bv64, R2_24:bv64, R3_15:bv64, R4_22:bv64, R5_22:bv64, R6_22:bv64, R7_22:bv64, R8_22:bv64, R9_22:bv64)
        := call @addflt_2672 (zero_extend(32, extract(32, 0, R20_14:bv64)), R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R18_in:bv64, zero_extend(32, extract(32, 0, R19_16:bv64)), bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), 0x74c:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_2:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64);
    goto(%main_14_retval_inline);
  ];
  block %main_24 {.address = 0x784; .originalLabel = "5XTRCkZ3QcKaU1/fLaDOTA=="} [
    goto(%phi_22, %phi_23);
  ];
  block %phi_15 {.originalLabel = "S+s/s/kOTIyDHQkDsll//g=="} [
    guard eq(extract(32, 0, R20_2:bv64), 0x0:bv32);
    var R20_14: bv64 := R20_2:bv64 { .label = "phiback" };
    var R2_16: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%main_24);
  ];
  block %phi_16 {.originalLabel = "S+s/s/kOTIyDHQkDsll//g=="} [
    guard boolnot(eq(extract(32, 0, R20_2:bv64), 0x0:bv32));
    var (R0_11:bv64, R1_3:bv64, R2_12:bv64) := call @base2flt.part.0_2368 (zero_extend(32, extract(32, 0, R20_2:bv64)), zero_extend(32, sign_extend(24, extract(8, 0, R21_2:bv64))));
    goto(%phi_16_retval_inline);
  ];
  block %phi_22 {.originalLabel = "5XTRCkZ3QcKaU1/fLaDOTA=="} [
    guard eq(extract(32, 0, R19_2:bv64), 0x0:bv32);
    var R19_16: bv64 := R19_2:bv64 { .label = "phiback" };
    var R2_23: bv64 := R2_16:bv64 { .label = "phiback" };
    goto(%main_14);
  ];
  block %phi_23 {.originalLabel = "5XTRCkZ3QcKaU1/fLaDOTA=="} [
    guard boolnot(eq(extract(32, 0, R19_2:bv64), 0x0:bv32));
    var (R0_14:bv64, R1_5:bv64, R2_19:bv64) := call @base2flt.part.0_2368 (zero_extend(32, extract(32, 0, R19_2:bv64)), zero_extend(32, sign_extend(24, extract(8, 0, R3_2:bv64))));
    goto(%phi_23_retval_inline);
  ];
  block %phi_31 {.originalLabel = "UO+bYZbvQre2I8fzdG1vlA=="} [
    guard boolnot(eq(extract(32, 0, R21_19:bv64), extract(32, 0, R0_20:bv64)));
    var (R0_retval_inlined_6:bv64, R17_24:bv64, R1_retval_inlined_10:bv64, R2_retval_inlined_14:bv64, R3_retval_inlined_16:bv64) := call @reach_error_2472 (R29_25:bv64, 0x744:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64)) { .label = "2000_2" };
    goto(%phi_31_retval_inline);
  ];
  block %phi_32 {.originalLabel = "UO+bYZbvQre2I8fzdG1vlA=="} [
    guard eq(extract(32, 0, R21_19:bv64), extract(32, 0, R0_20:bv64));
    var load9_1: bv64 := Stack_n16_n8:bv64 { .label = "1980_0_0" };
    var load10_1: bv64 := Stack_n32_n24:bv64 { .label = "1988_1_0" };
    var load11_1: bv64 := Stack_n24_n16:bv64 { .label = "1988_2_0" };
    var load12_1: bv64 := Stack_n48_n40:bv64 { .label = "1992_0_0" };
    var load13_1: bv64 := Stack_n40_n32:bv64 { .label = "1992_1_0" };
    var R29_33: bv64 := load12_1:bv64 { .label = "phiback" };
    var R31_30: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_30: bv64 := 0x20010:bv64 { .label = "phiback" };
    var R1_16: bv64 := R1_9:bv64 { .label = "phiback" };
    var R3_24: bv64 := R3_17:bv64 { .label = "phiback" };
    var R17_26: bv64 := load23_2:bv64 { .label = "phiback" };
    var R0_28: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_18: bv64 := load13_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_31_retval_inline [
    var R29_33: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffc0:bv64) { .label = "phiback" };
    var R31_30: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64) { .label = "phiback" };
    var R16_30: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R1_16: bv64 := 0xbd0:bv64 { .label = "phiback" };
    var R3_24: bv64 := 0xbc0:bv64 { .label = "phiback" };
    var R17_26: bv64 := R17_24:bv64 { .label = "phiback" };
    var R0_28: bv64 := 0xbe8:bv64 { .label = "phiback" };
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
  block %phi_29_retval_inline [
    var _PC_26: bv64 := _PC_24:bv64 { .label = "inlineret" };
    goto(%phi_31, %phi_32);
  ];
  block %main_14_retval_inline [
    var _PC_24: bv64 := _PC_in:bv64 { .label = "inlineret" };
    var R21_19: bv64 := zero_extend(32, extract(32, 0, R0_17:bv64)) { .label = "1956_0" };
    var (R0_20:bv64, R10_24:bv64, R11_24:bv64, R12_24:bv64, R13_24:bv64, R14_24:bv64, R15_24:bv64, R18_24:bv64, R1_9:bv64, R29_25:bv64, R2_26:bv64, R3_17:bv64, R4_24:bv64, R5_24:bv64, R6_24:bv64, R7_24:bv64, R8_24:bv64, R9_24:bv64)
        := call @addflt_2672 (zero_extend(32, extract(32, 0, R19_16:bv64)), R10_22:bv64, R11_22:bv64, R12_22:bv64, R13_22:bv64, R14_22:bv64, R15_22:bv64, R18_22:bv64, zero_extend(32, extract(32, 0, R20_14:bv64)), R29_23:bv64, 0x750:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), R3_15:bv64, R4_22:bv64, R5_22:bv64, R6_22:bv64, R7_22:bv64, R8_22:bv64, R9_22:bv64);
    goto(%phi_29_retval_inline);
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
  block %reach_error_entry {.address = 0x9a8; .originalLabel = "sTpQBO+yQAS6jkHEjyMVOQ=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2472_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2472_2" };
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 = R30_in" };
    var load5_1: bv64 := $Global_131112_131120:bv64 { .label = "1796_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0xbe8:bv64, load5_1:bv64, 0xbd0:bv64, 0x3:bv64, 0xbc0:bv64);
  ]
];


proc @addflt_2672
  (R0_in:bv64, R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R18_in:bv64, R1_in:bv64, R29_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64)
    -> (R0_out:bv64, R10_out:bv64, R11_out:bv64, R12_out:bv64, R13_out:bv64, R14_out:bv64, R15_out:bv64, R18_out:bv64, R1_out:bv64, R29_out:bv64, R2_out:bv64, R3_out:bv64, R4_out:bv64, R5_out:bv64, R6_out:bv64, R7_out:bv64, R8_out:bv64, R9_out:bv64)
  { .name = "addflt"; .address = 0xa70; .returnBlock = "addflt_return" }
[
  block %addflt_entry {.address = 0xa70; .originalLabel = "eJXUc89xSWyzmhr81sq7mA=="} [
    goto(%phi_4, %phi_5);
  ];
  block %addflt_8 {.address = 0xb10; .originalLabel = "v8x/S7o+Q1OguSK5QOnrzg=="} [
    assert eq(R30_in:bv64, 0x744:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_7:bv64, R17_29:bv64, R1_retval_inlined_11:bv64, R2_retval_inlined_15:bv64, R3_retval_inlined_17:bv64) := call @reach_error_2472 (bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), 0x744:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .label = "2832_2" };
    goto(%addflt_8_retval_inline);
  ];
  block %addflt_20 {.address = 0xae0; .originalLabel = "cHNfxeW/Re+pLLpV80t8aA=="} [
    var load3_1: bv64 := Stack_n16_n8:bv64 { .label = "2784_0_0" };
    var load4_1: bv64 := Stack_n8_0:bv64 { .label = "2784_1_0" };
    var R11_40: bv64 := R11_in:bv64 { .label = "phiback" };
    var R31_42: bv64 := R31_in:bv64 { .label = "phiback" };
    var R8_40: bv64 := R8_in:bv64 { .label = "phiback" };
    var R13_40: bv64 := R13_in:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_33:bv64 { .label = "phiback" };
    var R29_38: bv64 := load3_1:bv64 { .label = "phiback" };
    var R9_40: bv64 := R9_in:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_in:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_in:bv64 { .label = "phiback" };
    var R12_40: bv64 := R12_in:bv64 { .label = "phiback" };
    var R1_46: bv64 := R1_22:bv64 { .label = "phiback" };
    var R10_40: bv64 := R10_in:bv64 { .label = "phiback" };
    var R18_40: bv64 := R18_in:bv64 { .label = "phiback" };
    var R3_43: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_47: bv64 := R2_37:bv64 { .label = "phiback" };
    var R0_39: bv64 := R0_29:bv64 { .label = "phiback" };
    var R14_40: bv64 := R14_in:bv64 { .label = "phiback" };
    var R15_40: bv64 := R15_in:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_in:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %addflt_62 [
    var R0_9: bv64 := zero_extend(32, extract(32, 0, R2_6:bv64)) { .label = "2684_0" };
    goto(%phi_16, %phi_17);
  ];
  block %addflt_68 [
    goto(%phi_10, %phi_11);
  ];
  block %phi_4 {.originalLabel = "eJXUc89xSWyzmhr81sq7mA=="} [
    guard bvult(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R2_6: bv64 := zero_extend(32, extract(32, 0, R1_in:bv64)) { .label = "phiback" };
    goto(%addflt_68);
  ];
  block %phi_5 {.originalLabel = "eJXUc89xSWyzmhr81sq7mA=="} [
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
    var R11_40: bv64 := R11_in:bv64 { .label = "phiback" };
    var R31_42: bv64 := R31_in:bv64 { .label = "phiback" };
    var R8_40: bv64 := R8_in:bv64 { .label = "phiback" };
    var R13_40: bv64 := R13_in:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_in:bv64 { .label = "phiback" };
    var R29_38: bv64 := R29_in:bv64 { .label = "phiback" };
    var R9_40: bv64 := R9_in:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_in:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_in:bv64 { .label = "phiback" };
    var R12_40: bv64 := R12_in:bv64 { .label = "phiback" };
    var R1_46: bv64 := R1_13:bv64 { .label = "phiback" };
    var R10_40: bv64 := R10_in:bv64 { .label = "phiback" };
    var R18_40: bv64 := R18_in:bv64 { .label = "phiback" };
    var R3_43: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_47: bv64 := R2_6:bv64 { .label = "phiback" };
    var R0_39: bv64 := R0_9:bv64 { .label = "phiback" };
    var R14_40: bv64 := R14_in:bv64 { .label = "phiback" };
    var R15_40: bv64 := R15_in:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_in:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %phi_17 [
    guard boolnot(eq(extract(32, 0, R1_13:bv64), 0x0:bv32));
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2692_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2692_2" };
    var R4_14: bv64 := zero_extend(56, extract(32, 24, R2_6:bv64)) { .label = "2696_0" };
    var R3_14: bv64 := zero_extend(56, extract(32, 24, R1_13:bv64)) { .label = "2700_0" };
    goto(%phi_18, %phi_19);
  ];
  block %phi_18 [
    guard bvslt(extract(32, 0, R4_14:bv64), extract(32, 0, R3_14:bv64));
    var R1_42: bv64 := R1_13:bv64 { .label = "phiback" };
    var R3_39: bv64 := R3_14:bv64 { .label = "phiback" };
    var R2_43: bv64 := R2_6:bv64 { .label = "phiback" };
    var R0_35: bv64 := R0_9:bv64 { .label = "phiback" };
    goto(%addflt_8);
  ];
  block %phi_19 [
    guard bvsge(extract(32, 0, R4_14:bv64), extract(32, 0, R3_14:bv64));
    var R3_17: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_14:bv64), bvneg(extract(32, 0, R3_14:bv64)))) { .label = "2720_0" };
    var R1_19: bv64 := zero_extend(32, bvor(zero_extend(8, extract(24, 0, R1_13:bv64)), 0x1000000:bv32)) { .label = "2724_0" };
    goto(%phi_20, %phi_21);
  ];
  block %phi_20 [
    guard bvsgt(extract(32, 0, R3_17:bv64), 0x1f:bv32);
    assert eq(R30_in:bv64, 0x744:bv64) { .comment = "R30 = R30_in" };
    var load0_1: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "abort" };
    goto(%phi_40);
  ];
  block %phi_21 [
    guard bvsle(extract(32, 0, R3_17:bv64), 0x1f:bv32);
    var R1_22: bv64 := zero_extend(32, bvlshr(extract(32, 0, R1_19:bv64), zero_extend(27, extract(5, 0, R3_17:bv64)))) { .label = "2736_0" };
    goto(%phi_22, %phi_23);
  ];
  block %phi_22 [
    guard eq(extract(32, 0, R1_22:bv64), 0x0:bv32);
    var R4_33: bv64 := R4_14:bv64 { .label = "phiback" };
    var R2_37: bv64 := R2_6:bv64 { .label = "phiback" };
    var R0_29: bv64 := R0_9:bv64 { .label = "phiback" };
    goto(%addflt_20);
  ];
  block %phi_23 [
    guard boolnot(eq(extract(32, 0, R1_22:bv64), 0x0:bv32));
    var R2_21: bv32 := bvor(zero_extend(8, extract(24, 0, R2_6:bv64)), 0x1000000:bv32) { .label = "2748_0" };
    var R2_22: bv64 := zero_extend(32, bvadd(R2_21:bv32, extract(32, 0, R1_22:bv64))) { .label = "2752_0" };
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
    var R2_37: bv64 := R2_22:bv64 { .label = "phiback" };
    var R0_29: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    goto(%addflt_20);
  ];
  block %phi_27 [
    guard boolnot(eq(extract(32, 0, R4_14:bv64), 0xff:bv32));
    var R4_25: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_14:bv64), 0x1:bv32)) { .label = "2772_0" };
    var R0_18: bv64 := zero_extend(32, bvor(zero_extend(8, extract(25, 1, R2_22:bv64)), bvshl(zero_extend(24, extract(8, 0, R4_25:bv64)), 0x18:bv32))) { .label = "2780_0" };
    var R4_33: bv64 := R4_25:bv64 { .label = "phiback" };
    var R2_37: bv64 := zero_extend(40, extract(25, 1, R2_22:bv64)) { .label = "phiback" };
    var R0_29: bv64 := R0_18:bv64 { .label = "phiback" };
    goto(%addflt_20);
  ];
  block %phi_30 [
    guard bvugt(extract(32, 0, R2_22:bv64), 0x1ffffff:bv32);
    var R1_42: bv64 := R1_22:bv64 { .label = "phiback" };
    var R3_39: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_43: bv64 := R2_22:bv64 { .label = "phiback" };
    var R0_35: bv64 := 0x1ffffff:bv64 { .label = "phiback" };
    goto(%addflt_8);
  ];
  block %phi_31 [
    guard bvule(extract(32, 0, R2_22:bv64), 0x1ffffff:bv32);
    var R0_25: bv64 := zero_extend(32, bvor(zero_extend(8, extract(24, 0, R2_22:bv64)), bvshl(zero_extend(24, extract(8, 0, R4_14:bv64)), 0x18:bv32))) { .label = "2812_0" };
    var load1_1: bv64 := Stack_n16_n8:bv64 { .label = "2816_0_0" };
    var load2_1: bv64 := Stack_n8_0:bv64 { .label = "2816_1_0" };
    var R11_40: bv64 := R11_in:bv64 { .label = "phiback" };
    var R31_42: bv64 := R31_in:bv64 { .label = "phiback" };
    var R8_40: bv64 := R8_in:bv64 { .label = "phiback" };
    var R13_40: bv64 := R13_in:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_14:bv64 { .label = "phiback" };
    var R29_38: bv64 := load1_1:bv64 { .label = "phiback" };
    var R9_40: bv64 := R9_in:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_in:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_in:bv64 { .label = "phiback" };
    var R12_40: bv64 := R12_in:bv64 { .label = "phiback" };
    var R1_46: bv64 := R1_22:bv64 { .label = "phiback" };
    var R10_40: bv64 := R10_in:bv64 { .label = "phiback" };
    var R18_40: bv64 := R18_in:bv64 { .label = "phiback" };
    var R3_43: bv64 := R3_17:bv64 { .label = "phiback" };
    var R2_47: bv64 := zero_extend(40, extract(24, 0, R2_22:bv64)) { .label = "phiback" };
    var R0_39: bv64 := R0_25:bv64 { .label = "phiback" };
    var R14_40: bv64 := R14_in:bv64 { .label = "phiback" };
    var R15_40: bv64 := R15_in:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_in:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %phi_40 [
    var R11_40: bv64 := R11_34:bv64 { .label = "phiback" };
    var R31_42: bv64 := bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64) { .label = "phiback" };
    var R8_40: bv64 := R8_34:bv64 { .label = "phiback" };
    var R13_40: bv64 := R13_34:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_36:bv64 { .label = "phiback" };
    var R29_38: bv64 := R29_31:bv64 { .label = "phiback" };
    var R9_40: bv64 := R9_34:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_34:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_34:bv64 { .label = "phiback" };
    var R12_40: bv64 := R12_34:bv64 { .label = "phiback" };
    var R1_46: bv64 := R1_39:bv64 { .label = "phiback" };
    var R10_40: bv64 := R10_34:bv64 { .label = "phiback" };
    var R18_40: bv64 := R18_34:bv64 { .label = "phiback" };
    var R3_43: bv64 := R3_36:bv64 { .label = "phiback" };
    var R2_47: bv64 := R2_40:bv64 { .label = "phiback" };
    var R0_39: bv64 := R0_32:bv64 { .label = "phiback" };
    var R14_40: bv64 := R14_34:bv64 { .label = "phiback" };
    var R15_40: bv64 := R15_34:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_34:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %addflt_8_retval_inline [
    var R11_40: bv64 := R11_in:bv64 { .label = "phiback" };
    var R31_42: bv64 := bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64) { .label = "phiback" };
    var R8_40: bv64 := R8_in:bv64 { .label = "phiback" };
    var R13_40: bv64 := R13_in:bv64 { .label = "phiback" };
    var R4_42: bv64 := R4_14:bv64 { .label = "phiback" };
    var R29_38: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R9_40: bv64 := R9_in:bv64 { .label = "phiback" };
    var R7_40: bv64 := R7_in:bv64 { .label = "phiback" };
    var R5_40: bv64 := R5_in:bv64 { .label = "phiback" };
    var R12_40: bv64 := R12_in:bv64 { .label = "phiback" };
    var R1_46: bv64 := 0xbd0:bv64 { .label = "phiback" };
    var R10_40: bv64 := R10_in:bv64 { .label = "phiback" };
    var R18_40: bv64 := R18_in:bv64 { .label = "phiback" };
    var R3_43: bv64 := 0xbc0:bv64 { .label = "phiback" };
    var R2_47: bv64 := 0x3:bv64 { .label = "phiback" };
    var R0_39: bv64 := 0xbe8:bv64 { .label = "phiback" };
    var R14_40: bv64 := R14_in:bv64 { .label = "phiback" };
    var R15_40: bv64 := R15_in:bv64 { .label = "phiback" };
    var R6_40: bv64 := R6_in:bv64 { .label = "phiback" };
    goto(%addflt_return);
  ];
  block %addflt_return [
    assert eq(R31_in:bv64, R31_42:bv64) { .comment = "R31 preserved across calls" };
    return (R0_39:bv64, R10_40:bv64, R11_40:bv64, R12_40:bv64, R13_40:bv64, R14_40:bv64, R15_40:bv64, R18_40:bv64, R1_46:bv64, R29_38:bv64, R2_47:bv64, R3_43:bv64, R4_42:bv64, R5_40:bv64, R6_40:bv64, R7_40:bv64, R8_40:bv64, R9_40:bv64);
  ]
];


proc @base2flt.part.0_2368 (R0_in:bv64, R1_in:bv64) -> (R0_out:bv64, R1_out:bv64, R2_out:bv64)
  { .name = "base2flt.part.0"; .address = 0x940; .returnBlock = "base2flt.part.0_return" }
[
  block %base2flt.part.0_entry {.address = 0x940; .originalLabel = "GUYhvqiwSMaxv4uu+bCmaA=="} [
    goto(%phi_3, %phi_4);
  ];
  block %base2flt.part.0_4 {.address = 0x958; .originalLabel = "GU2ZvCQQSKKlpBqs5mk/qQ=="} [
    var R1_24: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_23:bv64), 0x80:bv32)) { .label = "2392_0" };
    var R0_26: bv32 := bvand(extract(32, 0, R0_25:bv64), 0xfeffffff:bv32) { .label = "2396_0" };
    var R0_27: bv64 := zero_extend(32, bvor(R0_26:bv32, bvshl(zero_extend(24, extract(8, 0, R1_24:bv64)), 0x18:bv32))) { .label = "2400_0" };
    var R1_26: bv64 := R1_24:bv64 { .label = "phiback" };
    var R0_29: bv64 := R0_27:bv64 { .label = "phiback" };
    var R2_25: bv64 := R2_23:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_return);
  ];
  block %base2flt.part.0_loop1_18 {.address = 0x978; .originalLabel = "1VaNXlkvRf6jksZrGQ2atQ=="} [
    goto(%phi_17, %phi_18);
  ];
  block %base2flt.part.0_loop2_34 {.address = 0x998; .originalLabel = "i0XdWQZcTbufqnlwMmyRWA=="} [
    goto(%phi_9, %phi_10);
  ];
  block %phi_3 {.originalLabel = "GUYhvqiwSMaxv4uu+bCmaA=="} [
    guard bvule(extract(32, 0, R0_in:bv64), 0xffffff:bv32);
    ( var R1_15: bv64 := R1_in:bv64,
      var R0_16: bv64 := R0_in:bv64 );
    goto(%base2flt.part.0_loop1_18);
  ];
  block %phi_4 {.originalLabel = "GUYhvqiwSMaxv4uu+bCmaA=="} [
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
  block %phi_9 {.originalLabel = "i0XdWQZcTbufqnlwMmyRWA=="} [
    guard bvsle(extract(32, 0, R1_7:bv64), 0x7e:bv32);
    var R0_12: bv64 := zero_extend(33, extract(32, 1, R0_7:bv64)) { .label = "2440_0" };
    var R1_11: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_7:bv64), 0x1:bv32)) { .label = "2444_0" };
    goto(%phi_12, %phi_13);
  ];
  block %phi_10 {.originalLabel = "i0XdWQZcTbufqnlwMmyRWA=="} [
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
  block %phi_17 {.originalLabel = "1VaNXlkvRf6jksZrGQ2atQ=="} [
    guard bvsge(extract(32, 0, R1_15:bv64), 0xffffff81:bv32);
    var R0_21: bv64 := zero_extend(32, bvshl(zero_extend(1, extract(31, 0, R0_16:bv64)), 0x1:bv32)) { .label = "2408_0" };
    var R1_19: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_15:bv64), 0xffffffff:bv32)) { .label = "2412_0" };
    goto(%phi_20, %phi_21);
  ];
  block %phi_18 {.originalLabel = "1VaNXlkvRf6jksZrGQ2atQ=="} [
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
      { .name = "_IO_stdin_used"; .address = 0xbb8; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xdc4; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xdc8; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20048; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x9e4; .size = 0xa0 };
      { .name = "_start"; .address = 0x800; .size = 0x1a0 };
      { .name = "addflt"; .address = 0xa70; .size = 0x540 };
      { .name = "assume_abort_if_not"; .address = 0x9d0; .size = 0xa0 };
      { .name = "base2flt"; .address = 0xa00; .size = 0x380 };
      { .name = "main"; .address = 0x740; .size = 0x4a0 };
      { .name = "mulflt"; .address = 0xb20; .size = 0x420 };
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
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2WQvpr5/+C8utOr3pwUuP/LcbGFYPVrAIMTSowkAAAA" ]
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
    .size = 0x464;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/5VSPWhTYRQ93/sKFuLSpKAUbfLSDvY59IegdOrLo5BBHWoyKAhN283oEAcpJJCUdhEdGiw4KLRdJOlUtKu2";
      "tUuhm8WCIpLUHwqtEIhBHySN53shbQkqOFzO++659+ace1NNvMpVJTKlsMiVPbCLtdqTHxLGJ2KZeEAsET8QPxNXgEBethuL";
      "nfDEgTlV+9LJeYyxc/DcYU7VF/hWdayfKzvvdkPVLPO9qiG2DkTKHtMG0tdL4WCumtjIrsnRnfvkvT757n/iPNJvOxlfJZYK";
      "0rR3u5D5Rk95oIiDkC3JtTAW6WGZ4eT3QrYJrGRrtTPqd/82GwKz8ImMIOrEIWB/jdoLnKHnQ/YYZxSlWILm3VFzmut1YMtf";
      "SW0HT0891CvBx/S9ssteqxiyx51e7ai3mnhdv4ULtof9UX9w0BS47Oj9ErLTrK/PN+179PGe4eP+on4xWHKZdjXxJtvs5SP9";
      "/Wt3Wn7V7YUWeyAQ0dbq3xc0RHRobZg85UZUGI6vSW9Yb8GIw9dqkaGK6L9NVPdz+KRQfJview7J/xLxu3XeXfe2mpPArGAo";
      "jyBOoDejm70ZLPRmxjnnGv3wJoFGvaob/kPuO3MN/XmBQMNDj3bsYZM3agPaT+rK0WOzrpO+suxp9tW8By9EzN+X7hB9Ux15";
      "qRlBiYDSNZw8G+5iKH3zkLEtyR3egnsa8oqO1oFUEvGrKte90TFGzRY5i3kLwmWJzUvzFRmnl4hFvTPUq3gz2mJUE+vOTR2t";
      "9DYKxPaos5lXfsq89XPu5ufh8X5O6lWelN5u6lT1M1HLNb0gR1IVEX/E3Sk+Ba3/Ir99Sh8DjsbWgcKE+cJKLjw1Kze2OXM/";
      "Rw2qj//NyPQzOWJWbm5PHO1KGg1NCn8DyXqdamQEAAA="
    ]
  };
  {
    .name = ".fini";
    .address = 0xba4;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0xbb8;
    .size = 0x32;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML84P60kPi0nP7Ek3kTXSC9ZLzkzRy+ZgcGAAQA9Yr++MgAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xbec;
    .size = 0x74;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrYuYGBg4AXikN///69hZGAQ+fP/fweQXwKk5wDpJUB6A5B+AKSPAGmTv///vwCpB9J/gPQeIC0A1PcE";
      "SGsA6R9A2gFkzr///yOAdAuQzgHSJv///58BpAHdod++dAAAAA=="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xc60;
    .size = 0x168;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiFt+//9vApJ0ZJcDiekA8QWgmAFUD0jMAYjfAMVsoGIKQBwCxCJ//v/3";
      "AOvlU5jLMo/ZaTKT3727l/lg+iqA2AWohgXJrB4gDgCKZUDFRIB4ARAvAYppQMwSmMs0jxEkvgOItwDFQWwGZ4T4BSDegCYO";
      "MvsFVH0B1GyQeX9A9v79/38FSMANojb83l0+BicI240LxHHkBunXYGRgmAJU24Kk3wYotuDn//9TIG4zmMs2j9V5MssU5qlM";
      "8UCtVy9fAemGqAcAG6YGXWgBAAA="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xdc8;
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
      "H4sIAAAAAAAA/7WQqxLCMBBFt9DwZgZBh/L4RywfhACHRFYikchKZA2i02nDMPdEpJ41Z+7eZO8miamuMIF3uICnkbhEn+fi";
      "NpxvdXOPnsAdLPAPPf/T+eOPt4G0o18NRWLtiT9DvyBrWA4zi4sx9vbKZ4xd4BqO4Sbkubi/cvHeBZz28huv94SjHbpM1fTo";
      "8M8V+oFfo1P7T30Bb98eK/ABAAA="
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
