var $Global_131104_131112: bv64;
var $Global_131112_131120: bv64;
var $Global_131120_131128: bv64;
declare-fun $__VERIFIER_nondet_uint : () -> bv32;
declare-fun $__VERIFIER_nondet_int : () -> bv32;

prog entry @main_1856;

proc @main_1856
  (R0_in:bv64, R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R29_out:bv64, _PC_out:bv64)
  { .name = "main"; .address = 0x740; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x740; .originalLabel = "Ox5oklSPSpORErL01WKlQg=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1856_2" };
    var (R0_2:bv64, R1_2:bv64, R2_2:bv64, R3_2:bv64) := call @ssl3_connect_2280 (R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), R2_in:bv64, 0x74c:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), R3_in:bv64);
    goto(%main_return);
  ];
  block %main_return [
    var _PC_2: bv64 := _PC_in:bv64 { .label = "inlineret" };
    var load2_1: bv64 := Stack_n16_n8:bv64 { .label = "1872_0_0" };
    var load3_1: bv64 := Stack_n8_0:bv64 { .label = "1872_1_0" };
    assert eq(R30_in:bv64, load3_1:bv64) { .comment = "R30 preserved across calls" };
    assert true { .comment = "R31 preserved across calls" };
    return (0x0:bv64, load2_1:bv64, _PC_2:bv64);
  ]
];


proc @reach_error_2240
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x8c0; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x8c0; .originalLabel = "enZlO5NtSomctuVHW9XOjg=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2240_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2240_2" };
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 = R30_in" };
    var load9_1: bv64 := $Global_131112_131120:bv64 { .label = "1796_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0xcc8:bv64, 0xcb0:bv64, 0x3:bv64, 0xca0:bv64);
  ]
];


proc @ssl3_connect_2280
  (R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64)
    -> (R0_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "ssl3_connect"; .address = 0x8e8; .returnBlock = "ssl3_connect_return" }
[
  block %ssl3_connect_entry {.address = 0x8e8; .originalLabel = "c+Tj9sLiSjG8wNJH9/gqRQ=="} [
    var Stack_n128_n120: bv64 := R29_in:bv64 { .label = "2280_1" };
    var Stack_n120_n112: bv64 := R30_in:bv64 { .label = "2280_2" };
    var Stack_n112_n104: bv64 := R19_in:bv64 { .label = "2288_1" };
    var Stack_n104_n96: bv64 := R20_in:bv64 { .label = "2288_2" };
    var Stack_n96_n88: bv64 := R21_in:bv64 { .label = "2292_1" };
    var Stack_n88_n80: bv64 := R22_in:bv64 { .label = "2292_2" };
    var Stack_n80_n72: bv64 := R23_in:bv64 { .label = "2296_1" };
    var Stack_n72_n64: bv64 := R24_in:bv64 { .label = "2296_2" };
    var Stack_n64_n56: bv64 := R25_in:bv64 { .label = "2300_1" };
    var Stack_n56_n48: bv64 := R26_in:bv64 { .label = "2300_2" };
    var Stack_n48_n40: bv64 := R27_in:bv64 { .label = "2304_1" };
    var Stack_n40_n32: bv64 := R28_in:bv64 { .label = "2304_2" };
    var load54_1: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load8_1: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load8_2: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv32 := $__VERIFIER_nondet_uint();
    var load54_2: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_3: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_4: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv32 := $__VERIFIER_nondet_int();
    var load54_5: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_10: bv32 := $__VERIFIER_nondet_int();
    var load54_6: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_12: bv32 := $__VERIFIER_nondet_int();
    var load54_7: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load8_3: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load8_4: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load8_5: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load8_6: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_8: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_19: bv32 := $__VERIFIER_nondet_int();
    var Stack_n24_n20: bv32 := R0_19:bv32 { .label = "2380_0" };
    var load54_9: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_10: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_11: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_23: bv32 := $__VERIFIER_nondet_int();
    var load54_12: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_13: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_26: bv32 := $__VERIFIER_nondet_int();
    var load54_14: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_15: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_29: bv32 := $__VERIFIER_nondet_int();
    var Stack_n20_n16: bv32 := R0_29:bv32 { .label = "2420_0" };
    var load8_7: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load8_8: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_16: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_33: bv32 := $__VERIFIER_nondet_int();
    var load54_17: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_35: bv32 := $__VERIFIER_nondet_int();
    var load54_18: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_37: bv32 := $__VERIFIER_nondet_int();
    var load54_19: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_39: bv32 := $__VERIFIER_nondet_int();
    var load54_20: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_41: bv32 := $__VERIFIER_nondet_int();
    var Stack_n12_n8: bv32 := R0_41:bv32 { .label = "2468_0" };
    var load54_21: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_43: bv32 := $__VERIFIER_nondet_int();
    var Stack_n8_n4: bv32 := R0_43:bv32 { .label = "2476_0" };
    var load54_22: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_45: bv32 := $__VERIFIER_nondet_int();
    var Stack_n16_n12: bv32 := R0_45:bv32 { .label = "2484_0" };
    var load54_23: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    goto(%phi_106, %phi_107);
  ];
  block %ssl3_connect_4 {.address = 0xad0; .originalLabel = "CRXits99QNSa77ugDYbZ8Q=="} [
    var load29_1: bv64 := Stack_n112_n104:bv64 { .label = "2768_1_0" };
    var load30_1: bv64 := Stack_n104_n96:bv64 { .label = "2768_2_0" };
    var load31_1: bv64 := Stack_n96_n88:bv64 { .label = "2776_1_0" };
    var load32_1: bv64 := Stack_n88_n80:bv64 { .label = "2776_2_0" };
    var load33_1: bv64 := Stack_n80_n72:bv64 { .label = "2780_1_0" };
    var load34_1: bv64 := Stack_n72_n64:bv64 { .label = "2780_2_0" };
    var load35_1: bv64 := Stack_n64_n56:bv64 { .label = "2784_1_0" };
    var load36_1: bv64 := Stack_n56_n48:bv64 { .label = "2784_2_0" };
    var load37_1: bv64 := Stack_n48_n40:bv64 { .label = "2788_1_0" };
    var load38_1: bv64 := Stack_n40_n32:bv64 { .label = "2788_2_0" };
    var load39_1: bv64 := Stack_n128_n120:bv64 { .label = "2792_0_0" };
    var load40_1: bv64 := Stack_n120_n112:bv64 { .label = "2792_1_0" };
    var R31_283: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_281: bv64 := R1_in:bv64 { .label = "phiback" };
    var R0_127: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    var R3_281: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_281: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_8 [
    guard eq(ZF_99:bv1, 0x1:bv1);
    goto(%ssl3_connect_4);
  ];
  block %ssl3_connect_10 {.address = 0xaa4; .originalLabel = "oA+DketjTGSwiIcBRemc/Q=="} [
    var load42_1: bv64 := Stack_n112_n104:bv64 { .label = "2724_1_0" };
    var load43_1: bv64 := Stack_n104_n96:bv64 { .label = "2724_2_0" };
    var load44_1: bv64 := Stack_n96_n88:bv64 { .label = "2728_1_0" };
    var load45_1: bv64 := Stack_n88_n80:bv64 { .label = "2728_2_0" };
    var load46_1: bv64 := Stack_n80_n72:bv64 { .label = "2732_1_0" };
    var load47_1: bv64 := Stack_n72_n64:bv64 { .label = "2732_2_0" };
    var load48_1: bv64 := Stack_n64_n56:bv64 { .label = "2736_1_0" };
    var load49_1: bv64 := Stack_n56_n48:bv64 { .label = "2736_2_0" };
    var load50_1: bv64 := Stack_n48_n40:bv64 { .label = "2740_1_0" };
    var load51_1: bv64 := Stack_n40_n32:bv64 { .label = "2740_2_0" };
    var load52_1: bv64 := Stack_n128_n120:bv64 { .label = "2744_0_0" };
    var load53_1: bv64 := Stack_n120_n112:bv64 { .label = "2744_1_0" };
    var R31_283: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_281: bv64 := R1_in:bv64 { .label = "phiback" };
    var R0_127: bv64 := R0_123:bv64 { .label = "phiback" };
    var R3_281: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_281: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_loop0_32 {.address = 0xa98; .originalLabel = "VFoMg2E4RVK3Vwtz7HwPow=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_375_loop_from_48:int, 0x2), eq(ssl3_connect_375_loop_from_48:int, 0x3)), eq(ssl3_connect_375_loop_from_48:int, 0x4)), eq(ssl3_connect_375_loop_from_48:int, 0x6)), eq(ssl3_connect_375_loop_from_48:int, 0x7)), eq(ssl3_connect_375_loop_from_48:int, 0x8)), eq(ssl3_connect_375_loop_from_48:int, 0xb)), eq(ssl3_connect_375_loop_from_48:int, 0xf)), eq(ssl3_connect_375_loop_from_48:int, 0x13)), eq(ssl3_connect_375_loop_from_48:int, 0x14)), eq(ssl3_connect_375_loop_from_48:int, 0x15)), eq(ssl3_connect_375_loop_from_48:int, 0x16)), eq(ssl3_connect_375_loop_from_48:int, 0x1a)), eq(ssl3_connect_375_loop_from_48:int, 0x1c));
    var load54_33: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_116: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_356, %phi_357);
  ];
  block %ssl3_connect_loop0_80 {.address = 0xb18; .originalLabel = "HZ8/f6K4ScCWDw64ZTmvIg=="} [
    ( var R21_47: bv64 := 0x1140:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %ssl3_connect_166 [
    guard eq(ZF_83:bv1, 0x1:bv1);
    goto(%ssl3_connect_4);
  ];
  block %ssl3_connect_loop1_398 {.address = 0x9f4; .originalLabel = "QvtvGKIvTHeZlG0yudu0ag=="} [
    assert eq(R24_59:bv64, 0x1120:bv64);
    goto(%phi_164, %phi_165);
  ];
  block %ssl3_connect_loop1_400 {.address = 0x9f0; .originalLabel = "yvms3ga2T0GMg/VAtlGStQ=="} [
    var R24_59: bv64 := 0x1120:bv64 { .label = "2544_0" };
    ( var R21_47: bv64 := R21_46:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %ssl3_connect_loop2_432 [
    goto(%phi_145, %phi_146);
  ];
  block %ssl3_connect_452 {.address = 0x9cc; .originalLabel = "sRluglh4T9aJD0HRBcM8uA=="} [
    goto(%phi_127, %phi_128);
  ];
  block %ssl3_connect_456 [
    guard eq(ZF_13:bv1, 0x1:bv1);
    goto(%ssl3_connect_4);
  ];
  block %phi_106 {.originalLabel = "tUvS+oEAQemDnELKggoaDg=="} [
    guard boolnot(eq(R0_4:bv32, 0xffff0400:bv32));
    goto(%ssl3_connect_4);
  ];
  block %phi_107 {.originalLabel = "tUvS+oEAQemDnELKggoaDg=="} [
    guard eq(R0_4:bv32, 0xffff0400:bv32);
    goto(%phi_108, %phi_109);
  ];
  block %phi_108 [
    guard eq(R0_10:bv32, 0x0:bv32);
    var load54_24: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_49: bv32 := $__VERIFIER_nondet_int();
    goto(%phi_113, %phi_114);
  ];
  block %phi_109 [
    guard boolnot(eq(R0_10:bv32, 0x0:bv32));
    goto(%ssl3_connect_452);
  ];
  block %phi_113 {.originalLabel = "Dkc0NnzzQOm+scKsVoX9TA=="} [
    guard boolnot(eq(R0_49:bv32, 0x0:bv32));
    var ZF_10: bv1 := bvcomp(R0_33:bv32, 0x0:bv32) { .label = "2760_1" };
    goto(%phi_117, %phi_118);
  ];
  block %phi_114 {.originalLabel = "Dkc0NnzzQOm+scKsVoX9TA=="} [
    guard eq(R0_49:bv32, 0x0:bv32);
    var ZF_13: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_456);
  ];
  block %phi_117 [
    guard boolnot(eq(R0_33:bv32, 0x0:bv32));
    goto(%ssl3_connect_452);
  ];
  block %phi_118 [
    guard eq(R0_33:bv32, 0x0:bv32);
    var ZF_13: bv1 := ZF_10:bv1 { .label = "phiback" };
    goto(%ssl3_connect_456);
  ];
  block %phi_127 {.originalLabel = "sRluglh4T9aJD0HRBcM8uA=="} [
    guard boolnot(eq(R0_35:bv32, 0x0:bv32));
    var ZF_21: bv1 := bvcomp(R0_37:bv32, 0x0:bv32) { .label = "2512_1" };
    goto(%phi_131, %phi_132);
  ];
  block %phi_128 {.originalLabel = "sRluglh4T9aJD0HRBcM8uA=="} [
    guard eq(R0_35:bv32, 0x0:bv32);
    var ZF_99: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_8);
  ];
  block %phi_131 [
    guard eq(R0_37:bv32, 0x0:bv32);
    var ZF_99: bv1 := ZF_21:bv1 { .label = "phiback" };
    goto(%ssl3_connect_8);
  ];
  block %phi_132 [
    guard boolnot(eq(R0_37:bv32, 0x0:bv32));
    goto(%phi_135, %phi_136);
  ];
  block %phi_135 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    var R21_33: bv64 := 0x1110:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_7: int := 0xe { .label = "phiback" };
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_136 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_137, %phi_138);
  ];
  block %phi_137 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_33: bv64 := 0x1110:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_7: int := 0x3 { .label = "phiback" };
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_138 [
    guard eq(R0_12:bv32, 0x0:bv32);
    var R21_33: bv64 := 0x1110:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_7: int := 0x10 { .label = "phiback" };
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_145 {.originalLabel = "7krzrUlCQ0iSQ6e75mNGxw=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_375_loop_from_7:int, 0x0), eq(ssl3_connect_375_loop_from_7:int, 0x1)), eq(ssl3_connect_375_loop_from_7:int, 0x5)), eq(ssl3_connect_375_loop_from_7:int, 0x9)), eq(ssl3_connect_375_loop_from_7:int, 0xa)), eq(ssl3_connect_375_loop_from_7:int, 0xc)), eq(ssl3_connect_375_loop_from_7:int, 0xd)), eq(ssl3_connect_375_loop_from_7:int, 0xe)), eq(ssl3_connect_375_loop_from_7:int, 0x10)), eq(ssl3_connect_375_loop_from_7:int, 0x11)), eq(ssl3_connect_375_loop_from_7:int, 0x12)), eq(ssl3_connect_375_loop_from_7:int, 0x17)), eq(ssl3_connect_375_loop_from_7:int, 0x18)), eq(ssl3_connect_375_loop_from_7:int, 0x19)), eq(ssl3_connect_375_loop_from_7:int, 0x1b)), eq(ssl3_connect_375_loop_from_7:int, 0x1d));
    var R0_51: bv64 := 0x1110:bv64 { .label = "2532_0" };
    goto(%phi_147, %phi_148);
  ];
  block %phi_146 {.originalLabel = "VFoMg2E4RVK3Vwtz7HwPow=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_375_loop_from_7:int, 0x2), eq(ssl3_connect_375_loop_from_7:int, 0x3)), eq(ssl3_connect_375_loop_from_7:int, 0x4)), eq(ssl3_connect_375_loop_from_7:int, 0x6)), eq(ssl3_connect_375_loop_from_7:int, 0x7)), eq(ssl3_connect_375_loop_from_7:int, 0x8)), eq(ssl3_connect_375_loop_from_7:int, 0xb)), eq(ssl3_connect_375_loop_from_7:int, 0xf)), eq(ssl3_connect_375_loop_from_7:int, 0x13)), eq(ssl3_connect_375_loop_from_7:int, 0x14)), eq(ssl3_connect_375_loop_from_7:int, 0x15)), eq(ssl3_connect_375_loop_from_7:int, 0x16)), eq(ssl3_connect_375_loop_from_7:int, 0x1a)), eq(ssl3_connect_375_loop_from_7:int, 0x1c));
    var R21_151: bv64 := R21_33:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := ssl3_connect_375_loop_from_7:int { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_147 {.originalLabel = "7krzrUlCQ0iSQ6e75mNGxw=="} [
    guard eq(extract(32, 0, R21_33:bv64), extract(32, 0, R0_51:bv64));
    var load54_25: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_52: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_152, %phi_153);
  ];
  block %phi_148 {.originalLabel = "7krzrUlCQ0iSQ6e75mNGxw=="} [
    guard boolnot(eq(extract(32, 0, R21_33:bv64), extract(32, 0, R0_51:bv64)));
    var R21_46: bv64 := R21_33:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_400);
  ];
  block %phi_152 {.originalLabel = "u4TowefMRJSQdk1JCr0lBw=="} [
    guard bvsle(extract(32, 0, R0_52:bv64), 0x0:bv32);
    var R0_123: bv64 := R0_52:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_153 {.originalLabel = "u4TowefMRJSQdk1JCr0lBw=="} [
    guard bvsgt(extract(32, 0, R0_52:bv64), 0x0:bv32);
    var R21_39: bv64 := 0x1120:bv64 { .label = "2700_0" };
    goto(%phi_154, %phi_155);
  ];
  block %phi_154 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    var R21_46: bv64 := R21_39:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_400);
  ];
  block %phi_155 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_156, %phi_157);
  ];
  block %phi_156 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_39:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x11 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_157 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_39:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x4 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_164 {.originalLabel = "QvtvGKIvTHeZlG0yudu0ag=="} [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R24_59:bv64));
    var load54_32: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_112: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_322, %phi_323);
  ];
  block %phi_165 {.originalLabel = "QvtvGKIvTHeZlG0yudu0ag=="} [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R24_59:bv64)));
    var R0_56: bv64 := 0x1130:bv64 { .label = "2556_0" };
    goto(%phi_166, %phi_167);
  ];
  block %phi_166 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_56:bv64));
    goto(%phi_301, %phi_302);
  ];
  block %phi_167 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_56:bv64)));
    var R0_57: bv64 := 0x1140:bv64 { .label = "2568_0" };
    goto(%phi_168, %phi_169);
  ];
  block %phi_168 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_57:bv64));
    var load54_30: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_102: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_287, %phi_288);
  ];
  block %phi_169 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_57:bv64)));
    var R0_58: bv64 := 0x1150:bv64 { .label = "2580_0" };
    goto(%phi_170, %phi_171);
  ];
  block %phi_170 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_58:bv64));
    var load54_29: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_98: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    assert eq(R30_in:bv64, 0x744:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_6:bv64, R1_retval_inlined_7:bv64, R2_retval_inlined_8:bv64, R3_retval_inlined_9:bv64) := call @reach_error_2240 (bvadd(R31_in:bv64, 0xffffffffffffff80:bv64), 0x744:bv64, bvadd(R31_in:bv64, 0xffffffffffffff80:bv64)) { .label = "3192_2" };
    goto(%phi_170_retval_inline);
  ];
  block %phi_171 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_58:bv64)));
    var R25_55: bv64 := 0x11a0:bv64 { .label = "2592_0" };
    goto(%phi_172, %phi_173);
  ];
  block %phi_172 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R25_55:bv64));
    var load54_28: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_89: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_260, %phi_261);
  ];
  block %phi_173 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R25_55:bv64)));
    var R0_59: bv64 := 0x11b0:bv64 { .label = "2604_0" };
    goto(%phi_174, %phi_175);
  ];
  block %phi_174 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_59:bv64));
    var load54_27: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_72: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_227, %phi_228);
  ];
  block %phi_175 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_59:bv64)));
    var R0_60: bv64 := 0x11d0:bv64 { .label = "2616_0" };
    goto(%phi_176, %phi_177);
  ];
  block %phi_176 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_60:bv64));
    var load54_26: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_67: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_204, %phi_205);
  ];
  block %phi_177 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_60:bv64)));
    var R0_61: bv64 := 0x1100:bv64 { .label = "2628_0" };
    goto(%phi_178, %phi_179);
  ];
  block %phi_178 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_61:bv64)));
    var R0_123: bv64 := 0x1:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_179 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_61:bv64));
    var load41_1: bv32 := Stack_n20_n16:bv32 { .label = "2640_0_0" };
    goto(%phi_180, %phi_181);
  ];
  block %phi_180 [
    guard bvsle(load41_1:bv32, 0x0:bv32);
    var load22_1: bv32 := Stack_n4_0:bv32 { .label = "3128_0_0" };
    var R21_69: bv64 := zero_extend(32, load22_1:bv32) { .label = "3128_0_1" };
    goto(%phi_193, %phi_194);
  ];
  block %phi_181 [
    guard bvsgt(load41_1:bv32, 0x0:bv32);
    var load28_1: bv32 := Stack_n16_n12:bv32 { .label = "2652_0_0" };
    goto(%phi_182, %phi_183);
  ];
  block %phi_182 [
    guard bvsle(load28_1:bv32, 0x0:bv32);
    goto(%ssl3_connect_4);
  ];
  block %phi_183 [
    guard bvsgt(load28_1:bv32, 0x0:bv32);
    var load23_1: bv32 := Stack_n16_n12:bv32 { .label = "2664_0_0" };
    var Stack_n20_n16: bv32 := load23_1:bv32 { .label = "2668_0" };
    var load24_1: bv32 := Stack_n4_0:bv32 { .label = "2672_0_0" };
    var R21_62: bv64 := zero_extend(32, load24_1:bv32) { .label = "2672_0_1" };
    goto(%phi_184, %phi_185);
  ];
  block %phi_184 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_62:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_185 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_186, %phi_187);
  ];
  block %phi_186 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_62:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x12 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_187 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_62:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x15 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_193 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_69:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_194 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_195, %phi_196);
  ];
  block %phi_195 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_69:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x5 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_196 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_69:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x14 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_204 {.originalLabel = "Ax+zFzpUT3mbT+/KeslDrg=="} [
    guard bvsle(extract(32, 0, R0_67:bv64), 0x0:bv32);
    var R0_123: bv64 := R0_67:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_205 {.originalLabel = "Ax+zFzpUT3mbT+/KeslDrg=="} [
    guard bvsgt(extract(32, 0, R0_67:bv64), 0x0:bv32);
    goto(%phi_206, %phi_207);
  ];
  block %phi_206 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_84: bv64 := 0x3:bv64 { .label = "3108_0" };
    goto(%phi_216, %phi_217);
  ];
  block %phi_207 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    var R21_76: bv64 := zero_extend(32, extract(32, 0, R25_55:bv64)) { .label = "2988_0" };
    goto(%phi_208, %phi_209);
  ];
  block %phi_208 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_76:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_209 [
    guard eq(R0_23:bv32, 0x0:bv32);
    var R21_79: bv64 := 0x11a0:bv64 { .label = "2996_0" };
    goto(%phi_210, %phi_211);
  ];
  block %phi_210 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_79:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x19 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_211 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_79:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x1a { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_216 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_84:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_217 [
    guard eq(R0_23:bv32, 0x0:bv32);
    var R21_87: bv64 := 0x3:bv64 { .label = "3116_0" };
    goto(%phi_218, %phi_219);
  ];
  block %phi_218 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_87:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x17 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_219 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_87:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x8 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_227 {.originalLabel = "ER1I3PPjSXGapWCXEirEcw=="} [
    guard bvsle(extract(32, 0, R0_72:bv64), 0x0:bv32);
    var R0_123: bv64 := R0_72:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_228 {.originalLabel = "ER1I3PPjSXGapWCXEirEcw=="} [
    guard bvsgt(extract(32, 0, R0_72:bv64), 0x0:bv32);
    var load27_1: bv32 := Stack_n24_n20:bv32 { .label = "3020_0_0" };
    var R0_77: bv64 := zero_extend(32, bvadd(load27_1:bv32, 0xfffffffb:bv32)) { .label = "3024_0" };
    var Stack_n24_n20: bv32 := bvadd(load27_1:bv32, 0xfffffffb:bv32) { .label = "3028_0" };
    goto(%phi_229, %phi_230);
  ];
  block %phi_229 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var Stack_n4_0: bv32 := 0x11d0:bv32 { .label = "3088_0" };
    var R21_108: bv64 := 0x1100:bv64 { .label = "3092_0" };
    goto(%phi_249, %phi_250);
  ];
  block %phi_230 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    goto(%phi_231, %phi_232);
  ];
  block %phi_231 [
    guard eq(extract(32, 0, R0_77:bv64), 0xfffffffe:bv32);
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3148_0" };
    var R21_100: bv64 := 0x1100:bv64 { .label = "3152_0" };
    goto(%phi_241, %phi_242);
  ];
  block %phi_232 [
    guard boolnot(eq(extract(32, 0, R0_77:bv64), 0xfffffffe:bv32));
    var R0_82: bv32 := bvshl(zero_extend(2, extract(30, 0, R0_77:bv64)), 0x2:bv32) { .label = "3044_0" };
    var R21_92: bv64 := 0x3:bv64 { .label = "3048_0" };
    var Stack_n24_n20: bv32 := R0_82:bv32 { .label = "3052_0" };
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3056_0" };
    goto(%phi_233, %phi_234);
  ];
  block %phi_233 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_92:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_234 [
    guard eq(R0_23:bv32, 0x0:bv32);
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3068_0" };
    var R21_95: bv64 := 0x3:bv64 { .label = "3072_0" };
    goto(%phi_235, %phi_236);
  ];
  block %phi_235 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_95:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x9 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_236 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_95:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0xf { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_241 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_100:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_242 [
    guard eq(R0_23:bv32, 0x0:bv32);
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3164_0" };
    var Stack_n24_n20: bv32 := 0xfffffffe:bv32 { .label = "3172_0" };
    var R21_103: bv64 := 0x1100:bv64 { .label = "3176_0" };
    goto(%phi_243, %phi_244);
  ];
  block %phi_243 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_103:bv64,
      var ssl3_connect_375_loop_from_7: int := 0xd );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_244 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_103:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x16 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_249 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_108:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_250 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_251, %phi_252);
  ];
  block %phi_251 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_108:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x1d );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_252 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_108:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0xb { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_260 {.originalLabel = "JcroMTVrS9eN6OrYBrgHhQ=="} [
    guard bvsle(extract(32, 0, R0_89:bv64), 0x0:bv32);
    var R0_123: bv64 := R0_89:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_261 {.originalLabel = "JcroMTVrS9eN6OrYBrgHhQ=="} [
    guard bvsgt(extract(32, 0, R0_89:bv64), 0x0:bv32);
    var load25_1: bv32 := Stack_n12_n8:bv32 { .label = "2936_0_0" };
    var load26_1: bv32 := Stack_n8_n4:bv32 { .label = "2944_0_0" };
    goto(%phi_262, %phi_263);
  ];
  block %phi_262 [
    guard boolnot(eq(load25_1:bv32, 0x0:bv32));
    var ZF_79: bv1 := bvcomp(load26_1:bv32, 0x0:bv32) { .label = "2948_1" };
    goto(%phi_266, %phi_267);
  ];
  block %phi_263 [
    guard eq(load25_1:bv32, 0x0:bv32);
    var ZF_83: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_166);
  ];
  block %phi_266 [
    guard eq(load26_1:bv32, 0x0:bv32);
    var ZF_83: bv1 := ZF_79:bv1 { .label = "phiback" };
    goto(%ssl3_connect_166);
  ];
  block %phi_267 [
    guard boolnot(eq(load26_1:bv32, 0x0:bv32));
    var R21_115: bv64 := 0x11b0:bv64 { .label = "2956_0" };
    goto(%phi_270, %phi_271);
  ];
  block %phi_270 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_115:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_271 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_272, %phi_273);
  ];
  block %phi_272 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_115:bv64,
      var ssl3_connect_375_loop_from_7: int := 0xa );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_273 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_115:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x7 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_287 {.originalLabel = "L8SpS+L2QPO+evild/0L9Q=="} [
    guard bvsle(extract(32, 0, R0_102:bv64), 0x0:bv32);
    var R0_123: bv64 := R0_102:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_288 {.originalLabel = "L8SpS+L2QPO+evild/0L9Q=="} [
    guard bvsgt(extract(32, 0, R0_102:bv64), 0x0:bv32);
    goto(%phi_289, %phi_290);
  ];
  block %phi_289 [
    guard eq(R0_39:bv32, 0x0:bv32);
    goto(%ssl3_connect_4);
  ];
  block %phi_290 [
    guard boolnot(eq(R0_39:bv32, 0x0:bv32));
    var R21_122: bv64 := 0x1150:bv64 { .label = "2908_0" };
    goto(%phi_291, %phi_292);
  ];
  block %phi_291 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_122:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_292 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_293, %phi_294);
  ];
  block %phi_293 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_122:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x18 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_294 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_122:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x1c { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_301 [
    guard eq(R0_26:bv32, 0xffffff00:bv32);
    var load54_31: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_107: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_306, %phi_307);
  ];
  block %phi_302 [
    guard boolnot(eq(R0_26:bv32, 0xffffff00:bv32));
    goto(%ssl3_connect_loop0_80);
  ];
  block %phi_306 {.originalLabel = "R4hEQ1xySUW/u6RQHHcsyQ=="} [
    guard bvsle(extract(32, 0, R0_107:bv64), 0x0:bv32);
    var R0_123: bv64 := R0_107:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_307 {.originalLabel = "R4hEQ1xySUW/u6RQHHcsyQ=="} [
    guard bvsgt(extract(32, 0, R0_107:bv64), 0x0:bv32);
    var R21_129: bv64 := 0x1140:bv64 { .label = "2860_0" };
    goto(%phi_308, %phi_309);
  ];
  block %phi_308 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    goto(%ssl3_connect_loop0_80);
  ];
  block %phi_309 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_310, %phi_311);
  ];
  block %phi_310 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_129:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x1 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_311 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_129:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x2 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_322 {.originalLabel = "8cXBVZw7Ra6M9EQnFl3few=="} [
    guard bvsle(extract(32, 0, R0_112:bv64), 0x0:bv32);
    var R0_123: bv64 := R0_112:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_323 {.originalLabel = "8cXBVZw7Ra6M9EQnFl3few=="} [
    guard bvsgt(extract(32, 0, R0_112:bv64), 0x0:bv32);
    goto(%phi_324, %phi_325);
  ];
  block %phi_324 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_144: bv64 := 0x1130:bv64 { .label = "2876_0" };
    goto(%phi_334, %phi_335);
  ];
  block %phi_325 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    var R21_137: bv64 := 0x11d0:bv64 { .label = "2816_0" };
    goto(%phi_326, %phi_327);
  ];
  block %phi_326 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_137:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_327 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_328, %phi_329);
  ];
  block %phi_328 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_137:bv64,
      var ssl3_connect_375_loop_from_7: int := 0xc );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_329 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_137:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x6 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_334 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_144:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_335 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_336, %phi_337);
  ];
  block %phi_336 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_144:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x1b );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_337 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_144:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x13 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_356 {.originalLabel = "UNLWlHR3Rx2cdGRNqquffA=="} [
    guard bvsgt(extract(32, 0, R0_116:bv64), 0x0:bv32);
    ( var R21_33: bv64 := R21_151:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x0 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_357 {.originalLabel = "UNLWlHR3Rx2cdGRNqquffA=="} [
    guard bvsle(extract(32, 0, R0_116:bv64), 0x0:bv32);
    var R0_123: bv64 := R0_116:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_170_retval_inline [
    var R31_283: bv64 := bvadd(R31_in:bv64, 0xffffffffffffff80:bv64) { .label = "phiback" };
    var R1_281: bv64 := 0xcb0:bv64 { .label = "phiback" };
    var R0_127: bv64 := 0xcc8:bv64 { .label = "phiback" };
    var R3_281: bv64 := 0xca0:bv64 { .label = "phiback" };
    var R2_281: bv64 := 0x3:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_return [
    assert eq(R31_in:bv64, R31_283:bv64) { .comment = "R31 preserved across calls" };
    return (R0_127:bv64, R1_281:bv64, R2_281:bv64, R3_281:bv64);
  ]
];




prog entry @main_1856 {
  .symbols = {
    .externalFunctions = [
      { .name = "_ITM_deregisterTMCloneTable"; .offset = 0x1ffc0 };
      { .name = "_ITM_registerTMCloneTable"; .offset = 0x1ffe0 };
      { .name = "__VERIFIER_nondet_int"; .offset = 0x20020 };
      { .name = "__VERIFIER_nondet_uint"; .offset = 0x20030 };
      { .name = "__assert_fail"; .offset = 0x20028 };
      { .name = "__cxa_finalize"; .offset = 0x1ffc8 };
      { .name = "__cxa_finalize"; .offset = 0x20008 };
      { .name = "__gmon_start__"; .offset = 0x1ffd0 };
      { .name = "__gmon_start__"; .offset = 0x20010 };
      { .name = "__libc_start_main@GLIBC_2.34"; .offset = 0x20000 };
      { .name = "abort"; .offset = 0x20018 }
    ];
    .globals = [
      { .name = "_DYNAMIC"; .address = 0x1fdc8; .size = 0x0 };
      { .name = "_GLOBAL_OFFSET_TABLE_"; .address = 0x1ffb8; .size = 0x0 };
      { .name = "_IO_stdin_used"; .address = 0xc98; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xe2c; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xe30; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20048; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "_start"; .address = 0x780; .size = 0x1a0 };
      { .name = "main"; .address = 0x740; .size = 0xc0 };
      { .name = "reach_error"; .address = 0x8c0; .size = 0x140 };
      { .name = "ssl3_connect"; .address = 0x8e8; .size = 0x1ce0 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x8a0 ]; [ 0x1fdc0; 0x84c ]; [ 0x1ffd8; 0x740 ]; [ 0x20040; 0x20040 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2WoZMs+vrC79bl8R/fB+xY8X88pPlUGAHsPgKIkAAAA" ]
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
      "H4sIAAAAAAAA/2NgwA2YGbgYKtiwiYszWDAwoYg1ArEQFjMYgVgBi/hkIFbCIi6LQ/0iHOa74RDXwWFOMQ71MTjEASOn/4Eg";
      "AQAA"
    ]
  };
  {
    .name = ".dynstr";
    .address = 0x3f0;
    .size = 0xd7;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3WNywrCQAxF80MWfKB7S5WBdlOK25C2aQlMMzAzgvj1xgeudJV7D4cbQNc1OHLkWVLm2DWlD8od9Z4BcV6C";
      "YsoUMyK81D/ipWrdyVUtatCRM4rmH/T6xpQS2+JE4q156YfPj4VEjQw3wkmUvNwZqA8xg0m2sbKRVKTwrIPdYg/n2h1L3BTr";
      "wzdud/AA6fpwjdcAAAA="
    ]
  };
  {
    .name = ".gnu.version";
    .address = 0x4c8;
    .size = 0x18;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgAAEmBkYGZiiGkAARr9YIGAAAAA==" ]
  };
  {
    .name = ".gnu.version_r";
    .address = 0x4e0;
    .size = 0x30;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NkYGLYzsDAIMAAAdMnTmNjYGBmOAgV2wLmMzGcgcoDAMfFBxgwAAAA" ]
  };
  {
    .name = ".rela.dyn";
    .address = 0x510;
    .size = 0xc0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/9vxl5EBBJhZwBTDAg4IfQBN3AcqfuM/qrgDO5RmYEIVh/IPQNUzAsWhUmBwAkmcFUn8ApI4G5L4AyRxTiRx";
      "AD83pNjAAAAA"
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
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBN9GBim/K0+uOIAc/w1ANWZudwYAAAA" ]
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
    .size = 0x544;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/41TTWxMURQ+b940LSpipqOtv5kpEWls6H2EjTdFZid0XkSQmLb+YiJNM60mfYtpbQSRGCpig0UXxpbgbXQq";
      "FhJWlJB0Ma2fkGoNM9N6nT7Xd+e9IkRjcfKdn++ce+4591r6QMqSKXmMqI+op8nSB2+m5YMv/QH5xf/KCup5thLyTqZbI7Jq";
      "jq6i5HvUzBBl6VPYlBFzQwY5v/IUUvJ/CJsq0Z1HnFfPdR5JdIECUlICBoFbicbSRNoIagQzYbMZNbKydItc/peizp/8INGT";
      "upnE81Bl77ngTOjSIPijyG3Mhs2WUq7rZ66lPyjNIreATC/yo3WhzapEm0r9vg2bPeDb9VXzIu7xGhLAzKJ10ubcAtW09Id/";
      "zW4Y95trdhbmLxNdkCDibAK29mxIBtMbkhRoSLag/mmcY+n37d4iUqqw35WaapVTZsydKsbLUjripyC9kG8y1XcBT0I6IZOw";
      "40Asob4dmAe2/RbvgIj4cbGXGBnHgEchRyA5cA8BWyFT0JuBUcFrI0PED0MOQAqI7QMWgXuB08A9wBmgJvhdZDQJ1MnYJTBO";
      "xk6Biesev0yx5grSXpcTS8jUvn2Z2p0pJ81Xd6opQqQMlZFC0AdcFLvhJq1mtdBrYmlwaI3tjyKf1tp6Zh70eltPe0irZUKv";
      "jQXmw7/R4VdC3+LwhT9g672LScu0qYafqH3hIuhxWz8h27q4dyGhGt4ZrnQUOSsnqlqOewjOON6kD715i1zpm+ZsieNfN821";
      "XCSEnTViZ9uws+3Y2Y6UpT8uvZVKh9e/VO2Wvtlc/EPPv/jk8E9YXFviIubDPS5NcSU/ydkbvDXucq+Pil4wj7uw89+d/oq8";
      "5Itw9Ffg7BViPszvdoErVbCHYH90uOfR8zDu58Mcb+cRz3OGf1s9Mhs3uZbpsmeT0VXDXaN2q8jxYb4NOdT/ylka/BcOfyHu";
      "hXfICnJtfcNXrviwk44vnN0D5+lsf5OoGVMNqqLd4h3elYj5K2i9itlTx8pIJ/6B8BcSZHizXIkKG7p4e1WfOetHLbFT4fNh";
      "n7kJrmgTnF2DX+TGYQu8M87ZVfjEHp+Pc4XBvgx7tp7I9Y7/qo//7RHnCv/QGGdnwb2Onj3O3z8D+wdMduwwRAUAAA=="
    ]
  };
  {
    .name = ".fini";
    .address = 0xc84;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0xc98;
    .size = 0x32;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML/YOD45J68k3ljPKUwvWS85M0fXKFEvmcGAAQAPWyEUMgAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xccc;
    .size = 0x4c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrb2YGBg4ADikl///zswMjBsAdIJQL7I7///S4C0C5DuANINQHoOkL4CpA8A6S9A+gqQlvnz//8bIA0A";
      "h9TrzEwAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xd18;
    .size = 0x118;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiH1+/f9vApJ0ZJcDiekA8QygmAFUD0jMAYi3AMVsoGIKQBwCxHeAYh5g";
      "vXwKc1nmMTtNZvK7d/cyH0xfBRDz/P7/nwWqTwSIe0D2AsU0IPoE5jLNYwwAMpcAsQZQfA4zWLyBca7APH63yXxTeKfyTOOe";
      "zjWDcybHLPbZbHNYmfK47t29fefmres3rl67fIWPwZHbG0OEQQZozA+Qf37+/y+BZJfLvbt8UOcwAAA3fjkrGAEAAA=="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xe30;
    .size = 0x20;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAGJGIHb3C2UAAWYgZmeAAAA9kbzyIAAAAA==" ]
  };
  {
    .name = ".init_array";
    .address = 0x1fdb8;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/1vAwQAGAIJ2gPwIAAAA" ]
  };
  {
    .name = ".fini_array";
    .address = 0x1fdc0;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA//PhYAADAKxG/ygIAAAA" ]
  };
  {
    .name = ".dynamic";
    .address = 0x1fdc8;
    .size = 0x1f0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/7WQsQ6CMBCGD6UgoAmDRAXekZUH8GEc3XRkZHRzdXRkcTBGasx9NSm7t3z57m97bQPROsAAnuAStpFyhe8J";
      "dvj5rTsrfAFL2JHXk/wx2ubL40zd0B/mSsbKhTzFrzCDW1iIXxwjd6vzOeb33jWM4cbNM34/N/69O5hM5r+svsctHfFbqE2L";
      "u38e8J78iYfyn/oAjdDO2vABAAA="
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
