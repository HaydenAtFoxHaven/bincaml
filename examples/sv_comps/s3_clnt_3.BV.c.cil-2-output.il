var $Global_131104_131112: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_int : () -> bv32;

prog entry @main_1792;

proc @main_1792
  (R0_in:bv64, R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R29_out:bv64, _PC_out:bv64)
  { .name = "main"; .address = 0x700; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x700; .originalLabel = "yBzJvRd4RnizvNnVCfy2RA=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1792_2" };
    var (R0_2:bv64, R1_2:bv64, R2_2:bv64, R3_2:bv64) := call @ssl3_connect_2216 (R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), R2_in:bv64, 0x70c:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), R3_in:bv64);
    goto(%main_return);
  ];
  block %main_return [
    var _PC_2: bv64 := _PC_in:bv64 { .label = "inlineret" };
    var load0_1: bv64 := Stack_n16_n8:bv64 { .label = "1808_0_0" };
    var load1_1: bv64 := Stack_n8_0:bv64 { .label = "1808_1_0" };
    assert eq(R30_in:bv64, load1_1:bv64) { .comment = "R30 preserved across calls" };
    assert true { .comment = "R31 preserved across calls" };
    return (0x0:bv64, load0_1:bv64, _PC_2:bv64);
  ]
];


proc @reach_error_2176
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x880; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x880; .originalLabel = "lxJkPFCRRpCTND97OK7Hyg=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2176_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2176_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load45_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0xc80:bv64, 0xc68:bv64, 0x3:bv64, 0xc58:bv64);
  ]
];


proc @ssl3_connect_2216
  (R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64)
    -> (R0_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "ssl3_connect"; .address = 0x8a8; .returnBlock = "ssl3_connect_return" }
[
  block %ssl3_connect_entry {.address = 0x8a8; .originalLabel = "+J3utSvKR1m84Fqhl4FDoQ=="} [
    var Stack_n128_n120: bv64 := R29_in:bv64 { .label = "2216_1" };
    var Stack_n120_n112: bv64 := R30_in:bv64 { .label = "2216_2" };
    var Stack_n112_n104: bv64 := R19_in:bv64 { .label = "2224_1" };
    var Stack_n104_n96: bv64 := R20_in:bv64 { .label = "2224_2" };
    var Stack_n96_n88: bv64 := R21_in:bv64 { .label = "2228_1" };
    var Stack_n88_n80: bv64 := R22_in:bv64 { .label = "2228_2" };
    var Stack_n80_n72: bv64 := R23_in:bv64 { .label = "2232_1" };
    var Stack_n72_n64: bv64 := R24_in:bv64 { .label = "2232_2" };
    var Stack_n64_n56: bv64 := R25_in:bv64 { .label = "2236_1" };
    var Stack_n56_n48: bv64 := R26_in:bv64 { .label = "2236_2" };
    var Stack_n48_n40: bv64 := R27_in:bv64 { .label = "2240_1" };
    var Stack_n40_n32: bv64 := R28_in:bv64 { .label = "2240_2" };
    var load52_1: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_2: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_3: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv32 := $__VERIFIER_nondet_int();
    var load52_4: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_5: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_6: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv32 := $__VERIFIER_nondet_int();
    var load52_7: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_10: bv32 := $__VERIFIER_nondet_int();
    var load52_8: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_12: bv32 := $__VERIFIER_nondet_int();
    var load52_9: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_10: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_11: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_12: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_13: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_14: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_19: bv32 := $__VERIFIER_nondet_int();
    var Stack_n24_n20: bv32 := R0_19:bv32 { .label = "2316_0" };
    var load52_15: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_16: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_17: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_23: bv32 := $__VERIFIER_nondet_int();
    var load52_18: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_19: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_26: bv32 := $__VERIFIER_nondet_int();
    var load52_20: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_21: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_29: bv32 := $__VERIFIER_nondet_int();
    var Stack_n20_n16: bv32 := R0_29:bv32 { .label = "2356_0" };
    var load52_22: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_23: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load52_24: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_33: bv32 := $__VERIFIER_nondet_int();
    var load52_25: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_35: bv32 := $__VERIFIER_nondet_int();
    var load52_26: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_37: bv32 := $__VERIFIER_nondet_int();
    var load52_27: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_39: bv32 := $__VERIFIER_nondet_int();
    var load52_28: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_41: bv32 := $__VERIFIER_nondet_int();
    var Stack_n12_n8: bv32 := R0_41:bv32 { .label = "2404_0" };
    var load52_29: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_43: bv32 := $__VERIFIER_nondet_int();
    var Stack_n8_n4: bv32 := R0_43:bv32 { .label = "2412_0" };
    var load52_30: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_45: bv32 := $__VERIFIER_nondet_int();
    var Stack_n16_n12: bv32 := R0_45:bv32 { .label = "2420_0" };
    var load52_31: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    goto(%phi_106, %phi_107);
  ];
  block %ssl3_connect_4 {.address = 0xa90; .originalLabel = "H8vzSgP4Q+C0VItcXXcWnA=="} [
    var load9_1: bv64 := Stack_n112_n104:bv64 { .label = "2704_1_0" };
    var load10_1: bv64 := Stack_n104_n96:bv64 { .label = "2704_2_0" };
    var load11_1: bv64 := Stack_n96_n88:bv64 { .label = "2712_1_0" };
    var load12_1: bv64 := Stack_n88_n80:bv64 { .label = "2712_2_0" };
    var load13_1: bv64 := Stack_n80_n72:bv64 { .label = "2716_1_0" };
    var load14_1: bv64 := Stack_n72_n64:bv64 { .label = "2716_2_0" };
    var load15_1: bv64 := Stack_n64_n56:bv64 { .label = "2720_1_0" };
    var load16_1: bv64 := Stack_n56_n48:bv64 { .label = "2720_2_0" };
    var load17_1: bv64 := Stack_n48_n40:bv64 { .label = "2724_1_0" };
    var load18_1: bv64 := Stack_n40_n32:bv64 { .label = "2724_2_0" };
    var load19_1: bv64 := Stack_n128_n120:bv64 { .label = "2728_0_0" };
    var load20_1: bv64 := Stack_n120_n112:bv64 { .label = "2728_1_0" };
    var R31_283: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_281: bv64 := R1_in:bv64 { .label = "phiback" };
    var R0_126: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    var R3_281: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_281: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_8 [
    guard eq(ZF_99:bv1, 0x1:bv1);
    goto(%ssl3_connect_4);
  ];
  block %ssl3_connect_10 {.address = 0xa64; .originalLabel = "2FNt5YjbTrmRVQoYWUCq5Q=="} [
    var load21_1: bv64 := Stack_n112_n104:bv64 { .label = "2660_1_0" };
    var load22_1: bv64 := Stack_n104_n96:bv64 { .label = "2660_2_0" };
    var load23_1: bv64 := Stack_n96_n88:bv64 { .label = "2664_1_0" };
    var load24_1: bv64 := Stack_n88_n80:bv64 { .label = "2664_2_0" };
    var load25_1: bv64 := Stack_n80_n72:bv64 { .label = "2668_1_0" };
    var load26_1: bv64 := Stack_n72_n64:bv64 { .label = "2668_2_0" };
    var load27_1: bv64 := Stack_n64_n56:bv64 { .label = "2672_1_0" };
    var load28_1: bv64 := Stack_n56_n48:bv64 { .label = "2672_2_0" };
    var load29_1: bv64 := Stack_n48_n40:bv64 { .label = "2676_1_0" };
    var load30_1: bv64 := Stack_n40_n32:bv64 { .label = "2676_2_0" };
    var load31_1: bv64 := Stack_n128_n120:bv64 { .label = "2680_0_0" };
    var load32_1: bv64 := Stack_n120_n112:bv64 { .label = "2680_1_0" };
    var R31_283: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_281: bv64 := R1_in:bv64 { .label = "phiback" };
    var R0_126: bv64 := R0_122:bv64 { .label = "phiback" };
    var R3_281: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_281: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_loop0_32 {.address = 0xa58; .originalLabel = "Z/NUIFTkRpCeSibnDIPCZg=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_375_loop_from_48:int, 0x0), eq(ssl3_connect_375_loop_from_48:int, 0x4)), eq(ssl3_connect_375_loop_from_48:int, 0x6)), eq(ssl3_connect_375_loop_from_48:int, 0x7)), eq(ssl3_connect_375_loop_from_48:int, 0xa)), eq(ssl3_connect_375_loop_from_48:int, 0xc)), eq(ssl3_connect_375_loop_from_48:int, 0xd)), eq(ssl3_connect_375_loop_from_48:int, 0x10)), eq(ssl3_connect_375_loop_from_48:int, 0x11)), eq(ssl3_connect_375_loop_from_48:int, 0x16)), eq(ssl3_connect_375_loop_from_48:int, 0x18)), eq(ssl3_connect_375_loop_from_48:int, 0x19)), eq(ssl3_connect_375_loop_from_48:int, 0x1a)), eq(ssl3_connect_375_loop_from_48:int, 0x1b));
    var load52_41: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_115: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_356, %phi_357);
  ];
  block %ssl3_connect_loop0_80 {.address = 0xad8; .originalLabel = "juWLVsPnTJKThfPn/I65qg=="} [
    ( var R21_47: bv64 := 0x1140:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %ssl3_connect_166 [
    guard eq(ZF_83:bv1, 0x1:bv1);
    goto(%ssl3_connect_4);
  ];
  block %ssl3_connect_loop1_398 {.address = 0x9b4; .originalLabel = "d/skwO2wTmOlafTMhLKDNw=="} [
    assert eq(R24_59:bv64, 0x1120:bv64);
    goto(%phi_164, %phi_165);
  ];
  block %ssl3_connect_loop1_400 {.address = 0x9b0; .originalLabel = "7fmMG/xiTpOc15rgR23GUQ=="} [
    var R24_59: bv64 := 0x1120:bv64 { .label = "2480_0" };
    ( var R21_47: bv64 := R21_46:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %ssl3_connect_loop2_432 [
    goto(%phi_145, %phi_146);
  ];
  block %ssl3_connect_452 {.address = 0x98c; .originalLabel = "7LqQCqZjT3CIx9rf54t7Xg=="} [
    goto(%phi_127, %phi_128);
  ];
  block %ssl3_connect_456 [
    guard eq(ZF_13:bv1, 0x1:bv1);
    goto(%ssl3_connect_4);
  ];
  block %phi_106 {.originalLabel = "Ku98HnflQbC8fuhYwcataA=="} [
    guard boolnot(eq(R0_4:bv32, 0xffff0400:bv32));
    goto(%ssl3_connect_4);
  ];
  block %phi_107 {.originalLabel = "Ku98HnflQbC8fuhYwcataA=="} [
    guard eq(R0_4:bv32, 0xffff0400:bv32);
    goto(%phi_108, %phi_109);
  ];
  block %phi_108 [
    guard eq(R0_10:bv32, 0x0:bv32);
    var load52_32: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_49: bv32 := $__VERIFIER_nondet_int();
    goto(%phi_113, %phi_114);
  ];
  block %phi_109 [
    guard boolnot(eq(R0_10:bv32, 0x0:bv32));
    goto(%ssl3_connect_452);
  ];
  block %phi_113 {.originalLabel = "31TY3c1/Q9u/ciK1+CRqZA=="} [
    guard boolnot(eq(R0_49:bv32, 0x0:bv32));
    var ZF_10: bv1 := bvcomp(R0_33:bv32, 0x0:bv32) { .label = "2696_1" };
    goto(%phi_117, %phi_118);
  ];
  block %phi_114 {.originalLabel = "31TY3c1/Q9u/ciK1+CRqZA=="} [
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
  block %phi_127 {.originalLabel = "7LqQCqZjT3CIx9rf54t7Xg=="} [
    guard boolnot(eq(R0_35:bv32, 0x0:bv32));
    var ZF_21: bv1 := bvcomp(R0_37:bv32, 0x0:bv32) { .label = "2448_1" };
    goto(%phi_131, %phi_132);
  ];
  block %phi_128 {.originalLabel = "7LqQCqZjT3CIx9rf54t7Xg=="} [
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
    var ssl3_connect_375_loop_from_7: int := 0x1d { .label = "phiback" };
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_136 [
    guard eq(R0_23:bv32, 0x0:bv32);
    goto(%phi_137, %phi_138);
  ];
  block %phi_137 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_33: bv64 := 0x1110:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_7: int := 0x11 { .label = "phiback" };
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_138 [
    guard eq(R0_12:bv32, 0x0:bv32);
    var R21_33: bv64 := 0x1110:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_7: int := 0x3 { .label = "phiback" };
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_145 {.originalLabel = "eUmYtN3HQ16wZXgso7cGTQ=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_375_loop_from_7:int, 0x1), eq(ssl3_connect_375_loop_from_7:int, 0x2)), eq(ssl3_connect_375_loop_from_7:int, 0x3)), eq(ssl3_connect_375_loop_from_7:int, 0x5)), eq(ssl3_connect_375_loop_from_7:int, 0x8)), eq(ssl3_connect_375_loop_from_7:int, 0x9)), eq(ssl3_connect_375_loop_from_7:int, 0xb)), eq(ssl3_connect_375_loop_from_7:int, 0xe)), eq(ssl3_connect_375_loop_from_7:int, 0xf)), eq(ssl3_connect_375_loop_from_7:int, 0x12)), eq(ssl3_connect_375_loop_from_7:int, 0x13)), eq(ssl3_connect_375_loop_from_7:int, 0x14)), eq(ssl3_connect_375_loop_from_7:int, 0x15)), eq(ssl3_connect_375_loop_from_7:int, 0x17)), eq(ssl3_connect_375_loop_from_7:int, 0x1c)), eq(ssl3_connect_375_loop_from_7:int, 0x1d));
    var R0_51: bv64 := 0x1110:bv64 { .label = "2468_0" };
    goto(%phi_147, %phi_148);
  ];
  block %phi_146 {.originalLabel = "Z/NUIFTkRpCeSibnDIPCZg=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_375_loop_from_7:int, 0x0), eq(ssl3_connect_375_loop_from_7:int, 0x4)), eq(ssl3_connect_375_loop_from_7:int, 0x6)), eq(ssl3_connect_375_loop_from_7:int, 0x7)), eq(ssl3_connect_375_loop_from_7:int, 0xa)), eq(ssl3_connect_375_loop_from_7:int, 0xc)), eq(ssl3_connect_375_loop_from_7:int, 0xd)), eq(ssl3_connect_375_loop_from_7:int, 0x10)), eq(ssl3_connect_375_loop_from_7:int, 0x11)), eq(ssl3_connect_375_loop_from_7:int, 0x16)), eq(ssl3_connect_375_loop_from_7:int, 0x18)), eq(ssl3_connect_375_loop_from_7:int, 0x19)), eq(ssl3_connect_375_loop_from_7:int, 0x1a)), eq(ssl3_connect_375_loop_from_7:int, 0x1b));
    var R21_151: bv64 := R21_33:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := ssl3_connect_375_loop_from_7:int { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_147 {.originalLabel = "eUmYtN3HQ16wZXgso7cGTQ=="} [
    guard eq(extract(32, 0, R21_33:bv64), extract(32, 0, R0_51:bv64));
    var load52_33: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_52: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_152, %phi_153);
  ];
  block %phi_148 {.originalLabel = "eUmYtN3HQ16wZXgso7cGTQ=="} [
    guard boolnot(eq(extract(32, 0, R21_33:bv64), extract(32, 0, R0_51:bv64)));
    var R21_46: bv64 := R21_33:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_400);
  ];
  block %phi_152 {.originalLabel = "duWGPDAfQmuXmrioMyTrsA=="} [
    guard bvsle(extract(32, 0, R0_52:bv64), 0x0:bv32);
    var R0_122: bv64 := R0_52:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_153 {.originalLabel = "duWGPDAfQmuXmrioMyTrsA=="} [
    guard bvsgt(extract(32, 0, R0_52:bv64), 0x0:bv32);
    var R21_39: bv64 := 0x1120:bv64 { .label = "2636_0" };
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
      var ssl3_connect_375_loop_from_7: int := 0x13 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_157 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_39:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0xd { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_164 {.originalLabel = "d/skwO2wTmOlafTMhLKDNw=="} [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R24_59:bv64));
    var load52_40: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_111: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_322, %phi_323);
  ];
  block %phi_165 {.originalLabel = "d/skwO2wTmOlafTMhLKDNw=="} [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R24_59:bv64)));
    var R0_56: bv64 := 0x1130:bv64 { .label = "2492_0" };
    goto(%phi_166, %phi_167);
  ];
  block %phi_166 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_56:bv64));
    goto(%phi_301, %phi_302);
  ];
  block %phi_167 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_56:bv64)));
    var R0_57: bv64 := 0x1140:bv64 { .label = "2504_0" };
    goto(%phi_168, %phi_169);
  ];
  block %phi_168 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_57:bv64));
    var load52_38: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_101: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_287, %phi_288);
  ];
  block %phi_169 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_57:bv64)));
    var R0_58: bv64 := 0x1150:bv64 { .label = "2516_0" };
    goto(%phi_170, %phi_171);
  ];
  block %phi_170 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_58:bv64));
    var load52_37: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_97: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    assert eq(R30_in:bv64, 0x704:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_6:bv64, R1_retval_inlined_7:bv64, R2_retval_inlined_8:bv64, R3_retval_inlined_9:bv64) := call @reach_error_2176 (bvadd(R31_in:bv64, 0xffffffffffffff80:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xffffffffffffff80:bv64)) { .label = "3120_2" };
    goto(%phi_170_retval_inline);
  ];
  block %phi_171 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_58:bv64)));
    var R25_55: bv64 := 0x11a0:bv64 { .label = "2528_0" };
    goto(%phi_172, %phi_173);
  ];
  block %phi_172 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R25_55:bv64));
    var load52_36: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_88: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_260, %phi_261);
  ];
  block %phi_173 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R25_55:bv64)));
    var R0_59: bv64 := 0x11b0:bv64 { .label = "2540_0" };
    goto(%phi_174, %phi_175);
  ];
  block %phi_174 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_59:bv64));
    var load52_35: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_72: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_227, %phi_228);
  ];
  block %phi_175 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_59:bv64)));
    var R0_60: bv64 := 0x11d0:bv64 { .label = "2552_0" };
    goto(%phi_176, %phi_177);
  ];
  block %phi_176 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_60:bv64));
    var load52_34: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_67: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_204, %phi_205);
  ];
  block %phi_177 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_60:bv64)));
    var R0_61: bv64 := 0x1100:bv64 { .label = "2564_0" };
    goto(%phi_178, %phi_179);
  ];
  block %phi_178 [
    guard boolnot(eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_61:bv64)));
    var R0_122: bv64 := 0x1:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_179 [
    guard eq(extract(32, 0, R21_47:bv64), extract(32, 0, R0_61:bv64));
    var load35_1: bv32 := Stack_n20_n16:bv32 { .label = "2576_0_0" };
    goto(%phi_180, %phi_181);
  ];
  block %phi_180 [
    guard bvsle(load35_1:bv32, 0x0:bv32);
    var load4_1: bv32 := Stack_n4_0:bv32 { .label = "3064_0_0" };
    var R21_69: bv64 := zero_extend(32, load4_1:bv32) { .label = "3064_0_1" };
    goto(%phi_193, %phi_194);
  ];
  block %phi_181 [
    guard bvsgt(load35_1:bv32, 0x0:bv32);
    var load5_1: bv32 := Stack_n16_n12:bv32 { .label = "2588_0_0" };
    goto(%phi_182, %phi_183);
  ];
  block %phi_182 [
    guard bvsle(load5_1:bv32, 0x0:bv32);
    goto(%ssl3_connect_4);
  ];
  block %phi_183 [
    guard bvsgt(load5_1:bv32, 0x0:bv32);
    var load7_1: bv32 := Stack_n16_n12:bv32 { .label = "2600_0_0" };
    var Stack_n20_n16: bv32 := load7_1:bv32 { .label = "2604_0" };
    var load8_1: bv32 := Stack_n4_0:bv32 { .label = "2608_0_0" };
    var R21_62: bv64 := zero_extend(32, load8_1:bv32) { .label = "2608_0_1" };
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
      var ssl3_connect_375_loop_from_7: int := 0x1 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_187 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_62:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x16 { .label = "phiback" };
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
      var ssl3_connect_375_loop_from_7: int := 0xf );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_196 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_69:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x18 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_204 {.originalLabel = "ncXQeIy6R7Ch5OwHEru31w=="} [
    guard bvsle(extract(32, 0, R0_67:bv64), 0x0:bv32);
    var R0_122: bv64 := R0_67:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_205 {.originalLabel = "ncXQeIy6R7Ch5OwHEru31w=="} [
    guard bvsgt(extract(32, 0, R0_67:bv64), 0x0:bv32);
    goto(%phi_206, %phi_207);
  ];
  block %phi_206 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_84: bv64 := 0x3:bv64 { .label = "3044_0" };
    goto(%phi_216, %phi_217);
  ];
  block %phi_207 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    var R21_76: bv64 := zero_extend(32, extract(32, 0, R25_55:bv64)) { .label = "2924_0" };
    goto(%phi_208, %phi_209);
  ];
  block %phi_208 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_76:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_209 [
    guard eq(R0_23:bv32, 0x0:bv32);
    var R21_79: bv64 := 0x11a0:bv64 { .label = "2932_0" };
    goto(%phi_210, %phi_211);
  ];
  block %phi_210 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_79:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x15 );
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
    var R21_87: bv64 := 0x3:bv64 { .label = "3052_0" };
    goto(%phi_218, %phi_219);
  ];
  block %phi_218 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_87:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x8 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_219 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_87:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0xc { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_227 {.originalLabel = "B2mwSMrFRZG5OZzncadVbA=="} [
    guard bvsle(extract(32, 0, R0_72:bv64), 0x0:bv32);
    var R0_122: bv64 := R0_72:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_228 {.originalLabel = "B2mwSMrFRZG5OZzncadVbA=="} [
    guard bvsgt(extract(32, 0, R0_72:bv64), 0x0:bv32);
    var load6_1: bv32 := Stack_n24_n20:bv32 { .label = "2956_0_0" };
    var R0_77: bv64 := zero_extend(32, bvadd(load6_1:bv32, 0xfffffffb:bv32)) { .label = "2960_0" };
    var Stack_n24_n20: bv32 := bvadd(load6_1:bv32, 0xfffffffb:bv32) { .label = "2964_0" };
    goto(%phi_229, %phi_230);
  ];
  block %phi_229 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var Stack_n4_0: bv32 := 0x11d0:bv32 { .label = "3024_0" };
    var R21_108: bv64 := 0x1100:bv64 { .label = "3028_0" };
    goto(%phi_249, %phi_250);
  ];
  block %phi_230 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    goto(%phi_231, %phi_232);
  ];
  block %phi_231 [
    guard eq(extract(32, 0, R0_77:bv64), 0xfffffffe:bv32);
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3084_0" };
    var R21_100: bv64 := 0x1100:bv64 { .label = "3088_0" };
    goto(%phi_241, %phi_242);
  ];
  block %phi_232 [
    guard boolnot(eq(extract(32, 0, R0_77:bv64), 0xfffffffe:bv32));
    var R0_82: bv32 := bvshl(zero_extend(2, extract(30, 0, R0_77:bv64)), 0x2:bv32) { .label = "2980_0" };
    var R21_92: bv64 := 0x3:bv64 { .label = "2984_0" };
    var Stack_n24_n20: bv32 := R0_82:bv32 { .label = "2988_0" };
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "2992_0" };
    goto(%phi_233, %phi_234);
  ];
  block %phi_233 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_92:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_234 [
    guard eq(R0_23:bv32, 0x0:bv32);
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3004_0" };
    var R21_95: bv64 := 0x3:bv64 { .label = "3008_0" };
    goto(%phi_235, %phi_236);
  ];
  block %phi_235 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_95:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x1c );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_236 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_95:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x1b { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_241 [
    guard boolnot(eq(R0_23:bv32, 0x0:bv32));
    ( var R21_47: bv64 := R21_100:bv64 );
    goto(%ssl3_connect_loop1_398);
  ];
  block %phi_242 [
    guard eq(R0_23:bv32, 0x0:bv32);
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3100_0" };
    var R21_103: bv64 := 0x1100:bv64 { .label = "3104_0" };
    goto(%phi_243, %phi_244);
  ];
  block %phi_243 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_103:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x5 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_244 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_103:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0xa { .label = "phiback" };
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
      var ssl3_connect_375_loop_from_7: int := 0x12 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_252 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_108:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x6 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_260 {.originalLabel = "h0kkboTqSTq47mN4PR3ZeA=="} [
    guard bvsle(extract(32, 0, R0_88:bv64), 0x0:bv32);
    var R0_122: bv64 := R0_88:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_261 {.originalLabel = "h0kkboTqSTq47mN4PR3ZeA=="} [
    guard bvsgt(extract(32, 0, R0_88:bv64), 0x0:bv32);
    var load33_1: bv32 := Stack_n12_n8:bv32 { .label = "2872_0_0" };
    var load34_1: bv32 := Stack_n8_n4:bv32 { .label = "2880_0_0" };
    goto(%phi_262, %phi_263);
  ];
  block %phi_262 [
    guard boolnot(eq(load33_1:bv32, 0x0:bv32));
    var ZF_79: bv1 := bvcomp(load34_1:bv32, 0x0:bv32) { .label = "2884_1" };
    goto(%phi_266, %phi_267);
  ];
  block %phi_263 [
    guard eq(load33_1:bv32, 0x0:bv32);
    var ZF_83: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_166);
  ];
  block %phi_266 [
    guard eq(load34_1:bv32, 0x0:bv32);
    var ZF_83: bv1 := ZF_79:bv1 { .label = "phiback" };
    goto(%ssl3_connect_166);
  ];
  block %phi_267 [
    guard boolnot(eq(load34_1:bv32, 0x0:bv32));
    var R21_115: bv64 := 0x11b0:bv64 { .label = "2892_0" };
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
      var ssl3_connect_375_loop_from_7: int := 0x9 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_273 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_115:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x4 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_287 {.originalLabel = "QmdiayYjR9ugfYSAkA5cDA=="} [
    guard bvsle(extract(32, 0, R0_101:bv64), 0x0:bv32);
    var R0_122: bv64 := R0_101:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_288 {.originalLabel = "QmdiayYjR9ugfYSAkA5cDA=="} [
    guard bvsgt(extract(32, 0, R0_101:bv64), 0x0:bv32);
    goto(%phi_289, %phi_290);
  ];
  block %phi_289 [
    guard eq(R0_39:bv32, 0x0:bv32);
    goto(%ssl3_connect_4);
  ];
  block %phi_290 [
    guard boolnot(eq(R0_39:bv32, 0x0:bv32));
    var R21_122: bv64 := 0x1150:bv64 { .label = "2844_0" };
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
      var ssl3_connect_375_loop_from_7: int := 0xb );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_294 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_122:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x7 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_301 [
    guard eq(R0_26:bv32, 0xffffff00:bv32);
    var load52_39: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_106: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_306, %phi_307);
  ];
  block %phi_302 [
    guard boolnot(eq(R0_26:bv32, 0xffffff00:bv32));
    goto(%ssl3_connect_loop0_80);
  ];
  block %phi_306 {.originalLabel = "eYeNDVgFSdyAytXTahc5Gg=="} [
    guard bvsle(extract(32, 0, R0_106:bv64), 0x0:bv32);
    var R0_122: bv64 := R0_106:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_307 {.originalLabel = "eYeNDVgFSdyAytXTahc5Gg=="} [
    guard bvsgt(extract(32, 0, R0_106:bv64), 0x0:bv32);
    var R21_129: bv64 := 0x1140:bv64 { .label = "2796_0" };
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
      var ssl3_connect_375_loop_from_7: int := 0xe );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_311 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_129:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x19 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_322 {.originalLabel = "xagSvNAVRdKcC+asbgaJhg=="} [
    guard bvsle(extract(32, 0, R0_111:bv64), 0x0:bv32);
    var R0_122: bv64 := R0_111:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_323 {.originalLabel = "xagSvNAVRdKcC+asbgaJhg=="} [
    guard bvsgt(extract(32, 0, R0_111:bv64), 0x0:bv32);
    goto(%phi_324, %phi_325);
  ];
  block %phi_324 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_144: bv64 := 0x1130:bv64 { .label = "2812_0" };
    goto(%phi_334, %phi_335);
  ];
  block %phi_325 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    var R21_137: bv64 := 0x11d0:bv64 { .label = "2752_0" };
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
      var ssl3_connect_375_loop_from_7: int := 0x2 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_329 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_137:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x0 { .label = "phiback" };
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
      var ssl3_connect_375_loop_from_7: int := 0x17 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_337 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_151: bv64 := R21_144:bv64 { .label = "phiback" };
    var ssl3_connect_375_loop_from_48: int := 0x10 { .label = "phiback" };
    goto(%ssl3_connect_loop0_32);
  ];
  block %phi_356 {.originalLabel = "FMaSscKIQnKnk1JHiIn47Q=="} [
    guard bvsgt(extract(32, 0, R0_115:bv64), 0x0:bv32);
    ( var R21_33: bv64 := R21_151:bv64,
      var ssl3_connect_375_loop_from_7: int := 0x14 );
    goto(%ssl3_connect_loop2_432);
  ];
  block %phi_357 {.originalLabel = "FMaSscKIQnKnk1JHiIn47Q=="} [
    guard bvsle(extract(32, 0, R0_115:bv64), 0x0:bv32);
    var R0_122: bv64 := R0_115:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_170_retval_inline [
    var R31_283: bv64 := bvadd(R31_in:bv64, 0xffffffffffffff80:bv64) { .label = "phiback" };
    var R1_281: bv64 := 0xc68:bv64 { .label = "phiback" };
    var R0_126: bv64 := 0xc80:bv64 { .label = "phiback" };
    var R3_281: bv64 := 0xc58:bv64 { .label = "phiback" };
    var R2_281: bv64 := 0x3:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_return [
    assert eq(R31_in:bv64, R31_283:bv64) { .comment = "R31 preserved across calls" };
    return (R0_126:bv64, R1_281:bv64, R2_281:bv64, R3_281:bv64);
  ]
];




prog entry @main_1792 {
  .symbols = {
    .externalFunctions = [
      { .name = "_ITM_deregisterTMCloneTable"; .offset = 0x1ffc0 };
      { .name = "_ITM_registerTMCloneTable"; .offset = 0x1ffe0 };
      { .name = "__VERIFIER_nondet_int"; .offset = 0x20020 };
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
      { .name = "_IO_stdin_used"; .address = 0xc50; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xde4; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xde8; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20040; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "_start"; .address = 0x740; .size = 0x1a0 };
      { .name = "main"; .address = 0x700; .size = 0xc0 };
      { .name = "reach_error"; .address = 0x880; .size = 0x140 };
      { .name = "ssl3_connect"; .address = 0x8a8; .size = 0x1ca0 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x860 ]; [ 0x1fdc0; 0x80c ]; [ 0x1ffd8; 0x700 ]; [ 0x20038; 0x20038 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2W4tkDgoPanM2of258WG78WNAw3ZwwBAExI17AkAAAA" ]
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
    .size = 0x108;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2NgwA2YGbgYDNiwiYszGDAwoYhlAbEQFjMYgVgBi3gNECthEZfFob4bh/luOMR1cJgTg0M9AKqFR7IIAQAA"
    ]
  };
  {
    .name = ".dynstr";
    .address = 0x3d8;
    .size = 0xc0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3WMywrCQAxF80MO+ED3lioDdlOK25BO0xKYZmBmFuLXG0Xcucq9l5MD6IcOJ868SKmch66JSXmgMTIgLmtS";
      "LJVyRYQP+ge8t72/+LZHTTpxRdFqK5XC9jqTRGtRxvCVrSRqS3gQzqIU5clAY8oVDDLFxhzFlfSuwa47wvXmzw3u3Pb0i/sD";
      "vAAkaXJ+wAAAAA=="
    ]
  };
  {
    .name = ".gnu.version";
    .address = 0x498;
    .size = 0x16;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgAAEmBkYGZigGkQDbLJj8FgAAAA==" ]
  };
  {
    .name = ".gnu.version_r";
    .address = 0x4b0;
    .size = 0x30;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NkYGJYwMDAIMAAAdMnTmNjYGBmWAUV2wLmMzFshcoDAOj7yeAwAAAA" ]
  };
  {
    .name = ".rela.dyn";
    .address = 0x4e0;
    .size = 0xc0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/9vxl5EBBJhZwBRDAgeEPoAmzgMVv/EfVZyBHUJZMDChiMP4B6DqGYHiMC0gcAJJnBVJ/AKSOBuS+AMkcU4k";
      "cQCkZ34mwAAAAA=="
    ]
  };
  {
    .name = ".rela.plt";
    .address = 0x5a0;
    .size = 0x90;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/03IKQ4AIBAAsclyBoVEIvn/CwmKqSwET2RIfF1f9FNf9Uvf9Fvf9Uc/9BcLhMffkAAAAA=="
    ]
  };
  {
    .name = ".init";
    .address = 0x630;
    .size = 0x18;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP9GBim/K0+uOIAc/w1AEoHgjAYAAAA" ]
  };
  {
    .name = ".plt";
    .address = 0x650;
    .size = 0x80;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA//tQvX/lBwaGD4L/3H8KPLKfqMAkf01egfkqDAswMkwQZHL4KcDEAJYD89mAfCUkPheQ74TE5wPyk5D4QkB+";
      "ExJfDMhfBOEDADC+jJiAAAAA"
    ]
  };
  {
    .name = ".text";
    .address = 0x700;
    .size = 0x53c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/41TS0wTURS906kBFWOkLR9/pWiMIW6QNxrdOPWT7ozSiTF+CxglViSkIJFZFN24QBPqJ8aNn8SFZYtRZ6Ng";
      "XJjoSoFI4qL4i0ZRpC0wlPF5XmfQRCNxcXLuve/cO/fd+8bSHyUtmRKNRJeJOmstvf9On3x4yF8hD/4vVlDni5XAe5l6RmTV";
      "fLOKEh9QM0U0Rl9CpowzN9DP+dXnQD7+MWSqRHefcF461/dIom4iKSGBA+AtRJ/7iLQR1AikQmYdaozJUg+5/EOizp/6ANGz";
      "ypn4y2DRma7ATPBSP/RvkLt1LGTW53Ndv3It/WF+FumFZHqQH3EFN6kSbcz3+y5kdkKfr79cNS/iHsNABWYWcUmb0gtV09If";
      "/zW717jfXLOzMH+ZqFsCxLcJ3BCpTgRuVsNen6hH/XP4jqU/sHsLS8nsfldyskFOmlF3Mhebl9Rx3gGcBqZkqmoHnwLagAn4";
      "MTCWUNUCzoCbwSeBJuAEEAWOi71EyWgEHwOOAmloj4AbgEnYdeCI0DWTcQh8EDgAZHG2D5wD7wVPg/eAZ8Ca0LeTUStYJ2OX";
      "4BgZOwXHbxT7ZYrWFZI2XEAsLlPL9mVqR6qANF/l2dowkTIwjxSC/chF0Ztu0spWC7ss2gcNrbHjEeTTWttOzYddZdudxaSV";
      "M2GXRysWIL7B0RfB3uzoRbzCtoNLSEs1q4afqGXRYtgx226SbVvcOxtXDc8MV1pznBUQeZfjHkIzijfpQ2+eHFcuT3NW4sTX";
      "TXMtHQ5iZ1uxs23Y2XbsbEfS0p/m30qRo7u9VO2Qpmwt/sPif+nJ0TdZXCtxEfPhHpcmuZKZ4Owt3hp3uasjohfM4x78zA+n";
      "vxzPx8Ic/WU5e4UzH+bXm+WKF/4A/E+O9gJ6fo37+TDH3gzOM5zhvy0dmT03uZZqt2eT0lXDXaZ2qMjxYb41adQf56wP+kFH";
      "vwj3wjtkWbm8qmacKz7spPU7Z/eheT7b3wRqRlWDvLRbvMN7EjF/IVWrmD21rgy34T8Q8WycDM8YVyLChy3envcbZ7dRS+xU";
      "xHzYZ/orV7SvnF1HXOTG4Au+O8rZNcTEHl+OcoXBvwJ/tp7I9Yz+ri987xfOzkNzC716nX++C/5PPVM4izwFAAA="
    ]
  };
  {
    .name = ".fini";
    .address = 0xc3c;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0xc50;
    .size = 0x32;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML/YOD45J68k3ljPKUwvWS85M0fXSC+ZgcGAAQCjJ99jMgAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xc84;
    .size = 0x4c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrb2YGBg4ADiml///zswMjDsAdIJQL7M7///S4C0D5DuANIdQHoOkL4DpA8A6T9A+gqQVvnz//8bIA0A";
      "Ig1j2kwAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xcd0;
    .size = 0x118;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiEN+/f9vApJ0ZJcDiekA8QKgmAFUD0jMAYj3AMVsoGIKIH1A/AQo5gHW";
      "y6cwl2Ues9NkJr97dy/zwfRVALHI7///WaD6RIC4B6QfKKYB0Scwl2keYwCQuQSIDYDiU5jB4g2McwXm8btN5pvCO5VnGvd0";
      "rhmcMzlmsc9mm8PKlMd17+7tOzdvXb9x9drlK3wMjtzeGCIMMkBjfgCxyc///yWQ7HK5d5cP6hwGAM0CDwsYAQAA"
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xde8;
    .size = 0x20;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAGJGIHb3C2UAAWYgZmeAAAA9kbzyIAAAAA==" ]
  };
  {
    .name = ".init_array";
    .address = 0x1fdb8;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/0vgYAADALUxJoYIAAAA" ]
  };
  {
    .name = ".fini_array";
    .address = 0x1fdc0;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/+PhYAADAEGEYgEIAAAA" ]
  };
  {
    .name = ".dynamic";
    .address = 0x1fdc8;
    .size = 0x1f0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/7WQPRKCMBCFF+THH+xgVOQQHMA7eRXtKDkCpaVHsKS0pLSxcBwSx9kvRejZ5pu3L7svSSBaVxjAFmawTpRb";
      "9AnjgL6NOnlEL2EJ7/jVxH8be/6zC1XH9PuFklh54K/dPriBe1iIX6yRwWo+a+QCc5jCHWxjv/+M/Hu7/NUk/2v1Pe6oQXfM";
      "W7T75xe6wf+gI5mnfrW8ovbwAQAA"
    ]
  };
  {
    .name = ".got";
    .address = 0x1ffb8;
    .size = 0x30;
    .readOnly = true;
    .bytes = [ "H4sIAAAAAAAA/zvxl5EBL2BH5QIA/iRaSjAAAAA=" ]
  };
  {
    .name = ".got.plt";
    .address = 0x1ffe8;
    .size = 0x48;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgwA4C2EijAUbxQWlIAAAA" ]
  };
  {
    .name = ".data";
    .address = 0x20030;
    .size = 0x10;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NggAALBiYwDQCWolv3EAAAAA==" ]
  };
  {
    .name = ".bss";
    .address = 0x20040;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NggAAAad8iZQgAAAA=" ]
  }
]
} ;
