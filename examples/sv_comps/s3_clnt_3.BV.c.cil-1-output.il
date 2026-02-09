var $Global_131104_131112: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_int : () -> bv32;

prog entry @main_1792;

proc @main_1792
  (R0_in:bv64, R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R29_out:bv64, _PC_out:bv64)
  { .name = "main"; .address = 0x700; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x700; .originalLabel = "Nys0ecWsS2KaKmH+0xZcOQ=="} [
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
  block %reach_error_entry {.address = 0x880; .originalLabel = "0MRF7u6iTnG1bbE9VWSfGw=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2176_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2176_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load55_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0xd70:bv64, 0xd58:bv64, 0x3:bv64, 0xd48:bv64);
  ]
];


proc @ssl3_connect_2216
  (R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64)
    -> (R0_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "ssl3_connect"; .address = 0x8a8; .returnBlock = "ssl3_connect_return" }
[
  block %ssl3_connect_entry {.address = 0x8a8; .originalLabel = "l8hYHZdERCOG8iwX798mTw=="} [
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
    var load54_1: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_2: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_3: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv32 := $__VERIFIER_nondet_int();
    var load54_4: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_5: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_6: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv32 := $__VERIFIER_nondet_int();
    var load54_7: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_10: bv32 := $__VERIFIER_nondet_int();
    var load54_8: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_12: bv32 := $__VERIFIER_nondet_int();
    var load54_9: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_10: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_11: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_12: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_13: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_14: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_19: bv32 := $__VERIFIER_nondet_int();
    var Stack_n20_n16: bv32 := R0_19:bv32 { .label = "2316_0" };
    var load54_15: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_21: bv32 := $__VERIFIER_nondet_int();
    var Stack_n28_n24: bv32 := R0_21:bv32 { .label = "2324_0" };
    var load54_16: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_17: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_24: bv32 := $__VERIFIER_nondet_int();
    var load54_18: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_19: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_27: bv32 := $__VERIFIER_nondet_int();
    var load54_20: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_21: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_30: bv32 := $__VERIFIER_nondet_int();
    var Stack_n24_n20: bv32 := R0_30:bv32 { .label = "2360_0" };
    var load54_22: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_23: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load54_24: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_34: bv32 := $__VERIFIER_nondet_int();
    var load54_25: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_36: bv32 := $__VERIFIER_nondet_int();
    var load54_26: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_38: bv32 := $__VERIFIER_nondet_int();
    var load54_27: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_40: bv32 := $__VERIFIER_nondet_int();
    var load54_28: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_42: bv32 := $__VERIFIER_nondet_int();
    var Stack_n12_n8: bv32 := R0_42:bv32 { .label = "2408_0" };
    var load54_29: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_44: bv32 := $__VERIFIER_nondet_int();
    var Stack_n8_n4: bv32 := R0_44:bv32 { .label = "2416_0" };
    var load54_30: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_46: bv32 := $__VERIFIER_nondet_int();
    var Stack_n16_n12: bv32 := R0_46:bv32 { .label = "2424_0" };
    var load54_31: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    goto(%phi_110, %phi_111);
  ];
  block %ssl3_connect_4 {.address = 0xac8; .originalLabel = "z0G+YFVaTSynZrMIym/lmg=="} [
    var load5_1: bv64 := Stack_n112_n104:bv64 { .label = "2760_1_0" };
    var load6_1: bv64 := Stack_n104_n96:bv64 { .label = "2760_2_0" };
    var load7_1: bv64 := Stack_n96_n88:bv64 { .label = "2768_1_0" };
    var load8_1: bv64 := Stack_n88_n80:bv64 { .label = "2768_2_0" };
    var load9_1: bv64 := Stack_n80_n72:bv64 { .label = "2772_1_0" };
    var load10_1: bv64 := Stack_n72_n64:bv64 { .label = "2772_2_0" };
    var load11_1: bv64 := Stack_n64_n56:bv64 { .label = "2776_1_0" };
    var load12_1: bv64 := Stack_n56_n48:bv64 { .label = "2776_2_0" };
    var load13_1: bv64 := Stack_n48_n40:bv64 { .label = "2780_1_0" };
    var load14_1: bv64 := Stack_n40_n32:bv64 { .label = "2780_2_0" };
    var load15_1: bv64 := Stack_n128_n120:bv64 { .label = "2784_0_0" };
    var load16_1: bv64 := Stack_n120_n112:bv64 { .label = "2784_1_0" };
    var R31_371: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_368: bv64 := R1_366:bv64 { .label = "phiback" };
    var R0_181: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    var R3_369: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_369: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_8 [
    guard eq(ZF_147:bv1, 0x1:bv1);
    var R1_366: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %ssl3_connect_10 {.address = 0xa9c; .originalLabel = "WhypEHqrSl63ZAYCGH3lHA=="} [
    var load20_1: bv64 := Stack_n112_n104:bv64 { .label = "2716_1_0" };
    var load21_1: bv64 := Stack_n104_n96:bv64 { .label = "2716_2_0" };
    var load22_1: bv64 := Stack_n96_n88:bv64 { .label = "2720_1_0" };
    var load23_1: bv64 := Stack_n88_n80:bv64 { .label = "2720_2_0" };
    var load24_1: bv64 := Stack_n80_n72:bv64 { .label = "2724_1_0" };
    var load25_1: bv64 := Stack_n72_n64:bv64 { .label = "2724_2_0" };
    var load26_1: bv64 := Stack_n64_n56:bv64 { .label = "2728_1_0" };
    var load27_1: bv64 := Stack_n56_n48:bv64 { .label = "2728_2_0" };
    var load28_1: bv64 := Stack_n48_n40:bv64 { .label = "2732_1_0" };
    var load29_1: bv64 := Stack_n40_n32:bv64 { .label = "2732_2_0" };
    var load30_1: bv64 := Stack_n128_n120:bv64 { .label = "2736_0_0" };
    var load31_1: bv64 := Stack_n120_n112:bv64 { .label = "2736_1_0" };
    var R31_371: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_368: bv64 := R1_361:bv64 { .label = "phiback" };
    var R0_181: bv64 := R0_177:bv64 { .label = "phiback" };
    var R3_369: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_369: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_loop0_30 {.address = 0xa90; .originalLabel = "kIkYGdIXRS2Uw/kDMEma6A=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_537_loop_from_57:int, 0x0), eq(ssl3_connect_537_loop_from_57:int, 0x1)), eq(ssl3_connect_537_loop_from_57:int, 0x2)), eq(ssl3_connect_537_loop_from_57:int, 0x3)), eq(ssl3_connect_537_loop_from_57:int, 0x4)), eq(ssl3_connect_537_loop_from_57:int, 0x5)), eq(ssl3_connect_537_loop_from_57:int, 0x7)), eq(ssl3_connect_537_loop_from_57:int, 0x8)), eq(ssl3_connect_537_loop_from_57:int, 0x9)), eq(ssl3_connect_537_loop_from_57:int, 0xb)), eq(ssl3_connect_537_loop_from_57:int, 0xe)), eq(ssl3_connect_537_loop_from_57:int, 0x15)), eq(ssl3_connect_537_loop_from_57:int, 0x18)), eq(ssl3_connect_537_loop_from_57:int, 0x19)), eq(ssl3_connect_537_loop_from_57:int, 0x1b)), eq(ssl3_connect_537_loop_from_57:int, 0x20)), eq(ssl3_connect_537_loop_from_57:int, 0x22));
    var load54_45: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_170: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_469, %phi_470);
  ];
  block %ssl3_connect_loop0_36 {.address = 0xb44; .originalLabel = "fTIp8ADeSKu9PARbAynQwg=="} [
    goto(%phi_446, %phi_447);
  ];
  block %ssl3_connect_loop0_68 {.address = 0xb00; .originalLabel = "hVeZ7c0lRB6b9NV97zhnnA=="} [
    goto(%phi_428, %phi_429);
  ];
  block %ssl3_connect_loop0_106 [
    goto(%phi_408, %phi_409);
  ];
  block %ssl3_connect_loop0_152 [
    goto(%phi_384, %phi_385);
  ];
  block %ssl3_connect_loop0_220 {.address = 0xbbc; .originalLabel = "9prPqUS9Qqe7hy9g5ZLatw=="} [
    var R21_146: bv64 := 0x1180:bv64 { .label = "3004_0" };
    goto(%phi_351, %phi_352);
  ];
  block %ssl3_connect_loop0_302 {.address = 0xc08; .originalLabel = "7kcGWvv0T42TGNYif6DB5A=="} [
    var R21_124: bv64 := 0x11a0:bv64 { .label = "3080_0" };
    goto(%phi_311, %phi_312);
  ];
  block %ssl3_connect_342 [
    guard eq(ZF_98:bv1, 0x1:bv1);
    var R1_366: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %ssl3_connect_loop1_578 {.address = 0x9bc; .originalLabel = "pQReZKk0Qp+vsBqNT4Qtsg=="} [
    assert eq(R25_55:bv64, 0x1120:bv64);
    goto(%phi_176, %phi_177);
  ];
  block %ssl3_connect_loop1_580 {.address = 0x9b8; .originalLabel = "N9v2CkEWSOSADh1lwf1gUQ=="} [
    var R25_55: bv64 := 0x1120:bv64 { .label = "2488_0" };
    ( var R21_53: bv64 := R21_52:bv64,
      var R24_92: bv64 := R24_91:bv64,
      var R1_119: bv64 := R1_96:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %ssl3_connect_loop1_582 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    var R21_52: bv64 := R21_39:bv64 { .label = "phiback" };
    var R24_91: bv64 := R24_89:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_580);
  ];
  block %ssl3_connect_loop1_590 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_166, %phi_167);
  ];
  block %ssl3_connect_loop2_616 [
    goto(%phi_149, %phi_150);
  ];
  block %ssl3_connect_636 {.address = 0x990; .originalLabel = "a2GioR8qQBm65Yt+OeSm4A=="} [
    goto(%phi_131, %phi_132);
  ];
  block %ssl3_connect_640 [
    guard eq(ZF_13:bv1, 0x1:bv1);
    var R1_366: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_110 {.originalLabel = "N9M0jGuISP+5dNonSDzCIA=="} [
    guard boolnot(eq(R0_4:bv32, 0xffff0400:bv32));
    var R1_366: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_111 {.originalLabel = "N9M0jGuISP+5dNonSDzCIA=="} [
    guard eq(R0_4:bv32, 0xffff0400:bv32);
    goto(%phi_112, %phi_113);
  ];
  block %phi_112 [
    guard eq(R0_10:bv32, 0x0:bv32);
    var load54_32: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_50: bv32 := $__VERIFIER_nondet_int();
    goto(%phi_117, %phi_118);
  ];
  block %phi_113 [
    guard boolnot(eq(R0_10:bv32, 0x0:bv32));
    goto(%ssl3_connect_636);
  ];
  block %phi_117 {.originalLabel = "A4DneS7FTJOAsob/oCrckg=="} [
    guard boolnot(eq(R0_50:bv32, 0x0:bv32));
    var ZF_10: bv1 := bvcomp(R0_34:bv32, 0x0:bv32) { .label = "2752_1" };
    goto(%phi_121, %phi_122);
  ];
  block %phi_118 {.originalLabel = "A4DneS7FTJOAsob/oCrckg=="} [
    guard eq(R0_50:bv32, 0x0:bv32);
    var ZF_13: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_640);
  ];
  block %phi_121 [
    guard boolnot(eq(R0_34:bv32, 0x0:bv32));
    goto(%ssl3_connect_636);
  ];
  block %phi_122 [
    guard eq(R0_34:bv32, 0x0:bv32);
    var ZF_13: bv1 := ZF_10:bv1 { .label = "phiback" };
    goto(%ssl3_connect_640);
  ];
  block %phi_131 {.originalLabel = "a2GioR8qQBm65Yt+OeSm4A=="} [
    guard boolnot(eq(R0_36:bv32, 0x0:bv32));
    var ZF_21: bv1 := bvcomp(R0_38:bv32, 0x0:bv32) { .label = "2452_1" };
    goto(%phi_135, %phi_136);
  ];
  block %phi_132 {.originalLabel = "a2GioR8qQBm65Yt+OeSm4A=="} [
    guard eq(R0_36:bv32, 0x0:bv32);
    var ZF_147: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_8);
  ];
  block %phi_135 [
    guard eq(R0_38:bv32, 0x0:bv32);
    var ZF_147: bv1 := ZF_21:bv1 { .label = "phiback" };
    goto(%ssl3_connect_8);
  ];
  block %phi_136 [
    guard boolnot(eq(R0_38:bv32, 0x0:bv32));
    goto(%phi_139, %phi_140);
  ];
  block %phi_139 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    var R21_33: bv64 := 0x1110:bv64 { .label = "phiback" };
    var R24_67: bv64 := 0x0:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_7: int := 0x14 { .label = "phiback" };
    var R1_96: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_140 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_141, %phi_142);
  ];
  block %phi_141 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_33: bv64 := 0x1110:bv64 { .label = "phiback" };
    var R24_67: bv64 := 0x0:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_7: int := 0x5 { .label = "phiback" };
    var R1_96: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_142 [
    guard eq(R0_12:bv32, 0x0:bv32);
    var R21_33: bv64 := 0x1110:bv64 { .label = "phiback" };
    var R24_67: bv64 := 0x0:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_7: int := 0x21 { .label = "phiback" };
    var R1_96: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_149 {.originalLabel = "5IELOz8ZSI+BKzthO2WX5A=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_537_loop_from_7:int, 0x6), eq(ssl3_connect_537_loop_from_7:int, 0xa)), eq(ssl3_connect_537_loop_from_7:int, 0xc)), eq(ssl3_connect_537_loop_from_7:int, 0xd)), eq(ssl3_connect_537_loop_from_7:int, 0xf)), eq(ssl3_connect_537_loop_from_7:int, 0x10)), eq(ssl3_connect_537_loop_from_7:int, 0x11)), eq(ssl3_connect_537_loop_from_7:int, 0x12)), eq(ssl3_connect_537_loop_from_7:int, 0x13)), eq(ssl3_connect_537_loop_from_7:int, 0x14)), eq(ssl3_connect_537_loop_from_7:int, 0x16)), eq(ssl3_connect_537_loop_from_7:int, 0x17)), eq(ssl3_connect_537_loop_from_7:int, 0x1a)), eq(ssl3_connect_537_loop_from_7:int, 0x1c)), eq(ssl3_connect_537_loop_from_7:int, 0x1d)), eq(ssl3_connect_537_loop_from_7:int, 0x1e)), eq(ssl3_connect_537_loop_from_7:int, 0x1f)), eq(ssl3_connect_537_loop_from_7:int, 0x21)), eq(ssl3_connect_537_loop_from_7:int, 0x23));
    var R0_52: bv64 := 0x1110:bv64 { .label = "2476_0" };
    goto(%phi_151, %phi_152);
  ];
  block %phi_150 {.originalLabel = "kIkYGdIXRS2Uw/kDMEma6A=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_537_loop_from_7:int, 0x0), eq(ssl3_connect_537_loop_from_7:int, 0x1)), eq(ssl3_connect_537_loop_from_7:int, 0x2)), eq(ssl3_connect_537_loop_from_7:int, 0x3)), eq(ssl3_connect_537_loop_from_7:int, 0x4)), eq(ssl3_connect_537_loop_from_7:int, 0x5)), eq(ssl3_connect_537_loop_from_7:int, 0x7)), eq(ssl3_connect_537_loop_from_7:int, 0x8)), eq(ssl3_connect_537_loop_from_7:int, 0x9)), eq(ssl3_connect_537_loop_from_7:int, 0xb)), eq(ssl3_connect_537_loop_from_7:int, 0xe)), eq(ssl3_connect_537_loop_from_7:int, 0x15)), eq(ssl3_connect_537_loop_from_7:int, 0x18)), eq(ssl3_connect_537_loop_from_7:int, 0x19)), eq(ssl3_connect_537_loop_from_7:int, 0x1b)), eq(ssl3_connect_537_loop_from_7:int, 0x20)), eq(ssl3_connect_537_loop_from_7:int, 0x22));
    var R21_198: bv64 := R21_33:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_67:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := ssl3_connect_537_loop_from_7:int { .label = "phiback" };
    var R1_353: bv64 := R1_96:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_151 {.originalLabel = "5IELOz8ZSI+BKzthO2WX5A=="} [
    guard eq(extract(32, 0, R21_33:bv64), extract(32, 0, R0_52:bv64));
    var load54_33: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_53: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_156, %phi_157);
  ];
  block %phi_152 {.originalLabel = "5IELOz8ZSI+BKzthO2WX5A=="} [
    guard boolnot(eq(extract(32, 0, R21_33:bv64), extract(32, 0, R0_52:bv64)));
    var R21_52: bv64 := R21_33:bv64 { .label = "phiback" };
    var R24_91: bv64 := R24_67:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_580);
  ];
  block %phi_156 {.originalLabel = "BTPdAFhTT+OlLX5X4+b62w=="} [
    guard bvsle(extract(32, 0, R0_53:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_96:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_53:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_157 {.originalLabel = "BTPdAFhTT+OlLX5X4+b62w=="} [
    guard bvsgt(extract(32, 0, R0_53:bv64), 0x0:bv32);
    var R21_39: bv64 := 0x1120:bv64 { .label = "2688_0" };
    goto(%phi_158, %phi_159);
  ];
  block %phi_158 [
    guard bvsgt(extract(32, 0, R24_67:bv64), 0x0:bv32);
    var R24_82: bv64 := zero_extend(32, extract(32, 0, R24_67:bv64)) { .label = "2692_0" };
    goto(%phi_162, %phi_163);
  ];
  block %phi_159 [
    guard bvsle(extract(32, 0, R24_67:bv64), 0x0:bv32);
    var R24_79: bv64 := 0x1:bv64 { .label = "2692_0" };
    goto(%phi_160, %phi_161);
  ];
  block %phi_160 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    var R24_89: bv64 := R24_79:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_582);
  ];
  block %phi_161 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var R24_85: bv64 := R24_79:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_590);
  ];
  block %phi_162 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    var R24_89: bv64 := R24_82:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_582);
  ];
  block %phi_163 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var R24_85: bv64 := R24_82:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_590);
  ];
  block %phi_166 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_39:bv64,
      var R24_67: bv64 := R24_85:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x11,
      var R1_96: bv64 := R1_96:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_167 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_39:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_85:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x2 { .label = "phiback" };
    var R1_353: bv64 := R1_96:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_176 {.originalLabel = "pQReZKk0Qp+vsBqNT4Qtsg=="} [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R25_55:bv64));
    var load54_44: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_158: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_418, %phi_419);
  ];
  block %phi_177 {.originalLabel = "pQReZKk0Qp+vsBqNT4Qtsg=="} [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R25_55:bv64)));
    var R0_57: bv64 := 0x1130:bv64 { .label = "2500_0" };
    goto(%phi_178, %phi_179);
  ];
  block %phi_178 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_57:bv64));
    var R21_167: bv64 := 0x1140:bv64 { .label = "2844_0" };
    goto(%phi_398, %phi_399);
  ];
  block %phi_179 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_57:bv64)));
    var R0_58: bv64 := 0x1140:bv64 { .label = "2512_0" };
    goto(%phi_180, %phi_181);
  ];
  block %phi_180 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_58:bv64));
    var load54_42: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_138: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    var R1_292: bv64 := 0x4:bv64 { .label = "2912_0" };
    goto(%phi_378, %phi_379);
  ];
  block %phi_181 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_58:bv64)));
    var R0_59: bv64 := 0x1150:bv64 { .label = "2524_0" };
    goto(%phi_182, %phi_183);
  ];
  block %phi_182 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_59:bv64));
    var load54_41: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_129: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_362, %phi_363);
  ];
  block %phi_183 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_59:bv64)));
    var R0_60: bv64 := 0x1160:bv64 { .label = "2536_0" };
    goto(%phi_184, %phi_185);
  ];
  block %phi_184 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_60:bv64));
    var load54_40: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_121: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_336, %phi_337);
  ];
  block %phi_185 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_60:bv64)));
    var R0_61: bv64 := 0x1170:bv64 { .label = "2548_0" };
    goto(%phi_186, %phi_187);
  ];
  block %phi_186 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_61:bv64));
    var load54_39: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_116: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_330, %phi_331);
  ];
  block %phi_187 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_61:bv64)));
    var R0_62: bv64 := 0x1180:bv64 { .label = "2560_0" };
    goto(%phi_188, %phi_189);
  ];
  block %phi_188 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_62:bv64));
    var load54_38: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_110: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_303, %phi_304);
  ];
  block %phi_189 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_62:bv64)));
    var R0_63: bv64 := 0x1190:bv64 { .label = "2572_0" };
    goto(%phi_190, %phi_191);
  ];
  block %phi_190 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_63:bv64));
    var load54_37: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_105: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_297, %phi_298);
  ];
  block %phi_191 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_63:bv64)));
    var R0_64: bv64 := 0x11a0:bv64 { .label = "2584_0" };
    goto(%phi_192, %phi_193);
  ];
  block %phi_192 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_64:bv64));
    var load54_36: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_96: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_273, %phi_274);
  ];
  block %phi_193 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_64:bv64)));
    var R0_65: bv64 := 0x11b0:bv64 { .label = "2596_0" };
    goto(%phi_194, %phi_195);
  ];
  block %phi_194 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_65:bv64));
    var load54_35: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_82: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_240, %phi_241);
  ];
  block %phi_195 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_65:bv64)));
    var R0_66: bv64 := 0x11d0:bv64 { .label = "2608_0" };
    goto(%phi_196, %phi_197);
  ];
  block %phi_196 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_66:bv64));
    var load54_34: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_77: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_224, %phi_225);
  ];
  block %phi_197 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_66:bv64)));
    var R0_67: bv64 := 0x1100:bv64 { .label = "2620_0" };
    goto(%phi_198, %phi_199);
  ];
  block %phi_198 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_67:bv64)));
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := 0x1:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_199 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_67:bv64));
    var load4_1: bv32 := Stack_n24_n20:bv32 { .label = "2632_0_0" };
    goto(%phi_200, %phi_201);
  ];
  block %phi_200 [
    guard bvsle(load4_1:bv32, 0x0:bv32);
    var load18_1: bv32 := Stack_n4_0:bv32 { .label = "3320_0_0" };
    var R21_82: bv64 := zero_extend(32, load18_1:bv32) { .label = "3320_0_1" };
    goto(%phi_213, %phi_214);
  ];
  block %phi_201 [
    guard bvsgt(load4_1:bv32, 0x0:bv32);
    var load38_1: bv32 := Stack_n16_n12:bv32 { .label = "2644_0_0" };
    goto(%phi_202, %phi_203);
  ];
  block %phi_202 [
    guard bvsle(load38_1:bv32, 0x0:bv32);
    var R1_366: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_203 [
    guard bvsgt(load38_1:bv32, 0x0:bv32);
    goto(%phi_204, %phi_205);
  ];
  block %phi_204 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var load35_1: bv32 := Stack_n16_n12:bv32 { .label = "3300_0_0" };
    var Stack_n24_n20: bv32 := load35_1:bv32 { .label = "3304_0" };
    var load36_1: bv32 := Stack_n4_0:bv32 { .label = "3308_0_0" };
    var R21_77: bv64 := zero_extend(32, load36_1:bv32) { .label = "3308_0_1" };
    goto(%phi_207, %phi_208);
  ];
  block %phi_205 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    var load19_1: bv32 := Stack_n4_0:bv32 { .label = "2660_0_0" };
    var Stack_n24_n20: bv32 := load38_1:bv32 { .label = "2664_0" };
    ( var R21_53: bv64 := zero_extend(32, load19_1:bv32),
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_207 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_77:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x1c,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_208 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_77:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x9 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_213 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_82:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_214 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_215, %phi_216);
  ];
  block %phi_215 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_82:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0xa,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_216 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_82:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0xe { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_224 {.originalLabel = "7rWPTof1Sqe8M2BwmmCg6g=="} [
    guard bvsle(extract(32, 0, R0_77:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_77:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_225 {.originalLabel = "7rWPTof1Sqe8M2BwmmCg6g=="} [
    guard bvsgt(extract(32, 0, R0_77:bv64), 0x0:bv32);
    goto(%phi_226, %phi_227);
  ];
  block %phi_226 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    goto(%ssl3_connect_loop0_302);
  ];
  block %phi_227 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_89: bv64 := 0x3:bv64 { .label = "3260_0" };
    goto(%phi_228, %phi_229);
  ];
  block %phi_228 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_89:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_229 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_230, %phi_231);
  ];
  block %phi_230 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_89:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x23,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_231 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_89:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0xb { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_240 {.originalLabel = "9Wp+Pu8BQcejMRlAVltPPw=="} [
    guard bvsle(extract(32, 0, R0_82:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_82:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_241 {.originalLabel = "9Wp+Pu8BQcejMRlAVltPPw=="} [
    guard bvsgt(extract(32, 0, R0_82:bv64), 0x0:bv32);
    var load37_1: bv32 := Stack_n20_n16:bv32 { .label = "3124_0_0" };
    var R0_87: bv64 := zero_extend(32, bvadd(load37_1:bv32, 0xfffffffb:bv32)) { .label = "3128_0" };
    var Stack_n20_n16: bv32 := bvadd(load37_1:bv32, 0xfffffffb:bv32) { .label = "3132_0" };
    goto(%phi_242, %phi_243);
  ];
  block %phi_242 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var Stack_n4_0: bv32 := 0x11d0:bv32 { .label = "3280_0" };
    var R21_110: bv64 := 0x1100:bv64 { .label = "3284_0" };
    goto(%phi_262, %phi_263);
  ];
  block %phi_243 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    goto(%phi_244, %phi_245);
  ];
  block %phi_244 [
    guard eq(extract(32, 0, R0_87:bv64), 0xfffffffe:bv32);
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3340_0" };
    var R21_103: bv64 := 0x1100:bv64 { .label = "3344_0" };
    goto(%phi_254, %phi_255);
  ];
  block %phi_245 [
    guard boolnot(eq(extract(32, 0, R0_87:bv64), 0xfffffffe:bv32));
    var R0_92: bv32 := bvshl(zero_extend(2, extract(30, 0, R0_87:bv64)), 0x2:bv32) { .label = "3148_0" };
    var R21_96: bv64 := 0x3:bv64 { .label = "3152_0" };
    var Stack_n20_n16: bv32 := R0_92:bv32 { .label = "3156_0" };
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3160_0" };
    goto(%phi_246, %phi_247);
  ];
  block %phi_246 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_96:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_247 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_248, %phi_249);
  ];
  block %phi_248 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_96:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x13,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_249 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_96:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x3 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_254 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_103:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_255 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_256, %phi_257);
  ];
  block %phi_256 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_103:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x1f,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_257 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_103:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x20 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_262 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_110:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_263 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_264, %phi_265);
  ];
  block %phi_264 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_110:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x1a,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_265 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_110:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x15 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_273 {.originalLabel = "8Vys1kkMSIWA27290gDuVQ=="} [
    guard bvsle(extract(32, 0, R0_96:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_96:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_274 {.originalLabel = "8Vys1kkMSIWA27290gDuVQ=="} [
    guard bvsgt(extract(32, 0, R0_96:bv64), 0x0:bv32);
    var load33_1: bv32 := Stack_n12_n8:bv32 { .label = "3188_0_0" };
    var load34_1: bv32 := Stack_n8_n4:bv32 { .label = "3196_0_0" };
    goto(%phi_275, %phi_276);
  ];
  block %phi_275 [
    guard boolnot(eq(load33_1:bv32, 0x0:bv32));
    var ZF_94: bv1 := bvcomp(load34_1:bv32, 0x0:bv32) { .label = "3200_1" };
    goto(%phi_279, %phi_280);
  ];
  block %phi_276 [
    guard eq(load33_1:bv32, 0x0:bv32);
    var ZF_98: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_342);
  ];
  block %phi_279 [
    guard eq(load34_1:bv32, 0x0:bv32);
    var ZF_98: bv1 := ZF_94:bv1 { .label = "phiback" };
    goto(%ssl3_connect_342);
  ];
  block %phi_280 [
    guard boolnot(eq(load34_1:bv32, 0x0:bv32));
    var R21_117: bv64 := 0x11b0:bv64 { .label = "3208_0" };
    goto(%phi_283, %phi_284);
  ];
  block %phi_283 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_117:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_284 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_285, %phi_286);
  ];
  block %phi_285 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_117:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x1e,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_286 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_117:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x4 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_297 {.originalLabel = "kOHdEgHxRKmgPNx6iFlT6w=="} [
    guard bvsgt(extract(32, 0, R0_105:bv64), 0x0:bv32);
    goto(%ssl3_connect_loop0_302);
  ];
  block %phi_298 {.originalLabel = "kOHdEgHxRKmgPNx6iFlT6w=="} [
    guard bvsle(extract(32, 0, R0_105:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_105:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_303 {.originalLabel = "Zl0PAWE6QuClXuEMf7NbuQ=="} [
    guard bvsle(extract(32, 0, R0_110:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_110:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_304 {.originalLabel = "Zl0PAWE6QuClXuEMf7NbuQ=="} [
    guard bvsgt(extract(32, 0, R0_110:bv64), 0x0:bv32);
    var load32_1: bv32 := Stack_n28_n24:bv32 { .label = "3068_0_0" };
    goto(%phi_305, %phi_306);
  ];
  block %phi_305 [
    guard eq(load32_1:bv32, 0x1:bv32);
    var R21_131: bv64 := 0x1190:bv64 { .label = "3224_0" };
    goto(%phi_319, %phi_320);
  ];
  block %phi_306 [
    guard boolnot(eq(load32_1:bv32, 0x1:bv32));
    goto(%ssl3_connect_loop0_302);
  ];
  block %phi_311 {.originalLabel = "7kcGWvv0T42TGNYif6DB5A=="} [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_124:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_312 {.originalLabel = "7kcGWvv0T42TGNYif6DB5A=="} [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_313, %phi_314);
  ];
  block %phi_313 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_124:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x10,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_314 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_124:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x1b { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_319 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_131:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_320 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var R21_134: bv64 := 0x1190:bv64 { .label = "3232_0" };
    goto(%phi_321, %phi_322);
  ];
  block %phi_321 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_134:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0xc,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_322 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_134:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x0 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_330 {.originalLabel = "ddskaYK4QWe2jMIjZQU/7Q=="} [
    guard bvsle(extract(32, 0, R0_116:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_116:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_331 {.originalLabel = "ddskaYK4QWe2jMIjZQU/7Q=="} [
    guard bvsgt(extract(32, 0, R0_116:bv64), 0x0:bv32);
    goto(%ssl3_connect_loop0_220);
  ];
  block %phi_336 {.originalLabel = "bfsvWCWLTwCMncPX3wc29A=="} [
    guard bvsle(extract(32, 0, R0_121:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_337 {.originalLabel = "bfsvWCWLTwCMncPX3wc29A=="} [
    guard bvsgt(extract(32, 0, R0_121:bv64), 0x0:bv32);
    var load17_1: bv32 := Stack_n28_n24:bv32 { .label = "3032_0_0" };
    goto(%phi_338, %phi_339);
  ];
  block %phi_338 [
    guard eq(load17_1:bv32, 0x0:bv32);
    goto(%ssl3_connect_loop0_220);
  ];
  block %phi_339 [
    guard boolnot(eq(load17_1:bv32, 0x0:bv32));
    var R21_139: bv64 := 0x1170:bv64 { .label = "3040_0" };
    goto(%phi_340, %phi_341);
  ];
  block %phi_340 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_139:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_341 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_342, %phi_343);
  ];
  block %phi_342 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_139:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x1d,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_343 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_139:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x19 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_351 {.originalLabel = "9prPqUS9Qqe7hy9g5ZLatw=="} [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_146:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_352 {.originalLabel = "9prPqUS9Qqe7hy9g5ZLatw=="} [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_353, %phi_354);
  ];
  block %phi_353 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_146:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x6,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_354 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_146:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x1 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_362 {.originalLabel = "Tne+7VUnQtiQ3ecXORujNQ=="} [
    guard eq(extract(32, 0, R24_92:bv64), 0x5:bv32);
    assert eq(R30_in:bv64, 0x704:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_6:bv64, R1_retval_inlined_7:bv64, R2_retval_inlined_8:bv64, R3_retval_inlined_9:bv64) := call @reach_error_2176 (bvadd(R31_in:bv64, 0xffffffffffffff80:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xffffffffffffff80:bv64)) { .label = "3360_2" };
    goto(%phi_362_retval_inline);
  ];
  block %phi_363 {.originalLabel = "Tne+7VUnQtiQ3ecXORujNQ=="} [
    guard boolnot(eq(extract(32, 0, R24_92:bv64), 0x5:bv32));
    goto(%phi_364, %phi_365);
  ];
  block %phi_364 [
    guard bvsle(extract(32, 0, R0_129:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_129:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_365 [
    guard bvsgt(extract(32, 0, R0_129:bv64), 0x0:bv32);
    var R21_153: bv64 := 0x1160:bv64 { .label = "2976_0" };
    goto(%phi_366, %phi_367);
  ];
  block %phi_366 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_153:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_367 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_368, %phi_369);
  ];
  block %phi_368 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_153:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x16,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_369 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_153:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x7 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_378 {.originalLabel = "To9qKOqCTz+rva0cY8grJg=="} [
    guard boolnot(eq(extract(32, 0, R24_92:bv64), 0x3:bv32));
    var R24_259: bv64 := zero_extend(32, extract(32, 0, R24_92:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_152);
  ];
  block %phi_379 {.originalLabel = "To9qKOqCTz+rva0cY8grJg=="} [
    guard eq(extract(32, 0, R24_92:bv64), 0x3:bv32);
    var R24_259: bv64 := zero_extend(32, extract(32, 0, R1_292:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_152);
  ];
  block %phi_384 [
    guard bvsle(extract(32, 0, R0_138:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_292:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_138:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_385 [
    guard bvsgt(extract(32, 0, R0_138:bv64), 0x0:bv32);
    goto(%phi_386, %phi_387);
  ];
  block %phi_386 [
    guard eq(R0_40:bv32, 0x0:bv32);
    var R1_366: bv64 := R1_292:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_387 [
    guard boolnot(eq(R0_40:bv32, 0x0:bv32));
    var R21_160: bv64 := 0x1150:bv64 { .label = "2932_0" };
    goto(%phi_388, %phi_389);
  ];
  block %phi_388 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_160:bv64,
      var R24_92: bv64 := R24_259:bv64,
      var R1_119: bv64 := R1_292:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_389 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_390, %phi_391);
  ];
  block %phi_390 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_160:bv64,
      var R24_67: bv64 := R24_259:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x17,
      var R1_96: bv64 := R1_292:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_391 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_160:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_259:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x18 { .label = "phiback" };
    var R1_353: bv64 := R1_292:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_398 [
    guard boolnot(eq(R0_27:bv32, 0xffffff00:bv32));
    ( var R21_53: bv64 := R21_167:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_399 [
    guard eq(R0_27:bv32, 0xffffff00:bv32);
    var load54_43: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_148: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    var R1_312: bv64 := 0x3:bv64 { .label = "2864_0" };
    goto(%phi_402, %phi_403);
  ];
  block %phi_402 {.originalLabel = "Xk5ubrtFRyKGsTm4V61frw=="} [
    guard boolnot(eq(extract(32, 0, R24_92:bv64), 0x2:bv32));
    var R24_280: bv64 := zero_extend(32, extract(32, 0, R24_92:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_106);
  ];
  block %phi_403 {.originalLabel = "Xk5ubrtFRyKGsTm4V61frw=="} [
    guard eq(extract(32, 0, R24_92:bv64), 0x2:bv32);
    var R24_280: bv64 := zero_extend(32, extract(32, 0, R1_312:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_106);
  ];
  block %phi_408 [
    guard bvsle(extract(32, 0, R0_148:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_312:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_148:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_409 [
    guard bvsgt(extract(32, 0, R0_148:bv64), 0x0:bv32);
    goto(%phi_410, %phi_411);
  ];
  block %phi_410 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_167:bv64,
      var R24_92: bv64 := R24_280:bv64,
      var R1_119: bv64 := R1_312:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_411 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var R21_193: bv64 := R21_167:bv64 { .label = "phiback" };
    var R24_312: bv64 := R24_280:bv64 { .label = "phiback" };
    var R1_348: bv64 := R1_312:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_36);
  ];
  block %phi_418 {.originalLabel = "QEOI2xrGRjW+V530gfB/1g=="} [
    guard eq(extract(32, 0, R24_92:bv64), 0x1:bv32);
    var R24_298: bv64 := 0x2:bv64 { .label = "phiback" };
    var R1_334: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_68);
  ];
  block %phi_419 {.originalLabel = "QEOI2xrGRjW+V530gfB/1g=="} [
    guard boolnot(eq(extract(32, 0, R24_92:bv64), 0x1:bv32));
    var R1_328: bv64 := 0x5:bv64 { .label = "2808_0" };
    goto(%phi_420, %phi_421);
  ];
  block %phi_420 [
    guard boolnot(eq(extract(32, 0, R24_92:bv64), 0x4:bv32));
    var R24_298: bv64 := zero_extend(32, extract(32, 0, R24_92:bv64)) { .label = "phiback" };
    var R1_334: bv64 := R1_328:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_68);
  ];
  block %phi_421 [
    guard eq(extract(32, 0, R24_92:bv64), 0x4:bv32);
    var R24_298: bv64 := zero_extend(32, extract(32, 0, R1_328:bv64)) { .label = "phiback" };
    var R1_334: bv64 := R1_328:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_68);
  ];
  block %phi_428 {.originalLabel = "hVeZ7c0lRB6b9NV97zhnnA=="} [
    guard bvsle(extract(32, 0, R0_158:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_334:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_158:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_429 {.originalLabel = "hVeZ7c0lRB6b9NV97zhnnA=="} [
    guard bvsgt(extract(32, 0, R0_158:bv64), 0x0:bv32);
    goto(%phi_430, %phi_431);
  ];
  block %phi_430 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_189: bv64 := 0x1130:bv64 { .label = "2892_0" };
    goto(%phi_440, %phi_441);
  ];
  block %phi_431 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    var R21_182: bv64 := 0x11d0:bv64 { .label = "2828_0" };
    goto(%phi_432, %phi_433);
  ];
  block %phi_432 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_182:bv64,
      var R24_92: bv64 := R24_298:bv64,
      var R1_119: bv64 := R1_334:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_433 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_434, %phi_435);
  ];
  block %phi_434 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_182:bv64,
      var R24_67: bv64 := R24_298:bv64,
      var ssl3_connect_537_loop_from_7: int := 0xf,
      var R1_96: bv64 := R1_334:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_435 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_182:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_298:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x8 { .label = "phiback" };
    var R1_353: bv64 := R1_334:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_440 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var R21_193: bv64 := R21_189:bv64 { .label = "phiback" };
    var R24_312: bv64 := R24_298:bv64 { .label = "phiback" };
    var R1_348: bv64 := R1_334:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_36);
  ];
  block %phi_441 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_189:bv64,
      var R24_92: bv64 := R24_298:bv64,
      var R1_119: bv64 := R1_334:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_446 {.originalLabel = "fTIp8ADeSKu9PARbAynQwg=="} [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_193:bv64,
      var R24_67: bv64 := R24_312:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x12,
      var R1_96: bv64 := R1_348:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_447 {.originalLabel = "fTIp8ADeSKu9PARbAynQwg=="} [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_193:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_312:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x22 { .label = "phiback" };
    var R1_353: bv64 := R1_348:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_469 {.originalLabel = "Zjl3ZzMsQGajdtpUPy0hsg=="} [
    guard bvsgt(extract(32, 0, R0_170:bv64), 0x0:bv32);
    ( var R21_33: bv64 := R21_198:bv64,
      var R24_67: bv64 := R24_317:bv64,
      var ssl3_connect_537_loop_from_7: int := 0xd,
      var R1_96: bv64 := R1_353:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_470 {.originalLabel = "Zjl3ZzMsQGajdtpUPy0hsg=="} [
    guard bvsle(extract(32, 0, R0_170:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_353:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_170:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_362_retval_inline [
    var R31_371: bv64 := bvadd(R31_in:bv64, 0xffffffffffffff80:bv64) { .label = "phiback" };
    var R1_368: bv64 := 0xd58:bv64 { .label = "phiback" };
    var R0_181: bv64 := 0xd70:bv64 { .label = "phiback" };
    var R3_369: bv64 := 0xd48:bv64 { .label = "phiback" };
    var R2_369: bv64 := 0x3:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_return [
    assert eq(R31_in:bv64, R31_371:bv64) { .comment = "R31 preserved across calls" };
    return (R0_181:bv64, R1_368:bv64, R2_369:bv64, R3_369:bv64);
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
      { .name = "_IO_stdin_used"; .address = 0xd40; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xed4; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xed8; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20040; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "_start"; .address = 0x740; .size = 0x1a0 };
      { .name = "main"; .address = 0x700; .size = 0xc0 };
      { .name = "reach_error"; .address = 0x880; .size = 0x140 };
      { .name = "ssl3_connect"; .address = 0x8a8; .size = 0x2420 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x860 ]; [ 0x1fdc0; 0x80c ]; [ 0x1ffd8; 0x700 ]; [ 0x20038; 0x20038 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2XILatT8tatWG0Rz9CbvOntPJHb+04CAAdy/BUkAAAA" ]
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
    .size = 0x62c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/41UXWwUVRQ+s7MIWBDS7WRLFXYXjSENGLF3MPjiFDH7YmNgx6hBw7YNlrjWZlygofOwW198ICYsbTTxwYIx";
      "hiU+GOXBeZHWmKhRXyg2mhCyNLSgIF06u5Rpuz1+d2dqCEbiw8n3zb3fOfeenzs1+1yxplLhINEwUX5vzR47Parun4jF1V//";
      "r22k/PlNsCmVzlxWDW/yUSpMI2aJqEw3kp6KvTBsjPnDn2H19WtJzyA6+x1z9H7nkULHiZSCAkwAnyW6PkpkXkaMRCnpdSJG";
      "WVXOUCg2IePcq08Q/bR5MTfevmbwWGKxfWgM+kn47ionva66b+gf35r9Tb0WbgN5EfinQ+07DYWert/3StLLQ1+P/4jhnUAe";
      "v8PiqFk6pOx0GwyvZn/7r9pdRH73q10N9VeJjisweTYBu+N6IZHWCzSqF7oQ/z2cU7O/9u+WUorVfaHiXLda9DLh4kJ2RdHG";
      "/gDsKOyOSq39wCOww7Db+M4C0YRWC1gB9gHfhvXC3oJlYG/KvvSRc1BiDzlvAA/AXOi7gV2wOfA0cL/UZMh5HfgabB+sir1X";
      "gQvAl4HzwJeAi8CU1PeTs0eiTc6LErPkdEjMjTTGVMooD5J5dDWJnErW7oeNgfxqMpuRu7b53b0pIt1cSTqBnwtRprSCzA2P";
      "Sb4hY0BHj/vrecSgLT6nNeCtPjfWgm8NfB8Cf8LnJ+X6k4FmHfhTPo+vBxfBeiP4jsBXap4JfCPgcZ8rUTJLGcOJEVkdGnjW";
      "570qmW1NJKo5w5H1uoBZWI+c5d42hUzkbWnIo/n7kZYhj/Umj8WqYP/zO2y6qXb0ehd6/Rx6vRu9fr5Ys3+oz9jSkq/7tMUY";
      "6Lzta/F+G/9LPyv1K8k6Gca5EbJOobbNkcEWGeOXRTZ3hEhoyC1bZf1ChcUl3FVDLTkU3j5WYXNS+jeQ1XmX39oFnOuybros";
      "zks9+vAVs/gIfELq15E1eJf+fY/Ni/MsNPSlbZb14Vss5Pt/BRp53o/SJ0pWGr2rx0cNNPRtvMy6KLNw5L8iyHvbHPbQO3cG";
      "58+w+BJ7TrDXgXqUegyHcBcNvR6/Cf+bLIrQfLHsX/U1sbBfEw39HvqL9coNFiPQfRboXmA2P8b3J8F3rwu/PsRuoj3yvRwJ";
      "k4itou30AObh0KbUYeQi16s5ciLXWT/0J4tj8D+x7H8L/v3+fJRswwk3GwPxWeSCGRv6A+dfY5GTtcQsRvAt0cQa3nd0cDm/";
      "GTY/mGddnuVeRf5XWbyDfTmbJZyrYS7bsD48zQLvOyrnUc6fnMPKFIserEkemcb98I33HU3Lewe+qSnWz15hgfcd/W3J/8dJ";
      "/jdLx4+8LAYAAA=="
    ]
  };
  {
    .name = ".fini";
    .address = 0xd2c;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0xd40;
    .size = 0x32;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML/YOD45J68k3ljPKUwvWS85M0fXUC+ZgcGAAQA+PTdSMgAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xd74;
    .size = 0x4c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrb2YGBg4ADinp///zswMjCcAdIJQL7Or///S4B0DJDuANIzgPQcIP0GSB8A0jy///+/AqRNgPQbIA0A";
      "SU8DUEwAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xdc0;
    .size = 0x118;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiFN+/v9vApJ0ZJcDiekA8QagmAFUD0jMAYjPAMVsoGIKQBwCxF+AYh5g";
      "vXwKc1nmMTtNZvK7d/cyH0xfBRCr/Pr/nwWqTwSIe4DYACimAdEnMJdpHmMAkLkEZA9QvIUFLN7AOFdgHr/bZL4pvFN5pnFP";
      "55rBOZNjFvtstjmsTDVc9+7evnPz1vUbV69dvsLH4MjtjSHCIAM05gcQu/z4/18CyS6Xe3f5oM5hAADlXtkOGAEAAA=="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xed8;
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
      "H4sIAAAAAAAA/7WQPRKCMBCFF+THH+xgVOQIFN7Mq2hHyREoLT2CJaUlpY2F45A4zn4pQs82X15edl+SQLSuMIAtzOApUW7R";
      "NYsD+jZq5xG9hCW841cT/23s+c8uVB2z3y+UxMoDf+3mwQ3cw0L8YowMVvMZIxeYwxTuYBv7+8/Iv7fLX03yv1bf444adEe/";
      "Rbt/fqEb/A86knnqB4vzTCfwAQAA"
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
