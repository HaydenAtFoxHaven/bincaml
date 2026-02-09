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
  block %main_entry {.address = 0x740; .originalLabel = "T+Iq/9RhRfKe+2fRZ6JXfg=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1856_2" };
    var (R0_2:bv64, R1_2:bv64, R2_2:bv64, R3_2:bv64) := call @ssl3_connect_2280 (R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), R2_in:bv64, 0x74c:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), R3_in:bv64);
    goto(%main_return);
  ];
  block %main_return [
    var _PC_2: bv64 := _PC_in:bv64 { .label = "inlineret" };
    var load37_1: bv64 := Stack_n16_n8:bv64 { .label = "1872_0_0" };
    var load38_1: bv64 := Stack_n8_0:bv64 { .label = "1872_1_0" };
    assert eq(R30_in:bv64, load38_1:bv64) { .comment = "R30 preserved across calls" };
    assert true { .comment = "R31 preserved across calls" };
    return (0x0:bv64, load37_1:bv64, _PC_2:bv64);
  ]
];


proc @reach_error_2240
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x8c0; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x8c0; .originalLabel = "lBTQ9kfxQMmTmeBf6oAC4A=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2240_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2240_2" };
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 = R30_in" };
    var load39_1: bv64 := $Global_131112_131120:bv64 { .label = "1796_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0xdb0:bv64, 0xd98:bv64, 0x3:bv64, 0xd88:bv64);
  ]
];


proc @ssl3_connect_2280
  (R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64)
    -> (R0_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "ssl3_connect"; .address = 0x8e8; .returnBlock = "ssl3_connect_return" }
[
  block %ssl3_connect_entry {.address = 0x8e8; .originalLabel = "TFKYXXP1TtqQH7O6OPc3kQ=="} [
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
    var load47_1: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load48_1: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load48_2: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv32 := $__VERIFIER_nondet_uint();
    var load47_2: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load47_3: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load47_4: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv32 := $__VERIFIER_nondet_int();
    var load47_5: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_10: bv32 := $__VERIFIER_nondet_int();
    var load47_6: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_12: bv32 := $__VERIFIER_nondet_int();
    var load47_7: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load48_3: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load48_4: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load48_5: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load48_6: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load47_8: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_19: bv32 := $__VERIFIER_nondet_int();
    var Stack_n20_n16: bv32 := R0_19:bv32 { .label = "2380_0" };
    var load47_9: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_21: bv32 := $__VERIFIER_nondet_int();
    var Stack_n28_n24: bv32 := R0_21:bv32 { .label = "2388_0" };
    var load47_10: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load47_11: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_24: bv32 := $__VERIFIER_nondet_int();
    var load47_12: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load47_13: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_27: bv32 := $__VERIFIER_nondet_int();
    var load47_14: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load47_15: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_30: bv32 := $__VERIFIER_nondet_int();
    var Stack_n24_n20: bv32 := R0_30:bv32 { .label = "2424_0" };
    var load48_7: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load48_8: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load47_16: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_34: bv32 := $__VERIFIER_nondet_int();
    var load47_17: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_36: bv32 := $__VERIFIER_nondet_int();
    var load47_18: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_38: bv32 := $__VERIFIER_nondet_int();
    var load47_19: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_40: bv32 := $__VERIFIER_nondet_int();
    var load47_20: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_42: bv32 := $__VERIFIER_nondet_int();
    var Stack_n12_n8: bv32 := R0_42:bv32 { .label = "2472_0" };
    var load47_21: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_44: bv32 := $__VERIFIER_nondet_int();
    var Stack_n8_n4: bv32 := R0_44:bv32 { .label = "2480_0" };
    var load47_22: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_46: bv32 := $__VERIFIER_nondet_int();
    var Stack_n16_n12: bv32 := R0_46:bv32 { .label = "2488_0" };
    var load47_23: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    goto(%phi_110, %phi_111);
  ];
  block %ssl3_connect_4 {.address = 0xb0c; .originalLabel = "hVFkW00kQRK4Wg7E5iOAfQ=="} [
    var load19_1: bv64 := Stack_n112_n104:bv64 { .label = "2828_1_0" };
    var load20_1: bv64 := Stack_n104_n96:bv64 { .label = "2828_2_0" };
    var load21_1: bv64 := Stack_n96_n88:bv64 { .label = "2836_1_0" };
    var load22_1: bv64 := Stack_n88_n80:bv64 { .label = "2836_2_0" };
    var load23_1: bv64 := Stack_n80_n72:bv64 { .label = "2840_1_0" };
    var load24_1: bv64 := Stack_n72_n64:bv64 { .label = "2840_2_0" };
    var load25_1: bv64 := Stack_n64_n56:bv64 { .label = "2844_1_0" };
    var load26_1: bv64 := Stack_n56_n48:bv64 { .label = "2844_2_0" };
    var load27_1: bv64 := Stack_n48_n40:bv64 { .label = "2848_1_0" };
    var load28_1: bv64 := Stack_n40_n32:bv64 { .label = "2848_2_0" };
    var load29_1: bv64 := Stack_n128_n120:bv64 { .label = "2852_0_0" };
    var load30_1: bv64 := Stack_n120_n112:bv64 { .label = "2852_1_0" };
    var R31_369: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_367: bv64 := R1_365:bv64 { .label = "phiback" };
    var R0_183: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    var R3_367: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_367: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_8 [
    guard eq(ZF_144:bv1, 0x1:bv1);
    var R1_365: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %ssl3_connect_10 {.address = 0xae0; .originalLabel = "ACZn5dElQua49V4rXR+wDg=="} [
    var load1_1: bv64 := Stack_n112_n104:bv64 { .label = "2784_1_0" };
    var load2_1: bv64 := Stack_n104_n96:bv64 { .label = "2784_2_0" };
    var load3_1: bv64 := Stack_n96_n88:bv64 { .label = "2788_1_0" };
    var load4_1: bv64 := Stack_n88_n80:bv64 { .label = "2788_2_0" };
    var load5_1: bv64 := Stack_n80_n72:bv64 { .label = "2792_1_0" };
    var load6_1: bv64 := Stack_n72_n64:bv64 { .label = "2792_2_0" };
    var load7_1: bv64 := Stack_n64_n56:bv64 { .label = "2796_1_0" };
    var load8_1: bv64 := Stack_n56_n48:bv64 { .label = "2796_2_0" };
    var load9_1: bv64 := Stack_n48_n40:bv64 { .label = "2800_1_0" };
    var load10_1: bv64 := Stack_n40_n32:bv64 { .label = "2800_2_0" };
    var load11_1: bv64 := Stack_n128_n120:bv64 { .label = "2804_0_0" };
    var load12_1: bv64 := Stack_n120_n112:bv64 { .label = "2804_1_0" };
    var R31_369: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_367: bv64 := R1_360:bv64 { .label = "phiback" };
    var R0_183: bv64 := R0_179:bv64 { .label = "phiback" };
    var R3_367: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_367: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_loop0_30 {.address = 0xad4; .originalLabel = "xWG7QdrERQyyrwd4vF8pkg=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_539_loop_from_57:int, 0x2), eq(ssl3_connect_539_loop_from_57:int, 0x3)), eq(ssl3_connect_539_loop_from_57:int, 0x5)), eq(ssl3_connect_539_loop_from_57:int, 0x6)), eq(ssl3_connect_539_loop_from_57:int, 0x9)), eq(ssl3_connect_539_loop_from_57:int, 0xc)), eq(ssl3_connect_539_loop_from_57:int, 0xd)), eq(ssl3_connect_539_loop_from_57:int, 0xf)), eq(ssl3_connect_539_loop_from_57:int, 0x10)), eq(ssl3_connect_539_loop_from_57:int, 0x13)), eq(ssl3_connect_539_loop_from_57:int, 0x14)), eq(ssl3_connect_539_loop_from_57:int, 0x16)), eq(ssl3_connect_539_loop_from_57:int, 0x19)), eq(ssl3_connect_539_loop_from_57:int, 0x1b)), eq(ssl3_connect_539_loop_from_57:int, 0x1e)), eq(ssl3_connect_539_loop_from_57:int, 0x1f)), eq(ssl3_connect_539_loop_from_57:int, 0x23));
    var load47_37: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_172: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_466, %phi_467);
  ];
  block %ssl3_connect_loop0_36 {.address = 0xb88; .originalLabel = "b2klegW/SBeZEA3kFMZ0Ag=="} [
    goto(%phi_443, %phi_444);
  ];
  block %ssl3_connect_loop0_68 [
    goto(%phi_425, %phi_426);
  ];
  block %ssl3_connect_loop0_98 [
    goto(%phi_409, %phi_410);
  ];
  block %ssl3_connect_loop0_144 [
    goto(%phi_385, %phi_386);
  ];
  block %ssl3_connect_loop0_212 {.address = 0xbf8; .originalLabel = "wMTc1agsReOlxF7octNK8A=="} [
    var R21_175: bv64 := 0x1180:bv64 { .label = "3064_0" };
    goto(%phi_352, %phi_353);
  ];
  block %ssl3_connect_loop0_294 {.address = 0xc44; .originalLabel = "d4iV7eCaRYip02cis95Zaw=="} [
    var R21_153: bv64 := 0x11a0:bv64 { .label = "3140_0" };
    goto(%phi_312, %phi_313);
  ];
  block %ssl3_connect_334 [
    guard eq(ZF_98:bv1, 0x1:bv1);
    var R1_365: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %ssl3_connect_loop1_570 {.address = 0x9f8; .originalLabel = "yxfax3Q2TTCUryUpQ1eB+w=="} [
    assert eq(R25_55:bv64, 0x1120:bv64);
    goto(%phi_177, %phi_178);
  ];
  block %ssl3_connect_loop1_572 {.address = 0x9f4; .originalLabel = "aPv2xfsXSJ6p/4v+KivgfQ=="} [
    var R25_55: bv64 := 0x1120:bv64 { .label = "2548_0" };
    ( var R21_82: bv64 := R21_81:bv64,
      var R22_60: bv64 := R22_59:bv64,
      var R1_121: bv64 := R1_120:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %ssl3_connect_loop1_588 {.address = 0xac0; .originalLabel = "rzcBMB71TU6JyKhe02QrWg=="} [
    goto(%phi_165, %phi_166);
  ];
  block %ssl3_connect_loop2_618 [
    goto(%phi_149, %phi_150);
  ];
  block %ssl3_connect_638 {.address = 0x9cc; .originalLabel = "BhtmOjPqQDak5Zv4eGSX4Q=="} [
    goto(%phi_131, %phi_132);
  ];
  block %ssl3_connect_642 [
    guard eq(ZF_13:bv1, 0x1:bv1);
    var R1_365: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_110 {.originalLabel = "UMSvIyBKQAO0I3tQ6e2nTw=="} [
    guard boolnot(eq(bvadd(R0_4:bv32, 0xffff0000:bv32), 0x200:bv32));
    var R1_365: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_111 {.originalLabel = "UMSvIyBKQAO0I3tQ6e2nTw=="} [
    guard eq(bvadd(R0_4:bv32, 0xffff0000:bv32), 0x200:bv32);
    goto(%phi_112, %phi_113);
  ];
  block %phi_112 [
    guard eq(R0_10:bv32, 0x0:bv32);
    var load47_24: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_49: bv32 := $__VERIFIER_nondet_int();
    goto(%phi_117, %phi_118);
  ];
  block %phi_113 [
    guard boolnot(eq(R0_10:bv32, 0x0:bv32));
    goto(%ssl3_connect_638);
  ];
  block %phi_117 {.originalLabel = "O/EZgvbWSfGh4yYDt5NbOA=="} [
    guard boolnot(eq(R0_49:bv32, 0x0:bv32));
    var ZF_10: bv1 := bvcomp(R0_34:bv32, 0x0:bv32) { .label = "2820_1" };
    goto(%phi_121, %phi_122);
  ];
  block %phi_118 {.originalLabel = "O/EZgvbWSfGh4yYDt5NbOA=="} [
    guard eq(R0_49:bv32, 0x0:bv32);
    var ZF_13: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_642);
  ];
  block %phi_121 [
    guard boolnot(eq(R0_34:bv32, 0x0:bv32));
    goto(%ssl3_connect_638);
  ];
  block %phi_122 [
    guard eq(R0_34:bv32, 0x0:bv32);
    var ZF_13: bv1 := ZF_10:bv1 { .label = "phiback" };
    goto(%ssl3_connect_642);
  ];
  block %phi_131 {.originalLabel = "BhtmOjPqQDak5Zv4eGSX4Q=="} [
    guard boolnot(eq(R0_36:bv32, 0x0:bv32));
    var ZF_21: bv1 := bvcomp(R0_38:bv32, 0x0:bv32) { .label = "2512_1" };
    goto(%phi_135, %phi_136);
  ];
  block %phi_132 {.originalLabel = "BhtmOjPqQDak5Zv4eGSX4Q=="} [
    guard eq(R0_36:bv32, 0x0:bv32);
    var ZF_144: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_8);
  ];
  block %phi_135 [
    guard eq(R0_38:bv32, 0x0:bv32);
    var ZF_144: bv1 := ZF_21:bv1 { .label = "phiback" };
    goto(%ssl3_connect_8);
  ];
  block %phi_136 [
    guard boolnot(eq(R0_38:bv32, 0x0:bv32));
    goto(%phi_139, %phi_140);
  ];
  block %phi_139 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    var R21_68: bv64 := 0x1110:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_7: int := 0x0 { .label = "phiback" };
    var R22_33: bv64 := 0x0:bv64 { .label = "phiback" };
    var R1_96: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_140 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_141, %phi_142);
  ];
  block %phi_141 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_68: bv64 := 0x1110:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_7: int := 0x5 { .label = "phiback" };
    var R22_33: bv64 := 0x0:bv64 { .label = "phiback" };
    var R1_96: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_142 [
    guard eq(R0_12:bv32, 0x0:bv32);
    var R21_68: bv64 := 0x1110:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_7: int := 0x17 { .label = "phiback" };
    var R22_33: bv64 := 0x0:bv64 { .label = "phiback" };
    var R1_96: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_149 {.originalLabel = "LfppHnbNTLurTBfkwhnJmw=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_539_loop_from_7:int, 0x0), eq(ssl3_connect_539_loop_from_7:int, 0x1)), eq(ssl3_connect_539_loop_from_7:int, 0x4)), eq(ssl3_connect_539_loop_from_7:int, 0x7)), eq(ssl3_connect_539_loop_from_7:int, 0x8)), eq(ssl3_connect_539_loop_from_7:int, 0xa)), eq(ssl3_connect_539_loop_from_7:int, 0xb)), eq(ssl3_connect_539_loop_from_7:int, 0xe)), eq(ssl3_connect_539_loop_from_7:int, 0x11)), eq(ssl3_connect_539_loop_from_7:int, 0x12)), eq(ssl3_connect_539_loop_from_7:int, 0x15)), eq(ssl3_connect_539_loop_from_7:int, 0x17)), eq(ssl3_connect_539_loop_from_7:int, 0x18)), eq(ssl3_connect_539_loop_from_7:int, 0x1a)), eq(ssl3_connect_539_loop_from_7:int, 0x1c)), eq(ssl3_connect_539_loop_from_7:int, 0x1d)), eq(ssl3_connect_539_loop_from_7:int, 0x20)), eq(ssl3_connect_539_loop_from_7:int, 0x21)), eq(ssl3_connect_539_loop_from_7:int, 0x22));
    var R0_51: bv64 := 0x1110:bv64 { .label = "2536_0" };
    goto(%phi_151, %phi_152);
  ];
  block %phi_150 {.originalLabel = "xWG7QdrERQyyrwd4vF8pkg=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_539_loop_from_7:int, 0x2), eq(ssl3_connect_539_loop_from_7:int, 0x3)), eq(ssl3_connect_539_loop_from_7:int, 0x5)), eq(ssl3_connect_539_loop_from_7:int, 0x6)), eq(ssl3_connect_539_loop_from_7:int, 0x9)), eq(ssl3_connect_539_loop_from_7:int, 0xc)), eq(ssl3_connect_539_loop_from_7:int, 0xd)), eq(ssl3_connect_539_loop_from_7:int, 0xf)), eq(ssl3_connect_539_loop_from_7:int, 0x10)), eq(ssl3_connect_539_loop_from_7:int, 0x13)), eq(ssl3_connect_539_loop_from_7:int, 0x14)), eq(ssl3_connect_539_loop_from_7:int, 0x16)), eq(ssl3_connect_539_loop_from_7:int, 0x19)), eq(ssl3_connect_539_loop_from_7:int, 0x1b)), eq(ssl3_connect_539_loop_from_7:int, 0x1e)), eq(ssl3_connect_539_loop_from_7:int, 0x1f)), eq(ssl3_connect_539_loop_from_7:int, 0x23));
    var R21_227: bv64 := R21_68:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := ssl3_connect_539_loop_from_7:int { .label = "phiback" };
    var R22_281: bv64 := R22_33:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_96:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_151 {.originalLabel = "LfppHnbNTLurTBfkwhnJmw=="} [
    guard eq(extract(32, 0, R21_68:bv64), extract(32, 0, R0_51:bv64));
    var load47_25: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_52: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_155, %phi_156);
  ];
  block %phi_152 {.originalLabel = "LfppHnbNTLurTBfkwhnJmw=="} [
    guard boolnot(eq(extract(32, 0, R21_68:bv64), extract(32, 0, R0_51:bv64)));
    var R21_81: bv64 := R21_68:bv64 { .label = "phiback" };
    var R22_59: bv64 := R22_33:bv64 { .label = "phiback" };
    var R1_120: bv64 := R1_96:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_572);
  ];
  block %phi_155 [
    guard eq(extract(32, 0, R22_33:bv64), 0x0:bv32);
    var R22_50: bv64 := 0x1:bv64 { .label = "phiback" };
    var R1_111: bv64 := R1_96:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_588);
  ];
  block %phi_156 [
    guard boolnot(eq(extract(32, 0, R22_33:bv64), 0x0:bv32));
    var R1_105: bv64 := 0x5:bv64 { .label = "2744_0" };
    goto(%phi_157, %phi_158);
  ];
  block %phi_157 [
    guard boolnot(eq(extract(32, 0, R22_33:bv64), 0x4:bv32));
    var R22_50: bv64 := zero_extend(32, extract(32, 0, R22_33:bv64)) { .label = "phiback" };
    var R1_111: bv64 := R1_105:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_588);
  ];
  block %phi_158 [
    guard eq(extract(32, 0, R22_33:bv64), 0x4:bv32);
    var R22_50: bv64 := zero_extend(32, extract(32, 0, R1_105:bv64)) { .label = "phiback" };
    var R1_111: bv64 := R1_105:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_588);
  ];
  block %phi_165 {.originalLabel = "rzcBMB71TU6JyKhe02QrWg=="} [
    guard bvsle(extract(32, 0, R0_52:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_111:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_52:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_166 {.originalLabel = "rzcBMB71TU6JyKhe02QrWg=="} [
    guard bvsgt(extract(32, 0, R0_52:bv64), 0x0:bv32);
    var R21_74: bv64 := 0x1120:bv64 { .label = "2760_0" };
    goto(%phi_167, %phi_168);
  ];
  block %phi_167 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    var R21_81: bv64 := R21_74:bv64 { .label = "phiback" };
    var R22_59: bv64 := R22_50:bv64 { .label = "phiback" };
    var R1_120: bv64 := R1_111:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_572);
  ];
  block %phi_168 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_169, %phi_170);
  ];
  block %phi_169 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_74:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x22,
      var R22_33: bv64 := R22_50:bv64,
      var R1_96: bv64 := R1_111:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_170 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_74:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x10 { .label = "phiback" };
    var R22_281: bv64 := R22_50:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_111:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_177 {.originalLabel = "yxfax3Q2TTCUryUpQ1eB+w=="} [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R25_55:bv64));
    var load47_36: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_163: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    var R1_328: bv64 := 0x2:bv64 { .label = "2868_0" };
    goto(%phi_419, %phi_420);
  ];
  block %phi_178 {.originalLabel = "yxfax3Q2TTCUryUpQ1eB+w=="} [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R25_55:bv64)));
    var R0_63: bv64 := 0x1130:bv64 { .label = "2560_0" };
    goto(%phi_179, %phi_180);
  ];
  block %phi_179 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_63:bv64));
    var R21_196: bv64 := 0x1140:bv64 { .label = "2912_0" };
    goto(%phi_399, %phi_400);
  ];
  block %phi_180 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_63:bv64)));
    var R0_64: bv64 := 0x1140:bv64 { .label = "2572_0" };
    goto(%phi_181, %phi_182);
  ];
  block %phi_181 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_64:bv64));
    var load47_34: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_143: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    var R1_296: bv64 := 0x4:bv64 { .label = "2980_0" };
    goto(%phi_379, %phi_380);
  ];
  block %phi_182 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_64:bv64)));
    var R0_65: bv64 := 0x1150:bv64 { .label = "2584_0" };
    goto(%phi_183, %phi_184);
  ];
  block %phi_183 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_65:bv64));
    var load47_33: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_134: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_363, %phi_364);
  ];
  block %phi_184 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_65:bv64)));
    var R0_66: bv64 := 0x1160:bv64 { .label = "2596_0" };
    goto(%phi_185, %phi_186);
  ];
  block %phi_185 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_66:bv64));
    var load47_32: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_126: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_337, %phi_338);
  ];
  block %phi_186 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_66:bv64)));
    var R0_67: bv64 := 0x1170:bv64 { .label = "2608_0" };
    goto(%phi_187, %phi_188);
  ];
  block %phi_187 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_67:bv64));
    var load47_31: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_121: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_331, %phi_332);
  ];
  block %phi_188 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_67:bv64)));
    var R0_68: bv64 := 0x1180:bv64 { .label = "2620_0" };
    goto(%phi_189, %phi_190);
  ];
  block %phi_189 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_68:bv64));
    var load47_30: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_115: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_304, %phi_305);
  ];
  block %phi_190 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_68:bv64)));
    var R0_69: bv64 := 0x1190:bv64 { .label = "2632_0" };
    goto(%phi_191, %phi_192);
  ];
  block %phi_191 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_69:bv64));
    var load47_29: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_110: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_298, %phi_299);
  ];
  block %phi_192 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_69:bv64)));
    var R0_70: bv64 := 0x11a0:bv64 { .label = "2644_0" };
    goto(%phi_193, %phi_194);
  ];
  block %phi_193 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_70:bv64));
    var load47_28: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_101: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_274, %phi_275);
  ];
  block %phi_194 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_70:bv64)));
    var R0_71: bv64 := 0x11b0:bv64 { .label = "2656_0" };
    goto(%phi_195, %phi_196);
  ];
  block %phi_195 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_71:bv64));
    var load47_27: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_88: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_241, %phi_242);
  ];
  block %phi_196 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_71:bv64)));
    var R0_72: bv64 := 0x11d0:bv64 { .label = "2668_0" };
    goto(%phi_197, %phi_198);
  ];
  block %phi_197 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_72:bv64));
    var load47_26: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_83: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_225, %phi_226);
  ];
  block %phi_198 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_72:bv64)));
    var R0_73: bv64 := 0x1100:bv64 { .label = "2680_0" };
    goto(%phi_199, %phi_200);
  ];
  block %phi_199 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_73:bv64)));
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := 0x1:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_200 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_73:bv64));
    var load18_1: bv32 := Stack_n24_n20:bv32 { .label = "2692_0_0" };
    goto(%phi_201, %phi_202);
  ];
  block %phi_201 [
    guard bvsle(load18_1:bv32, 0x0:bv32);
    var load17_1: bv32 := Stack_n4_0:bv32 { .label = "3384_0_0" };
    var R21_111: bv64 := zero_extend(32, load17_1:bv32) { .label = "3384_0_1" };
    goto(%phi_214, %phi_215);
  ];
  block %phi_202 [
    guard bvsgt(load18_1:bv32, 0x0:bv32);
    var load13_1: bv32 := Stack_n16_n12:bv32 { .label = "2704_0_0" };
    goto(%phi_203, %phi_204);
  ];
  block %phi_203 [
    guard bvsle(load13_1:bv32, 0x0:bv32);
    var R1_365: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_204 [
    guard bvsgt(load13_1:bv32, 0x0:bv32);
    goto(%phi_205, %phi_206);
  ];
  block %phi_205 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var load31_1: bv32 := Stack_n16_n12:bv32 { .label = "3364_0_0" };
    var Stack_n24_n20: bv32 := load31_1:bv32 { .label = "3368_0" };
    var load32_1: bv32 := Stack_n4_0:bv32 { .label = "3372_0_0" };
    var R21_106: bv64 := zero_extend(32, load32_1:bv32) { .label = "3372_0_1" };
    goto(%phi_208, %phi_209);
  ];
  block %phi_206 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    var load33_1: bv32 := Stack_n4_0:bv32 { .label = "2720_0_0" };
    var Stack_n24_n20: bv32 := load13_1:bv32 { .label = "2724_0" };
    ( var R21_82: bv64 := zero_extend(32, load33_1:bv32),
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_208 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_106:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x15,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_209 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_106:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x9 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_214 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_111:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_215 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_216, %phi_217);
  ];
  block %phi_216 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_111:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x7,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_217 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_111:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x1b { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_225 {.originalLabel = "UYYvE4JfQBW6N+O3VLpoXA=="} [
    guard bvsle(extract(32, 0, R0_83:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_83:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_226 {.originalLabel = "UYYvE4JfQBW6N+O3VLpoXA=="} [
    guard bvsgt(extract(32, 0, R0_83:bv64), 0x0:bv32);
    goto(%phi_227, %phi_228);
  ];
  block %phi_227 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    goto(%ssl3_connect_loop0_294);
  ];
  block %phi_228 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_118: bv64 := 0x3:bv64 { .label = "3324_0" };
    goto(%phi_229, %phi_230);
  ];
  block %phi_229 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_118:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_230 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_231, %phi_232);
  ];
  block %phi_231 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_118:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x20,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_232 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_118:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x13 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_241 {.originalLabel = "bCWe9Oe8QGOzc+1Ym7l6hQ=="} [
    guard bvsle(extract(32, 0, R0_88:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_88:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_242 {.originalLabel = "bCWe9Oe8QGOzc+1Ym7l6hQ=="} [
    guard bvsgt(extract(32, 0, R0_88:bv64), 0x0:bv32);
    var load34_1: bv32 := Stack_n20_n16:bv32 { .label = "3184_0_0" };
    var R1_183: bv64 := zero_extend(32, bvadd(load34_1:bv32, 0x5:bv32)) { .label = "3192_0" };
    var Stack_n20_n16: bv32 := bvadd(load34_1:bv32, 0x5:bv32) { .label = "3196_0" };
    goto(%phi_243, %phi_244);
  ];
  block %phi_243 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var Stack_n4_0: bv32 := 0x11d0:bv32 { .label = "3344_0" };
    var R21_139: bv64 := 0x1100:bv64 { .label = "3348_0" };
    goto(%phi_263, %phi_264);
  ];
  block %phi_244 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    goto(%phi_245, %phi_246);
  ];
  block %phi_245 [
    guard eq(extract(32, 0, R1_183:bv64), 0x2:bv32);
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3404_0" };
    var R21_132: bv64 := 0x1100:bv64 { .label = "3408_0" };
    goto(%phi_255, %phi_256);
  ];
  block %phi_246 [
    guard boolnot(eq(extract(32, 0, R1_183:bv64), 0x2:bv32));
    var R21_125: bv64 := 0x3:bv64 { .label = "3216_0" };
    var Stack_n20_n16: bv32 := bvadd(load34_1:bv32, 0x9:bv32) { .label = "3220_0" };
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3224_0" };
    goto(%phi_247, %phi_248);
  ];
  block %phi_247 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_125:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_183:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_248 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_249, %phi_250);
  ];
  block %phi_249 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_125:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x1c,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_183:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_250 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_125:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0xc { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_183:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_255 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_132:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_183:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_256 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_257, %phi_258);
  ];
  block %phi_257 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_132:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x1a,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_183:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_258 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_132:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x6 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_183:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_263 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_139:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_183:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_264 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_265, %phi_266);
  ];
  block %phi_265 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_139:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x1d,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_183:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_266 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_139:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x19 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_183:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_274 {.originalLabel = "joBgYcm7T7W+q2LFhqS8lg=="} [
    guard bvsle(extract(32, 0, R0_101:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_101:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_275 {.originalLabel = "joBgYcm7T7W+q2LFhqS8lg=="} [
    guard bvsgt(extract(32, 0, R0_101:bv64), 0x0:bv32);
    var load15_1: bv32 := Stack_n12_n8:bv32 { .label = "3252_0_0" };
    var load16_1: bv32 := Stack_n8_n4:bv32 { .label = "3260_0_0" };
    goto(%phi_276, %phi_277);
  ];
  block %phi_276 [
    guard boolnot(eq(load15_1:bv32, 0x0:bv32));
    var ZF_94: bv1 := bvcomp(load16_1:bv32, 0x0:bv32) { .label = "3264_1" };
    goto(%phi_280, %phi_281);
  ];
  block %phi_277 [
    guard eq(load15_1:bv32, 0x0:bv32);
    var ZF_98: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_334);
  ];
  block %phi_280 [
    guard eq(load16_1:bv32, 0x0:bv32);
    var ZF_98: bv1 := ZF_94:bv1 { .label = "phiback" };
    goto(%ssl3_connect_334);
  ];
  block %phi_281 [
    guard boolnot(eq(load16_1:bv32, 0x0:bv32));
    var R21_146: bv64 := 0x11b0:bv64 { .label = "3272_0" };
    goto(%phi_284, %phi_285);
  ];
  block %phi_284 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_146:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_285 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_286, %phi_287);
  ];
  block %phi_286 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_146:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x4,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_287 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_146:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0xd { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_298 {.originalLabel = "uyh5ZcoVTfiAi15i1iAA1Q=="} [
    guard bvsgt(extract(32, 0, R0_110:bv64), 0x0:bv32);
    goto(%ssl3_connect_loop0_294);
  ];
  block %phi_299 {.originalLabel = "uyh5ZcoVTfiAi15i1iAA1Q=="} [
    guard bvsle(extract(32, 0, R0_110:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_110:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_304 {.originalLabel = "pG5e1/FgRIidEEOPPAECCg=="} [
    guard bvsle(extract(32, 0, R0_115:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_115:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_305 {.originalLabel = "pG5e1/FgRIidEEOPPAECCg=="} [
    guard bvsgt(extract(32, 0, R0_115:bv64), 0x0:bv32);
    var load14_1: bv32 := Stack_n28_n24:bv32 { .label = "3128_0_0" };
    goto(%phi_306, %phi_307);
  ];
  block %phi_306 [
    guard eq(load14_1:bv32, 0x1:bv32);
    var R21_160: bv64 := 0x1190:bv64 { .label = "3288_0" };
    goto(%phi_320, %phi_321);
  ];
  block %phi_307 [
    guard boolnot(eq(load14_1:bv32, 0x1:bv32));
    goto(%ssl3_connect_loop0_294);
  ];
  block %phi_312 {.originalLabel = "d4iV7eCaRYip02cis95Zaw=="} [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_153:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_313 {.originalLabel = "d4iV7eCaRYip02cis95Zaw=="} [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_314, %phi_315);
  ];
  block %phi_314 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_153:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x18,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_315 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_153:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x14 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_320 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_160:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_321 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var R21_163: bv64 := 0x1190:bv64 { .label = "3296_0" };
    goto(%phi_322, %phi_323);
  ];
  block %phi_322 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_163:bv64,
      var ssl3_connect_539_loop_from_7: int := 0xb,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_323 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_163:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x1f { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_331 {.originalLabel = "0f35yymfSdKVePJqH2jraQ=="} [
    guard bvsle(extract(32, 0, R0_121:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_332 {.originalLabel = "0f35yymfSdKVePJqH2jraQ=="} [
    guard bvsgt(extract(32, 0, R0_121:bv64), 0x0:bv32);
    goto(%ssl3_connect_loop0_212);
  ];
  block %phi_337 {.originalLabel = "xBWthr6ZT3Wbih6PQHbkwQ=="} [
    guard bvsle(extract(32, 0, R0_126:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_126:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_338 {.originalLabel = "xBWthr6ZT3Wbih6PQHbkwQ=="} [
    guard bvsgt(extract(32, 0, R0_126:bv64), 0x0:bv32);
    var load0_1: bv32 := Stack_n28_n24:bv32 { .label = "3092_0_0" };
    goto(%phi_339, %phi_340);
  ];
  block %phi_339 [
    guard eq(load0_1:bv32, 0x0:bv32);
    goto(%ssl3_connect_loop0_212);
  ];
  block %phi_340 [
    guard boolnot(eq(load0_1:bv32, 0x0:bv32));
    var R21_168: bv64 := 0x1170:bv64 { .label = "3100_0" };
    goto(%phi_341, %phi_342);
  ];
  block %phi_341 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_168:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_342 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_343, %phi_344);
  ];
  block %phi_343 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_168:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x21,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_344 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_168:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x23 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_352 {.originalLabel = "wMTc1agsReOlxF7octNK8A=="} [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_175:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_353 {.originalLabel = "wMTc1agsReOlxF7octNK8A=="} [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_354, %phi_355);
  ];
  block %phi_354 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_175:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x11,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_355 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_175:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x16 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_363 {.originalLabel = "LZrzpN0ORq23kYo5cXGeHA=="} [
    guard eq(extract(32, 0, R22_60:bv64), 0x5:bv32);
    assert eq(R30_in:bv64, 0x744:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_6:bv64, R1_retval_inlined_7:bv64, R2_retval_inlined_8:bv64, R3_retval_inlined_9:bv64) := call @reach_error_2240 (bvadd(R31_in:bv64, 0xffffffffffffff80:bv64), 0x744:bv64, bvadd(R31_in:bv64, 0xffffffffffffff80:bv64)) { .label = "3424_2" };
    goto(%phi_363_retval_inline);
  ];
  block %phi_364 {.originalLabel = "LZrzpN0ORq23kYo5cXGeHA=="} [
    guard boolnot(eq(extract(32, 0, R22_60:bv64), 0x5:bv32));
    goto(%phi_365, %phi_366);
  ];
  block %phi_365 [
    guard bvsle(extract(32, 0, R0_134:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_134:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_366 [
    guard bvsgt(extract(32, 0, R0_134:bv64), 0x0:bv32);
    var R21_182: bv64 := 0x1160:bv64 { .label = "3036_0" };
    goto(%phi_367, %phi_368);
  ];
  block %phi_367 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_182:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_368 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_369, %phi_370);
  ];
  block %phi_369 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_182:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x12,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_370 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_182:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x2 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_379 {.originalLabel = "Pljn+dDGRd+WORjORcIFXw=="} [
    guard boolnot(eq(extract(32, 0, R22_60:bv64), 0x3:bv32));
    var R22_227: bv64 := zero_extend(32, extract(32, 0, R22_60:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_144);
  ];
  block %phi_380 {.originalLabel = "Pljn+dDGRd+WORjORcIFXw=="} [
    guard eq(extract(32, 0, R22_60:bv64), 0x3:bv32);
    var R22_227: bv64 := zero_extend(32, extract(32, 0, R1_296:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_144);
  ];
  block %phi_385 [
    guard bvsle(extract(32, 0, R0_143:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_296:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_143:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_386 [
    guard bvsgt(extract(32, 0, R0_143:bv64), 0x0:bv32);
    goto(%phi_387, %phi_388);
  ];
  block %phi_387 [
    guard eq(R0_40:bv32, 0x0:bv32);
    var R1_365: bv64 := R1_296:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_388 [
    guard boolnot(eq(R0_40:bv32, 0x0:bv32));
    var R21_189: bv64 := 0x1150:bv64 { .label = "3000_0" };
    goto(%phi_389, %phi_390);
  ];
  block %phi_389 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_189:bv64,
      var R22_60: bv64 := R22_227:bv64,
      var R1_121: bv64 := R1_296:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_390 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_391, %phi_392);
  ];
  block %phi_391 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_189:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x1,
      var R22_33: bv64 := R22_227:bv64,
      var R1_96: bv64 := R1_296:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_392 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_189:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x3 { .label = "phiback" };
    var R22_281: bv64 := R22_227:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_296:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_399 [
    guard boolnot(eq(R0_27:bv32, 0x100:bv32));
    ( var R21_82: bv64 := R21_196:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_400 [
    guard eq(R0_27:bv32, 0x100:bv32);
    var load47_35: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_153: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    var R1_316: bv64 := 0x3:bv64 { .label = "2932_0" };
    goto(%phi_403, %phi_404);
  ];
  block %phi_403 {.originalLabel = "rIubTfADQ4K9zlU2yTk4Yw=="} [
    guard boolnot(eq(extract(32, 0, R22_60:bv64), 0x2:bv32));
    var R22_248: bv64 := zero_extend(32, extract(32, 0, R22_60:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_98);
  ];
  block %phi_404 {.originalLabel = "rIubTfADQ4K9zlU2yTk4Yw=="} [
    guard eq(extract(32, 0, R22_60:bv64), 0x2:bv32);
    var R22_248: bv64 := zero_extend(32, extract(32, 0, R1_316:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_98);
  ];
  block %phi_409 [
    guard bvsle(extract(32, 0, R0_153:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_316:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_153:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_410 [
    guard bvsgt(extract(32, 0, R0_153:bv64), 0x0:bv32);
    goto(%phi_411, %phi_412);
  ];
  block %phi_411 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_196:bv64,
      var R22_60: bv64 := R22_248:bv64,
      var R1_121: bv64 := R1_316:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_412 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var R21_222: bv64 := R21_196:bv64 { .label = "phiback" };
    var R22_276: bv64 := R22_248:bv64 { .label = "phiback" };
    var R1_347: bv64 := R1_316:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_36);
  ];
  block %phi_419 {.originalLabel = "NgGnN7nIRGKQ68xt9rXjZg=="} [
    guard boolnot(eq(extract(32, 0, R22_60:bv64), 0x1:bv32));
    var R22_262: bv64 := zero_extend(32, extract(32, 0, R22_60:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_68);
  ];
  block %phi_420 {.originalLabel = "NgGnN7nIRGKQ68xt9rXjZg=="} [
    guard eq(extract(32, 0, R22_60:bv64), 0x1:bv32);
    var R22_262: bv64 := zero_extend(32, extract(32, 0, R1_328:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_68);
  ];
  block %phi_425 [
    guard bvsle(extract(32, 0, R0_163:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_328:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_163:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_426 [
    guard bvsgt(extract(32, 0, R0_163:bv64), 0x0:bv32);
    goto(%phi_427, %phi_428);
  ];
  block %phi_427 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_218: bv64 := 0x1130:bv64 { .label = "2960_0" };
    goto(%phi_437, %phi_438);
  ];
  block %phi_428 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    var R21_211: bv64 := 0x11d0:bv64 { .label = "2888_0" };
    goto(%phi_429, %phi_430);
  ];
  block %phi_429 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_211:bv64,
      var R22_60: bv64 := R22_262:bv64,
      var R1_121: bv64 := R1_328:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_430 [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_431, %phi_432);
  ];
  block %phi_431 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_211:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x8,
      var R22_33: bv64 := R22_262:bv64,
      var R1_96: bv64 := R1_328:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_432 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_211:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0xf { .label = "phiback" };
    var R22_281: bv64 := R22_262:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_328:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_437 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var R21_222: bv64 := R21_218:bv64 { .label = "phiback" };
    var R22_276: bv64 := R22_262:bv64 { .label = "phiback" };
    var R1_347: bv64 := R1_328:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_36);
  ];
  block %phi_438 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_218:bv64,
      var R22_60: bv64 := R22_262:bv64,
      var R1_121: bv64 := R1_328:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_443 {.originalLabel = "b2klegW/SBeZEA3kFMZ0Ag=="} [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_222:bv64,
      var ssl3_connect_539_loop_from_7: int := 0xa,
      var R22_33: bv64 := R22_276:bv64,
      var R1_96: bv64 := R1_347:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_444 {.originalLabel = "b2klegW/SBeZEA3kFMZ0Ag=="} [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_222:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x1e { .label = "phiback" };
    var R22_281: bv64 := R22_276:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_347:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_466 {.originalLabel = "PvGIyFgtQhK7HLpAKNklyw=="} [
    guard bvsgt(extract(32, 0, R0_172:bv64), 0x0:bv32);
    ( var R21_68: bv64 := R21_227:bv64,
      var ssl3_connect_539_loop_from_7: int := 0xe,
      var R22_33: bv64 := R22_281:bv64,
      var R1_96: bv64 := R1_352:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_467 {.originalLabel = "PvGIyFgtQhK7HLpAKNklyw=="} [
    guard bvsle(extract(32, 0, R0_172:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_352:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_172:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_363_retval_inline [
    var R31_369: bv64 := bvadd(R31_in:bv64, 0xffffffffffffff80:bv64) { .label = "phiback" };
    var R1_367: bv64 := 0xd98:bv64 { .label = "phiback" };
    var R0_183: bv64 := 0xdb0:bv64 { .label = "phiback" };
    var R3_367: bv64 := 0xd88:bv64 { .label = "phiback" };
    var R2_367: bv64 := 0x3:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_return [
    assert eq(R31_in:bv64, R31_369:bv64) { .comment = "R31 preserved across calls" };
    return (R0_183:bv64, R1_367:bv64, R2_367:bv64, R3_367:bv64);
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
      { .name = "_IO_stdin_used"; .address = 0xd80; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xf14; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xf18; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20048; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "_start"; .address = 0x780; .size = 0x1a0 };
      { .name = "main"; .address = 0x740; .size = 0xc0 };
      { .name = "reach_error"; .address = 0x8c0; .size = 0x140 };
      { .name = "ssl3_connect"; .address = 0x8e8; .size = 0x2420 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x8a0 ]; [ 0x1fdc0; 0x84c ]; [ 0x1ffd8; 0x740 ]; [ 0x20040; 0x20040 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2X4qSG5YVv2ukP77ovrhu/6npJ7d90SANK+DvIkAAAA" ]
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
    .size = 0x62c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/41UXWwUVRQ+s7PlH7Q/wwpGd7cSYxpjjN5Zgy/MImZfJAZ21BgSWVoV4to0kwU36Tx0lxcflISFJvoI8UEX";
      "w4MBE0cT2RoejPpES6MJCVtCoSLQrdOlnbbD8bs7U9NoJD6cfN/c+5177vm549sXqr5KlUNEw0Slvb498kVN3T8eT6iX/689";
      "RqVLj8MmVTozoRretSeocgNn1okadDvjqdiLwkaYP/kF1lqfyngG0fmLzLEHxSOFjlNCqSjAJHAH0R81InMCZyTrGe8Azmio";
      "yhmKxMflOf/UJ4l+7l4aGk1vKH+UXEqfHIH+Gnx3NjJeb8s38revb3/fqoW7nrxO+Oe609sNhV5o3fd6xitBH5xveCeQx2+w";
      "BGqW61a2u+sNz7d/+FftriC/B9XOR/1VouMKTMYmYF8iVUnmUhWqpSq9OP9DxPHtb4K7ZZVqc1+kOtenVr18tLpYaKva2D8K";
      "K8M0w9hTBH4AOwKbU6mnAEQTeizgLHBgxf5hmNx/T/ZlgJxDEg+S8y7wHZgLfR+wFzYPngPul5o8OXL/bdg+2D3svQlcBL4B";
      "XAC+BlwCZqW+SM4eiTY5r0oskLMb+HVkjZVeR6azlsSQStauR43B2loyNyNvrfvo3iyRPryadAK/EKF8vY3MLdsk35IvQUdP";
      "Bus1nEFPBdzYAN4T8o3gT4e+m8CfCfgpuf5sqHkI/LmAJx4GFwHPdYCnQl+peTGM1QmeCHgyRmY9bzhxIqtfAy8E/KxKZraL";
      "RHPIcGStxjAH7cj39TYSVzvIOo38xjvKW6X2DuZZQ05Zj/WxeRaroZPr78+z6WbT6PdO9Psl9HsX+v1y1bd/bM2Zfz/QXdxq";
      "DCbvBVq84Y7/0s9Af3UVWekVsTf6bBYjJDTkVmgi/iyLOu6aggbzHdNQ07gatcqzbE5I/3VkHVjpv8jmOZf1LpfFJalHP84x";
      "i0/BL0v9JrLKK/THPDavLLDQ0B93hnVzhoX8B/wktZvJKqF3UrcbuWvo22iDddFg8R00I2G+/XPYQ+/cafhPsziPvW/DvWOo";
      "Q/2g4RDuoKHXo3fhf5fFl9B8tezfDDTxKFm1KGqPfp+8w/rsbRanofs81L3CbJ7C92fh91kXNRhAP1WlJ9lF7RN4L8UoiR1r";
      "yKJVmIlt1H4Eucp31Bwix72F+91i8THOOLF8vxnELgYzUrcNJ/qIMWj8iXwwZ4XfUf8pFiVZR8yjO8W6RIE1vPFYefn+0+jZ";
      "Ausy1uhN5HeTBd5wTM5nHXE1zGYn1g/fYNGPdTmTcgblLI5NssAbj0nuTuJ++MYbjuXkvUPf57E+fJ3FW1j/9X7wj5P8L78x";
      "4yssBgAA"
    ]
  };
  {
    .name = ".fini";
    .address = 0xd6c;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0xd80;
    .size = 0x32;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML/YOD45J68k3kjPKUwvWS85M0fXMFEvmcGAAQBz95vKMgAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xdb4;
    .size = 0x4c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrb2YGBg4ADinp///zswMjCcAdIJQL7Or///S4B0DJDuANIzgPQcIP0GSB8A0jy///+/AqRNgPQbIA0A";
      "SU8DUEwAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xe00;
    .size = 0x118;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiFN+/v9vApJ0ZJcDiekA8QagmAFUD0jMAYjPAMVsoGIKQBwCxF+AYh5g";
      "vXwKc1nmMTtNZvK7d/cyH0xfBRCr/Pr/nwWqTwSIe4DYACimAdEnMJdpHmMAkLkEZA9QvIUFLN7AOFdgHr/bZL4pvFN5pnFP";
      "55rBOZNjFvtstjmsTLVc9+7evnPz1vUbV69dvsLH4MjtjSHCIAM05gcQu/z4/18CyS6Xe3f5oM5hAADrAhX5GAEAAA=="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xf18;
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
      "H4sIAAAAAAAA/7WQsQ6CMBBAD6UgoAmDRAU+kYTVT3J005GR0c3V0ZHFwRipMfdqUnZveX137V3bQDQOMIAnuIT7SLnCGxY7";
      "/PzWkxW+gCXsqNeT+mO07ZfHmbohP8yVjJUL9RS/wgxuYSF+0EbuVufT5vfeNYzhxs0zfj43/r07mEzmv6y+x20d8VuoSYu7";
      "fx7wnvoTD+U/8QEcaPuZ8AEAAA=="
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
