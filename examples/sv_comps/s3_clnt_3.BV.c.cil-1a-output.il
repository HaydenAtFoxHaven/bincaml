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
  block %main_entry {.address = 0x740; .originalLabel = "JAKsOHKjR3yC7ZW0jmzZCA=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1856_2" };
    var (R0_2:bv64, R1_2:bv64, R2_2:bv64, R3_2:bv64) := call @ssl3_connect_2280 (R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), R2_in:bv64, 0x74c:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), R3_in:bv64);
    goto(%main_return);
  ];
  block %main_return [
    var _PC_2: bv64 := _PC_in:bv64 { .label = "inlineret" };
    var load7_1: bv64 := Stack_n16_n8:bv64 { .label = "1872_0_0" };
    var load8_1: bv64 := Stack_n8_0:bv64 { .label = "1872_1_0" };
    assert eq(R30_in:bv64, load8_1:bv64) { .comment = "R30 preserved across calls" };
    assert true { .comment = "R31 preserved across calls" };
    return (0x0:bv64, load7_1:bv64, _PC_2:bv64);
  ]
];


proc @reach_error_2240
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x8c0; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x8c0; .originalLabel = "NtzJQwxQTDG3mcNTUrcXlw=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2240_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2240_2" };
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 = R30_in" };
    var load11_1: bv64 := $Global_131112_131120:bv64 { .label = "1796_0_0" };
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
  block %ssl3_connect_entry {.address = 0x8e8; .originalLabel = "ravMA2DqSa61KVjzHclBjA=="} [
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
    var load49_1: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load1_1: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load1_2: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv32 := $__VERIFIER_nondet_uint();
    var load49_2: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load49_3: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load49_4: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv32 := $__VERIFIER_nondet_int();
    var load49_5: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_10: bv32 := $__VERIFIER_nondet_int();
    var load49_6: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_12: bv32 := $__VERIFIER_nondet_int();
    var load49_7: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load1_3: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load49_8: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load1_4: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load1_5: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load49_9: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_19: bv32 := $__VERIFIER_nondet_int();
    var Stack_n20_n16: bv32 := R0_19:bv32 { .label = "2380_0" };
    var load49_10: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_21: bv32 := $__VERIFIER_nondet_int();
    var Stack_n28_n24: bv32 := R0_21:bv32 { .label = "2388_0" };
    var load49_11: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load49_12: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_24: bv32 := $__VERIFIER_nondet_int();
    var load49_13: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load49_14: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_27: bv32 := $__VERIFIER_nondet_int();
    var load49_15: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load49_16: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_30: bv32 := $__VERIFIER_nondet_int();
    var Stack_n24_n20: bv32 := R0_30:bv32 { .label = "2424_0" };
    var load1_6: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load1_7: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load49_17: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_34: bv32 := $__VERIFIER_nondet_int();
    var load49_18: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_36: bv32 := $__VERIFIER_nondet_int();
    var load49_19: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_38: bv32 := $__VERIFIER_nondet_int();
    var load49_20: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_40: bv32 := $__VERIFIER_nondet_int();
    var load49_21: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_42: bv32 := $__VERIFIER_nondet_int();
    var Stack_n12_n8: bv32 := R0_42:bv32 { .label = "2472_0" };
    var load49_22: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_44: bv32 := $__VERIFIER_nondet_int();
    var Stack_n8_n4: bv32 := R0_44:bv32 { .label = "2480_0" };
    var load49_23: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_46: bv32 := $__VERIFIER_nondet_int();
    var Stack_n16_n12: bv32 := R0_46:bv32 { .label = "2488_0" };
    var load49_24: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    goto(%phi_110, %phi_111);
  ];
  block %ssl3_connect_4 {.address = 0xb08; .originalLabel = "2mv8r6oRSviRqOG+DRv1IA=="} [
    var load20_1: bv64 := Stack_n112_n104:bv64 { .label = "2824_1_0" };
    var load21_1: bv64 := Stack_n104_n96:bv64 { .label = "2824_2_0" };
    var load22_1: bv64 := Stack_n96_n88:bv64 { .label = "2832_1_0" };
    var load23_1: bv64 := Stack_n88_n80:bv64 { .label = "2832_2_0" };
    var load24_1: bv64 := Stack_n80_n72:bv64 { .label = "2836_1_0" };
    var load25_1: bv64 := Stack_n72_n64:bv64 { .label = "2836_2_0" };
    var load26_1: bv64 := Stack_n64_n56:bv64 { .label = "2840_1_0" };
    var load27_1: bv64 := Stack_n56_n48:bv64 { .label = "2840_2_0" };
    var load28_1: bv64 := Stack_n48_n40:bv64 { .label = "2844_1_0" };
    var load29_1: bv64 := Stack_n40_n32:bv64 { .label = "2844_2_0" };
    var load30_1: bv64 := Stack_n128_n120:bv64 { .label = "2848_0_0" };
    var load31_1: bv64 := Stack_n120_n112:bv64 { .label = "2848_1_0" };
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
  block %ssl3_connect_10 {.address = 0xadc; .originalLabel = "dC1fn4MSRo2ByCalI381nQ=="} [
    var load35_1: bv64 := Stack_n112_n104:bv64 { .label = "2780_1_0" };
    var load36_1: bv64 := Stack_n104_n96:bv64 { .label = "2780_2_0" };
    var load37_1: bv64 := Stack_n96_n88:bv64 { .label = "2784_1_0" };
    var load38_1: bv64 := Stack_n88_n80:bv64 { .label = "2784_2_0" };
    var load39_1: bv64 := Stack_n80_n72:bv64 { .label = "2788_1_0" };
    var load40_1: bv64 := Stack_n72_n64:bv64 { .label = "2788_2_0" };
    var load41_1: bv64 := Stack_n64_n56:bv64 { .label = "2792_1_0" };
    var load42_1: bv64 := Stack_n56_n48:bv64 { .label = "2792_2_0" };
    var load43_1: bv64 := Stack_n48_n40:bv64 { .label = "2796_1_0" };
    var load44_1: bv64 := Stack_n40_n32:bv64 { .label = "2796_2_0" };
    var load45_1: bv64 := Stack_n128_n120:bv64 { .label = "2800_0_0" };
    var load46_1: bv64 := Stack_n120_n112:bv64 { .label = "2800_1_0" };
    var R31_371: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_368: bv64 := R1_361:bv64 { .label = "phiback" };
    var R0_181: bv64 := R0_177:bv64 { .label = "phiback" };
    var R3_369: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_369: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_loop0_30 {.address = 0xad0; .originalLabel = "yxEq7G+PS0OyYUwqxgtsSg=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_537_loop_from_57:int, 0x0), eq(ssl3_connect_537_loop_from_57:int, 0x1)), eq(ssl3_connect_537_loop_from_57:int, 0x2)), eq(ssl3_connect_537_loop_from_57:int, 0xd)), eq(ssl3_connect_537_loop_from_57:int, 0xe)), eq(ssl3_connect_537_loop_from_57:int, 0xf)), eq(ssl3_connect_537_loop_from_57:int, 0x10)), eq(ssl3_connect_537_loop_from_57:int, 0x11)), eq(ssl3_connect_537_loop_from_57:int, 0x14)), eq(ssl3_connect_537_loop_from_57:int, 0x15)), eq(ssl3_connect_537_loop_from_57:int, 0x16)), eq(ssl3_connect_537_loop_from_57:int, 0x17)), eq(ssl3_connect_537_loop_from_57:int, 0x19)), eq(ssl3_connect_537_loop_from_57:int, 0x1a)), eq(ssl3_connect_537_loop_from_57:int, 0x1b)), eq(ssl3_connect_537_loop_from_57:int, 0x1c)), eq(ssl3_connect_537_loop_from_57:int, 0x20));
    var load49_38: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_170: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_469, %phi_470);
  ];
  block %ssl3_connect_loop0_36 {.address = 0xb84; .originalLabel = "V6AhPKWYTRKSwtGKfY5VZg=="} [
    goto(%phi_446, %phi_447);
  ];
  block %ssl3_connect_loop0_68 {.address = 0xb40; .originalLabel = "wYBn9D91RBm3Gkk99r95Lg=="} [
    goto(%phi_428, %phi_429);
  ];
  block %ssl3_connect_loop0_106 [
    goto(%phi_408, %phi_409);
  ];
  block %ssl3_connect_loop0_152 [
    goto(%phi_384, %phi_385);
  ];
  block %ssl3_connect_loop0_220 {.address = 0xbfc; .originalLabel = "O5+lse05SxaN77BSH+QmDg=="} [
    var R21_146: bv64 := 0x1180:bv64 { .label = "3068_0" };
    goto(%phi_351, %phi_352);
  ];
  block %ssl3_connect_loop0_302 {.address = 0xc48; .originalLabel = "23KcPGijQZSegu7sMlvMpQ=="} [
    var R21_124: bv64 := 0x11a0:bv64 { .label = "3144_0" };
    goto(%phi_311, %phi_312);
  ];
  block %ssl3_connect_342 [
    guard eq(ZF_98:bv1, 0x1:bv1);
    var R1_366: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %ssl3_connect_loop1_578 {.address = 0x9fc; .originalLabel = "byQgqLyXSHa0qQ8Aj/Y70Q=="} [
    assert eq(R25_55:bv64, 0x1120:bv64);
    goto(%phi_176, %phi_177);
  ];
  block %ssl3_connect_loop1_580 {.address = 0x9f8; .originalLabel = "nb5gXzbOQMqSbHZ3GxbFtA=="} [
    var R25_55: bv64 := 0x1120:bv64 { .label = "2552_0" };
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
  block %ssl3_connect_636 {.address = 0x9d0; .originalLabel = "IAJqIXLDQJ6tcHovXeV12A=="} [
    goto(%phi_131, %phi_132);
  ];
  block %ssl3_connect_640 [
    guard eq(ZF_13:bv1, 0x1:bv1);
    var R1_366: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_110 {.originalLabel = "w2cSkIyxTRayWez7wqfxPA=="} [
    guard boolnot(eq(R0_4:bv32, 0xffff0400:bv32));
    var R1_366: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_111 {.originalLabel = "w2cSkIyxTRayWez7wqfxPA=="} [
    guard eq(R0_4:bv32, 0xffff0400:bv32);
    goto(%phi_112, %phi_113);
  ];
  block %phi_112 [
    guard eq(R0_10:bv32, 0x0:bv32);
    var load49_25: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_50: bv32 := $__VERIFIER_nondet_int();
    goto(%phi_117, %phi_118);
  ];
  block %phi_113 [
    guard boolnot(eq(R0_10:bv32, 0x0:bv32));
    goto(%ssl3_connect_636);
  ];
  block %phi_117 {.originalLabel = "9bAwLxNeQn24AJfbpjmzDQ=="} [
    guard boolnot(eq(R0_50:bv32, 0x0:bv32));
    var ZF_10: bv1 := bvcomp(R0_34:bv32, 0x0:bv32) { .label = "2816_1" };
    goto(%phi_121, %phi_122);
  ];
  block %phi_118 {.originalLabel = "9bAwLxNeQn24AJfbpjmzDQ=="} [
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
  block %phi_131 {.originalLabel = "IAJqIXLDQJ6tcHovXeV12A=="} [
    guard boolnot(eq(R0_36:bv32, 0x0:bv32));
    var ZF_21: bv1 := bvcomp(R0_38:bv32, 0x0:bv32) { .label = "2516_1" };
    goto(%phi_135, %phi_136);
  ];
  block %phi_132 {.originalLabel = "IAJqIXLDQJ6tcHovXeV12A=="} [
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
    var ssl3_connect_537_loop_from_7: int := 0x1e { .label = "phiback" };
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
    var ssl3_connect_537_loop_from_7: int := 0xd { .label = "phiback" };
    var R1_96: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_142 [
    guard eq(R0_12:bv32, 0x0:bv32);
    var R21_33: bv64 := 0x1110:bv64 { .label = "phiback" };
    var R24_67: bv64 := 0x0:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_7: int := 0x4 { .label = "phiback" };
    var R1_96: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_149 {.originalLabel = "MpL6oEHmQwqvVGSPaTvBgw=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_537_loop_from_7:int, 0x3), eq(ssl3_connect_537_loop_from_7:int, 0x4)), eq(ssl3_connect_537_loop_from_7:int, 0x5)), eq(ssl3_connect_537_loop_from_7:int, 0x6)), eq(ssl3_connect_537_loop_from_7:int, 0x7)), eq(ssl3_connect_537_loop_from_7:int, 0x8)), eq(ssl3_connect_537_loop_from_7:int, 0x9)), eq(ssl3_connect_537_loop_from_7:int, 0xa)), eq(ssl3_connect_537_loop_from_7:int, 0xb)), eq(ssl3_connect_537_loop_from_7:int, 0xc)), eq(ssl3_connect_537_loop_from_7:int, 0x12)), eq(ssl3_connect_537_loop_from_7:int, 0x13)), eq(ssl3_connect_537_loop_from_7:int, 0x18)), eq(ssl3_connect_537_loop_from_7:int, 0x1d)), eq(ssl3_connect_537_loop_from_7:int, 0x1e)), eq(ssl3_connect_537_loop_from_7:int, 0x1f)), eq(ssl3_connect_537_loop_from_7:int, 0x21)), eq(ssl3_connect_537_loop_from_7:int, 0x22)), eq(ssl3_connect_537_loop_from_7:int, 0x23));
    var R0_52: bv64 := 0x1110:bv64 { .label = "2540_0" };
    goto(%phi_151, %phi_152);
  ];
  block %phi_150 {.originalLabel = "yxEq7G+PS0OyYUwqxgtsSg=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_537_loop_from_7:int, 0x0), eq(ssl3_connect_537_loop_from_7:int, 0x1)), eq(ssl3_connect_537_loop_from_7:int, 0x2)), eq(ssl3_connect_537_loop_from_7:int, 0xd)), eq(ssl3_connect_537_loop_from_7:int, 0xe)), eq(ssl3_connect_537_loop_from_7:int, 0xf)), eq(ssl3_connect_537_loop_from_7:int, 0x10)), eq(ssl3_connect_537_loop_from_7:int, 0x11)), eq(ssl3_connect_537_loop_from_7:int, 0x14)), eq(ssl3_connect_537_loop_from_7:int, 0x15)), eq(ssl3_connect_537_loop_from_7:int, 0x16)), eq(ssl3_connect_537_loop_from_7:int, 0x17)), eq(ssl3_connect_537_loop_from_7:int, 0x19)), eq(ssl3_connect_537_loop_from_7:int, 0x1a)), eq(ssl3_connect_537_loop_from_7:int, 0x1b)), eq(ssl3_connect_537_loop_from_7:int, 0x1c)), eq(ssl3_connect_537_loop_from_7:int, 0x20));
    var R21_198: bv64 := R21_33:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_67:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := ssl3_connect_537_loop_from_7:int { .label = "phiback" };
    var R1_353: bv64 := R1_96:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_151 {.originalLabel = "MpL6oEHmQwqvVGSPaTvBgw=="} [
    guard eq(extract(32, 0, R21_33:bv64), extract(32, 0, R0_52:bv64));
    var load49_26: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_53: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_156, %phi_157);
  ];
  block %phi_152 {.originalLabel = "MpL6oEHmQwqvVGSPaTvBgw=="} [
    guard boolnot(eq(extract(32, 0, R21_33:bv64), extract(32, 0, R0_52:bv64)));
    var R21_52: bv64 := R21_33:bv64 { .label = "phiback" };
    var R24_91: bv64 := R24_67:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop1_580);
  ];
  block %phi_156 {.originalLabel = "u3ozNc4rSOWN1jnzVCvdQw=="} [
    guard bvsle(extract(32, 0, R0_53:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_96:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_53:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_157 {.originalLabel = "u3ozNc4rSOWN1jnzVCvdQw=="} [
    guard bvsgt(extract(32, 0, R0_53:bv64), 0x0:bv32);
    var R21_39: bv64 := 0x1120:bv64 { .label = "2752_0" };
    goto(%phi_158, %phi_159);
  ];
  block %phi_158 [
    guard bvsgt(extract(32, 0, R24_67:bv64), 0x0:bv32);
    var R24_82: bv64 := zero_extend(32, extract(32, 0, R24_67:bv64)) { .label = "2756_0" };
    goto(%phi_162, %phi_163);
  ];
  block %phi_159 [
    guard bvsle(extract(32, 0, R24_67:bv64), 0x0:bv32);
    var R24_79: bv64 := 0x1:bv64 { .label = "2756_0" };
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
      var ssl3_connect_537_loop_from_7: int := 0x3,
      var R1_96: bv64 := R1_96:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_167 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_39:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_85:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0xf { .label = "phiback" };
    var R1_353: bv64 := R1_96:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_176 {.originalLabel = "byQgqLyXSHa0qQ8Aj/Y70Q=="} [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R25_55:bv64));
    var load49_37: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_158: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_418, %phi_419);
  ];
  block %phi_177 {.originalLabel = "byQgqLyXSHa0qQ8Aj/Y70Q=="} [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R25_55:bv64)));
    var R0_57: bv64 := 0x1130:bv64 { .label = "2564_0" };
    goto(%phi_178, %phi_179);
  ];
  block %phi_178 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_57:bv64));
    var R21_167: bv64 := 0x1140:bv64 { .label = "2908_0" };
    goto(%phi_398, %phi_399);
  ];
  block %phi_179 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_57:bv64)));
    var R0_58: bv64 := 0x1140:bv64 { .label = "2576_0" };
    goto(%phi_180, %phi_181);
  ];
  block %phi_180 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_58:bv64));
    var load49_35: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_138: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    var R1_292: bv64 := 0x4:bv64 { .label = "2976_0" };
    goto(%phi_378, %phi_379);
  ];
  block %phi_181 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_58:bv64)));
    var R0_59: bv64 := 0x1150:bv64 { .label = "2588_0" };
    goto(%phi_182, %phi_183);
  ];
  block %phi_182 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_59:bv64));
    var load49_34: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_129: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_362, %phi_363);
  ];
  block %phi_183 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_59:bv64)));
    var R0_60: bv64 := 0x1160:bv64 { .label = "2600_0" };
    goto(%phi_184, %phi_185);
  ];
  block %phi_184 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_60:bv64));
    var load49_33: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_121: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_336, %phi_337);
  ];
  block %phi_185 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_60:bv64)));
    var R0_61: bv64 := 0x1170:bv64 { .label = "2612_0" };
    goto(%phi_186, %phi_187);
  ];
  block %phi_186 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_61:bv64));
    var load49_32: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_116: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_330, %phi_331);
  ];
  block %phi_187 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_61:bv64)));
    var R0_62: bv64 := 0x1180:bv64 { .label = "2624_0" };
    goto(%phi_188, %phi_189);
  ];
  block %phi_188 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_62:bv64));
    var load49_31: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_110: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_303, %phi_304);
  ];
  block %phi_189 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_62:bv64)));
    var R0_63: bv64 := 0x1190:bv64 { .label = "2636_0" };
    goto(%phi_190, %phi_191);
  ];
  block %phi_190 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_63:bv64));
    var load49_30: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_105: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_297, %phi_298);
  ];
  block %phi_191 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_63:bv64)));
    var R0_64: bv64 := 0x11a0:bv64 { .label = "2648_0" };
    goto(%phi_192, %phi_193);
  ];
  block %phi_192 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_64:bv64));
    var load49_29: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_96: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_273, %phi_274);
  ];
  block %phi_193 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_64:bv64)));
    var R0_65: bv64 := 0x11b0:bv64 { .label = "2660_0" };
    goto(%phi_194, %phi_195);
  ];
  block %phi_194 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_65:bv64));
    var load49_28: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_82: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_240, %phi_241);
  ];
  block %phi_195 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_65:bv64)));
    var R0_66: bv64 := 0x11d0:bv64 { .label = "2672_0" };
    goto(%phi_196, %phi_197);
  ];
  block %phi_196 [
    guard eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_66:bv64));
    var load49_27: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_77: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_224, %phi_225);
  ];
  block %phi_197 [
    guard boolnot(eq(extract(32, 0, R21_53:bv64), extract(32, 0, R0_66:bv64)));
    var R0_67: bv64 := 0x1100:bv64 { .label = "2684_0" };
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
    var load15_1: bv32 := Stack_n24_n20:bv32 { .label = "2696_0_0" };
    goto(%phi_200, %phi_201);
  ];
  block %phi_200 [
    guard bvsle(load15_1:bv32, 0x0:bv32);
    var load32_1: bv32 := Stack_n4_0:bv32 { .label = "3384_0_0" };
    var R21_82: bv64 := zero_extend(32, load32_1:bv32) { .label = "3384_0_1" };
    goto(%phi_213, %phi_214);
  ];
  block %phi_201 [
    guard bvsgt(load15_1:bv32, 0x0:bv32);
    var load19_1: bv32 := Stack_n16_n12:bv32 { .label = "2708_0_0" };
    goto(%phi_202, %phi_203);
  ];
  block %phi_202 [
    guard bvsle(load19_1:bv32, 0x0:bv32);
    var R1_366: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_203 [
    guard bvsgt(load19_1:bv32, 0x0:bv32);
    goto(%phi_204, %phi_205);
  ];
  block %phi_204 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var load33_1: bv32 := Stack_n16_n12:bv32 { .label = "3364_0_0" };
    var Stack_n24_n20: bv32 := load33_1:bv32 { .label = "3368_0" };
    var load34_1: bv32 := Stack_n4_0:bv32 { .label = "3372_0_0" };
    var R21_77: bv64 := zero_extend(32, load34_1:bv32) { .label = "3372_0_1" };
    goto(%phi_207, %phi_208);
  ];
  block %phi_205 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    var load16_1: bv32 := Stack_n4_0:bv32 { .label = "2724_0_0" };
    var Stack_n24_n20: bv32 := load19_1:bv32 { .label = "2728_0" };
    ( var R21_53: bv64 := zero_extend(32, load16_1:bv32),
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_207 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_77:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x8,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_208 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_77:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x1 { .label = "phiback" };
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
      var ssl3_connect_537_loop_from_7: int := 0x6,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_216 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_82:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x2 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_224 {.originalLabel = "dveh6Y01QqOGOBofGfrhVw=="} [
    guard bvsle(extract(32, 0, R0_77:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_77:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_225 {.originalLabel = "dveh6Y01QqOGOBofGfrhVw=="} [
    guard bvsgt(extract(32, 0, R0_77:bv64), 0x0:bv32);
    goto(%phi_226, %phi_227);
  ];
  block %phi_226 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    goto(%ssl3_connect_loop0_302);
  ];
  block %phi_227 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_89: bv64 := 0x3:bv64 { .label = "3324_0" };
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
    var ssl3_connect_537_loop_from_57: int := 0x10 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_240 {.originalLabel = "JkIS6gVvRleA9UalAT4Shg=="} [
    guard bvsle(extract(32, 0, R0_82:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_82:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_241 {.originalLabel = "JkIS6gVvRleA9UalAT4Shg=="} [
    guard bvsgt(extract(32, 0, R0_82:bv64), 0x0:bv32);
    var load17_1: bv32 := Stack_n20_n16:bv32 { .label = "3188_0_0" };
    var R0_87: bv64 := zero_extend(32, bvadd(load17_1:bv32, 0xfffffffb:bv32)) { .label = "3192_0" };
    var Stack_n20_n16: bv32 := bvadd(load17_1:bv32, 0xfffffffb:bv32) { .label = "3196_0" };
    goto(%phi_242, %phi_243);
  ];
  block %phi_242 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var Stack_n4_0: bv32 := 0x11d0:bv32 { .label = "3344_0" };
    var R21_110: bv64 := 0x1100:bv64 { .label = "3348_0" };
    goto(%phi_262, %phi_263);
  ];
  block %phi_243 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    goto(%phi_244, %phi_245);
  ];
  block %phi_244 [
    guard eq(extract(32, 0, R0_87:bv64), 0xfffffffe:bv32);
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3404_0" };
    var R21_103: bv64 := 0x1100:bv64 { .label = "3408_0" };
    goto(%phi_254, %phi_255);
  ];
  block %phi_245 [
    guard boolnot(eq(extract(32, 0, R0_87:bv64), 0xfffffffe:bv32));
    var R0_92: bv32 := bvshl(zero_extend(2, extract(30, 0, R0_87:bv64)), 0x2:bv32) { .label = "3212_0" };
    var R21_96: bv64 := 0x3:bv64 { .label = "3216_0" };
    var Stack_n20_n16: bv32 := R0_92:bv32 { .label = "3220_0" };
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3224_0" };
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
      var ssl3_connect_537_loop_from_7: int := 0x1f,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_249 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_96:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x1c { .label = "phiback" };
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
      var ssl3_connect_537_loop_from_7: int := 0x22,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_257 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_103:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x14 { .label = "phiback" };
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
      var ssl3_connect_537_loop_from_7: int := 0x5,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_265 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_110:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x16 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_273 {.originalLabel = "Wfs1fTcATxGWRdgmf/JW1g=="} [
    guard bvsle(extract(32, 0, R0_96:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_96:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_274 {.originalLabel = "Wfs1fTcATxGWRdgmf/JW1g=="} [
    guard bvsgt(extract(32, 0, R0_96:bv64), 0x0:bv32);
    var load47_1: bv32 := Stack_n12_n8:bv32 { .label = "3252_0_0" };
    var load48_1: bv32 := Stack_n8_n4:bv32 { .label = "3260_0_0" };
    goto(%phi_275, %phi_276);
  ];
  block %phi_275 [
    guard boolnot(eq(load47_1:bv32, 0x0:bv32));
    var ZF_94: bv1 := bvcomp(load48_1:bv32, 0x0:bv32) { .label = "3264_1" };
    goto(%phi_279, %phi_280);
  ];
  block %phi_276 [
    guard eq(load47_1:bv32, 0x0:bv32);
    var ZF_98: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_342);
  ];
  block %phi_279 [
    guard eq(load48_1:bv32, 0x0:bv32);
    var ZF_98: bv1 := ZF_94:bv1 { .label = "phiback" };
    goto(%ssl3_connect_342);
  ];
  block %phi_280 [
    guard boolnot(eq(load48_1:bv32, 0x0:bv32));
    var R21_117: bv64 := 0x11b0:bv64 { .label = "3272_0" };
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
      var ssl3_connect_537_loop_from_7: int := 0x18,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_286 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_117:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x17 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_297 {.originalLabel = "TiP+JwJNTgi+SjF22DVZow=="} [
    guard bvsgt(extract(32, 0, R0_105:bv64), 0x0:bv32);
    goto(%ssl3_connect_loop0_302);
  ];
  block %phi_298 {.originalLabel = "TiP+JwJNTgi+SjF22DVZow=="} [
    guard bvsle(extract(32, 0, R0_105:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_105:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_303 {.originalLabel = "o7upzRnFT3mYOHVd18cgiw=="} [
    guard bvsle(extract(32, 0, R0_110:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_110:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_304 {.originalLabel = "o7upzRnFT3mYOHVd18cgiw=="} [
    guard bvsgt(extract(32, 0, R0_110:bv64), 0x0:bv32);
    var load14_1: bv32 := Stack_n28_n24:bv32 { .label = "3132_0_0" };
    goto(%phi_305, %phi_306);
  ];
  block %phi_305 [
    guard eq(load14_1:bv32, 0x1:bv32);
    var R21_131: bv64 := 0x1190:bv64 { .label = "3288_0" };
    goto(%phi_319, %phi_320);
  ];
  block %phi_306 [
    guard boolnot(eq(load14_1:bv32, 0x1:bv32));
    goto(%ssl3_connect_loop0_302);
  ];
  block %phi_311 {.originalLabel = "23KcPGijQZSegu7sMlvMpQ=="} [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_124:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_312 {.originalLabel = "23KcPGijQZSegu7sMlvMpQ=="} [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_313, %phi_314);
  ];
  block %phi_313 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_124:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0xc,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_314 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_124:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0xe { .label = "phiback" };
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
    var R21_134: bv64 := 0x1190:bv64 { .label = "3296_0" };
    goto(%phi_321, %phi_322);
  ];
  block %phi_321 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_134:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x7,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_322 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_134:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x1b { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_330 {.originalLabel = "WD6KmSyTQ4usPmboKJnZlg=="} [
    guard bvsle(extract(32, 0, R0_116:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_116:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_331 {.originalLabel = "WD6KmSyTQ4usPmboKJnZlg=="} [
    guard bvsgt(extract(32, 0, R0_116:bv64), 0x0:bv32);
    goto(%ssl3_connect_loop0_220);
  ];
  block %phi_336 {.originalLabel = "LfoU+H9GSKWt3YDd/WKNdw=="} [
    guard bvsle(extract(32, 0, R0_121:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_119:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_337 {.originalLabel = "LfoU+H9GSKWt3YDd/WKNdw=="} [
    guard bvsgt(extract(32, 0, R0_121:bv64), 0x0:bv32);
    var load18_1: bv32 := Stack_n28_n24:bv32 { .label = "3096_0_0" };
    goto(%phi_338, %phi_339);
  ];
  block %phi_338 [
    guard eq(load18_1:bv32, 0x0:bv32);
    goto(%ssl3_connect_loop0_220);
  ];
  block %phi_339 [
    guard boolnot(eq(load18_1:bv32, 0x0:bv32));
    var R21_139: bv64 := 0x1170:bv64 { .label = "3104_0" };
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
      var ssl3_connect_537_loop_from_7: int := 0x12,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_343 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_139:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x20 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_351 {.originalLabel = "O5+lse05SxaN77BSH+QmDg=="} [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_53: bv64 := R21_146:bv64,
      var R24_92: bv64 := R24_92:bv64,
      var R1_119: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop1_578);
  ];
  block %phi_352 {.originalLabel = "O5+lse05SxaN77BSH+QmDg=="} [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_353, %phi_354);
  ];
  block %phi_353 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_146:bv64,
      var R24_67: bv64 := R24_92:bv64,
      var ssl3_connect_537_loop_from_7: int := 0xb,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_354 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_146:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x0 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_362 {.originalLabel = "1VQS1uzMSD+jkj9I9di5og=="} [
    guard eq(extract(32, 0, R24_92:bv64), 0x5:bv32);
    assert eq(R30_in:bv64, 0x744:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_6:bv64, R1_retval_inlined_7:bv64, R2_retval_inlined_8:bv64, R3_retval_inlined_9:bv64) := call @reach_error_2240 (bvadd(R31_in:bv64, 0xffffffffffffff80:bv64), 0x744:bv64, bvadd(R31_in:bv64, 0xffffffffffffff80:bv64)) { .label = "3424_2" };
    goto(%phi_362_retval_inline);
  ];
  block %phi_363 {.originalLabel = "1VQS1uzMSD+jkj9I9di5og=="} [
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
    var R21_153: bv64 := 0x1160:bv64 { .label = "3040_0" };
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
      var ssl3_connect_537_loop_from_7: int := 0x21,
      var R1_96: bv64 := R1_119:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_369 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_153:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_92:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x15 { .label = "phiback" };
    var R1_353: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_378 {.originalLabel = "GMVkeg0jRYe2+WeS5tiQ+w=="} [
    guard boolnot(eq(extract(32, 0, R24_92:bv64), 0x3:bv32));
    var R24_259: bv64 := zero_extend(32, extract(32, 0, R24_92:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_152);
  ];
  block %phi_379 {.originalLabel = "GMVkeg0jRYe2+WeS5tiQ+w=="} [
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
    var R21_160: bv64 := 0x1150:bv64 { .label = "2996_0" };
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
      var ssl3_connect_537_loop_from_7: int := 0x9,
      var R1_96: bv64 := R1_292:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_391 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_160:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_259:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x11 { .label = "phiback" };
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
    var load49_36: bv64 := $Global_131104_131112:bv64 { .label = "1780_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_148: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    var R1_312: bv64 := 0x3:bv64 { .label = "2928_0" };
    goto(%phi_402, %phi_403);
  ];
  block %phi_402 {.originalLabel = "kSiEb1YOQ1exd6BqeLM/5A=="} [
    guard boolnot(eq(extract(32, 0, R24_92:bv64), 0x2:bv32));
    var R24_280: bv64 := zero_extend(32, extract(32, 0, R24_92:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_106);
  ];
  block %phi_403 {.originalLabel = "kSiEb1YOQ1exd6BqeLM/5A=="} [
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
  block %phi_418 {.originalLabel = "OOQmrLrnT5yzKhAUqdzEvA=="} [
    guard eq(extract(32, 0, R24_92:bv64), 0x1:bv32);
    var R24_298: bv64 := 0x2:bv64 { .label = "phiback" };
    var R1_334: bv64 := R1_119:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_68);
  ];
  block %phi_419 {.originalLabel = "OOQmrLrnT5yzKhAUqdzEvA=="} [
    guard boolnot(eq(extract(32, 0, R24_92:bv64), 0x1:bv32));
    var R1_328: bv64 := 0x5:bv64 { .label = "2872_0" };
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
  block %phi_428 {.originalLabel = "wYBn9D91RBm3Gkk99r95Lg=="} [
    guard bvsle(extract(32, 0, R0_158:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_334:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_158:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_429 {.originalLabel = "wYBn9D91RBm3Gkk99r95Lg=="} [
    guard bvsgt(extract(32, 0, R0_158:bv64), 0x0:bv32);
    goto(%phi_430, %phi_431);
  ];
  block %phi_430 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_189: bv64 := 0x1130:bv64 { .label = "2956_0" };
    goto(%phi_440, %phi_441);
  ];
  block %phi_431 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    var R21_182: bv64 := 0x11d0:bv64 { .label = "2892_0" };
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
      var ssl3_connect_537_loop_from_7: int := 0x13,
      var R1_96: bv64 := R1_334:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_435 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_182:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_298:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x1a { .label = "phiback" };
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
  block %phi_446 {.originalLabel = "V6AhPKWYTRKSwtGKfY5VZg=="} [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_33: bv64 := R21_193:bv64,
      var R24_67: bv64 := R24_312:bv64,
      var ssl3_connect_537_loop_from_7: int := 0x1d,
      var R1_96: bv64 := R1_348:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_447 {.originalLabel = "V6AhPKWYTRKSwtGKfY5VZg=="} [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_198: bv64 := R21_193:bv64 { .label = "phiback" };
    var R24_317: bv64 := R24_312:bv64 { .label = "phiback" };
    var ssl3_connect_537_loop_from_57: int := 0x19 { .label = "phiback" };
    var R1_353: bv64 := R1_348:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_469 {.originalLabel = "B6efx2euTry2aG25O0KW7A=="} [
    guard bvsgt(extract(32, 0, R0_170:bv64), 0x0:bv32);
    ( var R21_33: bv64 := R21_198:bv64,
      var R24_67: bv64 := R24_317:bv64,
      var ssl3_connect_537_loop_from_7: int := 0xa,
      var R1_96: bv64 := R1_353:bv64 );
    goto(%ssl3_connect_loop2_616);
  ];
  block %phi_470 {.originalLabel = "B6efx2euTry2aG25O0KW7A=="} [
    guard bvsle(extract(32, 0, R0_170:bv64), 0x0:bv32);
    var R1_361: bv64 := R1_353:bv64 { .label = "phiback" };
    var R0_177: bv64 := R0_170:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_362_retval_inline [
    var R31_371: bv64 := bvadd(R31_in:bv64, 0xffffffffffffff80:bv64) { .label = "phiback" };
    var R1_368: bv64 := 0xd98:bv64 { .label = "phiback" };
    var R0_181: bv64 := 0xdb0:bv64 { .label = "phiback" };
    var R3_369: bv64 := 0xd88:bv64 { .label = "phiback" };
    var R2_369: bv64 := 0x3:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_return [
    assert eq(R31_in:bv64, R31_371:bv64) { .comment = "R31 preserved across calls" };
    return (R0_181:bv64, R1_368:bv64, R2_369:bv64, R3_369:bv64);
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
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2V4qSuq9qbw28t1kjO/3C5o+9/Wd5UFABm9lB8kAAAA" ]
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
      "H4sIAAAAAAAA/41UT2gcZRR/s7O1rWltyWZIGrG7G0UkWLHmm5V6cVIrezFIuyMqRbpJ1BTXEMZNG8wcdrcXD0XoNkHBg6ki";
      "4hYPoj04F5uIoKJemhoUimxDk1Zbm21mt+kk2Tx/385EimLx8Pi9773fe9/3/szU7bOlukrFw0TjRPkDdXvqk0n10Ew0pv78";
      "f+U+yp/bCZlT6fRF1fBm76fiPHKWiSp0Lemp8IUhU8zv/ghp2K8kPYPozDfMrXe6jxQ6QTGlqADjwCeJrk4SmReRI15Oer3I";
      "UVGV0xSKzsg8/+THiX7oWM1Nd28pHI+vdo9NgT+L2L2VpNfXiA39HVu3v2r0wm0iL4L4dEf3HkOhxxvvvZT08uD7+Q3vJOr4";
      "FRJDz9Idyh63yfDq9tf/6t0F1Hen3tXRf5XohAKRdxOwP5YoxtOJIk0min3I/xbuqdtf+m9LKaXawVBpqV8teZlwaSW7oWTD";
      "fwxSgNxSqXMEeBRyBHIT5ywQQ+i0gFXgUOAfhAxDpP81OZchcg5LHCDnVeArEBf8fmAfZAl6GnhIcjLkSP/LkIOQGnwvAleA";
      "zwOXgc8BV4EpyR8hZ79Em5xnJWbJ6ZGYm2iOqpRR7ibzzc0kcipZ++41RvObyWxD7VrHsQMpIt3cSDpBPxuiTHkDmTsekPqO";
      "jAEePejb88hBD/k6bYHe6evGVugPB7H3QH/E109J+6MBZxv0x3w9th26COzN0BNBrOQ8EcRGoMd8XWkls5wxnCiR1aNBz/r6";
      "oEpmVwuJWs5wZL/OYxe2o2bp26WQibotDXW0fTvRPuax3uKx2BT4P73Fppvqxqz3YtZPYdb7MOunS3X7u8aOra35vI/ajdHe";
      "mz4X32/zf/EXJX8jWafCuDdC1gfobVuk0C5z/LTKZiJEQkNt2Rrr56ssfsNbNfSSQ+HdU1U2Z2V8E1m9t8VtXcG9Luumy+Kc";
      "5GMOXzCL96DPSP42sgq38d/22LywzELDXLoWWR+/wUJ+/y+AI+/7Xsa0kpXG7Br50QMNc5uusC4qLBz5rwjq3rUEH2bnLuD+";
      "BRafw+cEvh70ozxgOIS3aJj19HXEX2dRAuez9fiaz4mG/Z5omPfYn6xXr7GYAO/jgPcMs/k+zh8G50EXcUPI3UL75fdyNEwi";
      "uol2013Yh+GdqSOoRdprOXIiV1kf/oPFccSfXI+/gfgRfz/KtuGE24zR2CJqwY6N/Y77r7DIyV5iFyM4SzRhG4WtsF7fApvv";
      "LLMu73Ivo/7LLN6AX+5mGfdq2Msu2MfnWbwOu9xHuX9yD6tzLAZgk3pkHu/DGd93a1q+O4hNzbF+5hKLl2D/Zc3/x0n9L2YJ";
      "n9QsBgAA"
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
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML/YOD45J68k3ljPKUwvWS85M0fXMFEvmcGAAQCSQcklMgAAAA=="
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
      "55rBOZNjFvtstjmsTDVc9+7evnPz1vUbV69dvsLH4MjtjSHCIAM05gcQu/z4/18CyS6Xe3f5oM5hAADlXtkOGAEAAA=="
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
