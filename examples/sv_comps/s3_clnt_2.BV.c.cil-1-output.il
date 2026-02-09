var $Global_131104_131112: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_int : () -> bv32;

prog entry @main_1792;

proc @main_1792
  (R0_in:bv64, R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R29_out:bv64, _PC_out:bv64)
  { .name = "main"; .address = 0x700; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x700; .originalLabel = "KY9I84glRcSONZi/3Uq3ng=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1792_2" };
    var (R0_2:bv64, R1_2:bv64, R2_2:bv64, R3_2:bv64) := call @ssl3_connect_2216 (R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R22_in:bv64, R23_in:bv64, R24_in:bv64, R25_in:bv64, R26_in:bv64, R27_in:bv64, R28_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), R2_in:bv64, 0x70c:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), R3_in:bv64);
    goto(%main_return);
  ];
  block %main_return [
    var _PC_2: bv64 := _PC_in:bv64 { .label = "inlineret" };
    var load18_1: bv64 := Stack_n16_n8:bv64 { .label = "1808_0_0" };
    var load19_1: bv64 := Stack_n8_0:bv64 { .label = "1808_1_0" };
    assert eq(R30_in:bv64, load19_1:bv64) { .comment = "R30 preserved across calls" };
    assert true { .comment = "R31 preserved across calls" };
    return (0x0:bv64, load18_1:bv64, _PC_2:bv64);
  ]
];


proc @reach_error_2176
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x880; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x880; .originalLabel = "Ng3lJgJ0QHetrwFA170Teg=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2176_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2176_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load21_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
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
  block %ssl3_connect_entry {.address = 0x8a8; .originalLabel = "8fk+ZInYSWKG7adofMJS2w=="} [
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
    var load20_1: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_2: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_3: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv32 := $__VERIFIER_nondet_int();
    var load20_4: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_5: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_6: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv32 := $__VERIFIER_nondet_int();
    var load20_7: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_10: bv32 := $__VERIFIER_nondet_int();
    var load20_8: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_12: bv32 := $__VERIFIER_nondet_int();
    var load20_9: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_10: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_11: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_12: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_13: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_14: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_19: bv32 := $__VERIFIER_nondet_int();
    var Stack_n20_n16: bv32 := R0_19:bv32 { .label = "2316_0" };
    var load20_15: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_21: bv32 := $__VERIFIER_nondet_int();
    var Stack_n28_n24: bv32 := R0_21:bv32 { .label = "2324_0" };
    var load20_16: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_17: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_24: bv32 := $__VERIFIER_nondet_int();
    var load20_18: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_19: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_27: bv32 := $__VERIFIER_nondet_int();
    var load20_20: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_21: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_30: bv32 := $__VERIFIER_nondet_int();
    var Stack_n24_n20: bv32 := R0_30:bv32 { .label = "2360_0" };
    var load20_22: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_23: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load20_24: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_34: bv32 := $__VERIFIER_nondet_int();
    var load20_25: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_36: bv32 := $__VERIFIER_nondet_int();
    var load20_26: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_38: bv32 := $__VERIFIER_nondet_int();
    var load20_27: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_40: bv32 := $__VERIFIER_nondet_int();
    var load20_28: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_42: bv32 := $__VERIFIER_nondet_int();
    var Stack_n12_n8: bv32 := R0_42:bv32 { .label = "2408_0" };
    var load20_29: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_44: bv32 := $__VERIFIER_nondet_int();
    var Stack_n8_n4: bv32 := R0_44:bv32 { .label = "2416_0" };
    var load20_30: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_46: bv32 := $__VERIFIER_nondet_int();
    var Stack_n16_n12: bv32 := R0_46:bv32 { .label = "2424_0" };
    var load20_31: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    goto(%phi_110, %phi_111);
  ];
  block %ssl3_connect_4 {.address = 0xacc; .originalLabel = "GuYI5lM3Te6blQCXJaiXmw=="} [
    var load46_1: bv64 := Stack_n112_n104:bv64 { .label = "2764_1_0" };
    var load47_1: bv64 := Stack_n104_n96:bv64 { .label = "2764_2_0" };
    var load48_1: bv64 := Stack_n96_n88:bv64 { .label = "2772_1_0" };
    var load49_1: bv64 := Stack_n88_n80:bv64 { .label = "2772_2_0" };
    var load50_1: bv64 := Stack_n80_n72:bv64 { .label = "2776_1_0" };
    var load51_1: bv64 := Stack_n72_n64:bv64 { .label = "2776_2_0" };
    var load52_1: bv64 := Stack_n64_n56:bv64 { .label = "2780_1_0" };
    var load53_1: bv64 := Stack_n56_n48:bv64 { .label = "2780_2_0" };
    var load54_1: bv64 := Stack_n48_n40:bv64 { .label = "2784_1_0" };
    var load55_1: bv64 := Stack_n40_n32:bv64 { .label = "2784_2_0" };
    var load56_1: bv64 := Stack_n128_n120:bv64 { .label = "2788_0_0" };
    var load57_1: bv64 := Stack_n120_n112:bv64 { .label = "2788_1_0" };
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
  block %ssl3_connect_10 {.address = 0xaa0; .originalLabel = "j7IyxAxFSvSQgoS1hUK3yA=="} [
    var load30_1: bv64 := Stack_n112_n104:bv64 { .label = "2720_1_0" };
    var load31_1: bv64 := Stack_n104_n96:bv64 { .label = "2720_2_0" };
    var load32_1: bv64 := Stack_n96_n88:bv64 { .label = "2724_1_0" };
    var load33_1: bv64 := Stack_n88_n80:bv64 { .label = "2724_2_0" };
    var load34_1: bv64 := Stack_n80_n72:bv64 { .label = "2728_1_0" };
    var load35_1: bv64 := Stack_n72_n64:bv64 { .label = "2728_2_0" };
    var load36_1: bv64 := Stack_n64_n56:bv64 { .label = "2732_1_0" };
    var load37_1: bv64 := Stack_n56_n48:bv64 { .label = "2732_2_0" };
    var load38_1: bv64 := Stack_n48_n40:bv64 { .label = "2736_1_0" };
    var load39_1: bv64 := Stack_n40_n32:bv64 { .label = "2736_2_0" };
    var load40_1: bv64 := Stack_n128_n120:bv64 { .label = "2740_0_0" };
    var load41_1: bv64 := Stack_n120_n112:bv64 { .label = "2740_1_0" };
    var R31_369: bv64 := R31_in:bv64 { .label = "phiback" };
    var R1_367: bv64 := R1_360:bv64 { .label = "phiback" };
    var R0_183: bv64 := R0_179:bv64 { .label = "phiback" };
    var R3_367: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_367: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_loop0_30 {.address = 0xa94; .originalLabel = "W1KXvcG4TMSw8WiLffGZeg=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_539_loop_from_57:int, 0x2), eq(ssl3_connect_539_loop_from_57:int, 0x9)), eq(ssl3_connect_539_loop_from_57:int, 0xa)), eq(ssl3_connect_539_loop_from_57:int, 0xb)), eq(ssl3_connect_539_loop_from_57:int, 0xc)), eq(ssl3_connect_539_loop_from_57:int, 0xd)), eq(ssl3_connect_539_loop_from_57:int, 0xe)), eq(ssl3_connect_539_loop_from_57:int, 0x10)), eq(ssl3_connect_539_loop_from_57:int, 0x11)), eq(ssl3_connect_539_loop_from_57:int, 0x17)), eq(ssl3_connect_539_loop_from_57:int, 0x18)), eq(ssl3_connect_539_loop_from_57:int, 0x1b)), eq(ssl3_connect_539_loop_from_57:int, 0x1c)), eq(ssl3_connect_539_loop_from_57:int, 0x1e)), eq(ssl3_connect_539_loop_from_57:int, 0x1f)), eq(ssl3_connect_539_loop_from_57:int, 0x21)), eq(ssl3_connect_539_loop_from_57:int, 0x23));
    var load20_45: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_172: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_466, %phi_467);
  ];
  block %ssl3_connect_loop0_36 {.address = 0xb48; .originalLabel = "w9lKWeJuQsKW9DWhEvp6xQ=="} [
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
  block %ssl3_connect_loop0_212 {.address = 0xbb8; .originalLabel = "+cV3c5mPQpKnuljiJRbdJA=="} [
    var R21_175: bv64 := 0x1180:bv64 { .label = "3000_0" };
    goto(%phi_352, %phi_353);
  ];
  block %ssl3_connect_loop0_294 {.address = 0xc04; .originalLabel = "RdELhXcNS8OVRvsdVKc30A=="} [
    var R21_153: bv64 := 0x11a0:bv64 { .label = "3076_0" };
    goto(%phi_312, %phi_313);
  ];
  block %ssl3_connect_334 [
    guard eq(ZF_98:bv1, 0x1:bv1);
    var R1_365: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %ssl3_connect_loop1_570 {.address = 0x9b8; .originalLabel = "C2G97daTSLiw4nVarDLY9g=="} [
    assert eq(R25_55:bv64, 0x1120:bv64);
    goto(%phi_177, %phi_178);
  ];
  block %ssl3_connect_loop1_572 {.address = 0x9b4; .originalLabel = "zsb4SMqnQEOopsD6MwApng=="} [
    var R25_55: bv64 := 0x1120:bv64 { .label = "2484_0" };
    ( var R21_82: bv64 := R21_81:bv64,
      var R22_60: bv64 := R22_59:bv64,
      var R1_121: bv64 := R1_120:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %ssl3_connect_loop1_588 {.address = 0xa80; .originalLabel = "ybkG9MgZTZyP4Am/tR4DQQ=="} [
    goto(%phi_165, %phi_166);
  ];
  block %ssl3_connect_loop2_618 [
    goto(%phi_149, %phi_150);
  ];
  block %ssl3_connect_638 {.address = 0x98c; .originalLabel = "INRUjy+uTvOj8qDhlJe1/g=="} [
    goto(%phi_131, %phi_132);
  ];
  block %ssl3_connect_642 [
    guard eq(ZF_13:bv1, 0x1:bv1);
    var R1_365: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_110 {.originalLabel = "AaXR0XTcR1uqKo2JhtBIRw=="} [
    guard boolnot(eq(bvadd(R0_4:bv32, 0xffff0000:bv32), 0x200:bv32));
    var R1_365: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_111 {.originalLabel = "AaXR0XTcR1uqKo2JhtBIRw=="} [
    guard eq(bvadd(R0_4:bv32, 0xffff0000:bv32), 0x200:bv32);
    goto(%phi_112, %phi_113);
  ];
  block %phi_112 [
    guard eq(R0_10:bv32, 0x0:bv32);
    var load20_32: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_49: bv32 := $__VERIFIER_nondet_int();
    goto(%phi_117, %phi_118);
  ];
  block %phi_113 [
    guard boolnot(eq(R0_10:bv32, 0x0:bv32));
    goto(%ssl3_connect_638);
  ];
  block %phi_117 {.originalLabel = "eEkiI1+CTNeggV+MYrqToQ=="} [
    guard boolnot(eq(R0_49:bv32, 0x0:bv32));
    var ZF_10: bv1 := bvcomp(R0_34:bv32, 0x0:bv32) { .label = "2756_1" };
    goto(%phi_121, %phi_122);
  ];
  block %phi_118 {.originalLabel = "eEkiI1+CTNeggV+MYrqToQ=="} [
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
  block %phi_131 {.originalLabel = "INRUjy+uTvOj8qDhlJe1/g=="} [
    guard boolnot(eq(R0_36:bv32, 0x0:bv32));
    var ZF_21: bv1 := bvcomp(R0_38:bv32, 0x0:bv32) { .label = "2448_1" };
    goto(%phi_135, %phi_136);
  ];
  block %phi_132 {.originalLabel = "INRUjy+uTvOj8qDhlJe1/g=="} [
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
    var ssl3_connect_539_loop_from_7: int := 0x12 { .label = "phiback" };
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
    var ssl3_connect_539_loop_from_7: int := 0xe { .label = "phiback" };
    var R22_33: bv64 := 0x0:bv64 { .label = "phiback" };
    var R1_96: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_142 [
    guard eq(R0_12:bv32, 0x0:bv32);
    var R21_68: bv64 := 0x1110:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_7: int := 0x7 { .label = "phiback" };
    var R22_33: bv64 := 0x0:bv64 { .label = "phiback" };
    var R1_96: bv64 := R1_in:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_149 {.originalLabel = "+pMWQw4XSMONgXvybkbN+w=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_539_loop_from_7:int, 0x0), eq(ssl3_connect_539_loop_from_7:int, 0x1)), eq(ssl3_connect_539_loop_from_7:int, 0x3)), eq(ssl3_connect_539_loop_from_7:int, 0x4)), eq(ssl3_connect_539_loop_from_7:int, 0x5)), eq(ssl3_connect_539_loop_from_7:int, 0x6)), eq(ssl3_connect_539_loop_from_7:int, 0x7)), eq(ssl3_connect_539_loop_from_7:int, 0x8)), eq(ssl3_connect_539_loop_from_7:int, 0xf)), eq(ssl3_connect_539_loop_from_7:int, 0x12)), eq(ssl3_connect_539_loop_from_7:int, 0x13)), eq(ssl3_connect_539_loop_from_7:int, 0x14)), eq(ssl3_connect_539_loop_from_7:int, 0x15)), eq(ssl3_connect_539_loop_from_7:int, 0x16)), eq(ssl3_connect_539_loop_from_7:int, 0x19)), eq(ssl3_connect_539_loop_from_7:int, 0x1a)), eq(ssl3_connect_539_loop_from_7:int, 0x1d)), eq(ssl3_connect_539_loop_from_7:int, 0x20)), eq(ssl3_connect_539_loop_from_7:int, 0x22));
    var R0_51: bv64 := 0x1110:bv64 { .label = "2472_0" };
    goto(%phi_151, %phi_152);
  ];
  block %phi_150 {.originalLabel = "W1KXvcG4TMSw8WiLffGZeg=="} [
    assume boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(boolor(eq(ssl3_connect_539_loop_from_7:int, 0x2), eq(ssl3_connect_539_loop_from_7:int, 0x9)), eq(ssl3_connect_539_loop_from_7:int, 0xa)), eq(ssl3_connect_539_loop_from_7:int, 0xb)), eq(ssl3_connect_539_loop_from_7:int, 0xc)), eq(ssl3_connect_539_loop_from_7:int, 0xd)), eq(ssl3_connect_539_loop_from_7:int, 0xe)), eq(ssl3_connect_539_loop_from_7:int, 0x10)), eq(ssl3_connect_539_loop_from_7:int, 0x11)), eq(ssl3_connect_539_loop_from_7:int, 0x17)), eq(ssl3_connect_539_loop_from_7:int, 0x18)), eq(ssl3_connect_539_loop_from_7:int, 0x1b)), eq(ssl3_connect_539_loop_from_7:int, 0x1c)), eq(ssl3_connect_539_loop_from_7:int, 0x1e)), eq(ssl3_connect_539_loop_from_7:int, 0x1f)), eq(ssl3_connect_539_loop_from_7:int, 0x21)), eq(ssl3_connect_539_loop_from_7:int, 0x23));
    var R21_227: bv64 := R21_68:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := ssl3_connect_539_loop_from_7:int { .label = "phiback" };
    var R22_281: bv64 := R22_33:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_96:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_151 {.originalLabel = "+pMWQw4XSMONgXvybkbN+w=="} [
    guard eq(extract(32, 0, R21_68:bv64), extract(32, 0, R0_51:bv64));
    var load20_33: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_52: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_155, %phi_156);
  ];
  block %phi_152 {.originalLabel = "+pMWQw4XSMONgXvybkbN+w=="} [
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
    var R1_105: bv64 := 0x5:bv64 { .label = "2680_0" };
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
  block %phi_165 {.originalLabel = "ybkG9MgZTZyP4Am/tR4DQQ=="} [
    guard bvsle(extract(32, 0, R0_52:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_111:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_52:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_166 {.originalLabel = "ybkG9MgZTZyP4Am/tR4DQQ=="} [
    guard bvsgt(extract(32, 0, R0_52:bv64), 0x0:bv32);
    var R21_74: bv64 := 0x1120:bv64 { .label = "2696_0" };
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
      var ssl3_connect_539_loop_from_7: int := 0x1,
      var R22_33: bv64 := R22_50:bv64,
      var R1_96: bv64 := R1_111:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_170 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_74:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x17 { .label = "phiback" };
    var R22_281: bv64 := R22_50:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_111:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_177 {.originalLabel = "C2G97daTSLiw4nVarDLY9g=="} [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R25_55:bv64));
    var load20_44: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_163: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    var R1_328: bv64 := 0x2:bv64 { .label = "2804_0" };
    goto(%phi_419, %phi_420);
  ];
  block %phi_178 {.originalLabel = "C2G97daTSLiw4nVarDLY9g=="} [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R25_55:bv64)));
    var R0_63: bv64 := 0x1130:bv64 { .label = "2496_0" };
    goto(%phi_179, %phi_180);
  ];
  block %phi_179 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_63:bv64));
    var R21_196: bv64 := 0x1140:bv64 { .label = "2848_0" };
    goto(%phi_399, %phi_400);
  ];
  block %phi_180 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_63:bv64)));
    var R0_64: bv64 := 0x1140:bv64 { .label = "2508_0" };
    goto(%phi_181, %phi_182);
  ];
  block %phi_181 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_64:bv64));
    var load20_42: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_143: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    var R1_296: bv64 := 0x4:bv64 { .label = "2916_0" };
    goto(%phi_379, %phi_380);
  ];
  block %phi_182 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_64:bv64)));
    var R0_65: bv64 := 0x1150:bv64 { .label = "2520_0" };
    goto(%phi_183, %phi_184);
  ];
  block %phi_183 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_65:bv64));
    var load20_41: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_134: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_363, %phi_364);
  ];
  block %phi_184 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_65:bv64)));
    var R0_66: bv64 := 0x1160:bv64 { .label = "2532_0" };
    goto(%phi_185, %phi_186);
  ];
  block %phi_185 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_66:bv64));
    var load20_40: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_126: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_337, %phi_338);
  ];
  block %phi_186 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_66:bv64)));
    var R0_67: bv64 := 0x1170:bv64 { .label = "2544_0" };
    goto(%phi_187, %phi_188);
  ];
  block %phi_187 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_67:bv64));
    var load20_39: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_121: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_331, %phi_332);
  ];
  block %phi_188 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_67:bv64)));
    var R0_68: bv64 := 0x1180:bv64 { .label = "2556_0" };
    goto(%phi_189, %phi_190);
  ];
  block %phi_189 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_68:bv64));
    var load20_38: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_115: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_304, %phi_305);
  ];
  block %phi_190 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_68:bv64)));
    var R0_69: bv64 := 0x1190:bv64 { .label = "2568_0" };
    goto(%phi_191, %phi_192);
  ];
  block %phi_191 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_69:bv64));
    var load20_37: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_110: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_298, %phi_299);
  ];
  block %phi_192 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_69:bv64)));
    var R0_70: bv64 := 0x11a0:bv64 { .label = "2580_0" };
    goto(%phi_193, %phi_194);
  ];
  block %phi_193 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_70:bv64));
    var load20_36: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_101: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_274, %phi_275);
  ];
  block %phi_194 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_70:bv64)));
    var R0_71: bv64 := 0x11b0:bv64 { .label = "2592_0" };
    goto(%phi_195, %phi_196);
  ];
  block %phi_195 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_71:bv64));
    var load20_35: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_88: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_241, %phi_242);
  ];
  block %phi_196 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_71:bv64)));
    var R0_72: bv64 := 0x11d0:bv64 { .label = "2604_0" };
    goto(%phi_197, %phi_198);
  ];
  block %phi_197 [
    guard eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_72:bv64));
    var load20_34: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_83: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    goto(%phi_225, %phi_226);
  ];
  block %phi_198 [
    guard boolnot(eq(extract(32, 0, R21_82:bv64), extract(32, 0, R0_72:bv64)));
    var R0_73: bv64 := 0x1100:bv64 { .label = "2616_0" };
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
    var load43_1: bv32 := Stack_n24_n20:bv32 { .label = "2628_0_0" };
    goto(%phi_201, %phi_202);
  ];
  block %phi_201 [
    guard bvsle(load43_1:bv32, 0x0:bv32);
    var load24_1: bv32 := Stack_n4_0:bv32 { .label = "3320_0_0" };
    var R21_111: bv64 := zero_extend(32, load24_1:bv32) { .label = "3320_0_1" };
    goto(%phi_214, %phi_215);
  ];
  block %phi_202 [
    guard bvsgt(load43_1:bv32, 0x0:bv32);
    var load42_1: bv32 := Stack_n16_n12:bv32 { .label = "2640_0_0" };
    goto(%phi_203, %phi_204);
  ];
  block %phi_203 [
    guard bvsle(load42_1:bv32, 0x0:bv32);
    var R1_365: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_4);
  ];
  block %phi_204 [
    guard bvsgt(load42_1:bv32, 0x0:bv32);
    goto(%phi_205, %phi_206);
  ];
  block %phi_205 [
    guard eq(R0_24:bv32, 0x0:bv32);
    var load28_1: bv32 := Stack_n16_n12:bv32 { .label = "3300_0_0" };
    var Stack_n24_n20: bv32 := load28_1:bv32 { .label = "3304_0" };
    var load29_1: bv32 := Stack_n4_0:bv32 { .label = "3308_0_0" };
    var R21_106: bv64 := zero_extend(32, load29_1:bv32) { .label = "3308_0_1" };
    goto(%phi_208, %phi_209);
  ];
  block %phi_206 [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    var load27_1: bv32 := Stack_n4_0:bv32 { .label = "2656_0_0" };
    var Stack_n24_n20: bv32 := load42_1:bv32 { .label = "2660_0" };
    ( var R21_82: bv64 := zero_extend(32, load27_1:bv32),
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_208 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_106:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x8,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_209 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_106:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x11 { .label = "phiback" };
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
      var ssl3_connect_539_loop_from_7: int := 0x1a,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_217 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_111:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x1e { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_225 {.originalLabel = "H35wszeQRtmL/CdncPmaPQ=="} [
    guard bvsle(extract(32, 0, R0_83:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_83:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_226 {.originalLabel = "H35wszeQRtmL/CdncPmaPQ=="} [
    guard bvsgt(extract(32, 0, R0_83:bv64), 0x0:bv32);
    goto(%phi_227, %phi_228);
  ];
  block %phi_227 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    goto(%ssl3_connect_loop0_294);
  ];
  block %phi_228 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var R21_118: bv64 := 0x3:bv64 { .label = "3260_0" };
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
      var ssl3_connect_539_loop_from_7: int := 0x13,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_232 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_118:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0xc { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_241 {.originalLabel = "dbRD4sLYT7uG3hpwySO5Ow=="} [
    guard bvsle(extract(32, 0, R0_88:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_88:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_242 {.originalLabel = "dbRD4sLYT7uG3hpwySO5Ow=="} [
    guard bvsgt(extract(32, 0, R0_88:bv64), 0x0:bv32);
    var load45_1: bv32 := Stack_n20_n16:bv32 { .label = "3120_0_0" };
    var R1_183: bv64 := zero_extend(32, bvadd(load45_1:bv32, 0x5:bv32)) { .label = "3128_0" };
    var Stack_n20_n16: bv32 := bvadd(load45_1:bv32, 0x5:bv32) { .label = "3132_0" };
    goto(%phi_243, %phi_244);
  ];
  block %phi_243 [
    guard eq(R0_8:bv32, 0x0:bv32);
    var Stack_n4_0: bv32 := 0x11d0:bv32 { .label = "3280_0" };
    var R21_139: bv64 := 0x1100:bv64 { .label = "3284_0" };
    goto(%phi_263, %phi_264);
  ];
  block %phi_244 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    goto(%phi_245, %phi_246);
  ];
  block %phi_245 [
    guard eq(extract(32, 0, R1_183:bv64), 0x2:bv32);
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3340_0" };
    var R21_132: bv64 := 0x1100:bv64 { .label = "3344_0" };
    goto(%phi_255, %phi_256);
  ];
  block %phi_246 [
    guard boolnot(eq(extract(32, 0, R1_183:bv64), 0x2:bv32));
    var R21_125: bv64 := 0x3:bv64 { .label = "3152_0" };
    var Stack_n20_n16: bv32 := bvadd(load45_1:bv32, 0x9:bv32) { .label = "3156_0" };
    var Stack_n4_0: bv32 := 0x3:bv32 { .label = "3160_0" };
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
      var ssl3_connect_539_loop_from_7: int := 0x5,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_183:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_250 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_125:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x2 { .label = "phiback" };
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
      var ssl3_connect_539_loop_from_7: int := 0x0,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_183:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_258 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_132:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x9 { .label = "phiback" };
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
      var ssl3_connect_539_loop_from_7: int := 0x16,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_183:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_266 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_139:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x23 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_183:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_274 {.originalLabel = "hZzxFEl3RmGxwG6iyjfJWg=="} [
    guard bvsle(extract(32, 0, R0_101:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_101:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_275 {.originalLabel = "hZzxFEl3RmGxwG6iyjfJWg=="} [
    guard bvsgt(extract(32, 0, R0_101:bv64), 0x0:bv32);
    var load25_1: bv32 := Stack_n12_n8:bv32 { .label = "3188_0_0" };
    var load26_1: bv32 := Stack_n8_n4:bv32 { .label = "3196_0_0" };
    goto(%phi_276, %phi_277);
  ];
  block %phi_276 [
    guard boolnot(eq(load25_1:bv32, 0x0:bv32));
    var ZF_94: bv1 := bvcomp(load26_1:bv32, 0x0:bv32) { .label = "3200_1" };
    goto(%phi_280, %phi_281);
  ];
  block %phi_277 [
    guard eq(load25_1:bv32, 0x0:bv32);
    var ZF_98: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%ssl3_connect_334);
  ];
  block %phi_280 [
    guard eq(load26_1:bv32, 0x0:bv32);
    var ZF_98: bv1 := ZF_94:bv1 { .label = "phiback" };
    goto(%ssl3_connect_334);
  ];
  block %phi_281 [
    guard boolnot(eq(load26_1:bv32, 0x0:bv32));
    var R21_146: bv64 := 0x11b0:bv64 { .label = "3208_0" };
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
      var ssl3_connect_539_loop_from_7: int := 0x15,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_287 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_146:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x1c { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_298 {.originalLabel = "+fU/1TdjS1WS5XAA5444iA=="} [
    guard bvsgt(extract(32, 0, R0_110:bv64), 0x0:bv32);
    goto(%ssl3_connect_loop0_294);
  ];
  block %phi_299 {.originalLabel = "+fU/1TdjS1WS5XAA5444iA=="} [
    guard bvsle(extract(32, 0, R0_110:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_110:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_304 {.originalLabel = "C3xumDu8QqSkWbCjofYTwg=="} [
    guard bvsle(extract(32, 0, R0_115:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_115:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_305 {.originalLabel = "C3xumDu8QqSkWbCjofYTwg=="} [
    guard bvsgt(extract(32, 0, R0_115:bv64), 0x0:bv32);
    var load58_1: bv32 := Stack_n28_n24:bv32 { .label = "3064_0_0" };
    goto(%phi_306, %phi_307);
  ];
  block %phi_306 [
    guard eq(load58_1:bv32, 0x1:bv32);
    var R21_160: bv64 := 0x1190:bv64 { .label = "3224_0" };
    goto(%phi_320, %phi_321);
  ];
  block %phi_307 [
    guard boolnot(eq(load58_1:bv32, 0x1:bv32));
    goto(%ssl3_connect_loop0_294);
  ];
  block %phi_312 {.originalLabel = "RdELhXcNS8OVRvsdVKc30A=="} [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_153:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_313 {.originalLabel = "RdELhXcNS8OVRvsdVKc30A=="} [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_314, %phi_315);
  ];
  block %phi_314 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_153:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x1d,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_315 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_153:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x1b { .label = "phiback" };
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
    var R21_163: bv64 := 0x1190:bv64 { .label = "3232_0" };
    goto(%phi_322, %phi_323);
  ];
  block %phi_322 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_163:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x20,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_323 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_163:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x21 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_331 {.originalLabel = "E6f2PD6hSA2NaHiSEaaXjw=="} [
    guard bvsle(extract(32, 0, R0_121:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_332 {.originalLabel = "E6f2PD6hSA2NaHiSEaaXjw=="} [
    guard bvsgt(extract(32, 0, R0_121:bv64), 0x0:bv32);
    goto(%ssl3_connect_loop0_212);
  ];
  block %phi_337 {.originalLabel = "iBs68DlhQzu1Qz5Y3aJz3g=="} [
    guard bvsle(extract(32, 0, R0_126:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_121:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_126:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_338 {.originalLabel = "iBs68DlhQzu1Qz5Y3aJz3g=="} [
    guard bvsgt(extract(32, 0, R0_126:bv64), 0x0:bv32);
    var load44_1: bv32 := Stack_n28_n24:bv32 { .label = "3028_0_0" };
    goto(%phi_339, %phi_340);
  ];
  block %phi_339 [
    guard eq(load44_1:bv32, 0x0:bv32);
    goto(%ssl3_connect_loop0_212);
  ];
  block %phi_340 [
    guard boolnot(eq(load44_1:bv32, 0x0:bv32));
    var R21_168: bv64 := 0x1170:bv64 { .label = "3036_0" };
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
      var ssl3_connect_539_loop_from_7: int := 0x4,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_344 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_168:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x18 { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_352 {.originalLabel = "+cV3c5mPQpKnuljiJRbdJA=="} [
    guard boolnot(eq(R0_24:bv32, 0x0:bv32));
    ( var R21_82: bv64 := R21_175:bv64,
      var R22_60: bv64 := R22_60:bv64,
      var R1_121: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop1_570);
  ];
  block %phi_353 {.originalLabel = "+cV3c5mPQpKnuljiJRbdJA=="} [
    guard eq(R0_24:bv32, 0x0:bv32);
    goto(%phi_354, %phi_355);
  ];
  block %phi_354 [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_175:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x6,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_355 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_175:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x1f { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_363 {.originalLabel = "PfQttZPWTxKxZ2Hn7OSETw=="} [
    guard eq(extract(32, 0, R22_60:bv64), 0x5:bv32);
    assert eq(R30_in:bv64, 0x704:bv64) { .comment = "R30 = R30_in" };
    var (R0_retval_inlined_6:bv64, R1_retval_inlined_7:bv64, R2_retval_inlined_8:bv64, R3_retval_inlined_9:bv64) := call @reach_error_2176 (bvadd(R31_in:bv64, 0xffffffffffffff80:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xffffffffffffff80:bv64)) { .label = "3360_2" };
    goto(%phi_363_retval_inline);
  ];
  block %phi_364 {.originalLabel = "PfQttZPWTxKxZ2Hn7OSETw=="} [
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
    var R21_182: bv64 := 0x1160:bv64 { .label = "2972_0" };
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
      var ssl3_connect_539_loop_from_7: int := 0xf,
      var R22_33: bv64 := R22_60:bv64,
      var R1_96: bv64 := R1_121:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_370 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_182:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0xd { .label = "phiback" };
    var R22_281: bv64 := R22_60:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_121:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_379 {.originalLabel = "BqRDgntJRo29Nex6N8k34w=="} [
    guard boolnot(eq(extract(32, 0, R22_60:bv64), 0x3:bv32));
    var R22_227: bv64 := zero_extend(32, extract(32, 0, R22_60:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_144);
  ];
  block %phi_380 {.originalLabel = "BqRDgntJRo29Nex6N8k34w=="} [
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
    var R21_189: bv64 := 0x1150:bv64 { .label = "2936_0" };
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
      var ssl3_connect_539_loop_from_7: int := 0x3,
      var R22_33: bv64 := R22_227:bv64,
      var R1_96: bv64 := R1_296:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_392 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_189:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0xb { .label = "phiback" };
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
    var load20_43: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_153: bv64 := zero_extend(32, $__VERIFIER_nondet_int());
    var R1_316: bv64 := 0x3:bv64 { .label = "2868_0" };
    goto(%phi_403, %phi_404);
  ];
  block %phi_403 {.originalLabel = "uW1+L5fJTS2acbEK4ks9Lg=="} [
    guard boolnot(eq(extract(32, 0, R22_60:bv64), 0x2:bv32));
    var R22_248: bv64 := zero_extend(32, extract(32, 0, R22_60:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_98);
  ];
  block %phi_404 {.originalLabel = "uW1+L5fJTS2acbEK4ks9Lg=="} [
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
  block %phi_419 {.originalLabel = "zyMlHottSxOX9z01wJ1d2Q=="} [
    guard boolnot(eq(extract(32, 0, R22_60:bv64), 0x1:bv32));
    var R22_262: bv64 := zero_extend(32, extract(32, 0, R22_60:bv64)) { .label = "phiback" };
    goto(%ssl3_connect_loop0_68);
  ];
  block %phi_420 {.originalLabel = "zyMlHottSxOX9z01wJ1d2Q=="} [
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
    var R21_218: bv64 := 0x1130:bv64 { .label = "2896_0" };
    goto(%phi_437, %phi_438);
  ];
  block %phi_428 [
    guard boolnot(eq(R0_8:bv32, 0x0:bv32));
    var R21_211: bv64 := 0x11d0:bv64 { .label = "2824_0" };
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
      var ssl3_connect_539_loop_from_7: int := 0x22,
      var R22_33: bv64 := R22_262:bv64,
      var R1_96: bv64 := R1_328:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_432 [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_211:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0x10 { .label = "phiback" };
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
  block %phi_443 {.originalLabel = "w9lKWeJuQsKW9DWhEvp6xQ=="} [
    guard eq(R0_12:bv32, 0x0:bv32);
    ( var R21_68: bv64 := R21_222:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x19,
      var R22_33: bv64 := R22_276:bv64,
      var R1_96: bv64 := R1_347:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_444 {.originalLabel = "w9lKWeJuQsKW9DWhEvp6xQ=="} [
    guard boolnot(eq(R0_12:bv32, 0x0:bv32));
    var R21_227: bv64 := R21_222:bv64 { .label = "phiback" };
    var ssl3_connect_539_loop_from_57: int := 0xa { .label = "phiback" };
    var R22_281: bv64 := R22_276:bv64 { .label = "phiback" };
    var R1_352: bv64 := R1_347:bv64 { .label = "phiback" };
    goto(%ssl3_connect_loop0_30);
  ];
  block %phi_466 {.originalLabel = "oJvRGz2XSIea3yZ1rTxV/g=="} [
    guard bvsgt(extract(32, 0, R0_172:bv64), 0x0:bv32);
    ( var R21_68: bv64 := R21_227:bv64,
      var ssl3_connect_539_loop_from_7: int := 0x14,
      var R22_33: bv64 := R22_281:bv64,
      var R1_96: bv64 := R1_352:bv64 );
    goto(%ssl3_connect_loop2_618);
  ];
  block %phi_467 {.originalLabel = "oJvRGz2XSIea3yZ1rTxV/g=="} [
    guard bvsle(extract(32, 0, R0_172:bv64), 0x0:bv32);
    var R1_360: bv64 := R1_352:bv64 { .label = "phiback" };
    var R0_179: bv64 := R0_172:bv64 { .label = "phiback" };
    goto(%ssl3_connect_10);
  ];
  block %phi_363_retval_inline [
    var R31_369: bv64 := bvadd(R31_in:bv64, 0xffffffffffffff80:bv64) { .label = "phiback" };
    var R1_367: bv64 := 0xd58:bv64 { .label = "phiback" };
    var R0_183: bv64 := 0xd70:bv64 { .label = "phiback" };
    var R3_367: bv64 := 0xd48:bv64 { .label = "phiback" };
    var R2_367: bv64 := 0x3:bv64 { .label = "phiback" };
    goto(%ssl3_connect_return);
  ];
  block %ssl3_connect_return [
    assert eq(R31_in:bv64, R31_369:bv64) { .comment = "R31 preserved across calls" };
    return (R0_183:bv64, R1_367:bv64, R2_367:bv64, R3_367:bv64);
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
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2W4tEFaKnfO6ZwWr7II1e91vGutM4QBrMJwoiQAAAA=" ]
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
      "H4sIAAAAAAAA/41UXWwUVRQ+s7PlH6Q/wwr+7C4SYxpjjN7B4AuziNkXiYEdJQaUpVUhLrWZrLix89BdX3xQEhaa6CPEB10M";
      "DwZMHE1ka3gw4hMtjSYkbAmFikC3Tpd22g7H7+5MTaOR+HDyfXPvd+655+eOb5+r+CqVDxINEBV3+fbgl1V130g8oV76v/YI";
      "FS8+ChtT6dSoanhXH6PydZxZI6rTrbSnYi8KG2T+9BdYc3087RlEZ88zx+4XjxQ6SqSUFWASuJXojyqROYozkrW0tx9n1FXl";
      "FEXiI/Kcf+qTRBc2zvcPpVaVPk7Op44PQn8Vvtvqaa+r6Rv529e3f2jWwl1JXjv8s5HUFkOh55r3vZb2itA3z3/Y8I4hj99g";
      "CdQsG1G2uCsNz7d//FftLiO/+9XOR/1VoqMKTMYmYHdCLyezepmqerkL53+EOL79bXC3jFJp7IlUprvVipeLVubyLRUb+32w";
      "D2CaYewsAN+HHYZNq9SZB6IJnRZwCtgLfBfWAzsEy8HekX3pJeegxAPkvA18C+ZC3w3sgs2AZ4H7pCZHzuvAvbA9sLvYew04";
      "B9wNnAW+ApwHZqS+QM5OiTY5L0vMk7MD+E1kmZVaQaaznES/Stb2h4y+6nIy1yFvbeOHuzJE+sBS0gn8XIRytRYy12+SfH2u";
      "CB09HqxXcQY9EXBjFXhnyFeDPxn6rgF/KuAn5PrToeYB8GcCnlgLLgKebQPfHPpKzfNhrHbwRMCTMTJrOcOJE1k9Gng+4KdV";
      "MjMdJBr9hiNrNYw5aEW+r7aQuNJG1knkN9JW2iC1tzHPGnLKeKwPz7BYCp1cPzTDpptJod/b0O8X0O/t6PeLFd/+qTln/r1A";
      "d36D0Ze8G2jxhtv+Sz8J/ZUlZKUWxV7ts1mIkNCQW76B+FMsarjrZmgw3zENNY2rUas0xeao9F9B1v7F/nNsnnFZ73BZXJR6";
      "9OMMs/gM/JLUryGrtEh/xGPz8iwLDf1xJ1k3J1nIf8DPUruOrCJ6J3U7kLuGvg3VWRd1Ft9DMxjm2zONPfTOnYD/BIuz2Psu";
      "3DuCOtQOGA7hDhp6PXQH/ndYfAXN1wv+jUATj5JVjaL26Pfx26xP3WJxErovQt1LzOYJfH8efp92UYNe9FNVOpMd1DqK91KI";
      "kti6jCxagpnYRK2Hkat8R41+ctybuN9NFp/gjGML95tE7EIwIzXbcKIPGn3Gn8gHc5b/HfUfZ1GUdcQ8uuOsSxRYwxuPlRbu";
      "P4GezbIuYw3dQH43WOCNx+R81hBXw2y2Y/296yzwxmNyJuUMylkcHmOBNx6T3B3D/fD9Jr6z8t6h77NYH7jG4g2s/3ov+MdJ";
      "/hckJ5lELAYAAA=="
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
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML/YOD45J68k3kjPKUwvWS85M0fXUC+ZgcGAAQDfi2W9MgAAAA=="
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
      "55rBOZNjFvtstjmsTLVc9+7evnPz1vUbV69dvsLH4MjtjSHCIAM05gcQu/z4/18CyS6Xe3f5oM5hAADrAhX5GAEAAA=="
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
