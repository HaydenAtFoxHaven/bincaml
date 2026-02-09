var $Global_131088_131096: bv64;
var $Global_131112_131120: bv64;
var $Global_131120_131128: bv64;
declare-fun $__VERIFIER_nondet_uint : () -> bv32;
declare-fun $__VERIFIER_nondet_char : () -> bv8;

prog entry @main_1856;

proc @main_1856
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R19_in:bv64, R1_in:bv64, R20_in:bv64, R21_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R1_out:bv64, R29_out:bv64, R3_out:bv64)
  { .name = "main"; .address = 0x740; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x740; .originalLabel = "8DiIOGkdRHK25jXpzv7MXg=="} [
    var Stack_n48_n40: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n40_n32: bv64 := R30_in:bv64 { .label = "1856_2" };
    var Stack_n32_n24: bv64 := R19_in:bv64 { .label = "1864_1" };
    var Stack_n24_n16: bv64 := R20_in:bv64 { .label = "1864_2" };
    var Stack_n16_n8: bv64 := R21_in:bv64 { .label = "1868_0" };
    var load25_1: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv32 := $__VERIFIER_nondet_uint();
    var R19_2: bv64 := zero_extend(32, R0_2:bv32) { .label = "1876_0" };
    var load5_1: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv64 := zero_extend(56, $__VERIFIER_nondet_char());
    var R21_2: bv64 := zero_extend(32, extract(32, 0, R0_4:bv64)) { .label = "1884_0" };
    var load25_2: bv64 := $Global_131120_131128:bv64 { .label = "1812_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_6: bv32 := $__VERIFIER_nondet_uint();
    var R20_2: bv64 := zero_extend(32, R0_6:bv32) { .label = "1892_0" };
    var load5_2: bv64 := $Global_131088_131096:bv64 { .label = "1748_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_8: bv64 := zero_extend(56, $__VERIFIER_nondet_char());
    var R3_2: bv64 := zero_extend(32, extract(32, 0, R0_8:bv64)) { .label = "1900_0" };
    goto(%phi_15, %phi_16);
  ];
  block %main_4 {.address = 0x798; .originalLabel = "jaCZm4kpSLuQuRZ7QEDseg=="} [
    var load17_1: bv64 := Stack_n16_n8:bv64 { .label = "1944_0_0" };
    var load18_1: bv64 := Stack_n32_n24:bv64 { .label = "1952_1_0" };
    var load19_1: bv64 := Stack_n24_n16:bv64 { .label = "1952_2_0" };
    var load20_1: bv64 := Stack_n48_n40:bv64 { .label = "1956_0_0" };
    var load21_1: bv64 := Stack_n40_n32:bv64 { .label = "1956_1_0" };
    var R29_30: bv64 := load20_1:bv64 { .label = "phiback" };
    var R31_32: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_32: bv64 := 0x20010:bv64 { .label = "phiback" };
    var R1_18: bv64 := R1_16:bv64 { .label = "phiback" };
    var R3_25: bv64 := R3_23:bv64 { .label = "phiback" };
    var R17_28: bv64 := load5_2:bv64 { .label = "phiback" };
    var R0_25: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_17: bv64 := load21_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_12 {.address = 0x7ac; .originalLabel = "BZ0rplKqQvOT6+EDb4iCgw=="} [
    var (R0_18:bv64, R1_10:bv64, R2_25:bv64, R3_17:bv64, R4_23:bv64) := call @mulflt_2736 (zero_extend(32, extract(32, 0, R19_14:bv64)), 0x0:bv64, R3_2:bv64, R4_in:bv64);
    goto(%phi_31, %phi_32);
  ];
  block %main_26 {.address = 0x784; .originalLabel = "Jlpt/Ta1SRyL6Y9F0r5UpA=="} [
    goto(%phi_22, %phi_23);
  ];
  block %phi_15 {.originalLabel = "e3kKD8U0RiyuKEepk/wxzg=="} [
    guard eq(extract(32, 0, R19_2:bv64), 0x0:bv32);
    var R19_14: bv64 := R19_2:bv64 { .label = "phiback" };
    var R2_16: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%main_26);
  ];
  block %phi_16 {.originalLabel = "e3kKD8U0RiyuKEepk/wxzg=="} [
    guard boolnot(eq(extract(32, 0, R19_2:bv64), 0x0:bv32));
    var (R0_11:bv64, R1_3:bv64, R2_12:bv64) := call @base2flt.part.0_2304 (zero_extend(32, extract(32, 0, R19_2:bv64)), zero_extend(32, sign_extend(24, extract(8, 0, R21_2:bv64))));
    goto(%phi_16_retval_inline);
  ];
  block %phi_22 {.originalLabel = "Jlpt/Ta1SRyL6Y9F0r5UpA=="} [
    guard eq(extract(32, 0, R20_2:bv64), 0x0:bv32);
    var R2_24: bv64 := R2_16:bv64 { .label = "phiback" };
    goto(%main_12);
  ];
  block %phi_23 {.originalLabel = "Jlpt/Ta1SRyL6Y9F0r5UpA=="} [
    guard boolnot(eq(extract(32, 0, R20_2:bv64), 0x0:bv32));
    var (R0_14:bv64, R1_5:bv64, R2_19:bv64) := call @base2flt.part.0_2304 (zero_extend(32, extract(32, 0, R20_2:bv64)), zero_extend(32, sign_extend(24, extract(8, 0, R3_2:bv64))));
    goto(%phi_24, %phi_25);
  ];
  block %phi_24 [
    guard eq(extract(32, 0, R0_14:bv64), 0x0:bv32);
    var R2_24: bv64 := R2_19:bv64 { .label = "phiback" };
    goto(%main_12);
  ];
  block %phi_25 [
    guard boolnot(eq(extract(32, 0, R0_14:bv64), 0x0:bv32));
    var R1_16: bv64 := R1_5:bv64 { .label = "phiback" };
    var R3_23: bv64 := R3_2:bv64 { .label = "phiback" };
    goto(%main_4);
  ];
  block %phi_31 {.originalLabel = "BZ0rplKqQvOT6+EDb4iCgw=="} [
    guard eq(extract(32, 0, R0_18:bv64), 0x0:bv32);
    var R1_16: bv64 := R1_10:bv64 { .label = "phiback" };
    var R3_23: bv64 := R3_17:bv64 { .label = "phiback" };
    goto(%main_4);
  ];
  block %phi_32 {.originalLabel = "BZ0rplKqQvOT6+EDb4iCgw=="} [
    guard boolnot(eq(extract(32, 0, R0_18:bv64), 0x0:bv32));
    var (R0_retval_inlined_6:bv64, R17_23:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_2408 (bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64), 0x744:bv64, bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64)) { .label = "1980_2" };
    goto(%phi_32_retval_inline);
  ];
  block %phi_32_retval_inline [
    var R29_30: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffc0:bv64) { .label = "phiback" };
    var R31_32: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64) { .label = "phiback" };
    var R16_32: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R1_18: bv64 := 0xb60:bv64 { .label = "phiback" };
    var R3_25: bv64 := 0xb50:bv64 { .label = "phiback" };
    var R17_28: bv64 := R17_23:bv64 { .label = "phiback" };
    var R0_25: bv64 := 0xb78:bv64 { .label = "phiback" };
    var R30_17: bv64 := 0x744:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_16_retval_inline [
    var R19_14: bv64 := zero_extend(32, extract(32, 0, R0_11:bv64)) { .label = "phiback" };
    var R2_16: bv64 := R2_12:bv64 { .label = "phiback" };
    goto(%main_26);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_17:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_32:bv64) { .comment = "R31 preserved across calls" };
    return (R0_25:bv64, R16_32:bv64, R17_28:bv64, R1_18:bv64, R29_30:bv64, R3_25:bv64);
  ]
];


proc @mulflt_2736
  (R0_in:bv64, R1_in:bv64, R3_in:bv64, R4_in:bv64)
    -> (R0_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64, R4_out:bv64)
  { .name = "mulflt"; .address = 0xab0; .returnBlock = "mulflt_return" }
[
  block %mulflt_entry {.address = 0xab0; .originalLabel = "WC0T7IkERCi0rbwM7c18eA=="} [
    goto(%phi_3, %phi_4);
  ];
  block %mulflt_4 {.address = 0xb28; .originalLabel = "B5nDXmKiSEWbdvZsSvNNag=="} [
    goto(%phi_38);
  ];
  block %mulflt_12 {.address = 0xb1c; .originalLabel = "BdDJ/3omTBmLlwyEX3AAlg=="} [
    var R3_28: bv64 := zero_extend(32, bvadd(extract(32, 0, R3_27:bv64), 0x80:bv32)) { .label = "2844_0" };
    var R0_29: bv32 := bvand(extract(32, 0, R0_28:bv64), 0xfeffffff:bv32) { .label = "2848_0" };
    var R0_30: bv64 := zero_extend(32, bvor(R0_29:bv32, bvshl(zero_extend(24, extract(8, 0, R3_28:bv64)), 0x18:bv32))) { .label = "2852_0" };
    var R1_33: bv64 := 0x1ffffff:bv64 { .label = "phiback" };
    var R4_32: bv64 := R4_15:bv64 { .label = "phiback" };
    var R0_35: bv64 := R0_30:bv64 { .label = "phiback" };
    var R3_33: bv64 := R3_28:bv64 { .label = "phiback" };
    var R2_33: bv64 := R2_20:bv64 { .label = "phiback" };
    goto(%mulflt_4);
  ];
  block %mulflt_40 [
    var R0_9: bv64 := 0x0:bv64 { .label = "2748_0" };
    goto(%phi_15, %phi_16);
  ];
  block %mulflt_46 [
    goto(%phi_9, %phi_10);
  ];
  block %phi_3 {.originalLabel = "WC0T7IkERCi0rbwM7c18eA=="} [
    guard bvult(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R2_6: bv64 := zero_extend(32, extract(32, 0, R1_in:bv64)) { .label = "phiback" };
    goto(%mulflt_46);
  ];
  block %phi_4 {.originalLabel = "WC0T7IkERCi0rbwM7c18eA=="} [
    guard bvuge(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R2_6: bv64 := zero_extend(32, extract(32, 0, R0_in:bv64)) { .label = "phiback" };
    goto(%mulflt_46);
  ];
  block %phi_9 [
    guard bvult(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R1_13: bv64 := zero_extend(32, extract(32, 0, R0_in:bv64)) { .label = "phiback" };
    goto(%mulflt_40);
  ];
  block %phi_10 [
    guard bvuge(extract(32, 0, R0_in:bv64), extract(32, 0, R1_in:bv64));
    var R1_13: bv64 := zero_extend(32, extract(32, 0, R1_in:bv64)) { .label = "phiback" };
    goto(%mulflt_40);
  ];
  block %phi_15 [
    guard eq(extract(32, 0, R1_13:bv64), 0x0:bv32);
    var R1_33: bv64 := R1_13:bv64 { .label = "phiback" };
    var R4_32: bv64 := R4_in:bv64 { .label = "phiback" };
    var R0_35: bv64 := R0_9:bv64 { .label = "phiback" };
    var R3_33: bv64 := R3_in:bv64 { .label = "phiback" };
    var R2_33: bv64 := R2_6:bv64 { .label = "phiback" };
    goto(%mulflt_4);
  ];
  block %phi_16 [
    guard boolnot(eq(extract(32, 0, R1_13:bv64), 0x0:bv32));
    var R4_15: bv64 := zero_extend(32, bvadd(zero_extend(24, extract(32, 24, R1_13:bv64)), zero_extend(24, extract(32, 24, R2_6:bv64)))) { .label = "2764_0" };
    var R3_14: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_15:bv64), 0xffffff18:bv32)) { .label = "2768_0" };
    goto(%phi_17, %phi_18);
  ];
  block %phi_17 [
    guard bvsgt(extract(32, 0, R3_14:bv64), 0x7f:bv32);
    var R1_33: bv64 := R1_13:bv64 { .label = "phiback" };
    var R4_32: bv64 := R4_15:bv64 { .label = "phiback" };
    var R0_35: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    var R3_33: bv64 := R3_14:bv64 { .label = "phiback" };
    var R2_33: bv64 := R2_6:bv64 { .label = "phiback" };
    goto(%mulflt_4);
  ];
  block %phi_18 [
    guard bvsle(extract(32, 0, R3_14:bv64), 0x7f:bv32);
    goto(%phi_19, %phi_20);
  ];
  block %phi_19 [
    guard bvslt(extract(32, 0, R3_14:bv64), 0xffffff80:bv32);
    var R1_33: bv64 := R1_13:bv64 { .label = "phiback" };
    var R4_32: bv64 := R4_15:bv64 { .label = "phiback" };
    var R0_35: bv64 := 0x0:bv64 { .label = "phiback" };
    var R3_33: bv64 := R3_14:bv64 { .label = "phiback" };
    var R2_33: bv64 := R2_6:bv64 { .label = "phiback" };
    goto(%mulflt_4);
  ];
  block %phi_20 [
    guard bvsge(extract(32, 0, R3_14:bv64), 0xffffff80:bv32);
    var R0_19: bv32 := bvor(zero_extend(8, extract(24, 0, R1_13:bv64)), 0x1000000:bv32) { .label = "2800_0" };
    var R2_19: bv32 := bvor(zero_extend(8, extract(24, 0, R2_6:bv64)), 0x1000000:bv32) { .label = "2804_0" };
    var R2_20: bv64 := bvmul(zero_extend(32, R2_19:bv32), zero_extend(32, R0_19:bv32)) { .label = "2812_0" };
    var R0_20: bv64 := zero_extend(24, extract(64, 24, R2_20:bv64)) { .label = "2816_0" };
    goto(%phi_21, %phi_22);
  ];
  block %phi_21 [
    guard bvule(R0_20:bv64, 0x1ffffff:bv64);
    var R0_28: bv64 := R0_20:bv64 { .label = "phiback" };
    var R3_27: bv64 := R3_14:bv64 { .label = "phiback" };
    goto(%mulflt_12);
  ];
  block %phi_22 [
    guard bvugt(R0_20:bv64, 0x1ffffff:bv64);
    goto(%phi_23, %phi_24);
  ];
  block %phi_23 [
    guard eq(extract(32, 0, R3_14:bv64), 0x7f:bv32);
    var R1_35: bv64 := 0x1ffffff:bv64 { .label = "phiback" };
    var R4_34: bv64 := R4_15:bv64 { .label = "phiback" };
    var R0_37: bv64 := 0xffffffff:bv64 { .label = "phiback" };
    var R3_35: bv64 := R3_14:bv64 { .label = "phiback" };
    var R2_35: bv64 := R2_20:bv64 { .label = "phiback" };
    goto(%mulflt_return);
  ];
  block %phi_24 [
    guard boolnot(eq(extract(32, 0, R3_14:bv64), 0x7f:bv32));
    var R3_23: bv64 := zero_extend(32, bvadd(extract(32, 0, R4_15:bv64), 0xffffff19:bv32)) { .label = "2836_0" };
    var R0_28: bv64 := zero_extend(25, extract(64, 25, R2_20:bv64)) { .label = "phiback" };
    var R3_27: bv64 := R3_23:bv64 { .label = "phiback" };
    goto(%mulflt_12);
  ];
  block %phi_38 {.originalLabel = "B5nDXmKiSEWbdvZsSvNNag=="} [
    var R1_35: bv64 := R1_33:bv64 { .label = "phiback" };
    var R4_34: bv64 := R4_32:bv64 { .label = "phiback" };
    var R0_37: bv64 := R0_35:bv64 { .label = "phiback" };
    var R3_35: bv64 := R3_33:bv64 { .label = "phiback" };
    var R2_35: bv64 := R2_33:bv64 { .label = "phiback" };
    goto(%mulflt_return);
  ];
  block %mulflt_return [
    return (R0_37:bv64, R1_35:bv64, R2_35:bv64, R3_35:bv64, R4_34:bv64);
  ]
];


proc @base2flt.part.0_2304 (R0_in:bv64, R1_in:bv64) -> (R0_out:bv64, R1_out:bv64, R2_out:bv64)
  { .name = "base2flt.part.0"; .address = 0x900; .returnBlock = "base2flt.part.0_return" }
[
  block %base2flt.part.0_entry {.address = 0x900; .originalLabel = "e6cZhlpWThm6raFxzKAAzQ=="} [
    goto(%phi_3, %phi_4);
  ];
  block %base2flt.part.0_4 {.address = 0x918; .originalLabel = "y2t5BkZuSeO4BIrkO2eAnA=="} [
    var R1_24: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_23:bv64), 0x80:bv32)) { .label = "2328_0" };
    var R0_26: bv32 := bvand(extract(32, 0, R0_25:bv64), 0xfeffffff:bv32) { .label = "2332_0" };
    var R0_27: bv64 := zero_extend(32, bvor(R0_26:bv32, bvshl(zero_extend(24, extract(8, 0, R1_24:bv64)), 0x18:bv32))) { .label = "2336_0" };
    var R1_26: bv64 := R1_24:bv64 { .label = "phiback" };
    var R0_29: bv64 := R0_27:bv64 { .label = "phiback" };
    var R2_25: bv64 := R2_23:bv64 { .label = "phiback" };
    goto(%base2flt.part.0_return);
  ];
  block %base2flt.part.0_loop1_18 {.address = 0x938; .originalLabel = "eXhQE2weTyK4yqKXjjKyAw=="} [
    goto(%phi_17, %phi_18);
  ];
  block %base2flt.part.0_loop2_34 {.address = 0x958; .originalLabel = "VIOU+mziRWKjJu3dvJ7Mug=="} [
    goto(%phi_9, %phi_10);
  ];
  block %phi_3 {.originalLabel = "e6cZhlpWThm6raFxzKAAzQ=="} [
    guard bvule(extract(32, 0, R0_in:bv64), 0xffffff:bv32);
    ( var R1_15: bv64 := R1_in:bv64,
      var R0_16: bv64 := R0_in:bv64 );
    goto(%base2flt.part.0_loop1_18);
  ];
  block %phi_4 {.originalLabel = "e6cZhlpWThm6raFxzKAAzQ=="} [
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
  block %phi_9 {.originalLabel = "VIOU+mziRWKjJu3dvJ7Mug=="} [
    guard bvsle(extract(32, 0, R1_7:bv64), 0x7e:bv32);
    var R0_12: bv64 := zero_extend(33, extract(32, 1, R0_7:bv64)) { .label = "2376_0" };
    var R1_11: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_7:bv64), 0x1:bv32)) { .label = "2380_0" };
    goto(%phi_12, %phi_13);
  ];
  block %phi_10 {.originalLabel = "VIOU+mziRWKjJu3dvJ7Mug=="} [
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
  block %phi_17 {.originalLabel = "eXhQE2weTyK4yqKXjjKyAw=="} [
    guard bvsge(extract(32, 0, R1_15:bv64), 0xffffff81:bv32);
    var R0_21: bv64 := zero_extend(32, bvshl(zero_extend(1, extract(31, 0, R0_16:bv64)), 0x1:bv32)) { .label = "2344_0" };
    var R1_19: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_15:bv64), 0xffffffff:bv32)) { .label = "2348_0" };
    goto(%phi_20, %phi_21);
  ];
  block %phi_18 {.originalLabel = "eXhQE2weTyK4yqKXjjKyAw=="} [
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


proc @reach_error_2408
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x968; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x968; .originalLabel = "Z7KQ6I1HT7+NtdNsYqau8Q=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2408_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2408_2" };
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 = R30_in" };
    var load16_1: bv64 := $Global_131112_131120:bv64 { .label = "1796_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x768:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0xb78:bv64, load16_1:bv64, 0xb60:bv64, 0x3:bv64, 0xb50:bv64);
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
      { .name = "_IO_stdin_used"; .address = 0xb48; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xd20; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xd24; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20048; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x990; .size = 0xa0 };
      { .name = "_start"; .address = 0x7c0; .size = 0x1a0 };
      { .name = "addflt"; .address = 0xa20; .size = 0x480 };
      { .name = "base2flt"; .address = 0x9a4; .size = 0x380 };
      { .name = "main"; .address = 0x740; .size = 0x400 };
      { .name = "mulflt"; .address = 0xab0; .size = 0x420 };
      { .name = "reach_error"; .address = 0x968; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x8e0 ]; [ 0x1fdc0; 0x88c ]; [ 0x1ffd8; 0x740 ]; [ 0x20040; 0x20040 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2XIDJhz6/au+Q+WRT5VfBBhvc1ab1EBALQoKmEkAAAA" ]
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
      "H4sIAAAAAAAA/9vxl5EBBJhZwBTDAw4IfQBNvAcqfuM/qrgDO5RmYEIVh/IPQNUzAsWhUmBwAkmcFUn8ApI4O5L4AyRxTiRx";
      "AKHovbvAAAAA"
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
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBNjGBim/K0+uOIAc/w1ACl0odAYAAAA" ]
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
    .size = 0x3f4;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3VSPWhTURg9992Ahbg0KShFm7y0g00ptCUonfryEDI4xWRQqDRtN4NDt0ICTW0HRYcGBQeFtlvTRdQOLtrU";
      "LgU3iwVF5LX+ILRDMBZ88NLnuS+kpkGHj/Ped77vu+d899Zyr0o1iWI1JUqHQdgV131UlYh+Jh4SD4i/iB+JX4gvgJglg9Hl";
      "LgTHgYeqNi0QGz+HoCU7oqPMlVlzGDRsoHC1moqXarnNlbIc21F9grl11sB1Y1liKCzfn0fhXRfjm8TqrjTsvW4Uv1OTBVRw";
      "kLAlOR/jGTWUGV7+R8I2gLWXrntGzVZz/hUQWEBYFAVRJ44A+9SX3uUM3UrY9LBWkWIVWmhHzWmt14G3EWdmO3569p7uxB9s";
      "sH6PvWYlYU94vdpxby33ur5LP+wg+zOR+LAhcMnT+zVhF1hfn2/Yt+njAyPMfWQiYrjqN+xa7s1Kq5dP9Pc/byo0az0Qgpa9";
      "K5DWyvXvCxrSOrR2TJ8KICOinq/pUEr3IenxrpseccTgTaK6I4/PC8W3K773iPxvMXWrzgfq3tZLElgQDOURxEmjv6gX+ouw";
      "+osTnHODfngnsUa9qvup7ovvo6GzV/urc4v30A50NJ9doo/Ws5u1r7CnVXur1xM7gshGBgqdYmC205JadEND7HL+bKqbsQiZ";
      "7ZPc1SgCc5BXdLQN6T2bncvUazJn8t+E8Jti6+KiI6fUu5mnTpN6FW9kfPXdNnTS1xiQvcO6Zr6xi6fcRbMepT8uEeuhFjVj";
      "PmP655ZkcsYRU/e5J8XPQBvs43dY6WHA09Q2tDtpPDfzS48N59o2Z+6XeKbq41tLzz2RScO5vj15vBd5Qucfk64hxvQDAAA="
    ]
  };
  {
    .name = ".fini";
    .address = 0xb34;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0xb48;
    .size = 0x32;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML84P60kPi0nP7Ek3lQvWS85M0cvGSRuwAAANHPCOjIAAAA="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xb7c;
    .size = 0x6c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrbOYGBg4AHiI7///69gZGBw+fP/fwOQvwRITwHSV4D0CiAt8Pf//z1AOgVIPwDSLUD6C5B+A6Q5gPpE";
      "/v3/rwCkNYC0BZBeAqR9gLTJ////U4A0AIbDjc1sAAAA"
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xbe8;
    .size = 0x13c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiPf8/v/fBCTpyC4HEtMBYo4///8bQPWAxByAWAUoZgMVUwDiECD2AYp5";
      "gPXyKcxlmcfsNJnJ797dy3wwfRVAXANUw4JkVg8QdwDFMqBiIkC8AIjvAMU0IGYJzGWaxwgS3wHEb4DiIDaDM0QcZMYFIH4B";
      "FC9AMuMJEAf8/f9/AkggCaH2DxCfAIq3QNWC7BBgZGBw+fX/fwPEPoO5bPNYnSezTGGeyhTGde/u1ctX+BgcuSHqAY/ypu48";
      "AQAA"
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xd24;
    .size = 0x20;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAGJGIHb3C2UAAWYgZmeAAAA9kbzyIAAAAA==" ]
  };
  {
    .name = ".init_array";
    .address = 0x1fdb8;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/3vAwQAGAG+0HdUIAAAA" ]
  };
  {
    .name = ".fini_array";
    .address = 0x1fdc0;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/+vhYAADAJsBWVIIAAAA" ]
  };
  {
    .name = ".dynamic";
    .address = 0x1fdc8;
    .size = 0x1f0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/7WQqw7CQBBFp9DlTYKgoTw+g//C8kngkMhKJBJZiaxBNE27hNyzYusZc3Ln7s6d3cRUV5jAO1zA80hcoo9z";
      "cRvOt7q5R0/gDhb4h57/6fzpx9tA2tGvhiKx9sSfoV+QNSyHmcXFGHt75TPGLnANx3AT8lzcX7l47wJOe/mN13vC0Q5dpmp6";
      "dPjnCv3Ar9Gp/ae+fqka/vABAAA="
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
