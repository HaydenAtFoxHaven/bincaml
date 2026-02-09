var $Global_131088_131096: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_char : () -> bv8;

prog entry @main_1792;

proc @main_1792
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R19_in:bv64, R1_in:bv64, R20_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R29_out:bv64, R2_out:bv64)
  { .name = "main"; .address = 0x700; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x700; .originalLabel = "WmA53UkzRvyBfEpTSyGiyQ=="} [
    var Stack_n32_n24: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n24_n16: bv64 := R30_in:bv64 { .label = "1792_2" };
    var Stack_n16_n8: bv64 := R19_in:bv64 { .label = "1800_1" };
    var Stack_n8_0: bv64 := R20_in:bv64 { .label = "1800_2" };
    var load1_1: bv64 := $Global_131088_131096:bv64 { .label = "1684_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv8 := $__VERIFIER_nondet_char();
    var R19_2: bv32 := sign_extend(24, R0_2:bv8) { .label = "1808_0" };
    var load1_2: bv64 := $Global_131088_131096:bv64 { .label = "1684_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv8 := $__VERIFIER_nondet_char();
    var R2_3: bv64 := zero_extend(32, bvneg(zero_extend(24, R0_4:bv8))) { .label = "1832_0" };
    var R20_6: bv32 := sign_extend(24, extract(8, 0, bvneg(zero_extend(24, R0_2:bv8)))) { .label = "1836_0" };
    var R0_6: bv64 := zero_extend(32, sign_extend(24, R0_4:bv8)) { .label = "1840_0" };
    goto(%phi_9, %phi_10);
  ];
  block %main_8 {.address = 0x768; .originalLabel = "O4vSUJd+Rw66ygkhoqBM9A=="} [
    var load13_1: bv64 := Stack_n16_n8:bv64 { .label = "1896_1_0" };
    var load14_1: bv64 := Stack_n8_0:bv64 { .label = "1896_2_0" };
    var load15_1: bv64 := Stack_n32_n24:bv64 { .label = "1904_0_0" };
    var load16_1: bv64 := Stack_n24_n16:bv64 { .label = "1904_1_0" };
    var R29_37: bv64 := load15_1:bv64 { .label = "phiback" };
    var R31_40: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_40: bv64 := 0x20010:bv64 { .label = "phiback" };
    var R2_40: bv64 := R2_35:bv64 { .label = "phiback" };
    var R17_38: bv64 := load1_2:bv64 { .label = "phiback" };
    var R0_37: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_10: bv64 := load16_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_10 [
    guard eq(NF_13:bv1, VF_13:bv1);
    var R2_35: bv64 := R2_24:bv64 { .label = "phiback" };
    goto(%main_8);
  ];
  block %main_loop0_20 [
    var R1_24: bv64 := zero_extend(32, bvsub(extract(32, 0, R19_18:bv64), extract(32, 0, bvmul(zero_extend(32, extract(32, 0, R1_23:bv64)), zero_extend(32, extract(32, 0, R2_18:bv64)))))) { .label = "1868_0" };
    var R19_24: bv64 := zero_extend(32, extract(32, 0, R2_18:bv64)) { .label = "1872_0" };
    var R2_24: bv64 := zero_extend(32, sign_extend(24, extract(8, 0, R1_24:bv64))) { .label = "1876_0" };
    goto(%phi_30, %phi_31);
  ];
  block %main_loop1_26 {.address = 0x748; .originalLabel = "JkuFi95tS5qvok8Hc9vxrg=="} [
    goto(%phi_24, %phi_25);
  ];
  block %main_40 [
    var R2_9: bv64 := zero_extend(32, sign_extend(24, extract(8, 0, R2_3:bv64))) { .label = "1848_0" };
    goto(%phi_15, %phi_16);
  ];
  block %phi_9 {.originalLabel = "zR10aGOCRfuxvkNaU8YmrA=="} [
    guard bvslt(R19_2:bv32, 0x0:bv32);
    var R19_11: bv64 := zero_extend(32, R20_6:bv32) { .label = "phiback" };
    goto(%main_40);
  ];
  block %phi_10 {.originalLabel = "zR10aGOCRfuxvkNaU8YmrA=="} [
    guard bvsge(R19_2:bv32, 0x0:bv32);
    var R19_11: bv64 := zero_extend(32, R19_2:bv32) { .label = "phiback" };
    goto(%main_40);
  ];
  block %phi_15 [
    guard bvslt(extract(32, 0, R0_6:bv64), 0x0:bv32);
    var R1_17: bv64 := R1_in:bv64 { .label = "phiback" };
    var R19_18: bv64 := R19_11:bv64 { .label = "phiback" };
    var R2_18: bv64 := R2_9:bv64 { .label = "phiback" };
    goto(%main_loop1_26);
  ];
  block %phi_16 [
    guard bvsge(extract(32, 0, R0_6:bv64), 0x0:bv32);
    goto(%phi_17, %phi_18);
  ];
  block %phi_17 [
    guard eq(extract(32, 0, R0_6:bv64), 0x0:bv32);
    var R2_35: bv64 := R2_9:bv64 { .label = "phiback" };
    goto(%main_8);
  ];
  block %phi_18 [
    guard boolnot(eq(extract(32, 0, R0_6:bv64), 0x0:bv32));
    var R1_17: bv64 := R1_in:bv64 { .label = "phiback" };
    var R19_18: bv64 := R19_11:bv64 { .label = "phiback" };
    var R2_18: bv64 := zero_extend(32, extract(32, 0, R0_6:bv64)) { .label = "phiback" };
    goto(%main_loop1_26);
  ];
  block %phi_24 {.originalLabel = "JkuFi95tS5qvok8Hc9vxrg=="} [
    guard eq(extract(32, 0, R2_18:bv64), 0x0:bv32);
    var R1_23: bv64 := 0x0:bv64 { .label = "phiback" };
    goto(%main_loop0_20);
  ];
  block %phi_25 {.originalLabel = "JkuFi95tS5qvok8Hc9vxrg=="} [
    guard boolnot(eq(extract(32, 0, R2_18:bv64), 0x0:bv32));
    var R1_23: bv64 := R1_17:bv64 { .label = "phiback" };
    goto(%main_loop0_20);
  ];
  block %phi_30 [
    guard boolnot(eq(extract(32, 0, R1_24:bv64), 0x0:bv32));
    ( var R1_17: bv64 := R1_24:bv64,
      var R19_18: bv64 := R19_24:bv64,
      var R2_18: bv64 := R2_24:bv64 );
    goto(%main_loop1_26);
  ];
  block %phi_31 [
    guard eq(extract(32, 0, R1_24:bv64), 0x0:bv32);
    var Cse2__5_7_1: bv32 := bvnot(extract(32, 0, R19_24:bv64)) { .label = "1888_0" };
    var Cse0__5_8_1: bv32 := bvadd(extract(32, 0, R0_6:bv64), bvnot(extract(32, 0, R19_24:bv64))) { .label = "1888_1" };
    goto(%phi_32, %phi_33);
  ];
  block %phi_32 [
    guard bvsgt(extract(32, 0, R0_6:bv64), 0x0:bv32);
    var VF_10: bv1 := bvnot(bvcomp(sign_extend(32, bvadd(Cse0__5_8_1:bv32, 0x1:bv32)), bvadd(bvadd(sign_extend(32, extract(32, 0, R0_6:bv64)), sign_extend(32, Cse2__5_7_1:bv32)), 0x1:bv64))) { .label = "1888_2" };
    var NF_10: bv1 := extract(32, 31, bvadd(Cse0__5_8_1:bv32, 0x1:bv32)) { .label = "1888_2" };
    goto(%phi_36, %phi_37);
  ];
  block %phi_33 [
    guard bvsle(extract(32, 0, R0_6:bv64), 0x0:bv32);
    var NF_13: bv1 := 0x0:bv1 { .label = "phiback" };
    var VF_13: bv1 := 0x0:bv1 { .label = "phiback" };
    goto(%main_10);
  ];
  block %phi_36 [
    guard bvslt(extract(32, 0, R0_6:bv64), extract(32, 0, R19_24:bv64));
    var R30_8: bv64 := 0x704:bv64 { .label = "1912_0" };
    var (R0_retval_inlined_6:bv64, R17_36:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_2240 (bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64)) { .label = "1912_2" };
    goto(%main_6_retval_inline);
  ];
  block %phi_37 [
    guard bvsge(extract(32, 0, R0_6:bv64), extract(32, 0, R19_24:bv64));
    var NF_13: bv1 := NF_10:bv1 { .label = "phiback" };
    var VF_13: bv1 := VF_10:bv1 { .label = "phiback" };
    goto(%main_10);
  ];
  block %main_6_retval_inline [
    var R29_37: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64) { .label = "phiback" };
    var R31_40: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R16_40: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R2_40: bv64 := 0x3:bv64 { .label = "phiback" };
    var R17_38: bv64 := R17_36:bv64 { .label = "phiback" };
    var R0_37: bv64 := 0x990:bv64 { .label = "phiback" };
    var R30_10: bv64 := R30_8:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_10:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_40:bv64) { .comment = "R31 preserved across calls" };
    return (R0_37:bv64, R16_40:bv64, R17_38:bv64, R29_37:bv64, R2_40:bv64);
  ]
];


proc @reach_error_2240
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x8c0; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x8c0; .originalLabel = "A+gdnIN+R6uou6frUN+XFg=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2240_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2240_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load3_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0x990:bv64, load3_1:bv64, 0x988:bv64, 0x3:bv64, 0x978:bv64);
  ]
];




prog entry @main_1792 {
  .symbols = {
    .externalFunctions = [
      { .name = "_ITM_deregisterTMCloneTable"; .offset = 0x1ffc0 };
      { .name = "_ITM_registerTMCloneTable"; .offset = 0x1ffe0 };
      { .name = "__VERIFIER_nondet_char"; .offset = 0x20010 };
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
      { .name = "_IO_stdin_used"; .address = 0x970; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xadc; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xae0; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20040; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x8e8; .size = 0xa0 };
      { .name = "_start"; .address = 0x780; .size = 0x1a0 };
      { .name = "gcd_test"; .address = 0x900; .size = 0x2c0 };
      { .name = "main"; .address = 0x700; .size = 0x3e0 };
      { .name = "reach_error"; .address = 0x8c0; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x8a0 ]; [ 0x1fdc0; 0x84c ]; [ 0x1ffd8; 0x700 ]; [ 0x20038; 0x20038 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2VwjbqU1lu4x9ba6IyRitu15B8BvSkA/e2pSSQAAAA=" ]
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
      "H4sIAAAAAAAA/2NgwA2YGbgYDNiwiYszGDAwoYhlA7EQFjMYgVgBi3gtECthEXfDYY4sDnN6cKjXwaE+Fod6AGH19TYIAQAA"
    ]
  };
  {
    .name = ".dynstr";
    .address = 0x3d8;
    .size = 0xc1;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3WMywrCMBBF54cM+ED3liqBdlOC22GaTmsgnUCShfj1jiLuXM29lzMH0LoeJ868hFI5u76JSdjRGBkQlzUJ";
      "lkq5IsIH/QPe2sFebDugJJm4or9T1plKYf2dKURtMYz+a1spiC7+QTgHoRieDDSmXEEhdWxUUkxJ7+r1miNcO3tucGe2p1/c";
      "H+AFOlBhZsEAAAA="
    ]
  };
  {
    .name = ".gnu.version";
    .address = 0x49a;
    .size = 0x16;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgAAEmBkYGZiCGkMwMAK2KdfMWAAAA" ]
  };
  {
    .name = ".gnu.version_r";
    .address = 0x4b0;
    .size = 0x30;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NkYGJYyMDAIMAAAdMnTmNjYGBmWA0V2wLmMzFsg8oDAE6hS8UwAAAA" ]
  };
  {
    .name = ".rela.dyn";
    .address = 0x4e0;
    .size = 0xc0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/9vxl5EBBJhZwBTDAg4IfQBN3AcqfuM/qjgDO4SyYGBCEYfxD0DVMwLFYVpA4ASSOCuS+AUkcXYk8QdI4pxI";
      "4gBiiAzrwAAAAA=="
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
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBPjGBim/K0+uOIAc/w1ALbqmjwYAAAA" ]
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
    .size = 0x258;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3VRMWtaURT+7r3ZDBmqUDA2+ixxcFYkU99zeYObZo+aX+BUiIMvXbvkYaB/oaZLGzJkakzWdGqIEAhFpQ2B";
      "dJCawQu+vn73FUuxdPg4l3vO+c53vhO0P/YCBX9aE71RGL6JpxBPpPDkC9+PKlGRfHckWmMlK4cbiIP57nE3WWasY1ayBQpj";
      "hXxj7SJpfZLrUyXzWeb2w7CYBlro1/beAdvTmtMDvGrQvnjbVzuDKnCYzqhrg2fwPm8Q3xSORsrW4+fw76hpCEzw3dWKuRXi";
      "AzX1iej/3tU2cHIahk8N34JrGRA4AIQvGC3GF8BDn3pG5LCGrm6QY6LEEWR6YHiW6y3gMjvvXDmr+6+tudM9Z/2YveWJq5tR";
      "r/zTGyy8jEHH2V+Xzhb9KUV6v7raY33En7L1K+5xQ2ToSV2KrWnM1gtv/tZ/y/3+t5tB0D7rKeBAEGY2GHeHm76Vyfmwc36T";
      "/C85h14Vfms8izT+4F/kD29lEbxhxdzL3NV+7yWFmJW4a0GunifLnlgfKpF3mKPuouEZKVExff/kf4bFGTX/AqxGJyBYAgAA"
    ]
  };
  {
    .name = ".fini";
    .address = 0x958;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0x970;
    .size = 0x22;
    .readOnly = true;
    .bytes = [ "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiMD89OSXeSC+ZwYABABO05eMiAAAA" ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0x994;
    .size = 0x54;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrYOYGBg4ATinL///yswMjC8AdIZQL7Pv///a4B0DZCeAKR3AOklQJrn////J4C0DpC+A6RDgPQXkH4g";
      "zQPUDwDPndvrVAAAAA=="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0x9e8;
    .size = 0xf8;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiGv+/v9vApJ0ZJcDiekA8QmgmAFUD0jMAYifAMVsoGIKQBwCxDz//v/3";
      "AOvlU5jLMo/ZaTKT3727l/lg+iqA2AaohgWqTwSIe4DYAyimAdEnMJdpHiNIfAkQRwDFQWwGZ4g4yIw9UPEIqBkqQHwBiF3+";
      "/P9fg2r3FMYoLqD1V/gYHLnBagHm94gW+AAAAA=="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xae0;
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
      "H4sIAAAAAAAA/7XQPRKCMBCG4UV+BH86HAQ9hMfxFl7FsbTSG1BS4g0oLS0paSgYR8Iw+1KE3m2e+bJJFuKI1g0dfOIGT4G6";
      "JZ8jNSUXPz15IIeYYUn/OOu3vbmM5gvNPutvV2WsVPRX5BeucY87sYtrpDY6n2vkijEuMcGHb69/PPu7S4xm879G/2fa2pNz";
      "zhvy9M4N+U6/I3vynxoA1UFVgPABAAA="
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
