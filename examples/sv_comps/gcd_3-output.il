var $Global_131088_131096: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_char : () -> bv8;

prog entry @main_1792;

proc @main_1792
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R19_in:bv64, R1_in:bv64, R20_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R1_out:bv64, R29_out:bv64)
  { .name = "main"; .address = 0x700; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x700; .originalLabel = "gFel/3hjSieZyWZx/KXK7Q=="} [
    var Stack_n32_n24: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n24_n16: bv64 := R30_in:bv64 { .label = "1792_2" };
    var Stack_n16_n8: bv64 := R19_in:bv64 { .label = "1800_1" };
    var Stack_n8_0: bv64 := R20_in:bv64 { .label = "1800_2" };
    var load0_1: bv64 := $Global_131088_131096:bv64 { .label = "1684_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv8 := $__VERIFIER_nondet_char();
    var R20_2: bv64 := zero_extend(56, R0_2:bv8) { .label = "1808_0" };
    var R19_2: bv32 := sign_extend(24, R0_2:bv8) { .label = "1812_0" };
    var load0_2: bv64 := $Global_131088_131096:bv64 { .label = "1684_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv8 := $__VERIFIER_nondet_char();
    var R1_2: bv64 := zero_extend(56, R0_4:bv8) { .label = "1820_0" };
    var R0_6: bv64 := zero_extend(32, sign_extend(24, R0_4:bv8)) { .label = "1824_0" };
    goto(%phi_9, %phi_10);
  ];
  block %main_8 {.address = 0x760; .originalLabel = "fVysv8ojTWulPXI7/+DXoQ=="} [
    var load9_1: bv64 := Stack_n16_n8:bv64 { .label = "1888_1_0" };
    var load10_1: bv64 := Stack_n8_0:bv64 { .label = "1888_2_0" };
    var load11_1: bv64 := Stack_n32_n24:bv64 { .label = "1896_0_0" };
    var load12_1: bv64 := Stack_n24_n16:bv64 { .label = "1896_1_0" };
    var R29_42: bv64 := load11_1:bv64 { .label = "phiback" };
    var R31_46: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_46: bv64 := 0x20010:bv64 { .label = "phiback" };
    var R1_45: bv64 := R1_40:bv64 { .label = "phiback" };
    var R17_44: bv64 := load0_2:bv64 { .label = "phiback" };
    var R0_41: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_10: bv64 := load12_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_10 [
    guard eq(NF_10:bv1, VF_10:bv1);
    var R1_40: bv64 := R1_29:bv64 { .label = "phiback" };
    goto(%main_8);
  ];
  block %main_loop0_20 [
    var R1_29: bv64 := zero_extend(32, bvsub(extract(32, 0, R2_16:bv64), extract(32, 0, bvmul(zero_extend(32, extract(32, 0, R1_28:bv64)), zero_extend(32, extract(32, 0, R0_21:bv64)))))) { .label = "1860_0" };
    var R2_22: bv64 := zero_extend(32, extract(32, 0, R0_21:bv64)) { .label = "1864_0" };
    var R0_27: bv64 := zero_extend(32, sign_extend(24, extract(8, 0, R1_29:bv64))) { .label = "1868_0" };
    goto(%phi_37, %phi_38);
  ];
  block %main_loop1_26 {.address = 0x740; .originalLabel = "JsBM+vkdRaCVXy2Ok3i99A=="} [
    assert booland(bvsle(0x80000000:bv32, R19_2:bv32), bvsle(R19_2:bv32, 0x7fffffff:bv32));
    goto(%phi_31, %phi_32);
  ];
  block %main_28 {.address = 0x774; .originalLabel = "wBGTIG+lQIC4zK5ivSSmaA=="} [
    var R0_21: bv64 := zero_extend(32, sign_extend(24, extract(8, 0, bvneg(extract(32, 0, R1_2:bv64))))) { .label = "phiback" };
    var R1_22: bv64 := zero_extend(32, bvneg(extract(32, 0, R1_2:bv64))) { .label = "phiback" };
    var R2_16: bv64 := R2_14:bv64 { .label = "phiback" };
    goto(%main_loop1_26);
  ];
  block %phi_9 {.originalLabel = "uidxyBPrTcqJ7KI/qAalYQ=="} [
    guard bvslt(R19_2:bv32, 0x0:bv32);
    var R2_7: bv64 := zero_extend(32, sign_extend(24, extract(8, 0, bvneg(extract(32, 0, R20_2:bv64))))) { .label = "1924_0" };
    goto(%phi_18, %phi_19);
  ];
  block %phi_10 {.originalLabel = "uidxyBPrTcqJ7KI/qAalYQ=="} [
    guard bvsge(R19_2:bv32, 0x0:bv32);
    goto(%phi_11, %phi_12);
  ];
  block %phi_11 [
    guard bvslt(extract(32, 0, R0_6:bv64), 0x0:bv32);
    var R2_14: bv64 := zero_extend(32, R19_2:bv32) { .label = "phiback" };
    goto(%main_28);
  ];
  block %phi_12 [
    guard bvsge(extract(32, 0, R0_6:bv64), 0x0:bv32);
    goto(%phi_13, %phi_14);
  ];
  block %phi_13 [
    guard eq(extract(32, 0, R0_6:bv64), 0x0:bv32);
    var R1_40: bv64 := R1_2:bv64 { .label = "phiback" };
    goto(%main_8);
  ];
  block %phi_14 [
    guard boolnot(eq(extract(32, 0, R0_6:bv64), 0x0:bv32));
    var R0_21: bv64 := R0_6:bv64 { .label = "phiback" };
    var R1_22: bv64 := R1_2:bv64 { .label = "phiback" };
    var R2_16: bv64 := zero_extend(32, R19_2:bv32) { .label = "phiback" };
    goto(%main_loop1_26);
  ];
  block %phi_18 [
    guard bvslt(extract(32, 0, R0_6:bv64), 0x0:bv32);
    var R2_14: bv64 := R2_7:bv64 { .label = "phiback" };
    goto(%main_28);
  ];
  block %phi_19 [
    guard bvsge(extract(32, 0, R0_6:bv64), 0x0:bv32);
    goto(%phi_20, %phi_21);
  ];
  block %phi_20 [
    guard boolnot(eq(extract(32, 0, R0_6:bv64), 0x0:bv32));
    var R0_21: bv64 := R0_6:bv64 { .label = "phiback" };
    var R1_22: bv64 := R1_2:bv64 { .label = "phiback" };
    var R2_16: bv64 := R2_7:bv64 { .label = "phiback" };
    goto(%main_loop1_26);
  ];
  block %phi_21 [
    guard eq(extract(32, 0, R0_6:bv64), 0x0:bv32);
    var R1_40: bv64 := R1_2:bv64 { .label = "phiback" };
    goto(%main_8);
  ];
  block %phi_31 {.originalLabel = "JsBM+vkdRaCVXy2Ok3i99A=="} [
    guard eq(extract(32, 0, R0_21:bv64), 0x0:bv32);
    var R1_28: bv64 := 0x0:bv64 { .label = "phiback" };
    goto(%main_loop0_20);
  ];
  block %phi_32 {.originalLabel = "JsBM+vkdRaCVXy2Ok3i99A=="} [
    guard boolnot(eq(extract(32, 0, R0_21:bv64), 0x0:bv32));
    var R1_28: bv64 := R1_22:bv64 { .label = "phiback" };
    goto(%main_loop0_20);
  ];
  block %phi_37 [
    guard boolnot(eq(extract(32, 0, R1_29:bv64), 0x0:bv32));
    ( var R0_21: bv64 := R0_27:bv64,
      var R1_22: bv64 := R1_29:bv64,
      var R2_16: bv64 := R2_22:bv64 );
    goto(%main_loop1_26);
  ];
  block %phi_38 [
    guard eq(extract(32, 0, R1_29:bv64), 0x0:bv32);
    var Cse2__5_6_1: bv32 := bvnot(extract(32, 0, R2_22:bv64)) { .label = "1880_0" };
    var Cse0__5_7_1: bv32 := bvadd(R19_2:bv32, bvnot(extract(32, 0, R2_22:bv64))) { .label = "1880_1" };
    goto(%phi_39, %phi_40);
  ];
  block %phi_39 [
    guard bvsgt(R19_2:bv32, 0x0:bv32);
    var VF_7: bv1 := bvnot(bvcomp(sign_extend(32, bvadd(Cse0__5_7_1:bv32, 0x1:bv32)), bvadd(bvadd(sign_extend(32, R19_2:bv32), sign_extend(32, Cse2__5_6_1:bv32)), 0x1:bv64))) { .label = "1880_2" };
    var NF_7: bv1 := extract(32, 31, bvadd(Cse0__5_7_1:bv32, 0x1:bv32)) { .label = "1880_2" };
    goto(%phi_43, %phi_44);
  ];
  block %phi_40 [
    guard bvsle(R19_2:bv32, 0x0:bv32);
    var NF_10: bv1 := 0x0:bv1 { .label = "phiback" };
    var VF_10: bv1 := 0x0:bv1 { .label = "phiback" };
    goto(%main_10);
  ];
  block %phi_43 [
    guard bvslt(R19_2:bv32, extract(32, 0, R2_22:bv64));
    var R30_8: bv64 := 0x704:bv64 { .label = "1940_0" };
    var (R0_retval_inlined_6:bv64, R17_42:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_2304 (bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64)) { .label = "1940_2" };
    goto(%main_6_retval_inline);
  ];
  block %phi_44 [
    guard bvsge(R19_2:bv32, extract(32, 0, R2_22:bv64));
    var NF_10: bv1 := NF_7:bv1 { .label = "phiback" };
    var VF_10: bv1 := VF_7:bv1 { .label = "phiback" };
    goto(%main_10);
  ];
  block %main_6_retval_inline [
    var R29_42: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64) { .label = "phiback" };
    var R31_46: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R16_46: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R1_45: bv64 := 0x9c8:bv64 { .label = "phiback" };
    var R17_44: bv64 := R17_42:bv64 { .label = "phiback" };
    var R0_41: bv64 := 0x9d0:bv64 { .label = "phiback" };
    var R30_10: bv64 := R30_8:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_10:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_46:bv64) { .comment = "R31 preserved across calls" };
    return (R0_41:bv64, R16_46:bv64, R17_44:bv64, R1_45:bv64, R29_42:bv64);
  ]
];


proc @reach_error_2304
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x900; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x900; .originalLabel = "q4Nt9taHTR2QmcpWPBuVNg=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2304_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2304_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load16_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0x9d0:bv64, load16_1:bv64, 0x9c8:bv64, 0x3:bv64, 0x9b8:bv64);
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
      { .name = "_IO_stdin_used"; .address = 0x9b0; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xb1c; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xb20; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20040; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x928; .size = 0xa0 };
      { .name = "_start"; .address = 0x7c0; .size = 0x1a0 };
      { .name = "gcd_test"; .address = 0x940; .size = 0x2c0 };
      { .name = "main"; .address = 0x700; .size = 0x4c0 };
      { .name = "reach_error"; .address = 0x900; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x8e0 ]; [ 0x1fdc0; 0x88c ]; [ 0x1ffd8; 0x700 ]; [ 0x20038; 0x20038 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2XYty0sLL+icsfxNRu9fp35/vXib/+HAFpEq34kAAAA" ]
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
      "H4sIAAAAAAAA/9vxl5EBBJhZwBTDAw4IfQBNvAcqfuM/qjgDO4SyYGBCEYfxD0DVMwLFYVpA4ASSOCuS+AUkcXYk8QdI4pxI";
      "4gBpg2UdwAAAAA=="
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
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBPzGBim/K0+uOIAc/w1ALLcsygYAAAA" ]
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
    .size = 0x298;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/4VSPUhbURT+7rtuZmoEIcYmr4KBzAnBqe9leUO2ms2hqQ6d42iGPJ0KXXy00FU345ShcxNd3VoaEEpJHlUE";
      "O0TjkAt5Xr/7JEVaqsPHPZyf73znnBs1vrQiiWC0KloDrT/NpfEsmUbyJ21BG7RH1rjkEHsChVAm85ms/D6Fm+im7HdYCCXy";
      "WeZua11sWqjXjstbJwLV0arbAvxXUeP4oCtf90z9QIqKyb3Sej6Uc5Uy7ZrWpb1IF2/oWwM+PuzxFBbhf31OnEkcDqSjwiUE";
      "55ypDwzx21OSsRlinzO1idh/4SkH+HzAfkbX/7ghsAuIQPC1+b4ELrtAdUAOu++pN+QYSnEIK9MzPH/n28DJi0nzm5vYfm9P";
      "3A9HzA9ZWx56aj2utf7URtNbzEIlWV+z3BVHoBTr/eUpn/kxf9pRm5zjlMhytzVLrIxmHTXd8UP9PzjfY7uLGp2WBHYFYXqD";
      "70Z/ObCzuQBOLlgn/1v24a4K9xo7scZr+uL98HY2wftXMkDd3NJp+ykhxiXOWrASR6myLxb6UuRdxnb4PwyP+QOm7p/4rS6O";
      "qfkOGMgDK5gCAAA="
    ]
  };
  {
    .name = ".fini";
    .address = 0x998;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0x9b0;
    .size = 0x22;
    .readOnly = true;
    .bytes = [ "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiMD89OSXeWC+ZwYABALZnuSgiAAAA" ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0x9d4;
    .size = 0x54;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrYOYGBg4ARinb///yswMjC8AdIZQL7Pv///a4B0DZCeAKR3AOklQJrn////J0DqgfQdIB0CpL8A6Rwg";
      "zQPUDwB16lXdVAAAAA=="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xa28;
    .size = 0xf8;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiGv+/v9vApJ0ZJcDiekA8QmgmAFUD0jMAYifAMVsoGIKQBwCxDz//v/3";
      "AOvlU5jLMo/ZaTKT3727l/lg+iqA2AaohgWqTwSIe4DYAyimAdEnMJdpHiNIfAkQRwDFQWwGZ4g4yIw9UPEIqBkqQHwBiFn+";
      "/P8/A9XuKYwRXEDrr/AxOHKD1QIAkch/WfgAAAA="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xb20;
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
      "H4sIAAAAAAAA/7XQPQ6CQBCG4UF+BH86DIIewpt5FWNlrPQGlJR4A0pLS0oaCmJkCZmXYumd5sm3s7sD64jWFR184gZPgbol";
      "3yI1JRc/PXkgh5hhSf8467e9OY/mC80+629XZaxU9FfkF65xjzuxi2ukNjqfa+SCMS4xwYdvr388+7tLjGbzv0b/Z9rak3PO";
      "G/L0zg35Tr8je/KfGgBi3phv8AEAAA=="
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
