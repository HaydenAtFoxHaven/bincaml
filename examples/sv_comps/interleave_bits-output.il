memory shared $mem : (bv64 -> bv8);
var $Global_131104_131112: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_ushort : () -> bv64;

prog entry @main_1856;

proc @main_1856
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R19_in:bv64, R1_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, V0_in:bv128, V1_in:bv128, V30_in:bv128, V31_in:bv128, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R1_out:bv64, R29_out:bv64, R2_out:bv64)
  { .name = "main"; .address = 0x740; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x740; .originalLabel = "AbMgDP19RNiD5R+9dUybBw=="} [
    var Stack_n32_n24: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n24_n16: bv64 := R30_in:bv64 { .label = "1856_2" };
    var Stack_n16_n8: bv64 := R19_in:bv64 { .label = "1864_0" };
    var load16_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv64 := 0x2abc;
    var R19_2: bv64 := zero_extend(48, extract(16, 0, R0_2:bv64)) { .label = "1872_0" };
    var load16_2: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv64 := 0x3b45;
    var R0_6: bv64 := zero_extend(48, extract(16, 0, R0_4:bv64)) { .label = "1884_0" };
    var load21_1: bv128 := load le $mem 0xa00:bv64 128 { .label = "1904_0_0" };
    ( var V29_2: bv128 := 0x0:bv128,
      var V0_6: bv128 := V0_in:bv128,
      var R1_3: bv64 := 0x0:bv64 );
    goto(%main_loop1_16);
  ];
  block %main_loop1_16 {.address = 0x77c; .originalLabel = "cQbcHbVeScS9lhwJ+ZFsEg=="} [
    var R1_4: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_3:bv64), 0x1:bv32)) { .label = "1920_0" };
    var V0_7: bv128 := bvand(V31_in:bv128, V0_6:bv128) { .label = "1932_0" };
    var V0_8: bv128 := bvor(V1_in:bv128, V0_7:bv128) { .label = "1948_0" };
    var V29_3: bv128 := bvor(V29_2:bv128, V0_8:bv128) { .label = "1952_0" };
    goto(%phi_10, %phi_11);
  ];
  block %phi_10 {.originalLabel = "cQbcHbVeScS9lhwJ+ZFsEg=="} [
    guard boolnot(eq(extract(32, 0, R1_4:bv64), 0x4:bv32));
    ( var V29_2: bv128 := V29_3:bv128,
      var V0_6: bv128 := V0_8:bv128,
      var R1_3: bv64 := R1_4:bv64 );
    goto(%main_loop1_16);
  ];
  block %phi_11 {.originalLabel = "cQbcHbVeScS9lhwJ+ZFsEg=="} [
    guard eq(extract(32, 0, R1_4:bv64), 0x4:bv32);
    var R0_10: bv32 := bvor(extract(32, 0, R0_6:bv64), bvshl(zero_extend(8, extract(24, 0, R0_6:bv64)), 0x8:bv32)) { .label = "1968_0" };
    var R19_8: bv32 := bvor(extract(32, 0, R19_2:bv64), bvshl(zero_extend(8, extract(24, 0, R19_2:bv64)), 0x8:bv32)) { .label = "1976_0" };
    var R0_12: bv32 := bvor(bvand(R0_10:bv32, 0xff00ff:bv32), bvshl(zero_extend(4, extract(28, 0, bvand(R0_10:bv32, 0xff00ff:bv32))), 0x4:bv32)) { .label = "1984_0" };
    var R1_8: bv32 := bvor(bvand(R19_8:bv32, 0xff00ff:bv32), bvshl(zero_extend(4, extract(28, 0, bvand(R19_8:bv32, 0xff00ff:bv32))), 0x4:bv32)) { .label = "1996_0" };
    var R0_14: bv32 := bvor(bvand(R0_12:bv32, 0xf0f0f0f:bv32), bvshl(zero_extend(2, extract(30, 0, bvand(R0_12:bv32, 0xf0f0f0f:bv32))), 0x2:bv32)) { .label = "2004_0" };
    var V25_2: bv128 := bvor(zero_extend(64, extract(128, 64, V29_3:bv128)), V29_3:bv128) { .label = "2012_0" };
    var R1_10: bv32 := bvor(bvand(R1_8:bv32, 0xf0f0f0f:bv32), bvshl(zero_extend(2, extract(30, 0, bvand(R1_8:bv32, 0xf0f0f0f:bv32))), 0x2:bv32)) { .label = "2016_0" };
    var R0_16: bv64 := zero_extend(32, bvor(bvand(R0_14:bv32, 0x33333333:bv32), bvshl(zero_extend(1, extract(31, 0, bvand(R0_14:bv32, 0x33333333:bv32))), 0x1:bv32))) { .label = "2024_0" };
    var R1_12: bv32 := bvor(bvand(R1_10:bv32, 0x33333333:bv32), bvshl(zero_extend(1, extract(31, 0, bvand(R1_10:bv32, 0x33333333:bv32))), 0x1:bv32)) { .label = "2028_0" };
    var R0_17: bv32 := bvshl(zero_extend(1, extract(31, 0, R0_16:bv64)), 0x1:bv32) { .label = "2032_0" };
    var R0_19: bv64 := zero_extend(32, bvor(bvand(R0_17:bv32, 0xaaaaaaaa:bv32), bvand(R1_12:bv32, 0x55555555:bv32))) { .label = "2048_0" };
    var V25_3: bv128 := bvor(zero_extend(32, extract(128, 32, V25_2:bv128)), V25_2:bv128) { .label = "2052_0" };
    var R1_14: bv64 := zero_extend(32, extract(32, 0, V25_3:bv128)) { .label = "2056_0" };
    goto(%phi_12, %phi_13);
  ];
  block %phi_12 [
    guard boolnot(eq(extract(32, 0, R0_19:bv64), extract(32, 0, R1_14:bv64)));
    var R30_8: bv64 := 0x704:bv64 { .label = "2084_0" };
    var (R0_retval_inlined_6:bv64, R17_11:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_1792 (bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64)) { .label = "2084_2" };
    goto(%phi_12_retval_inline);
  ];
  block %phi_13 [
    guard eq(extract(32, 0, R0_19:bv64), extract(32, 0, R1_14:bv64));
    var load18_1: bv64 := Stack_n16_n8:bv64 { .label = "2068_0_0" };
    var load19_1: bv64 := Stack_n32_n24:bv64 { .label = "2076_0_0" };
    var load20_1: bv64 := Stack_n24_n16:bv64 { .label = "2076_1_0" };
    var R29_16: bv64 := load19_1:bv64 { .label = "phiback" };
    var R31_15: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_15: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R1_20: bv64 := R1_14:bv64 { .label = "phiback" };
    var R2_11: bv64 := 0x0:bv64 { .label = "phiback" };
    var R17_13: bv64 := load16_2:bv64 { .label = "phiback" };
    var R0_26: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_10: bv64 := load20_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_12_retval_inline [
    var R29_16: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64) { .label = "phiback" };
    var R31_15: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R16_15: bv64 := 0x20020:bv64 { .label = "phiback" };
    var R1_20: bv64 := 0x9b8:bv64 { .label = "phiback" };
    var R2_11: bv64 := 0xb:bv64 { .label = "phiback" };
    var R17_13: bv64 := R17_11:bv64 { .label = "phiback" };
    var R0_26: bv64 := 0x9f0:bv64 { .label = "phiback" };
    var R30_10: bv64 := R30_8:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_10:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_15:bv64) { .comment = "R31 preserved across calls" };
    return (R0_26:bv64, R16_15:bv64, R17_13:bv64, R1_20:bv64, R29_16:bv64, R2_11:bv64);
  ]
];


proc @reach_error_1792
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x700; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x700; .originalLabel = "Q4lxbQCfQI2WOlWUePZLYw=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1792_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load4_1: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0x9f0:bv64, load4_1:bv64, 0x9b8:bv64, 0xb:bv64, 0xa10:bv64);
  ]
];




prog entry @main_1856 {
  .symbols = {
    .externalFunctions = [
      { .name = "_ITM_deregisterTMCloneTable"; .offset = 0x1ffc0 };
      { .name = "_ITM_registerTMCloneTable"; .offset = 0x1ffe0 };
      { .name = "__VERIFIER_nondet_ushort"; .offset = 0x20028 };
      { .name = "__assert_fail"; .offset = 0x20020 };
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
      { .name = "_IO_stdin_used"; .address = 0x9b0; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xb44; .size = 0x0 };
      { .name = "__PRETTY_FUNCTION__.0"; .address = 0xa10; .size = 0x60 };
      { .name = "__abi_tag"; .address = 0xb48; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20040; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x980; .size = 0xa0 };
      { .name = "_start"; .address = 0x840; .size = 0x1a0 };
      { .name = "main"; .address = 0x740; .size = 0x740 };
      { .name = "reach_error"; .address = 0x700; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x960 ]; [ 0x1fdc0; 0x90c ]; [ 0x1ffd8; 0x740 ]; [ 0x20038; 0x20038 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2XwC7/4JGBSBt/uAjmGG31G/dfWvNAEAKHZWCEkAAAA" ]
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
      "H4sIAAAAAAAA/2NgwA2YGbgYLNiwiYszGDAwoYjlArEQFjMYgVgBi3g9ECthEZfFob4Ph/k6ONTH41DvhkMcAI8Nc7MIAQAA"
    ]
  };
  {
    .name = ".dynstr";
    .address = 0x3d8;
    .size = 0xc3;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3WMTQvCMAyG+4cs+IHeHVMK22UUryHtslnoWmgqiL/eTMSbp+RNnvdRYGwPIxWaA1cqtm9iTmTRRVIA85IT";
      "cMVSAdQH/QPe2sFcTDtAymmkCg++51Llgcwk7QlDlBSD81/fgiHJxT8RppAwhhcpdGtJILFsRMOa8xq9TH1U186cG9jp7em3";
      "7g/qDeqT9w7DAAAA"
    ]
  };
  {
    .name = ".gnu.version";
    .address = 0x49c;
    .size = 0x16;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgAAEmBkYGZiQMANKGp2QWAAAA" ]
  };
  {
    .name = ".gnu.version_r";
    .address = 0x4b8;
    .size = 0x30;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NkYGJYzMDAIMAAAdMnTmNjYGBmWAsV2wLmMzHsgMoDAOiRrDQwAAAA" ]
  };
  {
    .name = ".rela.dyn";
    .address = 0x4e8;
    .size = 0xc0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/9vxl5EBBJhZwBRDAieEPoAmzgMVv/EfVdyBHUJbMDChiMP4B6DqGYHiUCkwOIEkzookfgFJnA1J/AGSOAeS";
      "OAAxOZpzwAAAAA=="
    ]
  };
  {
    .name = ".rela.plt";
    .address = 0x5a8;
    .size = 0x90;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/03IqxIAEAAAwRtvkiiK/v8LjeQ2LgSekCDyNX3WT33RL33Vb33XH/3QX55Qt0qQAAAA"
    ]
  };
  {
    .name = ".init";
    .address = 0x638;
    .size = 0x18;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBN7GBim/K0+uOIAc/w1AMVBHYwYAAAA" ]
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
    .size = 0x294;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/31RQUgUYRh9//xzEJTYZg970Z35FSzmLMhS4awFc/uDzaPQasdAkC7BHpyFwIMdGjoEIeHe1HMQlubmtU5F";
      "UlSwmkWQhwFPP7iOb0YKifTweD/ffO993/em29hckcAjQXQlYpDvBJdj1RmO0b4UT4uo9j1Nn7ie/Pg/dBuvVzLdQS/MN/YV";
      "r8L5QrboA77nLthaIKqV+2w9YOPmZLR17Qr5KVEP17WycbE5/0p/cj3dIUTY0rixrhfnX2qvf0lvuEt6rIDZ1lE6UaIGHnws";
      "wrk3WPSnnsFBAf7a9dIM3sFRBeErMnrYswen4m5o1cMa37DhK1v4uO/eGh0qzaiEtUQ4gPBNeU0rOVx2Ie62gImD3sCAO3cb";
      "W8tteXv7xTn3ZxhA9L5M/JBY3ZGB2R1C/JOZdIAE+6GR/GYTTfo8JPL6r9AEwPMHaVrKZpzlDcEcIWJBVuQx4HebO+7QQ3VC";
      "M0WPRIpVWO525vNvvwLeDh7Ofaj2NRfUYfXxG/bvUjuehGY611p/taf/ZZH6ulWtBAKj+b57oYnYn/v3B6bGOz4THnOqW6KS";
      "ZfYnr9P7f+V952XHDEZOZm/msyfpeQxbpARSlAIAAA=="
    ]
  };
  {
    .name = ".fini";
    .address = 0x994;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0x9b0;
    .size = 0x6c;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAAT09/eKy5PzcAt2czLSSYn0ImZlXklqUk5pYlhqflInJ10tmMGDABIxADDKVGYiLUhOTM+JTi4ry";
      "ixgAsXB9lmwAAAA="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0xa1c;
    .size = 0x4c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrb2YGBg4ADiJ3/+/78CpFX+/v/Pwgik//3/nwDktwDpEiC9BUh3AOkPQHoOkHb5////ASCdAqTfAGkA";
      "gA5C8kwAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xa68;
    .size = 0xe0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiPf8/f/fBCTpyC4HEtMBYo5///8bQPWAxByAWAUoZgMVUwDiECD2AYp5";
      "gPXyKcxlmcfsNJnJ797dy3wwfRVAXANUwwLVJwLEPSDz//z/rwHRJzCXaR4jSHwJEBcA1YLYDM4QcZA9e0DuBKp/gWpPKRfY";
      "IkdukDAAMWH68eAAAAA="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xb48;
    .size = 0x20;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAGJGIHb3C2UAAWYgZmeAAAA9kbzyIAAAAA==" ]
  };
  {
    .name = ".init_array";
    .address = 0x1fdb8;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/0vgZAADAAE6USAIAAAA" ]
  };
  {
    .name = ".fini_array";
    .address = 0x1fdc0;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/+PhZAADAPWPFacIAAAA" ]
  };
  {
    .name = ".dynamic";
    .address = 0x1fdc8;
    .size = 0x1f0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/7XQPRKCMBCG4eVXUexg/D2It/IqFpZ0NpaWlMxwAUqOQGlDwTASx9k3RejZ5pkvm2QDnmg90MMnpniN1Z3d";
      "n6hHcvnVk2fyGk9Y0b/M+v1kbn/fvuaI9TZQGSsN/Q25xi0eMBe3uEY6o/O5Ru6Y4Qr3+Irc9S50311hMps/Gv0eu3Uil5w3";
      "ZPufP+SC/kAOZZn6AXc8Rp/wAQAA"
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
