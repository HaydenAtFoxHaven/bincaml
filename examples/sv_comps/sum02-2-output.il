var $Global_131104_131112: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_uint : () -> bv32;

prog entry @main_1792;

proc @main_1792
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R1_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R1_out:bv64, R29_out:bv64, R2_out:bv64)
  { .name = "main"; .address = 0x700; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x700; .originalLabel = "s00v1lh8Sn6mBVUXlXvJWw=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1792_2" };
    var load12_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv64 := zero_extend(32, $__VERIFIER_nondet_uint());
    ( var R1_3: bv64 := 0x0:bv64,
      var R2_3: bv64 := 0x0:bv64 );
    goto(%main_loop1_20);
  ];
  block %main_10 [
    guard eq(ZF_11:bv1, 0x1:bv1);
    var load8_1: bv64 := Stack_n16_n8:bv64 { .label = "1872_0_0" };
    var load9_1: bv64 := Stack_n8_0:bv64 { .label = "1872_1_0" };
    var R29_19: bv64 := load8_1:bv64 { .label = "phiback" };
    var R31_19: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_19: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R1_22: bv64 := R1_10:bv64 { .label = "phiback" };
    var R2_18: bv64 := R2_4:bv64 { .label = "phiback" };
    var R17_18: bv64 := load12_1:bv64 { .label = "phiback" };
    var R0_18: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_8: bv64 := load9_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_loop1_20 {.address = 0x720; .originalLabel = "wPSLvbHBSbqH9SrVRyahAA=="} [
    var R2_4: bv64 := bvadd(R2_3:bv64, zero_extend(32, extract(32, 0, R1_3:bv64))) { .label = "1824_0" };
    var R1_4: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_3:bv64), 0x1:bv32)) { .label = "1828_0" };
    goto(%phi_7, %phi_8);
  ];
  block %phi_7 {.originalLabel = "wPSLvbHBSbqH9SrVRyahAA=="} [
    guard bvuge(extract(32, 0, R0_2:bv64), extract(32, 0, R1_4:bv64));
    ( var R1_3: bv64 := R1_4:bv64,
      var R2_3: bv64 := R2_4:bv64 );
    goto(%main_loop1_20);
  ];
  block %phi_8 {.originalLabel = "wPSLvbHBSbqH9SrVRyahAA=="} [
    guard bvult(extract(32, 0, R0_2:bv64), extract(32, 0, R1_4:bv64));
    var R1_9: bv64 := bvmul(zero_extend(32, extract(32, 0, bvadd(zero_extend(32, extract(32, 0, R0_2:bv64)), 0x1:bv64))), zero_extend(32, extract(32, 0, R0_2:bv64))) { .label = "1852_0" };
    var R1_10: bv64 := zero_extend(1, extract(64, 1, R1_9:bv64)) { .label = "1856_0" };
    var Cse0__5_9_1: bv64 := bvadd(zero_extend(1, extract(64, 1, R1_9:bv64)), bvnot(R2_4:bv64)) { .label = "1860_1" };
    goto(%phi_9, %phi_10);
  ];
  block %phi_9 [
    guard boolnot(eq(R2_4:bv64, 0x0:bv64));
    var ZF_8: bv1 := bvcomp(bvadd(Cse0__5_9_1:bv64, 0x1:bv64), 0x0:bv64) { .label = "1860_2" };
    goto(%phi_13, %phi_14);
  ];
  block %phi_10 [
    guard eq(R2_4:bv64, 0x0:bv64);
    var ZF_11: bv1 := 0x1:bv1 { .label = "phiback" };
    goto(%main_10);
  ];
  block %phi_13 [
    guard boolnot(eq(R1_10:bv64, R2_4:bv64));
    guard boolnot(eq(zero_extend(1, extract(64, 1, R1_9:bv64)), R2_4:bv64));
    var R30_6: bv64 := 0x704:bv64 { .label = "1880_0" };
    var (R0_retval_inlined_6:bv64, R17_16:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_2240 (bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .label = "1880_2" };
    goto(%main_6_retval_inline);
  ];
  block %phi_14 [
    guard eq(R1_10:bv64, R2_4:bv64);
    var ZF_11: bv1 := ZF_8:bv1 { .label = "phiback" };
    goto(%main_10);
  ];
  block %main_6_retval_inline [
    var R29_19: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R31_19: bv64 := bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64) { .label = "phiback" };
    var R16_19: bv64 := 0x20020:bv64 { .label = "phiback" };
    var R1_22: bv64 := 0x940:bv64 { .label = "phiback" };
    var R2_18: bv64 := 0x3:bv64 { .label = "phiback" };
    var R17_18: bv64 := R17_16:bv64 { .label = "phiback" };
    var R0_18: bv64 := 0x950:bv64 { .label = "phiback" };
    var R30_8: bv64 := R30_6:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_8:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_19:bv64) { .comment = "R31 preserved across calls" };
    return (R0_18:bv64, R16_19:bv64, R17_18:bv64, R1_22:bv64, R29_19:bv64, R2_18:bv64);
  ]
];


proc @reach_error_2240
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x8c0; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x8c0; .originalLabel = "menKG/UPSkq5WA09QGC0qw=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2240_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2240_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load13_1: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0x950:bv64, load13_1:bv64, 0x940:bv64, 0x3:bv64, 0x930:bv64);
  ]
];




prog entry @main_1792 {
  .symbols = {
    .externalFunctions = [
      { .name = "_ITM_deregisterTMCloneTable"; .offset = 0x1ffc0 };
      { .name = "_ITM_registerTMCloneTable"; .offset = 0x1ffe0 };
      { .name = "__VERIFIER_nondet_uint"; .offset = 0x20028 };
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
      { .name = "_IO_stdin_used"; .address = 0x928; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xa98; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xa9c; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20040; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x900; .size = 0xa0 };
      { .name = "_start"; .address = 0x780; .size = 0x1a0 };
      { .name = "assume_abort_if_not"; .address = 0x8e8; .size = 0xa0 };
      { .name = "main"; .address = 0x700; .size = 0x2e0 };
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
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2UwsD8lm3ve6efliadZzOVe3uj5dXIxADSDfi0kAAAA" ]
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
      "H4sIAAAAAAAA/2NgwA2YGbgYDNiwiYszGDAwoYhlA7EQFjMYgVgBi3gtECthEZfFob4Hh/k6ONTH4lDvhkMcACeceRQIAQAA"
    ]
  };
  {
    .name = ".dynstr";
    .address = 0x3d8;
    .size = 0xc1;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3WMywrCQAxF80MWfKB7S5WBdlMGtyFt0xKYZmBmBPHrjSLuXOXey8kBdL7DiRMvkgsn39UhKnsaAgPiskbF";
      "XCgVRPigf8Bb07uLa3rUqBMXvIsWmylntt+ZJFgLMoxf20qitowPwlmUgjwZaIipgEHm2JgkVzm+62i3OsK1decad9X29Iv7";
      "A7wA1bqrOsEAAAA="
    ]
  };
  {
    .name = ".gnu.version";
    .address = 0x49a;
    .size = 0x16;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgAAEmBkYGZiQMANKGp2QWAAAA" ]
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
      "H4sIAAAAAAAA/9vxl5EBBJhZwBTDAg4IfQBN3AcqfuM/qjgDO4SyYGBCEYfxD0DVMwLFYVpA4ASSOCuS+AUkcTYk8QdI4hxI";
      "4gCYENnlwAAAAA=="
    ]
  };
  {
    .name = ".rela.plt";
    .address = 0x5a0;
    .size = 0x90;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/03IqxIAEAAAwRtvkiiK/v8LjeQ2LgSekCDyNX3WT33RL33Vb33XH/3QX55Qt0qQAAAA"
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
    .size = 0x214;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/31RMUhCURQ97z83G4qGlkp/6dIchFNPl7+HU4tmW42NP0hbXfwUNLREk7kFjlHf1rYkIWhQqQiSMJxe+Pmd";
      "/6UIIYfDhfPuOffc+zz75sKTcD58/8RA8V6guBGLy4cfZJRZNiOYiUHsnvt+tiOxkgM+yTnm/tmpOUw3E9OZrxKQBbWe3ai6";
      "MtfaBI7/+kzCAucuEi8StY5UursM55WZ2kAfPUtLvkWIS2a8IkL+zdIKqNd9fy6Y9583BCqAcASryboOvLvM2qGH2bb0Fj36";
      "UtRgxFqBz3i/CdwtDQ+a6alSmbseNdjfpTbTt3Qh1Bq/Ws++Dm85iELPUp830iklsBbmfbZ0kf2h/7zSh9zjkYjzZnlDpAZR";
      "pT37tjq+yxP3m3Q7j/8ngYoggtlg3XYTzJ10oJJOgf57nMNbrY4yjv57h1ygH+d75L8Buuq/kxQCAAA="
    ]
  };
  {
    .name = ".fini";
    .address = 0x914;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0x928;
    .size = 0x2a;
    .readOnly = true;
    .bytes = [ "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiML+4NNfASNdIL5kBAgwYACNN6XcqAAAA" ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0x954;
    .size = 0x54;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrYOYGBg4ATiNX///1dhZGDQ+ff/fwaQ3wOka4D0HiA9AUj/ANJLgLTP////TwDpHCB9B0hPAdJfQPqB";
      "NA9QPwCwnYugVAAAAA=="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0x9a8;
    .size = 0xf4;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiPf8/f/fBCTpyC4HEtMBYo5///8bQPWAxByAWAUoZgMVUwDiECD2AYp5";
      "gPXyKcxlmcfsNJnJ797dy3wwfRVAXANUwwLVJwLEPUDcARTTgOgTmMs0jxEkvgSIZwDFQWwGZ4T4HiziMkDmFSBu+PP/fwyS";
      "OSFc9+7yMThyg4QAAN3Pn/QAAAA="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xa9c;
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
      "H4sIAAAAAAAA/7WQMRKCQAwAg4KKYqcjCI/wZ37FsaSCH1Ba4g8sLS0taSgYRo5hslccvWl2NrlLLueJxh16sIQRvKyUe/wQ";
      "KhP88dObKb6BZ1hTz2b1djDXidVCPSD/XioZKy/qW/wJdzCGR3GDNvI1Op82crN7wDU8wSJw8x/ffXcNw9n83ug+9uiAV9w3";
      "uP3nBs+pd7gv/4kRf5wXhPABAAA="
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
