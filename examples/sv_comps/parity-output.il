var $Global_131104_131112: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_uint : () -> bv32;

prog entry @main_1856;

proc @main_1856
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R1_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R29_out:bv64)
  { .name = "main"; .address = 0x740; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x740; .originalLabel = "lwsJdMBDReqpZoENv4Awag=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1856_2" };
    var load16_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv64 := zero_extend(32, $__VERIFIER_nondet_uint());
    goto(%phi_5, %phi_6);
  ];
  block %main_4 {.address = 0x790; .originalLabel = "dOkS9PMITa2WgB9rQ9EXzA=="} [
    var load13_1: bv64 := Stack_n16_n8:bv64 { .label = "1940_0_0" };
    var load14_1: bv64 := Stack_n8_0:bv64 { .label = "1940_1_0" };
    var R29_15: bv64 := load13_1:bv64 { .label = "phiback" };
    var R31_17: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_17: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R17_16: bv64 := load16_1:bv64 { .label = "phiback" };
    var R0_19: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_8: bv64 := load14_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_loop1_18 {.address = 0x760; .originalLabel = "CV1UpmalRNKCJ7gclJFx6Q=="} [
    var R2_2: bv64 := zero_extend(32, bvadd(extract(32, 0, R1_3:bv64), 0xffffffff:bv32)) { .label = "1888_0" };
    var R3_4: bv64 := zero_extend(32, bvxor(extract(32, 0, R3_3:bv64), 0x1:bv32)) { .label = "1892_0" };
    var Cse0__5_6_1: bv32 := bvand(extract(32, 0, R1_3:bv64), extract(32, 0, R2_2:bv64)) { .label = "1896_0" };
    var R1_4: bv64 := zero_extend(32, Cse0__5_6_1:bv32) { .label = "1896_5" };
    goto(%phi_8, %phi_9);
  ];
  block %phi_5 [
    guard eq(extract(32, 0, R0_2:bv64), 0x0:bv32);
    goto(%main_4);
  ];
  block %phi_6 [
    guard boolnot(eq(extract(32, 0, R0_2:bv64), 0x0:bv32));
    ( var R1_3: bv64 := zero_extend(32, extract(32, 0, R0_2:bv64)),
      var R3_3: bv64 := 0x0:bv64 );
    goto(%main_loop1_18);
  ];
  block %phi_8 {.originalLabel = "CV1UpmalRNKCJ7gclJFx6Q=="} [
    guard boolnot(eq(bvand(extract(32, 0, R1_3:bv64), extract(32, 0, R2_2:bv64)), 0x0:bv32));
    ( var R1_3: bv64 := R1_4:bv64,
      var R3_3: bv64 := R3_4:bv64 );
    goto(%main_loop1_18);
  ];
  block %phi_9 {.originalLabel = "CV1UpmalRNKCJ7gclJFx6Q=="} [
    guard eq(bvand(extract(32, 0, R1_3:bv64), extract(32, 0, R2_2:bv64)), 0x0:bv32);
    var R0_8: bv64 := zero_extend(32, bvxor(extract(32, 0, R0_2:bv64), zero_extend(1, extract(32, 1, R0_2:bv64)))) { .label = "1904_0" };
    var R1_7: bv64 := 0x11111111:bv64 { .label = "1908_0" };
    var R0_9: bv32 := bvxor(extract(32, 0, R0_8:bv64), zero_extend(2, extract(32, 2, R0_8:bv64))) { .label = "1912_0" };
    var R0_11: bv64 := zero_extend(32, extract(32, 0, bvmul(zero_extend(32, bvand(R0_9:bv32, 0x11111111:bv32)), 0x11111111:bv64))) { .label = "1920_0" };
    var R0_12: bv64 := zero_extend(63, extract(29, 28, R0_11:bv64)) { .label = "1924_0" };
    goto(%phi_10, %phi_11);
  ];
  block %phi_10 [
    guard boolnot(eq(extract(32, 0, R0_12:bv64), extract(32, 0, R3_4:bv64)));
    var R30_4: bv64 := 0x704:bv64 { .label = "1948_0" };
    var (R0_retval_inlined_6:bv64, R17_11:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_1792 (bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .label = "1948_2" };
    goto(%phi_10_retval_inline);
  ];
  block %phi_11 [
    guard eq(extract(32, 0, R0_12:bv64), extract(32, 0, R3_4:bv64));
    goto(%main_4);
  ];
  block %phi_10_retval_inline [
    var R29_15: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R31_17: bv64 := bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64) { .label = "phiback" };
    var R16_17: bv64 := 0x20020:bv64 { .label = "phiback" };
    var R17_16: bv64 := R17_11:bv64 { .label = "phiback" };
    var R0_19: bv64 := 0x958:bv64 { .label = "phiback" };
    var R30_8: bv64 := R30_4:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_8:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_17:bv64) { .comment = "R31 preserved across calls" };
    return (R0_19:bv64, R16_17:bv64, R17_16:bv64, R29_15:bv64);
  ]
];


proc @reach_error_1792
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x700; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x700; .originalLabel = "hNAjotfzSG23PB2mVXdmnQ=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1792_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load12_1: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0x958:bv64, load12_1:bv64, 0x930:bv64, 0xb:bv64, 0x960:bv64);
  ]
];




prog entry @main_1856 {
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
      { .name = "__FRAME_END__"; .address = 0xa90; .size = 0x0 };
      { .name = "__PRETTY_FUNCTION__.0"; .address = 0x960; .size = 0x60 };
      { .name = "__abi_tag"; .address = 0xa94; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20040; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x900; .size = 0xa0 };
      { .name = "_start"; .address = 0x7c0; .size = 0x1a0 };
      { .name = "main"; .address = 0x740; .size = 0x300 };
      { .name = "reach_error"; .address = 0x700; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x8e0 ]; [ 0x1fdc0; 0x88c ]; [ 0x1ffd8; 0x740 ]; [ 0x20038; 0x20038 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2U4f547hTNt3fXZj1jqNyUest3+p/YhAMx2rcUkAAAA" ]
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
      "H4sIAAAAAAAA/9vxl5EBBJhZwBTDAw4IfQBNvAcqfuM/qrgDO4S2YGBCEYfxD0DVMwLFoVJgcAJJnBVJ/AKSOBuS+AMkcQ4k";
      "cQCYb1ZawAAAAA=="
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
    .size = 0x214;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/31RO0jDUBQ9L6+DUCcdHPykqXZxlIJ08sUl0M3SUbC2my7imoLp7NLg0FlwqMXRWVNXtxYLgkjSqgg6BDo9";
      "aIg3KYoU7XC4kHfP554E5u0lB+qMEHDYoFmxMrbmrNkoZewyswqDMGyoKf7wFwLiR7xn2kkpyHoc6xxW4fs9ncBOBShoUA7O";
      "w7CIhMh7A2xgRuThYg5Vtoij3a4KflgDiiBuYLabDt/rPU7x/Y1lWJ0VwitHy+NC9ldhv1EmF/DxaUjK00kQyL9xRYi/vxtS";
      "ANcXYbgQef2nDYY6wGxGU6O5BXw4lNMjDc015D5p+Jy1oKi9SGdyXwPu06OTrj5bO9VG+lmb9vvE3fYNWY65yg83MG/iLodJ";
      "yHnilxQ9Jxg247wvhrRoP9ZfEvKY7oj6SVFfJYXlhkkhA/OuOXnLE903rTvqIDv2Hv/HKml+AVEc0GwUAgAA"
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
    .size = 0x44;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAAT09/eKy5PzcAt2czLSSYn0IWZBYlFlSCaX0koHqDBggoCg1MTkjPrWoKL+IAQAk109nRAAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0x96c;
    .size = 0x4c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrb2YGBg4ADiKX///78CpK8AaRZGBoaQf///JwD5W4B0CZB+AqQ7gLTC////5wDpEiB9AKQPSL8B0gCM";
      "gBAlTAAAAA=="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0x9b8;
    .size = 0xdc;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiN/8/f/fBCTpyC4HEtMBYot///8bQPWAxByAOAQoZgMVUwDxgbgGKOYB";
      "1sunMJdlHrPTZCa/e3cv88H0VQDxGqAaFqg+ESDuAeIdf/7/14DoE5jLNI8RJL4EiBcA1YLYDM4QcRkgcw8QnwCqT0BSH8p1";
      "7y4fgyM3SAgA3XcbyNwAAAA="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xa94;
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
