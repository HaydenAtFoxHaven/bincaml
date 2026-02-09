memory shared $mem : (bv64 -> bv8);
var $Global_131080_131088: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_uchar : () -> bv8;

prog entry @main_1792;

proc @main_1792
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R1_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, V31_in:bv128, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R1_out:bv64, R29_out:bv64)
  { .name = "main"; .address = 0x700; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x700; .originalLabel = "qA1LACdFTXO7ZP6K2xA6jg=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1792_2" };
    var load11_1: bv64 := $Global_131080_131088:bv64 { .label = "1668_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv64 := zero_extend(56, $__VERIFIER_nondet_uchar());
    var load6_1: bv64 := load le $mem 0x908:bv64 64 { .label = "1812_0_0" };
    var V31_4: bv128 := zero_extend(64, bvand(extract(64, 0, V31_in:bv128), load6_1:bv64)) { .label = "1820_0" };
    var V31_5: bv128 := zero_extend(120, bvadd(bvadd(bvadd(extract(8, 0, V31_4:bv128), extract(16, 8, V31_4:bv128)), bvadd(extract(24, 16, V31_4:bv128), extract(32, 24, V31_4:bv128))), bvadd(bvadd(extract(40, 32, V31_4:bv128), extract(48, 40, V31_4:bv128)), bvadd(extract(56, 48, V31_4:bv128), extract(64, 56, V31_4:bv128))))) { .label = "1824_0" };
    var R1_3: bv64 := zero_extend(32, extract(32, 0, V31_5:bv128)) { .label = "1828_0" };
    goto(%phi_6, %phi_7);
  ];
  block %phi_6 {.originalLabel = "L0xNpZ3VRpKQpan5/V8leQ=="} [
    guard boolnot(eq(extract(32, 0, R1_3:bv64), zero_extend(24, extract(8, 0, R0_2:bv64))));
    var (R0_retval_inlined_6:bv64, R17_7:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_2176 (bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .label = "1852_2" };
    goto(%phi_6_retval_inline);
  ];
  block %phi_7 {.originalLabel = "L0xNpZ3VRpKQpan5/V8leQ=="} [
    guard eq(extract(32, 0, R1_3:bv64), zero_extend(24, extract(8, 0, R0_2:bv64)));
    var load7_1: bv64 := Stack_n16_n8:bv64 { .label = "1844_0_0" };
    var load8_1: bv64 := Stack_n8_0:bv64 { .label = "1844_1_0" };
    var R29_11: bv64 := load7_1:bv64 { .label = "phiback" };
    var R31_10: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_10: bv64 := 0x20008:bv64 { .label = "phiback" };
    var R1_9: bv64 := R1_3:bv64 { .label = "phiback" };
    var R17_9: bv64 := load11_1:bv64 { .label = "phiback" };
    var R0_10: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_8: bv64 := load8_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_6_retval_inline [
    var R29_11: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R31_10: bv64 := bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64) { .label = "phiback" };
    var R16_10: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R1_9: bv64 := 0x8e8:bv64 { .label = "phiback" };
    var R17_9: bv64 := R17_7:bv64 { .label = "phiback" };
    var R0_10: bv64 := 0x900:bv64 { .label = "phiback" };
    var R30_8: bv64 := 0x704:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_8:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_10:bv64) { .comment = "R31 preserved across calls" };
    return (R0_10:bv64, R16_10:bv64, R17_9:bv64, R1_9:bv64, R29_11:bv64);
  ]
];


proc @reach_error_2176
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x880; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x880; .originalLabel = "9HlPHlvJRmWQcuhsUYuBkQ=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2176_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2176_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load13_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0x900:bv64, load13_1:bv64, 0x8e8:bv64, 0x3:bv64, 0x8d8:bv64);
  ]
];




prog entry @main_1792 {
  .symbols = {
    .externalFunctions = [
      { .name = "_ITM_deregisterTMCloneTable"; .offset = 0x1ffc0 };
      { .name = "_ITM_registerTMCloneTable"; .offset = 0x1ffe0 };
      { .name = "__VERIFIER_nondet_uchar"; .offset = 0x20008 };
      { .name = "__assert_fail"; .offset = 0x20028 };
      { .name = "__cxa_finalize"; .offset = 0x1ffc8 };
      { .name = "__cxa_finalize"; .offset = 0x20010 };
      { .name = "__gmon_start__"; .offset = 0x1ffd0 };
      { .name = "__gmon_start__"; .offset = 0x20018 };
      { .name = "__libc_start_main@GLIBC_2.34"; .offset = 0x20000 };
      { .name = "abort"; .offset = 0x20020 }
    ];
    .globals = [
      { .name = "_DYNAMIC"; .address = 0x1fdc8; .size = 0x0 };
      { .name = "_GLOBAL_OFFSET_TABLE_"; .address = 0x1ffb8; .size = 0x0 };
      { .name = "_IO_stdin_used"; .address = 0x8d0; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xa38; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xa3c; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20040; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x8a8; .size = 0xa0 };
      { .name = "_start"; .address = 0x740; .size = 0x1a0 };
      { .name = "main"; .address = 0x700; .size = 0x200 };
      { .name = "reach_error"; .address = 0x880; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x860 ]; [ 0x1fdc0; 0x80c ]; [ 0x1ffd8; 0x700 ]; [ 0x20038; 0x20038 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2WI9PfQ2du1qVzQzaNvQ6ZJXe3vL4YArWIexyQAAAA=" ]
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
      "H4sIAAAAAAAA/2NgwA2YGbgYDNiwiYszGDAwoYjlALEQFjMYgVgBi7gbDvV1QKyERVwWhzm9OMzRwaE+Dod6ANTpsO8IAQAA"
    ]
  };
  {
    .name = ".dynstr";
    .address = 0x3d8;
    .size = 0xc2;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3WMywrCMBBF54cM+ED3lioBuynB7TBNp3UgTSCJIH69o4g7V3Pv5cwBtK7DkTPPUipn1zUhRXY0BAbEeUkR";
      "S6VcEeGD/gGvbW9Ptu0xpjhyxbu/UdadSmF9nkiCtiCD/+oWkqiLfxBOEinIk4GGlCsopJKVWoop6V29XrOH88UeG9yY9eEX";
      "tzt4AWNLn6zCAAAA"
    ]
  };
  {
    .name = ".gnu.version";
    .address = 0x49a;
    .size = 0x16;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgAAEmBkYgZIZjAA/EuxsWAAAA" ]
  };
  {
    .name = ".gnu.version_r";
    .address = 0x4b0;
    .size = 0x30;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NkYGJYxMDAIMAAAdMnTmNjYGBmWAMV2wLmMzFsh8oDAAHegUYwAAAA" ]
  };
  {
    .name = ".rela.dyn";
    .address = 0x4e0;
    .size = 0xc0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/9vxl5EBBJhZwBRDAgeEPoAmzgMVv/EfVZyBHUJZMDChiMP4B6DqGYHiMC0gcAJJnA1J/AKSODuS+AMkcU4k";
      "cQDhJgs3wAAAAA=="
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
    .size = 0x1bc;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3VRMUvDQBh9l3Nr6eLgok1jxV0QpEubipBZcTfW0Z+QwRQEBwcbFF0da2c3QRsnwUUUC4JIW1QEHYKdDnrE";
      "lxQcig6P77j73vu+9057V2daIniJ4xMBNMysyJV3V3R8UM7FJnGxkOvJ+XwFhe06sA74a9oLm2250VkFjsyCfJyBf58n3iRa";
      "PWmrfhHBOzW7QIQvR0m+TRAhZ9wR6f2Ho2zg/CaOpxKtROcvQKABiECwWqwV4LPNPXrUsLqO2qRGJEULhtlJdMb7LeB2drjz";
      "UM3W961h9TBkf5/c5chRtZRr/HK1d5lmMchATZLvGtWSLbCU7vvqKJ/9qf60rY7p44koMA/XEKVBxlbau26Oe3mmv/+8JdDM";
      "XzL3JPtkNli33GJgnRZ5ngtq1N/jHGa1ONpx9F/fvPsBYQ8eV7wBAAA="
    ]
  };
  {
    .name = ".fini";
    .address = 0x8bc;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0x8d0;
    .size = 0x40;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiMD+vNDc+OT+vLLWoODM/L95ILxkszGAAoRgYmVg4BBQcGgBVjiu7QAAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0x910;
    .size = 0x4c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrb2YWBg4ADiD3///+dgZGAw+Pf/fwqQPwFIVwDpA0C6B0j/AdILgHTA////jwDpAiB9A0jPANIfgDQA";
      "n1HBwkwAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0x960;
    .size = 0xdc;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiI/8/f/fBCTpyC4HEtMBYoF///8bQPWAxBxA4kAxG6iYAhCHgDBQzAOs";
      "l09hLss8ZqfJTH737l7mg+mrAOIWoBoWqD4RIO4B4glAMQ2IPoG5TPMYQeJLgHgBUBzEZnCGiMsAmXuA+MGf//8dkNT7ct27";
      "y8fgyA0SAgB6fQJR3AAAAA=="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xa3c;
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
      "H4sIAAAAAAAA/7WQMQ6CQBBFBwRRgU6CqIfwZl7FhI7KeAJKCgrCCSgtLS1pLIyRNWYexdIzzcvbvzuzu45o5dCBNxjB01IZ";
      "4/VKmeHVV08ecGLZw4b8OMlfgzn/WbrqPuv3hZKx0pFv8BaGcAcTsYs28jQ6nzZygVsYwBRefXv94dn3buB6Mv9j9D3j1gEv";
      "OW/w8Z97vCB/457MUz+0w7158AEAAA=="
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
