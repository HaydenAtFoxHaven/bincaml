var $Global_131104_131112: bv64;

prog entry @main_1664;

proc @main_1664
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R1_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R1_out:bv64, R2_out:bv64)
  { .name = "main"; .address = 0x680; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x680; .originalLabel = "ZHuKZJ+uR3iBfnRvw0G7LQ=="} [
    ( var R1_3: bv64 := 0x12:bv64,
      var R0_3: bv64 := 0x3f:bv64 );
    goto(%main_loop2_54);
  ];
  block %main_6 {.address = 0x6d4; .originalLabel = "ovfjddq/RJWtolx0IlWOog=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1748_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1748_2" };
    var (R0_retval_inlined_6:bv64, R17_33:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_2112 (bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), 0x68c:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .label = "1756_2" };
    goto(%main_6_retval_inline);
  ];
  block %main_22 [
    var R1_28: bv64 := bvsub(R2_10:bv64, extract(64, 0, bvmul(zero_extend(64, R1_27:bv64), zero_extend(64, R0_12:bv64)))) { .label = "1724_0" };
    goto(%phi_30, %phi_31);
  ];
  block %main_32 [
    var R1_20: bv64 := bvsub(R2_2:bv64, extract(64, 0, bvmul(zero_extend(64, R1_19:bv64), zero_extend(64, R0_12:bv64)))) { .label = "1708_0" };
    goto(%phi_22, %phi_23);
  ];
  block %main_loop0_42 {.address = 0x69c; .originalLabel = "9dbvwCbSQ4mFUKGe0R/pfQ=="} [
    var Cse0__5_6_1: bv64 := bvadd(R1_3:bv64, bvnot(R0_12:bv64)) { .label = "1692_1" };
    goto(%phi_14, %phi_15);
  ];
  block %main_loop1_50 {.address = 0x690; .originalLabel = "RrXnCMdvRmWdUEfr7mKWfg=="} [
    var R0_7: bv64 := bvadd(R0_6:bv64, bvneg(R1_3:bv64)) { .label = "1680_0" };
    goto(%phi_7, %phi_8);
  ];
  block %main_loop2_54 {.address = 0x688; .originalLabel = "A4mIPRvPQXO5Dd9IHKjVmw=="} [
    goto(%phi_4, %phi_5);
  ];
  block %phi_4 {.originalLabel = "A4mIPRvPQXO5Dd9IHKjVmw=="} [
    guard bvsge(R1_3:bv64, R0_3:bv64);
    var R0_12: bv64 := R0_3:bv64 { .label = "phiback" };
    goto(%main_loop0_42);
  ];
  block %phi_5 {.originalLabel = "A4mIPRvPQXO5Dd9IHKjVmw=="} [
    guard bvslt(R1_3:bv64, R0_3:bv64);
    ( var R0_6: bv64 := R0_3:bv64 );
    goto(%main_loop1_50);
  ];
  block %phi_7 {.originalLabel = "RrXnCMdvRmWdUEfr7mKWfg=="} [
    guard bvslt(R1_3:bv64, R0_7:bv64);
    ( var R0_6: bv64 := R0_7:bv64 );
    goto(%main_loop1_50);
  ];
  block %phi_8 {.originalLabel = "RrXnCMdvRmWdUEfr7mKWfg=="} [
    guard bvsge(R1_3:bv64, R0_7:bv64);
    var R0_12: bv64 := R0_7:bv64 { .label = "phiback" };
    goto(%main_loop0_42);
  ];
  block %phi_14 {.originalLabel = "9dbvwCbSQ4mFUKGe0R/pfQ=="} [
    guard boolnot(eq(R1_3:bv64, R0_12:bv64));
    ( var R1_3: bv64 := bvadd(Cse0__5_6_1:bv64, 0x1:bv64),
      var R0_3: bv64 := R0_12:bv64 );
    goto(%main_loop2_54);
  ];
  block %phi_15 {.originalLabel = "9dbvwCbSQ4mFUKGe0R/pfQ=="} [
    guard eq(R1_3:bv64, R0_12:bv64);
    var R2_2: bv64 := 0x3f:bv64 { .label = "1700_0" };
    goto(%phi_16, %phi_17);
  ];
  block %phi_16 [
    guard eq(R0_12:bv64, 0x0:bv64);
    var R1_19: bv64 := 0x0:bv64 { .label = "phiback" };
    goto(%main_32);
  ];
  block %phi_17 [
    guard boolnot(eq(R0_12:bv64, 0x0:bv64));
    var R1_15: bv64 := extract(64, 0, bvsdiv(zero_extend(64, R2_2:bv64), zero_extend(64, R0_12:bv64))) { .label = "1704_0" };
    var R1_19: bv64 := R1_15:bv64 { .label = "phiback" };
    goto(%main_32);
  ];
  block %phi_22 [
    guard boolnot(eq(R1_20:bv64, 0x0:bv64));
    var R1_37: bv64 := R1_20:bv64 { .label = "phiback" };
    var R2_24: bv64 := R2_2:bv64 { .label = "phiback" };
    goto(%main_6);
  ];
  block %phi_23 [
    guard eq(R1_20:bv64, 0x0:bv64);
    var R2_10: bv64 := 0x12:bv64 { .label = "1716_0" };
    goto(%phi_24, %phi_25);
  ];
  block %phi_24 [
    guard eq(R0_12:bv64, 0x0:bv64);
    var R1_27: bv64 := 0x0:bv64 { .label = "phiback" };
    goto(%main_22);
  ];
  block %phi_25 [
    guard boolnot(eq(R0_12:bv64, 0x0:bv64));
    var R1_23: bv64 := extract(64, 0, bvsdiv(zero_extend(64, R2_10:bv64), zero_extend(64, R0_12:bv64))) { .label = "1720_0" };
    var R1_27: bv64 := R1_23:bv64 { .label = "phiback" };
    goto(%main_22);
  ];
  block %phi_30 [
    guard boolnot(eq(R1_28:bv64, 0x0:bv64));
    var R1_37: bv64 := R1_28:bv64 { .label = "phiback" };
    var R2_24: bv64 := R2_10:bv64 { .label = "phiback" };
    goto(%main_6);
  ];
  block %phi_31 [
    guard eq(R1_28:bv64, 0x0:bv64);
    goto(%phi_32, %phi_33);
  ];
  block %phi_32 [
    guard boolnot(eq(R0_12:bv64, 0x9:bv64));
    var R1_37: bv64 := R1_28:bv64 { .label = "phiback" };
    var R2_24: bv64 := R2_10:bv64 { .label = "phiback" };
    goto(%main_6);
  ];
  block %phi_33 [
    guard eq(R0_12:bv64, 0x9:bv64);
    var R1_40: bv64 := R1_28:bv64 { .label = "phiback" };
    var R0_39: bv64 := 0x0:bv64 { .label = "phiback" };
    var R2_27: bv64 := R2_10:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_6_retval_inline [
    var R1_40: bv64 := 0x8f0:bv64 { .label = "phiback" };
    var R0_39: bv64 := 0x8f8:bv64 { .label = "phiback" };
    var R2_27: bv64 := 0x3:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_return [
    return (R0_39:bv64, R1_40:bv64, R2_27:bv64);
  ]
];


proc @reach_error_2112
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x840; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x840; .originalLabel = "h0TocFcdSzCh6kFkDvM26A=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2112_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2112_2" };
    assert eq(R30_in:bv64, 0x6a8:bv64) { .comment = "R30 = R30_in" };
    var load15_1: bv64 := $Global_131104_131112:bv64 { .label = "1636_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x6a8:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0x8f8:bv64, load15_1:bv64, 0x8f0:bv64, 0x3:bv64, 0x8e0:bv64);
  ]
];




prog entry @main_1664 {
  .symbols = {
    .externalFunctions = [
      { .name = "_ITM_deregisterTMCloneTable"; .offset = 0x1ffc0 };
      { .name = "_ITM_registerTMCloneTable"; .offset = 0x1ffe0 };
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
      { .name = "_IO_stdin_used"; .address = 0x8d8; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xa34; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xa38; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20038; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x868; .size = 0xa0 };
      { .name = "_start"; .address = 0x700; .size = 0x1a0 };
      { .name = "gcd_test"; .address = 0x880; .size = 0x200 };
      { .name = "main"; .address = 0x680; .size = 0x300 };
      { .name = "reach_error"; .address = 0x840; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x820 ]; [ 0x1fdc0; 0x7cc ]; [ 0x1ffd8; 0x680 ]; [ 0x20030; 0x20030 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2XIvM6675+4tP569p1bpLp9uG5+WpYIAAt2o2skAAAA" ]
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
    .size = 0xf0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2NgwA2YGbgYXrBiExdn0GBgQhELAWIhLGYwArECFvE0IFbCIi6LQ30pDvN1cKh3w6EeAD5w0D/wAAAA"
    ]
  };
  {
    .name = ".dynstr";
    .address = 0x3c0;
    .size = 0xaa;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3WLTQsCMQxE84cs+IHe3YMsuLfeQ9rNLoFsCk0P4q+3injzNPOGN4BjnHDmyqt44xqnQYtxpKQMiOtWDL1R";
      "bYjwUf+I5M5dWki0k0rK39tGYn3JD8JFjFSeDJRKbdAlK7abuXnw8sbcM5zhdh+vAx7C/vKrxxO8AI9z/PGqAAAA"
    ]
  };
  {
    .name = ".gnu.version";
    .address = 0x46a;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgAAEmBkYGZjgGANruhkcUAAAA" ]
  };
  {
    .name = ".gnu.version_r";
    .address = 0x480;
    .size = 0x30;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NkYGLoYmBgEGCAgOkTp7ExMDAzTIGKbQHzmRjmQ+UBzcDC8DAAAAA=" ]
  };
  {
    .name = ".rela.dyn";
    .address = 0x4b0;
    .size = 0xc0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/9vxl5EBBJhZwBSDAgeEPoAmfoYdQt/4jyrewAahDRiYUMRh/ANQ9YxAcagUGJxAEmdFEr+AJM6GJP4ASZwD";
      "SRwADIPMfMAAAAA="
    ]
  };
  {
    .name = ".rela.plt";
    .address = 0x570;
    .size = 0x78;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgYGIAASYWBgZmBgTgQBJnRRIXQBJnQxKXQBJnRxJXQBLnRBIHALXel4N4AAAA" ]
  };
  {
    .name = ".init";
    .address = 0x5e8;
    .size = 0x18;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBMDGBim/K0+uOIAc/w1AKg5q9UYAAAA" ]
  };
  {
    .name = ".plt";
    .address = 0x600;
    .size = 0x70;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA//tQvX/lBwaGD4L/3H8KPLKfqMAkf01egfkqDAswMkwQZHL4KcDEAJYD89mAfCUkPheQ74TE5wPyk5D4QkB+";
      "E4QPAHQ88URwAAAA"
    ]
  };
  {
    .name = ".text";
    .address = 0x680;
    .size = 0x240;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/4VSMUvDQBh9SQSFujnoomlaf4IgnUy6ZJcuTtb6Mzo03URRGhQEnYQO2rkd1egk1KliweKQBhWhDq2dDhri";
      "uyAqBXX4eJfL99597935k07LUp3WCtDbBnKA0pTrZhTlDKJFDGTPlHdkbOHYUNDIqt/fJ0BDX8RgI+Y6q5623g6Ll2ehBncN";
      "ONCT2v1/NQ+ntcB61lDraqYI0nBfyPeBPt5sofHfBOs8ig5vWPH+qy1MoO5F0aw88zdtKKjAh6sQDaL05nHWLjUM3xacu97X";
      "lBpUvS11xvuZQTM1Kt1Z0+UdY2TtX7E/IDfbt0Uh5qpf3LB4EfseJiBmyM8HZsZUsBzP+2QLh/2x/pwp9ujjgZVkZvkAmWHC";
      "FGHx+nTcyyP9/ZWdzFoDKgpLng3ippN2DS/twk+7BeqXeA6zWvp5N+/ck3zmMUhVyx2dmFc4X9Xp0Htdh9rbje9Ubcr1Ld9B";
      "9vM9SB2fviV+AMSGbYpAAgAA"
    ]
  };
  {
    .name = ".fini";
    .address = 0x8c0;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0x8d8;
    .size = 0x22;
    .readOnly = true;
    .bytes = [ "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiMD89OSXeRC+ZwYABAA5XvDUiAAAA" ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0x8fc;
    .size = 0x54;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrYOYGBg4ATilr///yswMjCw/Pv/PwPITwHSNUB6CpCeAKQvAOklQFrl////J4C0C5C+A6RzgPQXkH4g";
      "zQPUDwDAT8bPVAAAAA=="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0x950;
    .size = 0xe8;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiKf8/f/fBCTpyC4HEtMB4gdAMQOoHpCYAxD/AYrZQMUUgDgEiFX+/f/v";
      "AdbLpzCXZR6z02Qmv3t3L/PB9FWA1AHVsED1iQBxDxAnAMU0IPoE5jLNYwSJLwHiAqA4iM3gDBEHmbEHKu6AZMYFII758/9/";
      "AkggDKIWxAQAQrWTE+gAAAA="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xa38;
    .size = 0x20;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAGJGIHb3C2UAAWYgZmeAAAA9kbzyIAAAAA==" ]
  };
  {
    .name = ".init_array";
    .address = 0x1fdb8;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/1PgYAADAFjzu68IAAAA" ]
  };
  {
    .name = ".fini_array";
    .address = 0x1fdc0;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/zvDzgAGAJ+zjI0IAAAA" ]
  };
  {
    .name = ".dynamic";
    .address = 0x1fdc8;
    .size = 0x1f0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/7WQPRKCMBBGFyH+oHY6CnhCGyidsbH2KFaUlhzBY1jSUDiMhHH2bRF6t3nz8m2ySSLRusII3uEGvp1yizdL";
      "ZYY/v7qzwIklt37y0yTvBl/+WM/UnfXHyjn+Ik/xB1zDI9xLWLHd3+t8jpEL3MEFPMDKhet1Et67gavJ/N7re6x1wG/s97j9";
      "c4ufyT94Iv+pESzKj/7wAQAA"
    ]
  };
  {
    .name = ".got";
    .address = 0x1ffb8;
    .size = 0x30;
    .readOnly = true;
    .bytes = [ "H4sIAAAAAAAA/zvxl5EBH2hgQ+UDAOISXK8wAAAA" ]
  };
  {
    .name = ".got.plt";
    .address = 0x1ffe8;
    .size = 0x40;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgwAHYiKMB1b16g0AAAAA=" ]
  };
  {
    .name = ".data";
    .address = 0x20028;
    .size = 0x10;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NggAADBiYwDQAjub4kEAAAAA==" ]
  };
  {
    .name = ".bss";
    .address = 0x20038;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NggAAAad8iZQgAAAA=" ]
  }
]
} ;
