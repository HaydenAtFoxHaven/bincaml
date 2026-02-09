var $Global_131088_131096: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_char : () -> bv8;

prog entry @main_1792;

proc @main_1792
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R19_in:bv64, R1_in:bv64, R20_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R29_out:bv64, R3_out:bv64)
  { .name = "main"; .address = 0x700; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x700; .originalLabel = "/1jeF2KVTJi9ztYgfdzt6g=="} [
    var Stack_n32_n24: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n24_n16: bv64 := R30_in:bv64 { .label = "1792_2" };
    var Stack_n16_n8: bv64 := R19_in:bv64 { .label = "1800_1" };
    var Stack_n8_0: bv64 := R20_in:bv64 { .label = "1800_2" };
    var load16_1: bv64 := $Global_131088_131096:bv64 { .label = "1684_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv8 := 0x1;
    var R20_2: bv64 := zero_extend(56, R0_2:bv8) { .label = "1808_0" };
    var load16_2: bv64 := $Global_131088_131096:bv64 { .label = "1684_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv8 := 0x6;
    var R3_2: bv64 := zero_extend(56, R0_4:bv8) { .label = "1816_0" };
    var R0_6: bv64 := zero_extend(32, sign_extend(24, R0_4:bv8)) { .label = "1820_0" };
    goto(%phi_9, %phi_10);
  ];
  block %main_4 {.address = 0x75c; .originalLabel = "qzXzbnweSZ2OkL7G9ny2iQ=="} [
    var load3_1: bv64 := Stack_n16_n8:bv64 { .label = "1884_1_0" };
    var load4_1: bv64 := Stack_n8_0:bv64 { .label = "1884_2_0" };
    var load5_1: bv64 := Stack_n32_n24:bv64 { .label = "1892_0_0" };
    var load6_1: bv64 := Stack_n24_n16:bv64 { .label = "1892_1_0" };
    var R29_35: bv64 := load5_1:bv64 { .label = "phiback" };
    var R31_38: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_38: bv64 := 0x20010:bv64 { .label = "phiback" };
    var R3_31: bv64 := R3_29:bv64 { .label = "phiback" };
    var R17_36: bv64 := load16_2:bv64 { .label = "phiback" };
    var R0_35: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_10: bv64 := load6_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_loop0_20 [
    var R2_29: bv64 := zero_extend(32, bvsub(extract(32, 0, R1_16:bv64), extract(32, 0, bvmul(zero_extend(32, extract(32, 0, R2_28:bv64)), zero_extend(32, extract(32, 0, R3_13:bv64)))))) { .label = "1860_0" };
    var R1_22: bv64 := zero_extend(32, extract(32, 0, R3_13:bv64)) { .label = "1864_0" };
    var R3_19: bv64 := zero_extend(32, sign_extend(24, extract(8, 0, R2_29:bv64))) { .label = "1868_0" };
    goto(%phi_32, %phi_33);
  ];
  block %main_loop1_26 {.address = 0x740; .originalLabel = "ddq733EGQFWwtLgGwEDBmA=="} [
    goto(%phi_26, %phi_27);
  ];
  block %main_28 {.address = 0x73c; .originalLabel = "4DaflJHkSMSb4/tzZudHuw=="} [
    ( var R1_16: bv64 := R1_15:bv64,
      var R3_13: bv64 := zero_extend(32, extract(32, 0, R0_6:bv64)),
      var R2_22: bv64 := R2_14:bv64 );
    goto(%main_loop1_26);
  ];
  block %main_40 [
    var R2_14: bv64 := zero_extend(32, bvsub(extract(32, 0, R1_2:bv64), extract(32, 0, bvmul(zero_extend(32, extract(32, 0, R2_13:bv64)), zero_extend(32, extract(32, 0, R3_2:bv64)))))) { .label = "1840_0" };
    goto(%phi_17, %phi_18);
  ];
  block %phi_9 {.originalLabel = "+ZB10e31R3yfiySs+oyfpQ=="} [
    guard bvsle(extract(32, 0, R0_6:bv64), 0x0:bv32);
    var R3_29: bv64 := R3_2:bv64 { .label = "phiback" };
    goto(%main_4);
  ];
  block %phi_10 {.originalLabel = "+ZB10e31R3yfiySs+oyfpQ=="} [
    guard bvsgt(extract(32, 0, R0_6:bv64), 0x0:bv32);
    var R1_2: bv64 := zero_extend(32, sign_extend(24, extract(8, 0, R20_2:bv64))) { .label = "1832_0" };
    goto(%phi_11, %phi_12);
  ];
  block %phi_11 [
    guard eq(extract(32, 0, R3_2:bv64), 0x0:bv32);
    var R2_13: bv64 := 0x0:bv64 { .label = "phiback" };
    goto(%main_40);
  ];
  block %phi_12 [
    guard boolnot(eq(extract(32, 0, R3_2:bv64), 0x0:bv32));
    var R2_13: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%main_40);
  ];
  block %phi_17 [
    guard boolnot(eq(extract(32, 0, R2_14:bv64), 0x0:bv32));
    var R3_29: bv64 := R3_2:bv64 { .label = "phiback" };
    goto(%main_4);
  ];
  block %phi_18 [
    guard eq(extract(32, 0, R2_14:bv64), 0x0:bv32);
    goto(%phi_19, %phi_20);
  ];
  block %phi_19 [
    guard bvslt(extract(32, 0, R1_2:bv64), 0x0:bv32);
    var R1_15: bv64 := zero_extend(32, sign_extend(24, extract(8, 0, bvneg(extract(32, 0, R20_2:bv64))))) { .label = "phiback" };
    goto(%main_28);
  ];
  block %phi_20 [
    guard bvsge(extract(32, 0, R1_2:bv64), 0x0:bv32);
    var R1_15: bv64 := R1_2:bv64 { .label = "phiback" };
    goto(%main_28);
  ];
  block %phi_26 {.originalLabel = "ddq733EGQFWwtLgGwEDBmA=="} [
    guard eq(extract(32, 0, R3_13:bv64), 0x0:bv32);
    var R2_28: bv64 := 0x0:bv64 { .label = "phiback" };
    goto(%main_loop0_20);
  ];
  block %phi_27 {.originalLabel = "ddq733EGQFWwtLgGwEDBmA=="} [
    guard boolnot(eq(extract(32, 0, R3_13:bv64), 0x0:bv32));
    var R2_28: bv64 := R2_22:bv64 { .label = "phiback" };
    goto(%main_loop0_20);
  ];
  block %phi_32 [
    guard boolnot(eq(extract(32, 0, R2_29:bv64), 0x0:bv32));
    ( var R1_16: bv64 := R1_22:bv64,
      var R3_13: bv64 := R3_19:bv64,
      var R2_22: bv64 := R2_29:bv64 );
    goto(%main_loop1_26);
  ];
  block %phi_33 [
    guard eq(extract(32, 0, R2_29:bv64), 0x0:bv32);
    goto(%phi_34, %phi_35);
  ];
  block %phi_34 [
    guard boolnot(eq(extract(32, 0, R0_6:bv64), extract(32, 0, R1_22:bv64)));
    var R30_6: bv64 := 0x704:bv64 { .label = "1912_0" };
    var (R0_retval_inlined_6:bv64, R17_30:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_2240 (bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64)) { .label = "1912_2" };
    goto(%phi_34_retval_inline);
  ];
  block %phi_35 [
    guard eq(extract(32, 0, R0_6:bv64), extract(32, 0, R1_22:bv64));
    var R3_29: bv64 := R3_19:bv64 { .label = "phiback" };
    goto(%main_4);
  ];
  block %phi_34_retval_inline [
    var R29_35: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64) { .label = "phiback" };
    var R31_38: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R16_38: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R3_31: bv64 := 0x978:bv64 { .label = "phiback" };
    var R17_36: bv64 := R17_30:bv64 { .label = "phiback" };
    var R0_35: bv64 := 0x990:bv64 { .label = "phiback" };
    var R30_10: bv64 := R30_6:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_10:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_38:bv64) { .comment = "R31 preserved across calls" };
    return (R0_35:bv64, R16_38:bv64, R17_36:bv64, R29_35:bv64, R3_31:bv64);
  ]
];


proc @reach_error_2240
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x8c0; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x8c0; .originalLabel = "GIUUMDoFR22/yQ/FpKVj6Q=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2240_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2240_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load9_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0x990:bv64, load9_1:bv64, 0x988:bv64, 0x3:bv64, 0x978:bv64);
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
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2Vo6ZHed2gZk9DyDbc8dsufi1fdt0QBALWM/N0kAAAA" ]
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
      "H4sIAAAAAAAA/3VRO0wbQRScvUdnVxgJyXawDwSFayzLVe6O4gp3QM8nJRUVhQuOKF0anxLJdbqYKpFSpAoGSkSTCCQkJHxO";
      "gpCgsDAFK3G5zF7iKCJKMXqr3Tez8+bFzU+dWBAOl1QnSpL2RBHjF6zCiiJyJWDzWGF5Zwq56exh3nshBU+h+kbd174KKqO7";
      "SKSywP7nSVItQW0ocoZLbgcIFuPmwduurJzeyUTD6NwmyeQi8LpUlhODJwg+TxHfBbuROLo/g/CSnnrAADe+Fr6NEe/pq0uk";
      "91e+doAPH6lltEdajwGFFqBC+mnZrE+B6y6wHFHD7vl6jRoDUbuwSqdG53G/DRxNP2x/cbM7L+0H99U++/vkegNfr6dc6w83";
      "HmWZgc6Rv2q5dUehlvr95uuA/al+0dHMqX1GlJnPqqXqw4yjRzn97f+c8/1vNoO4udcRoKUI8zdYn/VmQ7s8F8KZC9epv8V/";
      "mNX8L497qUfuoJ3mw53ZRF/QMLv2eHbeBXnF/XLWeSu7n/cCVeiJqri/92t0IlENw/vn/UdSvafnn0/gVwlYAgAA"
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
    .bytes = [ "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiMD89OSXeUC+ZwYABAL3GcWUiAAAA" ]
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
      "/P9fg2r3FMZwLqD1V/gYHLnBagHqhYbq+AAAAA=="
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
