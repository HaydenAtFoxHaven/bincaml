var $Global_131096_131104: bv64;
var $Global_131104_131112: bv64;
var $Global_131112_131120: bv64;
declare-fun $__VERIFIER_nondet_uint : () -> bv32;

prog entry @main_1856;

proc @main_1856
  (R0_in:bv64, R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R16_in:bv64, R17_in:bv64, R18_in:bv64, R19_in:bv64, R1_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64, R16_out:bv64, R17_out:bv64, R29_out:bv64)
  { .name = "main"; .address = 0x740; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x740; .originalLabel = "U8UoZ9rXS0ePK6kFIl/qiQ=="} [
    var Stack_n32_n24: bv64 := R29_in:bv64 { .label = "1856_1" };
    var Stack_n24_n16: bv64 := R30_in:bv64 { .label = "1856_2" };
    var Stack_n16_n8: bv64 := R19_in:bv64 { .label = "1864_0" };
    var load19_1: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_2: bv32 := $__VERIFIER_nondet_uint();
    var R19_2: bv64 := zero_extend(32, R0_2:bv32) { .label = "1872_0" };
    var load19_2: bv64 := $Global_131112_131120:bv64 { .label = "1732_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var R0_4: bv64 := zero_extend(32, $__VERIFIER_nondet_uint());
    goto(%phi_10, %phi_11);
  ];
  block %main_12 {.address = 0x7b8; .originalLabel = "lyX7lZEaRn6qUCGUSQjBbQ=="} [
    var load11_1: bv64 := Stack_n16_n8:bv64 { .label = "1976_0_0" };
    var load12_1: bv64 := Stack_n32_n24:bv64 { .label = "1984_0_0" };
    var load13_1: bv64 := Stack_n24_n16:bv64 { .label = "1984_1_0" };
    var R29_41: bv64 := load12_1:bv64 { .label = "phiback" };
    var R31_42: bv64 := R31_in:bv64 { .label = "phiback" };
    var R16_44: bv64 := 0x20028:bv64 { .label = "phiback" };
    var R17_41: bv64 := load19_2:bv64 { .label = "phiback" };
    var R0_38: bv64 := 0x0:bv64 { .label = "phiback" };
    var R30_13: bv64 := load13_1:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_20 [
    var R0_28: bv64 := zero_extend(32, bvsub(extract(32, 0, R19_21:bv64), extract(32, 0, bvmul(zero_extend(32, extract(32, 0, R0_22:bv64)), zero_extend(32, extract(32, 0, Cse0__5_10_1:bv64)))))) { .label = "1964_0" };
    goto(%phi_40, %phi_41);
  ];
  block %main_26 [
    goto(%phi_34, %phi_35);
  ];
  block %main_32 {.address = 0x7a0; .originalLabel = "VdnT6JQ/S+2y2NH1fVEmpw=="} [
    goto(%phi_28, %phi_29);
  ];
  block %main_loop1_46 {.address = 0x788; .originalLabel = "jGu0b3CyRdSwECHznKHqFA=="} [
    var R2_12: bv64 := zero_extend(32, bvand(extract(32, 0, Cse0__5_10_1:bv64), extract(32, 0, R1_9:bv64))) { .label = "1928_0" };
    var R1_10: bv64 := zero_extend(32, bvlshr(extract(32, 0, R1_9:bv64), zero_extend(27, extract(5, 0, R0_4:bv64)))) { .label = "1932_0" };
    var R19_14: bv64 := zero_extend(32, bvadd(extract(32, 0, R19_13:bv64), extract(32, 0, R2_12:bv64))) { .label = "1936_0" };
    goto(%phi_18, %phi_19);
  ];
  block %main_loop2_48 {.address = 0x780; .originalLabel = "oHy9p96xSJCRP1HHgcLQWQ=="} [
    ( var R1_9: bv64 := zero_extend(32, extract(32, 0, R19_11:bv64)),
      var R19_13: bv64 := 0x0:bv64 );
    assert eq(R19_13:bv64, 0x0:bv64);
    goto(%main_loop1_46);
  ];
  block %phi_10 {.originalLabel = "S9wt0XGzRkibvyjpPPVlDQ=="} [
    guard bvugt(extract(32, 0, R0_4:bv64), 0x1e:bv32);
    var load7_1: bv64 := $Global_131096_131104:bv64 { .label = "1700_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "abort" };
    goto(%phi_49);
  ];
  block %phi_11 {.originalLabel = "S9wt0XGzRkibvyjpPPVlDQ=="} [
    guard bvule(extract(32, 0, R0_4:bv64), 0x1e:bv32);
    var R3_9: bv32 := bvshl(0x1:bv32, zero_extend(27, extract(5, 0, R0_4:bv64))) { .label = "1892_0" };
    var Cse0__5_10_1: bv64 := zero_extend(32, bvadd(R3_9:bv32, 0xffffffff:bv32)) { .label = "1896_1" };
    goto(%phi_12, %phi_13);
  ];
  block %phi_12 [
    guard eq(R3_9:bv32, 0x1:bv32);
    goto(%main_12);
  ];
  block %phi_13 [
    guard boolnot(eq(R3_9:bv32, 0x1:bv32));
    goto(%phi_14, %phi_15);
  ];
  block %phi_14 [
    guard bvule(extract(32, 0, R19_2:bv64), bvadd(R3_9:bv32, 0xffffffff:bv32));
    var R19_21: bv64 := R19_2:bv64 { .label = "phiback" };
    var R2_19: bv64 := R2_in:bv64 { .label = "phiback" };
    goto(%main_32);
  ];
  block %phi_15 [
    guard bvugt(extract(32, 0, R19_2:bv64), bvadd(R3_9:bv32, 0xffffffff:bv32));
    ( var R19_11: bv64 := R19_2:bv64 );
    goto(%main_loop2_48);
  ];
  block %phi_18 {.originalLabel = "jGu0b3CyRdSwECHznKHqFA=="} [
    guard boolnot(eq(extract(32, 0, R1_10:bv64), 0x0:bv32));
    ( var R1_9: bv64 := R1_10:bv64,
      var R19_13: bv64 := R19_14:bv64 );
    goto(%main_loop1_46);
  ];
  block %phi_19 {.originalLabel = "jGu0b3CyRdSwECHznKHqFA=="} [
    guard eq(extract(32, 0, R1_10:bv64), 0x0:bv32);
    goto(%phi_20, %phi_21);
  ];
  block %phi_20 [
    guard bvult(bvadd(R3_9:bv32, 0xffffffff:bv32), extract(32, 0, R19_14:bv64));
    ( var R19_11: bv64 := R19_14:bv64 );
    goto(%main_loop2_48);
  ];
  block %phi_21 [
    guard bvuge(bvadd(R3_9:bv32, 0xffffffff:bv32), extract(32, 0, R19_14:bv64));
    var R19_21: bv64 := R19_14:bv64 { .label = "phiback" };
    var R2_19: bv64 := R2_12:bv64 { .label = "phiback" };
    goto(%main_32);
  ];
  block %phi_28 {.originalLabel = "VdnT6JQ/S+2y2NH1fVEmpw=="} [
    guard eq(R3_9:bv32, 0x1:bv32);
    var R0_22: bv64 := 0x0:bv64 { .label = "phiback" };
    goto(%main_26);
  ];
  block %phi_29 {.originalLabel = "VdnT6JQ/S+2y2NH1fVEmpw=="} [
    guard boolnot(eq(R3_9:bv32, 0x1:bv32));
    var R0_18: bv64 := zero_extend(32, extract(32, 0, bvsdiv(zero_extend(32, extract(32, 0, R19_21:bv64)), zero_extend(32, extract(32, 0, Cse0__5_10_1:bv64))))) { .label = "1952_0" };
    var R0_22: bv64 := R0_18:bv64 { .label = "phiback" };
    goto(%main_26);
  ];
  block %phi_34 [
    guard boolnot(eq(bvadd(R3_9:bv32, 0xffffffff:bv32), extract(32, 0, R19_21:bv64)));
    var R1_17: bv64 := zero_extend(32, extract(32, 0, R19_21:bv64)) { .label = "phiback" };
    goto(%main_20);
  ];
  block %phi_35 [
    guard eq(bvadd(R3_9:bv32, 0xffffffff:bv32), extract(32, 0, R19_21:bv64));
    var R1_17: bv64 := 0x0:bv64 { .label = "phiback" };
    goto(%main_20);
  ];
  block %phi_40 [
    guard boolnot(eq(extract(32, 0, R0_28:bv64), extract(32, 0, R1_17:bv64)));
    var (R0_retval_inlined_6:bv64, R17_33:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_1792 (bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64), 0x704:bv64, bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64)) { .label = "1996_2" };
    goto(%phi_40_retval_inline);
  ];
  block %phi_41 [
    guard eq(extract(32, 0, R0_28:bv64), extract(32, 0, R1_17:bv64));
    goto(%main_12);
  ];
  block %phi_49 [
    var R29_41: bv64 := R29_39:bv64 { .label = "phiback" };
    var R31_42: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R16_44: bv64 := R16_42:bv64 { .label = "phiback" };
    var R17_41: bv64 := R17_39:bv64 { .label = "phiback" };
    var R0_38: bv64 := R0_36:bv64 { .label = "phiback" };
    var R30_13: bv64 := 0x704:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_40_retval_inline [
    var R29_41: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffd0:bv64) { .label = "phiback" };
    var R31_42: bv64 := bvadd(R31_in:bv64, 0xffffffffffffffe0:bv64) { .label = "phiback" };
    var R16_44: bv64 := 0x20020:bv64 { .label = "phiback" };
    var R17_41: bv64 := R17_33:bv64 { .label = "phiback" };
    var R0_38: bv64 := 0x9c0:bv64 { .label = "phiback" };
    var R30_13: bv64 := 0x704:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_return [
    assert eq(R30_in:bv64, R30_13:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, R31_42:bv64) { .comment = "R31 preserved across calls" };
    return (R0_38:bv64, R16_44:bv64, R17_41:bv64, R29_41:bv64);
  ]
];


proc @reach_error_1792
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x700; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x700; .originalLabel = "/NhByeSGTXqhf/0IoS+OtA=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1792_2" };
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 = R30_in" };
    var load15_1: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x728:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0x9c0:bv64, load15_1:bv64, 0x990:bv64, 0xf:bv64, 0x9c8:bv64);
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
      { .name = "_IO_stdin_used"; .address = 0x988; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xb1c; .size = 0x0 };
      { .name = "__PRETTY_FUNCTION__.0"; .address = 0x9c8; .size = 0x60 };
      { .name = "__abi_tag"; .address = 0xb20; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20040; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x960; .size = 0xa0 };
      { .name = "_start"; .address = 0x800; .size = 0x1a0 };
      { .name = "assume_abort_if_not"; .address = 0x940; .size = 0xa0 };
      { .name = "main"; .address = 0x740; .size = 0x480 };
      { .name = "reach_error"; .address = 0x700; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x920 ]; [ 0x1fdc0; 0x8cc ]; [ 0x1ffd8; 0x740 ]; [ 0x20038; 0x20038 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2XIO/2sfOPCpn6FhTy3O1Zpn7p55ZUaAJRCWpQkAAAA" ]
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
      "H4sIAAAAAAAA/9vxl5EBBJhZwBSDAieEPoAmfoYDQt/4jyruwA6hLRiYUMRh/ANQ9YxAcagUGJxAEmdFEr+AJM6GJP4ASZwD";
      "SRwANRI7HMAAAAA="
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
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBPrGBim/K0+uOIAc/w1AE4xqyQYAAAA" ]
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
    .size = 0x274;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/31RPUjDUBD+Xl6n1skOQvxpYsVCZ0U6mbpkL9lNWwelU3EROjTOLg0KLoK42c7F0UYd1UWxICq09QdBh0Kn";
      "Bw3xEqlI0Q4f93h333d337mlRpUDFUZwOWxQzCsJW9Xm6Z2wO8zKPHvefkzhd3/BLZ1WfV4vAvFEdT2O5INfv4XiOocRh5XJ";
      "K46cD6FoSjDKEi9sMBgDfptHk1GqyYGF1TlH3pSkyJHnLZYRLcQ9zzDDF7L/zo4fyrjikzGwwhlg9CKaAPHc0vmxw1ebJ9Tz";
      "esScozAN62aG8MpRa3NNdOKw32inFtDFpy445UIEm/QPCMH/uy40oL7neRN+//+0wVABmM0oqhSXgQ+H5m+ThtrSRZY0upzV";
      "IMWavs5wvQpczvbLt+mx7R21n96l3esd4q50dZELuNIP9/ctosQ3pXRKY1gK5n3RhUX1gf6UJnK0xz1BIQ9NiaV8Pwde/p7/";
      "kfYb5R15sPDduxH0NoZuMJxfo/wXQTicpHQCAAA="
    ]
  };
  {
    .name = ".fini";
    .address = 0x974;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0x988;
    .size = 0x4c;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAAT09/eKy5PzcAt2czLSSYn0ImZufUppTWqxrhGDpJYPVGzBAQFFqYnJGfGpRUX4RAwBT83NVTAAA";
      "AA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0x9d4;
    .size = 0x54;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrYOYGBg4ARinb///38B0jlAWoURyP/3/38GkN8DpGuA9B4gPQFI/wDSS4C0z////0+A1APpOyB1QJoH";
      "qA8A2IIOW1QAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0xa28;
    .size = 0xf8;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiPf8/f/fBCTpyC4HEtMBYo5///8bQPWAxByAWAUoZgMVUwDiECD2AYp5";
      "gPXyKcxlmcfsNJnJ797dy3wwfRVAXANUwwLVJwLEPUDcARQDsRmc+QTmMs1jBLGXALHBn///NSDmwcX3gMxBUw+y/wrIXUD1";
      "E1Dtj+MCO8CRGyQMAINS5ED4AAAA"
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
    .bytes = [ "H4sIAAAAAAAA/1PgZAADAOz4zAkIAAAA" ]
  };
  {
    .name = ".fini_array";
    .address = 0x1fdc0;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/zvDwQAGAHbDxHsIAAAA" ]
  };
  {
    .name = ".dynamic";
    .address = 0x1fdc8;
    .size = 0x1f0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/7XQPRKCMBCG4UV+BH86HAQ9hDez8SCOpZXegJISb0BpaUlJQ8E4EobZlyL0bvPMl02yEEe0bujgEzd4CtQt";
      "+RKpKbn46ckDOcQMS/rHWb/tzXk0X2j2WX+7KmOlor8iv3CNe9yJXVwjtdH5XCNXjHGJCT58e/3j2d9dYjSb/zX6P9PWnpxz";
      "3pCnd27Id/od2ZP/1ACE0Eke8AEAAA=="
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
