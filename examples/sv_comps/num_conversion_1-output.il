memory shared $mem : (bv64 -> bv8);
var $Global_131104_131112: bv64;

prog entry @main_1664;

proc @main_1664
  (R0_in:bv64, R16_in:bv64, R17_in:bv64, R1_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, _PC_in:bv64)
    -> (R0_out:bv64)
  { .name = "main"; .address = 0x680; .returnBlock = "main_return" }
[
  block %main_entry {.address = 0x680; .originalLabel = "+bIQolDTSZCMdfosvhtMOQ=="} [
    var load7_1: bv64 := load le $mem 0x888:bv64 64 { .label = "1668_0_0" };
    var V31_2: bv128 := zero_extend(120, bvadd(bvadd(bvadd(extract(8, 0, load7_1:bv64), extract(16, 8, load7_1:bv64)), bvadd(extract(24, 16, load7_1:bv64), extract(32, 24, load7_1:bv64))), bvadd(bvadd(extract(40, 32, load7_1:bv64), extract(48, 40, load7_1:bv64)), bvadd(extract(56, 48, load7_1:bv64), extract(64, 56, load7_1:bv64))))) { .label = "1672_0" };
    var R0_3: bv64 := zero_extend(32, extract(32, 0, V31_2:bv128)) { .label = "1676_0" };
    goto(%phi_3, %phi_4);
  ];
  block %phi_3 {.originalLabel = "+bIQolDTSZCMdfosvhtMOQ=="} [
    guard boolnot(eq(extract(32, 0, R0_3:bv64), 0x25:bv32));
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1696_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1696_2" };
    var (R0_retval_inlined_6:bv64, R17_4:bv64, R1_retval_inlined_8:bv64, R2_retval_inlined_10:bv64, R3_retval_inlined_11:bv64) := call @reach_error_2048 (bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64), 0x68c:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .label = "1704_2" };
    goto(%phi_3_retval_inline);
  ];
  block %phi_4 {.originalLabel = "+bIQolDTSZCMdfosvhtMOQ=="} [
    guard eq(extract(32, 0, R0_3:bv64), 0x25:bv32);
    var R0_10: bv64 := 0x0:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %phi_3_retval_inline [
    var R0_10: bv64 := 0x880:bv64 { .label = "phiback" };
    goto(%main_return);
  ];
  block %main_return [
    return (R0_10:bv64);
  ]
];


proc @reach_error_2048
  (R29_in:bv64, R30_in:bv64, R31_in:bv64) -> (R0_out:bv64, R17_out:bv64, R1_out:bv64, R2_out:bv64, R3_out:bv64)
  { .name = "reach_error"; .address = 0x800; .returnBlock = "reach_error_return" }
[
  block %reach_error_entry {.address = 0x800; .originalLabel = "2JS8FyfaRceElW2hIPB/gg=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "2048_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "2048_2" };
    assert eq(R30_in:bv64, 0x6a8:bv64) { .comment = "R30 = R30_in" };
    var load17_1: bv64 := $Global_131104_131112:bv64 { .label = "1636_0_0" };
    assert true { .comment = "R30 = R30_in" };
    assert false { .comment = "call __assert_fail " };
    goto(%reach_error_return);
  ];
  block %reach_error_return [
    assert eq(R30_in:bv64, 0x6a8:bv64) { .comment = "R30 preserved across calls" };
    assert eq(R31_in:bv64, bvadd(R31_in:bv64, 0xfffffffffffffff0:bv64)) { .comment = "R31 preserved across calls" };
    return (0x880:bv64, load17_1:bv64, 0x868:bv64, 0x3:bv64, 0x858:bv64);
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
      { .name = "_IO_stdin_used"; .address = 0x850; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0x9b0; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0x9b4; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20038; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x828; .size = 0xa0 };
      { .name = "_start"; .address = 0x6c0; .size = 0x1a0 };
      { .name = "main"; .address = 0x680; .size = 0x160 };
      { .name = "reach_error"; .address = 0x800; .size = 0x140 }
    ];
    .globalOffsets = [ [ 0x1fdb8; 0x7e0 ]; [ 0x1fdc0; 0x78c ]; [ 0x1ffd8; 0x680 ]; [ 0x20030; 0x20030 ] ]
  };
  .initial_memory = [
  {
    .name = ".note.gnu.build-id";
    .address = 0x270;
    .size = 0x24;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2Xwn+7cvUD3vnjWM96lKaVvquSkJnEAAOx31rgkAAAA" ]
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
      "H4sIAAAAAAAA/9vxl5EBBJhZwBTDA3YIfQBNvAcqfuM/qngDG4Q2YGBCEYfxD0DVMwLFoVJgcAJJnBVJ/AKSOBuS+AMkcQ4k";
      "cQBVX7iMwAAAAA=="
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
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBMdGBim/K0+uOIAc/w1AFTUs9kYAAAA" ]
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
    .size = 0x1bc;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3VRsUoDQRB9m7WL2FhoYy4bwV4QJJUbCVwvYusZv8D6Cs/awiwG7MRSU6cTNNqKIIpBweJyqAhaHKZayHG+";
      "u0IkmOIxy+y8N/NmADSdej1JzxenQrlQclrY2QLWgWCtKzd7iX95lkiYDaDllOXjf5hDcF8i3iTafaltNA/zTk4IxPhyreTf";
      "BHGbpkdPRJ7/cK0GOndpOpP1GacNgSZCGMGoGFeAzy7n61NDha7lrJ1YijYKTi/TGa1XwE1luPtQm9zbV8Pa4RXrI3JXY9c2";
      "cm7hl5v4F7nXQRF2mnwv0lUtsJzP++ragPW5/qy2x/TxTJS5Jy9CdVDUNvGvT0e9vNDfOG8Zsv1K3kAQWW8wbnvKqBPFd8U0";
      "qH/APtzV0t97fDP3A57CPBm8AQAA"
    ]
  };
  {
    .name = ".fini";
    .address = 0x83c;
    .size = 0x14;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/5NXYL76t3r/yr/MDBP/Vh9ccYA5/hoA8Q4mSxQAAAA=" ]
  };
  {
    .name = ".rodata";
    .address = 0x850;
    .size = 0x40;
    .readOnly = true;
    .bytes = [
      "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiMD+vNDc+OT+vLLWoODM/L95QLxkszGAAoRgYGVgYGBQYGABU+fFkQAAAAA=="
    ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0x890;
    .size = 0x4c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrb2YWBg4ADiD3///+dgZGAw+Pf/fwqQPwFIVwDpA0C6B0j/AdILgHTA////jwDpAiB9A0jPANIfgDQA";
      "n1HBwkwAAAA="
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0x8e0;
    .size = 0xd4;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiI/8/f/fBCTpyC4HEtMBYoF///8bQPWAxBxA4kAxG6iYAhCHgDBQzAOs";
      "l09hLss8ZqfJTH737l7mg+mrAOIWoBoWqD4RIO4B4glAMQ2IPoG5TPMYQeJLgHgBUBzEZnBGiO8B4gd//v8HuYvBEyIOYgIA";
      "vhL7zNQAAAA="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0x9b4;
    .size = 0x20;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAGJGIHb3C2UAAWYgZmeAAAA9kbzyIAAAAA==" ]
  };
  {
    .name = ".init_array";
    .address = 0x1fdb8;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/3vAzgAGAIbEVSMIAAAA" ]
  };
  {
    .name = ".fini_array";
    .address = 0x1fdc0;
    .size = 0x8;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/+thZwADAHJxEaQIAAAA" ]
  };
  {
    .name = ".dynamic";
    .address = 0x1fdc8;
    .size = 0x1f0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/7WQOw6CQBCGh8eqgHYSH3gUTkSDpYmNtUexoqTkCBzD0sbCGFli5tti6Znmy7f/zL4C0brCAN7hGj6NcoOX";
      "K+UBb386WeDEcoQd+WmSvwdb/9mE6sb1R8oF3pOn+ANmcA9z8Sty97d6PtvIBW7hEu7g2fjrTezfu4PJ5Pyv1fe41gG/MW9x";
      "988vvCL/4LHMUyMBWCzv8AEAAA=="
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
