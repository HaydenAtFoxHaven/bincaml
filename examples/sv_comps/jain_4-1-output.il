var $Global_131104_131112: bv64;

prog entry @main_1792;

proc @main_1792
  (R0_in:bv64, R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R16_in:bv64, R17_in:bv64, R18_in:bv64, R1_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64, _PC_in:bv64)
    -> (_PC_out:bv64)
  { .name = "main"; .address = 0x700 }
[
  block %main_entry {.address = 0x700; .originalLabel = "r7OJTxELRZKyn9pRD5ZNnQ=="} [
    var Stack_n16_n8: bv64 := R29_in:bv64 { .label = "1792_1" };
    var Stack_n8_0: bv64 := R30_in:bv64 { .label = "1792_2" };
    goto(%main_loop1_27);
  ];
  block %main_loop1_27 {.address = 0x708; .originalLabel = "BLh8QeoBTcaOCuwUQFAA6g=="} [
    var load18_1: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load18_2: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    var load18_3: bv64 := $Global_131104_131112:bv64 { .label = "1716_0_0" };
    assert true { .comment = "R30 = R30_in" };
    goto(%main_loop1_27);
  ]
];




prog entry @main_1792 {
  .symbols = {
    .externalFunctions = [
      { .name = "_ITM_deregisterTMCloneTable"; .offset = 0x1ffc0 };
      { .name = "_ITM_registerTMCloneTable"; .offset = 0x1ffe0 };
      { .name = "__VERIFIER_nondet_int"; .offset = 0x20020 };
      { .name = "__assert_fail"; .offset = 0x20028 };
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
      { .name = "_IO_stdin_used"; .address = 0x8d0; .size = 0x20 };
      { .name = "__FRAME_END__"; .address = 0xa18; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0xa1c; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20040; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x8a8; .size = 0xa0 };
      { .name = "_start"; .address = 0x740; .size = 0x1a0 };
      { .name = "main"; .address = 0x700; .size = 0xc0 };
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
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2XYvfHlHZcJJ5/t9edlV7P3LZu8UjcJALM/ghYkAAAA" ]
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
      "H4sIAAAAAAAA/2NgwA2YGbgYDNiwiYszGDAwoYhlAbEQFjMYgVgBi3gNECthEZfFob4bh/luOMR1cJgTg0M9AKqFR7IIAQAA"
    ]
  };
  {
    .name = ".dynstr";
    .address = 0x3d8;
    .size = 0xc0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/3WMywrCQAxF80MO+ED3lioDdlOK25BO0xKYZmBmFuLXG0Xcucq9l5MD6IcOJ868SKmch66JSXmgMTIgLmtS";
      "LJVyRYQP+ge8t72/+LZHTTpxRdFqK5XC9jqTRGtRxvCVrSRqS3gQzqIU5clAY8oVDDLFxhzFlfSuwa47wvXmzw3u3Pb0i/sD";
      "vAAkaXJ+wAAAAA=="
    ]
  };
  {
    .name = ".gnu.version";
    .address = 0x498;
    .size = 0x16;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NgAAEmBkYGZigGkQDbLJj8FgAAAA==" ]
  };
  {
    .name = ".gnu.version_r";
    .address = 0x4b0;
    .size = 0x30;
    .readOnly = false;
    .bytes = [ "H4sIAAAAAAAA/2NkYGJYwMDAIMAAAdMnTmNjYGBmWAUV2wLmMzFshcoDAOj7yeAwAAAA" ]
  };
  {
    .name = ".rela.dyn";
    .address = 0x4e0;
    .size = 0xc0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/9vxl5EBBJhZwBRDAgeEPoAmzgMVv/EfVZyBHUJZMDChiMP4B6DqGYHiMC0gcAJJnBVJ/AKSOBuS+AMkcU4k";
      "cQCkZ34mwAAAAA=="
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
      "H4sIAAAAAAAA/42RL08DQRDF397iikNggPa4r0BCqtjDrCd4jvIxTnAoBKYLAouEajS0BAcKQhMSxLUBUv6IC1WbdHO8bhNE";
      "EwLiZZLZmd/MvHXp5ZmTMO9lefxGDShXlvPVmnz4rxaR3S1RLxKtnlS2H8G8kpkDBT61lXyboTpk31I+P9BWAefXnNWWW93f";
      "2BBoAsIIxpBxDfhoA5s9MsJc220yCilaCKrdMWe6PgRulke79/Hs3kE4io86rO+zd73QtuF7g59el154L4YV2Dn2J0FcVwKr";
      "ft9nbTPWe/6Csoe845GqIdtIAlEfVpR16dXp9C1Pf3jp6L8EmoIazwbjThKZ8CQyyCPTIH+fc+jVymTHyX99MfcNPCMfF7wB";
      "AAA="
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
    .size = 0x2a;
    .readOnly = true;
    .bytes = [ "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiMD8rMTMv3kTXUC8ZzGUwYAAAFSdWNyoAAAA=" ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0x8fc;
    .size = 0x4c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrb2YGBg4ABiln///7MwMjC4AOkEIH8JkC4B0leAdAeQFvj///8cIJ0CpA8A6RYgfQVIrwHSb4A0ANNN";
      "DQVMAAAA"
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0x948;
    .size = 0xd4;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiO/8/f/fBCTpyC4HEtMBYo1///8bQPWAxByA2AUoZgMVUwDiECDOAYp5";
      "gPXyKcxlmcfsNJnJ797dy3wwfRVAPAeohgWqTwSIe4B4BVBMA6JPYC7TPEaQ+BIg3gEUB7EZnBHie4D4x5///yWQ1IOYAHE4";
      "Z6HUAAAA"
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0xa1c;
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
      "H4sIAAAAAAAA/7WQPRKCMBCFF+THH+hgVOQQ3MyraGfJESgtLDyCJaUlpY2F45A4zn4pQs8237x92X1JAtE6wwC2MINNoszR";
      "t6Vyj76OOnlAY0sF7/j1xH8be/yzC1XH9PuFklh54K/dPriBO1iKX6yRwWo+a+QEC5jCLWxjv/+M/Hu7/NUk/2v1Pe6oQXfM";
      "W7T75xf6gv9BRzJP/QB4EzTo8AEAAA=="
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
