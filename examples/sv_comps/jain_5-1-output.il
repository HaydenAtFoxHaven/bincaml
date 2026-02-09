
prog entry @main_1664;

proc @main_1664
  (R0_in:bv64, R10_in:bv64, R11_in:bv64, R12_in:bv64, R13_in:bv64, R14_in:bv64, R15_in:bv64, R16_in:bv64, R17_in:bv64, R18_in:bv64, R1_in:bv64, R29_in:bv64, R2_in:bv64, R30_in:bv64, R31_in:bv64, R3_in:bv64, R4_in:bv64, R5_in:bv64, R6_in:bv64, R7_in:bv64, R8_in:bv64, R9_in:bv64)
    -> (R0_out:bv64, R10_out:bv64, R11_out:bv64, R12_out:bv64, R13_out:bv64, R14_out:bv64, R15_out:bv64, R16_out:bv64, R17_out:bv64, R18_out:bv64, R1_out:bv64, R29_out:bv64, R2_out:bv64, R3_out:bv64, R4_out:bv64, R5_out:bv64, R6_out:bv64, R7_out:bv64, R8_out:bv64, R9_out:bv64)
  { .name = "main"; .address = 0x680 }
[
  block %main_entry [
    goto(%main_loop1_3);
  ];
  block %main_loop1_3 {.address = 0x680; .originalLabel = "D+qOyNP6TkyraIjxg6FmEw=="} [
    goto(%main_loop1_3);
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
      { .name = "__FRAME_END__"; .address = 0x994; .size = 0x0 };
      { .name = "__abi_tag"; .address = 0x998; .size = 0x100 };
      { .name = "__do_global_dtors_aux_fini_array_entry"; .address = 0x1fdc0; .size = 0x0 };
      { .name = "__frame_dummy_init_array_entry"; .address = 0x1fdb8; .size = 0x0 };
      { .name = "completed.0"; .address = 0x20038; .size = 0x8 }
    ];
    .funcEntries = [
      { .name = "__VERIFIER_assert"; .address = 0x828; .size = 0xa0 };
      { .name = "_start"; .address = 0x6c0; .size = 0x1a0 };
      { .name = "main"; .address = 0x680; .size = 0x20 };
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
    .bytes = [ "H4sIAAAAAAAA/2NhYGAQAWJmIHb3C2U45qPa6Z3Ts2/bv7mbVVXZpu//LuIFADIXXagkAAAA" ]
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
      "H4sIAAAAAAAA/6VQPUsDQRSczaaLXQTTaLLxLwiSyo3N9mLvGX/GFZ61hVks7MTSpLY2H60IohgULC6HiqDFYaqFHOdkBYuA";
      "NhbDwHtv5s17ABarNXn/Hywjul0hXiS6Y6ldsgr7KmFjIMWHcZK9InGd5ycPhK+/GaeBi5s8X+rLndFv3hBoI4YVZEXeAN77";
      "wPaYHio2bpceqRRdFKqjmc/8vAKu6tP9u+bCwaGaNo8HnE+o3UyNa3lt4UebhZedjLknJbgy9UGiG1pg3ed9Ni7ivPevaHfK";
      "Ox6JGqKtIEFjUtIuC4fn87c88b6/fpeFvY4E2oKY7QZ5L1BWnSmLWNkW/Y+4h79a+87Y8xk/WfsCcdeSjrwBAAA="
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
    .size = 0x2a;
    .readOnly = true;
    .bytes = [ "H4sIAAAAAAAA/2NkYGIAgaLUxOSM+NSiovwiMD8rMTMv3lTXUC8ZzGUwYAAAkP7A6ioAAAA=" ]
  };
  {
    .name = ".eh_frame_hdr";
    .address = 0x87c;
    .size = 0x4c;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/2OUZrb2YGBg4ABiln///7MwMjC4AOkEIH8JkC4B0leAdAeQFvj///8cIJ0CpA8A6RYgfQVIrwHSb4A0ANNN";
      "DQVMAAAA"
    ]
  };
  {
    .name = ".eh_frame";
    .address = 0x8c8;
    .size = 0xd0;
    .readOnly = false;
    .bytes = [
      "H4sIAAAAAAAA/xNggADGqiAGlgo5RmkeeQYBIF8CiO/8/f/fBCTpyC4HEtMBYo1///8bQPWAxByA2AUoZgMVUwDiECDOAYp5";
      "gPXyKcxlmcfsNJnJ797dy3wwfRVAPAeohgWqTwSIe4B4BVBMA6JPYC7TPEaQ+BIg3gEUB7EZnCHiIDP2APGPPwgzQAAAwmRY";
      "9NAAAAA="
    ]
  };
  {
    .name = ".note.ABI-tag";
    .address = 0x998;
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
