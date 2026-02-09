open Bincaml_util.Common
open Bitvec
open Analysis.Tnum_wint_reduced_product
open Analysis.Known_bits.IsKnownLattice
open Analysis.Wrapped_intervals.WrappedIntervalsLattice

let%test_unit "tnum_to_wint_known" =
  let v = of_int ~size:3 5 in
  let m = zero ~size:3 in
  let tnum_value = TNum { value = v; mask = m } in
  let result = tnum_to_wint tnum_value in
  match result.v with
  | Interval { lower; upper } ->
      assert (Bitvec.equal lower v);
      assert (Bitvec.equal upper v)
  | _ -> assert false

let%test_unit "tnum_to_wint_with_mask" =
  let v = of_int ~size:3 4 in
  let m = of_int ~size:3 1 in
  let tnum_value = TNum { value = v; mask = m } in
  let result = tnum_to_wint tnum_value in
  match result.v with
  | Interval { lower; upper } ->
      assert (Bitvec.equal lower (of_int ~size:3 4));
      assert (Bitvec.equal upper (of_int ~size:3 5))
  | _ -> assert false


let%test_unit "wint_to_tnum_single_value" =
  let v = of_int ~size:8 42 in
  let wint = { v = Interval { lower = v; upper = v }; w = None } in
  let result = wint_to_tnum wint in
  match result with
  | TNum { value; mask } ->
      assert (Bitvec.equal value v);
      assert (Bitvec.equal mask (zero ~size:8))
  | _ -> assert false

let%test_unit "wint_to_tnum_full_range" =
  let w = 8 in
  let lower = zero ~size:w in
  let upper = ones ~size:w in
  let wint = { v = Interval { lower; upper }; w = None } in
  let result = wint_to_tnum wint in
  match result with
  | TNum { value; mask } ->
      assert (Bitvec.equal value (zero ~size:w));
      assert (Bitvec.equal mask (ones ~size:w))
  | _ -> assert false

let%test_unit "wint_to_tnum_adjacent_values" =
  (* Interval [4, 5] on 3 bits (0b100 to 0b101) *)
  let lower = of_int ~size:3 4 in (* 0b100 *)
  let upper = of_int ~size:3 5 in (* 0b101 *)
  let wint = { v = Interval { lower; upper }; w = None } in
  let result = wint_to_tnum wint in
  match result with
  | TNum { value; mask } ->
      (* diff = 4 XOR 5 = 0b001 *)
      (* k = 1 (one bit differs) *)
      (* mask should be 0b001 *)
      (* value should be lower & ~mask = 0b100 & 0b110 = 0b100 *)
      assert (Bitvec.equal mask (of_int ~size:3 1));
      assert (Bitvec.equal value (of_int ~size:3 4))
  | _ -> assert false

let%test_unit "wint_to_tnum_power_of_two_range" =
  (* Interval [0, 3] on 4 bits (0b0000 to 0b0011) *)
  let lower = of_int ~size:4 0 in  (* 0b0000 *)
  let upper = of_int ~size:4 3 in  (* 0b0011 *)
  let wint = { v = Interval { lower; upper }; w = None } in
  let result = wint_to_tnum wint in
  match result with
  | TNum { value; mask } ->
      (* diff = 0 XOR 3 = 0b0011 *)
      (* k = 2 (two bits differ) *)
      (* mask should be 0b0011 *)
      (* value should be 0b0000 & ~0b0011 = 0b0000 *)
      assert (Bitvec.equal mask (of_int ~size:4 3));
      assert (Bitvec.equal value (of_int ~size:4 0))
  | _ -> assert false

let%test_unit "wint_to_tnum_middle_range" =
  (* Interval [8, 11] on 5 bits (0b01000 to 0b01011) *)
  let lower = of_int ~size:5 8 in  (* 0b01000 *)
  let upper = of_int ~size:5 11 in (* 0b01011 *)
  let wint = { v = Interval { lower; upper }; w = None } in
  let result = wint_to_tnum wint in
  match result with
  | TNum { value; mask } ->
      (* diff = 8 XOR 11 = 0b00011 *)
      (* k = 2 *)
      (* mask should be 0b00011 *)
      (* value should be 0b01000 & ~0b00011 = 0b01000 *)
      assert (Bitvec.equal mask (of_int ~size:5 3));
      assert (Bitvec.equal value (of_int ~size:5 8))
  | _ -> assert false

let%test_unit "wint_to_tnum_large_gap" =
  (* Interval [0, 15] on 4 bits - covers many values *)
  let lower = of_int ~size:4 0 in  (* 0b0000 *)
  let upper = of_int ~size:4 15 in (* 0b1111 *)
  let wint = { v = Interval { lower; upper }; w = None } in
  let result = wint_to_tnum wint in
  match result with
  | TNum { value; mask } ->
      (* diff = 0 XOR 15 = 0b1111 *)
      (* k = 4 *)
      (* mask should be 0b1111 *)
      (* value should be 0b0000 *)
      assert (Bitvec.equal mask (of_int ~size:4 15));
      assert (Bitvec.equal value (of_int ~size:4 0))
  | _ -> assert false

let%test_unit "wint_to_tnum_high_values" =
  (* Interval [12, 13] on 4 bits (0b1100 to 0b1101) *)
  let lower = of_int ~size:4 12 in (* 0b1100 *)
  let upper = of_int ~size:4 13 in (* 0b1101 *)
  let wint = { v = Interval { lower; upper }; w = None } in
  let result = wint_to_tnum wint in
  match result with
  | TNum { value; mask } ->
      (* diff = 12 XOR 13 = 0b0001 *)
      (* k = 1 *)
      (* mask should be 0b0001 *)
      (* value should be 0b1100 & ~0b0001 = 0b1100 *)
      assert (Bitvec.equal mask (of_int ~size:4 1));
      assert (Bitvec.equal value (of_int ~size:4 12))
  | _ -> assert false