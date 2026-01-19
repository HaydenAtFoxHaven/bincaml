open Bincaml_util.Common
open Analysis.Wrapping_intervals.WrappingIntervalsLattice

let dbg x =
  print_endline (show x);
  x

let%test_unit "cardinality" =
  let ( = ) a b = Z.equal a (Z.of_int b) in
  let iv a b = interval (Bitvec.of_int ~size:4 a) (Bitvec.of_int ~size:4 b) in
  assert (cardinality bottom = 0);
  assert (cardinality { w = Some 4; v = Top } = 16);
  assert (cardinality (iv 0 15) = 16);
  assert (cardinality (iv 3 12) = 10);
  assert (cardinality (iv 15 0) = 2);
  assert (cardinality (iv 13 13) = 1)

let%test_unit "member" =
  let iv a b =
    Interval
      { lower = Bitvec.of_int ~size:4 a; upper = Bitvec.of_int ~size:4 b }
  in
  let member t e = member t (Bitvec.of_int ~size:4 e) in
  assert (member Top 0);
  assert (not (member Bot 0));
  assert (member (iv 2 6) 4);
  assert (member (iv 2 6) 6);
  assert (member (iv 2 6) 2);
  assert (not (member (iv 2 6) 7));
  assert (not (member (iv 6 2) 4));
  assert (member (iv 6 2) 6);
  assert (member (iv 6 2) 2);
  assert (member (iv 6 2) 7)

let%test_unit "partial_order" =
  let ( <= ) a b = compare a b <= 0 in
  let ( > ) a b = compare a b > 0 in
  let iv a b = interval (Bitvec.of_int ~size:4 a) (Bitvec.of_int ~size:4 b) in
  assert (top <= top);
  assert (bottom <= top);
  assert (bottom <= bottom);
  (* Fig 2.a *)
  assert (iv 0 8 <= iv 0 9);
  assert (iv 3 5 <= iv 0 8);
  (* Fig 2.b *)
  assert (iv 0 9 > iv 8 1);
  assert (iv 8 1 > iv 0 9);
  (* Fig 2.c *)
  assert (iv 0 9 > iv 4 10);
  assert (iv 4 10 > iv 0 9);
  (* Fig 2.d *)
  assert (iv 0 4 > iv 5 6);
  assert (iv 5 6 > iv 0 4)

let%test_unit "join" =
  let ( = ) = equal in
  let iv a b = interval (Bitvec.of_int ~size:4 a) (Bitvec.of_int ~size:4 b) in
  assert (join bottom top = top);
  assert (join (iv 1 4) bottom = iv 1 4);
  (* Fig 2.a *)
  assert (join (iv 1 4) (iv 0 5) = iv 0 5);
  (* Fig 2.b *)
  assert (join (iv 0 9) (iv 8 1) = top);
  assert (join (iv 6 5) (iv 3 0) = top);
  (* Fig 2.c *)
  assert (join (iv 0 9) (iv 4 10) = iv 0 10);
  (* Fig 2.d *)
  assert (join (iv 0 4) (iv 5 6) = iv 0 6)

let%test_unit "lub" =
  let ( = ) = equal in
  let iv a b = interval (Bitvec.of_int ~size:4 a) (Bitvec.of_int ~size:4 b) in
  assert (lub [ bottom; top; bottom ] = top);
  assert (lub [ bottom; iv 0 9; top ] = top);
  assert (lub [ iv 0 3; iv 3 5; iv 4 6 ] = iv 0 6);
  assert (lub [ iv 0 3; iv 6 10; iv 14 15 ] = iv 14 10)

let%test_unit "intersect" =
  let ( = ) = List.equal equal in
  let iv a b = interval (Bitvec.of_int ~size:4 a) (Bitvec.of_int ~size:4 b) in
  assert (List.is_empty (intersect bottom bottom));
  assert (List.is_empty (intersect top bottom));
  assert (intersect top (iv 1 2) = [ iv 1 2 ]);
  assert (intersect (iv 0 4) (iv 2 1) = [ iv 0 1; iv 4 2 ]);
  assert (intersect (iv 0 8) (iv 3 6) = [ iv 3 6 ]);
  assert (intersect (iv 3 7) (iv 6 11) = [ iv 7 6 ])
