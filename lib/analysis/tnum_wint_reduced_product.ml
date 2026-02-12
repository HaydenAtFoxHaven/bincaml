(** Combines Known bit analysis and wrapped interval analysis to get more
    presice values. *)

open Bincaml_util.Common
open Bitvec
open Wrapped_intervals
open WrappedIntervalsLattice
open Known_bits
open IsKnownLattice

module TnumWintReducedProductLattice = struct
  let name = "tnumWintReduceProduct"

  type t = {
    tnum : Known_bits.IsKnownLattice.t;
    wint : Wrapped_intervals.WrappedIntervalsLattice.t;
  }

  let tnum_to_wint tnum =
    match tnum with
    | Bot -> { v = Bot; w = None }
    | Top -> { v = Top; w = None }
    | TNum { value = v; mask = m } ->
        let lower = bitand v (bitnot m) in
        let upper = bitor v m in
        interval lower upper

  let wint_to_tnum wint =
    match wint with
    | { v = Bot; w = _ } -> Bot
    | { v = Top; w = _ } -> Top
    | { v = Interval { lower; upper }; w = _ } ->
        let w = size lower in

        if WrappedIntervalsLattice.compare (sp w) wint <= 0 then
          TNum { value = zero ~size:w; mask = ones ~size:w }
        else
          let diff = bitxor lower upper in
          let k = Z.numbits @@ to_unsigned_bigint diff in
          if k = 0 then known lower
          else
            let mask = concat (zero ~size:(w - k)) (ones ~size:k) in
            let value = bitand lower @@ bitnot mask in
            tnum value mask

  let compare s t =
    if
      IsKnownLattice.equal s.tnum t.tnum
      && WrappedIntervalsLattice.equal s.wint t.wint
    then 0
    else if
      IsKnownLattice.compare s.tnum t.tnum <= 0
      && WrappedIntervalsLattice.compare s.wint t.wint <= 0
    then -1
    else 1

  let reduce tnum wint =
    let wint_from_tnum = tnum_to_wint tnum in
    let intersected = intersect wint_from_tnum wint in
    let wint_reduced = lub intersected in
    let tnum_from_wint = wint_to_tnum wint_reduced in
    let tnum_reduced = IsKnownLattice.join tnum tnum_from_wint in
    { tnum = tnum_reduced; wint = wint_reduced }

  let join s t =
    let tnum_joined = IsKnownLattice.join s.tnum t.tnum in
    let wint_joined = WrappedIntervalsLattice.join s.wint t.wint in
    reduce tnum_joined wint_joined
end

module Tnum_Wint_Reduced_productValueAbstractionBasil = struct
  include TnumWintReducedProductLattice
  module E = Lang.Expr.BasilExpr
end
