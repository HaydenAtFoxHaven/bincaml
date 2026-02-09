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

            (* join  compare
             then reduce
            x meet x
           

             *)
end

module Tnum_Wint_Reduced_productValueAbstractionBasil = struct
  include TnumWintReducedProductLattice
  module E = Lang.Expr.BasilExpr
end
