(** Combines Known bit analysis and wrapped interval analysis to get more
    precise values. *)

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

  let reduce_wint wint tnum =
    let mssb x =
      let w = size x in
      let k = Z.numbits @@ to_unsigned_bigint x in
      if k = 0 then zero ~size:w
      else concat (zero ~size:(w - k + 1)) (ones ~size:(k - 1))
    in
    let lssb x = bitand x (bitnot x) in
    let above p = bitnot (bitor p (sub p (ones ~size:(size p)))) in
    let below p = sub p (ones ~size:(size p)) in
    let mergeon a b p = bitor (bitand a (above p)) (bitand b (below p)) in
    let refine_lower_bound a tnum =
      match tnum with
      | Bot -> a
      | Top -> a
      | TNum { value = v; mask = m } -> (
          let diff = mssb (bitand (bitxor a v) (bitnot m)) in
          let wint_result = tnum_to_wint tnum in
          match wint_result.v with
          | Bot -> a
          | Top -> a
          | Interval { lower = tmin; upper = _ } ->
              if is_zero diff then a
              else if is_zero (bitand a diff) then
                bitor diff (mergeon a tmin diff)
              else
                let carry = lssb (bitand (bitand (above diff) (bitnot a)) m) in
                bitor carry (mergeon a tmin carry))
    in
    let refine_upper_bound b tnum =
      match tnum with
      | Bot -> b
      | Top -> b
      | TNum { value = v; mask = m } -> (
          let diff = mssb (bitand (bitxor b v) (bitnot m)) in
          let wint_result = tnum_to_wint tnum in
          match wint_result.v with
          | Bot -> b
          | Top -> b
          | Interval { lower = _; upper = tmax } ->
              if is_zero diff then b
              else if not (is_zero (bitand b diff)) then mergeon b tmax diff
              else
                let borrow = lssb (bitand (bitand (above diff) b) m) in
                mergeon b tmax borrow)
    in
    match tnum with
    | Bot | Top -> wint
    | TNum _ -> (
        match wint.v with
        | Bot -> wint
        | Top -> tnum_to_wint tnum
        | Interval { lower; upper } ->
            let refined_lower = refine_lower_bound lower tnum in
            let refined_upper = refine_upper_bound upper tnum in
            interval refined_lower refined_upper)

  let reduce_tnum wint tnum =
    let tnumed_wint = wint_to_tnum wint in
    match (tnumed_wint, tnum) with
    | Bot, _ | _, Bot -> IsKnownLattice.Bot
    | Top, t | t, Top -> t
    | TNum { value = av; mask = am }, TNum { value = bv; mask = bm } ->
        if is_nonzero (bitxor (bitand av am) (bitand bv bm)) then Bot
        else
          let m = bitand am bm in
          let v = bitand (bitor av bv) (bitnot m) in
          TNum { value = v; mask = m }

  let reduce { wint; tnum } =
    let wint' = reduce_wint wint tnum in
    let tnum' = reduce_tnum wint' tnum in
    { wint = wint'; tnum = tnum' }

  let join s t =
    let tnum_joined = IsKnownLattice.join s.tnum t.tnum in
    let wint_joined = WrappedIntervalsLattice.join s.wint t.wint in
    reduce { tnum = tnum_joined; wint = wint_joined }

  let widening s t =
    let tnum = IsKnownLattice.widening s.tnum t.tnum in
    let wint = WrappedIntervalsLattice.widening s.wint t.wint in
    { tnum; wint }
end

module TnumWintValueAbstraction = struct
  include TnumWintReducedProductLattice

  let eval_const (op : Lang.Ops.AllOps.const) rt =
    let tnum = IsKnownBitsValueAbstraction.eval_const op in
    let wint = WrappedIntervalsValueAbstraction.eval_const op rt in
    { tnum; wint }

  let eval_unop (op : Lang.Ops.AllOps.unary) (a, ta) rt =
    let tnum = IsKnownBitsValueAbstraction.eval_unop op a.tnum in
    let wint = WrappedIntervalsValueAbstraction.eval_unop op (a.wint, ta) rt in
    { tnum; wint }

  let eval_binop (op : Lang.Ops.AllOps.binary) (a, ta) (b, tb) rt =
    let tnum = IsKnownBitsValueAbstraction.eval_binop op a.tnum b.tnum in
    let wint =
      WrappedIntervalsValueAbstraction.eval_binop op (a.wint, ta) (b.wint, tb)
        rt
    in
    { tnum; wint }

  let eval_intrin (op : Lang.Ops.AllOps.intrin) (args : (t * Types.t) list) rt =
    let tnum_args = List.map (fun (arg, _) -> arg.tnum) args in
    let wint_args = List.map (fun (arg, ty) -> (arg.wint, ty)) args in

    let tnum = IsKnownBitsValueAbstraction.eval_intrin op tnum_args in
    let wint = WrappedIntervalsValueAbstraction.eval_intrin op wint_args rt in
    { tnum; wint }
end

module Tnum_Wint_Reduced_productValueAbstractionBasil = struct
  include TnumWintValueAbstraction
  module E = Lang.Expr.BasilExpr
end
