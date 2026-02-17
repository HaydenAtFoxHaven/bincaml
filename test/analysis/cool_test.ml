(* (⊤, ⟦0x0:bv50, 0x80af748b1425:bv50⟧) ⊆ (00000000000000000000000000000000000000000000000000, ⟦0x0:bv50, 0x0:bv50⟧) *)

open Bincaml_util.Common
open Analysis
open Known_bits
open Wrapped_intervals
open Tnum_wint_reduced_product

let%test "compare" =
  let iv s t =
    WrappedIntervalsLattice.interval (Bitvec.of_int ~size:50 s)
      (Bitvec.of_int ~size:50 t)
  in
  let (abst : TnumWintReducedProductLattice.t) =
    { tnum = IsKnownLattice.Top; wint = iv 0 0x80af748b1425 }
  in
  let (conc : TnumWintReducedProductLattice.t) =
    { tnum = IsKnownLattice.known (Bitvec.zero ~size:50); wint = iv 0 0 }
  in
  IsKnownLattice.compare conc.tnum abst.tnum <= 0 &&
  WrappedIntervalsLattice.compare conc.wint abst.wint <= 0 &&
  TnumWintReducedProductLattice.compare conc abst <= 0 &&
  TnumWintReducedProductLattice.equal abst (TnumWintReducedProductLattice.join abst conc)
