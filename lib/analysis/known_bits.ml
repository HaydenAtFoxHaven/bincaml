open Bincaml_util.Common

module IsKnownLattice = struct
  let name = "tnum"

  type t = Bot | TNum of { value : Bitvec.t; mask : Bitvec.t } | Top
  [@@deriving eq]

  let tnum v m =
    assert (Bitvec.(is_zero (bitand v m)));
    Bitvec.size_is_equal v m;
    TNum { value = v; mask = m }

  let known v = tnum v Bitvec.(zero ~size:(size v))

  let show = function
    | Top -> "⊤"
    | Bot -> "⊥"
    | TNum { value = v; mask = m } ->
        let size = Bitvec.size v in
        let rec result acc i v m =
          if i >= size then acc
          else
            let one = Bitvec.(of_int ~size:(size v) 1) in
            let mask_bit = Bitvec.(is_nonzero @@ bitand m one) in
            let value_bit = Bitvec.(is_nonzero @@ bitand v one) in

            let bit_str =
              if mask_bit then "μ" else if value_bit then "1" else "0"
            in

            let new_acc = bit_str ^ acc in
            result new_acc (i + 1) (Bitvec.lshr v one) (Bitvec.lshr m one)
        in
        result "" 0 v m

  let compare a b =
    if equal a b then 0
    else
      match (a, b) with
      | TNum { value = av; mask = am }, TNum { value = bv; mask = bm } ->
          if
            Bitvec.(
              (is_zero @@ bitand am (bitnot bm))
              && equal (bitand av (bitnot am)) (bitand bv (bitnot bm)))
          then -1
          else 1
      | Bot, _ | _, Top -> -1
      | _, Bot | Top, _ -> 1

  let bottom = Bot
  let top = Top
  let pretty t = Containers_pp.text (show t)

  let join a b =
    match (a, b) with
    | Top, _ | _, Top -> Top
    | Bot, x | x, Bot -> x
    | TNum { value = av; mask = am }, TNum { value = bv; mask = bm } ->
        let mask = Bitvec.bitxor av bv |> Bitvec.bitor am |> Bitvec.bitor bm in
        let value =
          Bitvec.bitnot mask |> Bitvec.bitand @@ Bitvec.bitand av bv
        in
        tnum value mask

  let widening a b = join a b
end

module IsKnownBitsOps = struct
  include IsKnownLattice

  let bind1 f a =
    match a with TNum { value; mask } -> f (value, mask) | _ -> a

  let bind2 f a b =
    match (a, b) with
    | Bot, _ | _, Bot -> Bot
    | Top, _ | _, Top -> Top
    | TNum { value = av; mask = am }, TNum { value = bv; mask = bm } ->
        f (av, am) (bv, bm)

  let zero_extend k =
    bind1 (fun (v, m) ->
        tnum
          (Bitvec.zero_extend ~extension:k v)
          (Bitvec.zero_extend ~extension:k m))

  let sign_extend k =
    bind1 (fun (v, m) ->
        tnum
          (Bitvec.sign_extend ~extension:k v)
          (Bitvec.zero_extend ~extension:k m))

  let extract (hi, lo) =
    bind1 (fun (v, m) ->
        tnum (Bitvec.extract ~hi ~lo v) (Bitvec.extract ~hi ~lo m))

  let bitnot = bind1 (fun (v, m) -> tnum Bitvec.(bitnot @@ bitor v m) m)

  let bitand =
    bind2 (fun (av, am) (bv, bm) ->
        let v = Bitvec.bitand av bv in
        let alpha = Bitvec.bitor av am in
        let beta = Bitvec.bitor bv bm in
        let m = Bitvec.(bitand (bitnot v) @@ bitand alpha beta) in
        tnum v m)

  let bitor =
    bind2 (fun (av, am) (bv, bm) ->
        let v = Bitvec.(bitor av bv) in
        let m = Bitvec.(bitand (bitor am bm) (bitnot v)) in
        tnum v m)

  let bitxor =
    bind2 (fun (av, am) (bv, bm) ->
        let v = Bitvec.(bitand (bitxor av bv) (bitnot @@ bitor am bm)) in
        tnum v Bitvec.(bitor am bm))

  let add =
    bind2 (fun (av, am) (bv, bm) ->
        let sm = Bitvec.add am bm in
        let sv = Bitvec.add av bv in
        let sigma = Bitvec.add sv sm in
        let chi = Bitvec.bitxor sigma sv in
        let mu = Bitvec.(bitor chi (bitor am bm)) in
        tnum Bitvec.(bitand sv (bitnot mu)) mu)

  let sub =
    bind2 (fun (av, am) (bv, bm) ->
        let dv = Bitvec.sub av bv in
        let alpha = Bitvec.add dv am in
        let beta = Bitvec.sub dv bm in
        let xi = Bitvec.bitxor alpha beta in
        let last = Bitvec.(bitor xi (bitor am bm)) in
        tnum Bitvec.(bitand dv (bitnot last)) last)

  let neg =
    bind1 (fun (v, m) ->
        let zero = Bitvec.(zero ~size:(size v)) in
        sub (known zero) (tnum v m))

  let bitSHL =
    bind2 (fun (av, am) (bv, bm) ->
        if Bitvec.is_nonzero bm then Top
        else tnum (Bitvec.shl av bv) (Bitvec.shl am bv))

  let bitLSHR =
    bind2 (fun (av, am) (bv, bm) ->
        if Bitvec.is_nonzero bm then Top
        else tnum (Bitvec.lshr av bv) (Bitvec.shl am bv))

  let bitASHR =
    bind2 (fun (av, am) (bv, bm) ->
        if Bitvec.is_nonzero bm then Top
        else tnum (Bitvec.ashr av bv) (Bitvec.shl am bv))

  let mul =
    bind2 (fun (av, am) (bv, bm) ->
        let t_zero = known Bitvec.(of_int ~size:(size av) 0) in
        let one = Bitvec.(of_int ~size:(size av) 1) in

        let rec tnum_mul_aux accv accm a b =
          let av, am = a in
          let bv, bm = b in

          if Bitvec.(is_zero @@ bitor av am) then add accv accm
          else
            let a_lsb = Bitvec.bitand av one in
            let a_mask_lsb = Bitvec.bitand am one in
            let b_tnum = tnum bv bm in
            let recurse accv accm =
              let a_next =
                bind1
                  (fun (v, m) -> tnum Bitvec.(lshr v one) (Bitvec.lshr m one))
                  (tnum av am)
              in
              let b_next =
                bind1
                  (fun (v, m) -> tnum Bitvec.(shl v one) Bitvec.(shl m one))
                  b_tnum
              in
              bind2 (tnum_mul_aux accv accm) a_next b_next
            in

            if Bitvec.(is_nonzero a_lsb) then
              let accv' = add accv (known bv) in
              recurse accv' accm
            else if Bitvec.(is_nonzero a_mask_lsb) then
              let accm' =
                add accm (tnum Bitvec.(of_int ~size:(size bm) 0) bm)
              in
              recurse accv accm'
            else recurse accv accm
        in

        tnum_mul_aux t_zero t_zero (av, am) (bv, bm))

  let concat a b =
    match (a, b) with
    | Bot, t | t, Bot -> t
    | Top, _ | _, Top -> Top
    | TNum { value = av; mask = am }, TNum { value = bv; mask = bm } ->
        tnum (Bitvec.concat av bv) (Bitvec.concat am bm)
end

module IsKnownBitsValueAbstraction = struct
  include IsKnownBitsOps

  let eval_const (op : Lang.Ops.AllOps.const) =
    match op with
    | `Bitvector a -> known a
    | `Bool true -> known @@ Bitvec.ones ~size:1
    | `Bool false -> known @@ Bitvec.zero ~size:1
    | _ -> Top

  let eval_unop (op : Lang.Ops.AllOps.unary) a =
    match op with
    | `BVNOT -> bitnot a
    | `ZeroExtend k -> zero_extend k a
    | `SignExtend k -> sign_extend k a
    | `Extract (hi, lo) -> extract (hi, lo) a
    | `BVNEG -> neg a
    | _ -> Top

  let eval_binop (op : Lang.Ops.AllOps.binary) a b =
    match op with
    | `BVADD -> add a b
    | `BVSUB -> sub a b
    | `BVAND -> bitand a b
    | `BVNAND -> bitnot (bitand a b)
    | `BVOR -> bitor a b
    | `BVXOR -> bitxor a b
    | `BVSHL -> bitSHL a b
    | `BVLSHR -> bitLSHR a b
    | `BVASHR -> bitASHR a b
    | `BVMUL -> mul a b
    | _ -> Top

  let eval_intrin (op : Lang.Ops.AllOps.intrin) (args : t list) =
    let fold f args =
      List.map Option.some args
      |> List.fold_left
           (fun acc t ->
             match acc with None -> t | Some a -> Option.map (f a) t)
           None
      |> function
      | Some t -> t
      | None -> Top
    in
    let f =
      match op with
      | `BVADD -> eval_binop `BVADD
      | `BVOR -> eval_binop `BVOR
      | `BVXOR -> eval_binop `BVXOR
      | `BVAND -> eval_binop `BVAND
      | `BVConcat -> concat
      | _ -> fun _ _ -> Top
    in
    fold f args
end

module IsKnownValueAbstractionBasil = struct
  include IsKnownBitsValueAbstraction
  module E = Lang.Expr.BasilExpr
end

include Dataflow_graph.EasyForwardAnalysisPack (IsKnownValueAbstractionBasil)
