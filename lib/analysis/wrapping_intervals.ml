open Bincaml_util.Common

module WrappingIntervalsLattice = struct
  let name = "wrappingIntervals"

  type l = Top | Interval of { lower : Bitvec.t; upper : Bitvec.t } | Bot
  [@@deriving eq, show { with_path = false }]

  type t = { w : int option; v : l } [@@deriving show { with_path = false }]

  let equal s t = equal_l s.v t.v

  let interval lower upper =
    Bitvec.size_is_equal lower upper;
    {
      w = Some (Bitvec.size lower);
      v =
        (if Bitvec.(equal lower (add upper (of_int ~size:(size upper) 1))) then
           Top
         else Interval { lower; upper });
    }

  let infer { w = w1; v = a } { w = w2; v = b } =
    match (w1, w2) with
    | Some w1, Some w2 ->
        (* Disable assertion when running `dune test` or the soundness check crashes *)
        assert (w1 = w2);
        ({ w = Some w1; v = a }, { w = Some w2; v = b })
    | Some w1, None -> ({ w = Some w1; v = a }, { w = Some w1; v = b })
    | None, Some w2 -> ({ w = Some w2; v = a }, { w = Some w2; v = b })
    | None, None -> ({ w = None; v = a }, { w = None; v = b })

  let umin width = Bitvec.zero ~size:width
  let umax width = Bitvec.ones ~size:width
  let smin width = Bitvec.(concat (ones ~size:1) (zero ~size:(width - 1)))
  let smax width = Bitvec.(zero_extend ~extension:1 (ones ~size:(width - 1)))
  let sp width = interval (umax width) (umin width)
  let np width = interval (smax width) (smin width)
  let top = { w = None; v = Top }
  let bottom = { w = None; v = Bot }
  let pretty t = Containers_pp.text (show t)

  let cardinality { w; v } =
    match v with
    | Bot -> Z.of_int 0
    | Top -> (
        match w with
        | Some w -> Z.pow (Z.of_int 2) w
        | None -> failwith "Cannot determine cardinality for Top without width")
    | Interval { lower; upper } ->
        Bitvec.(sub upper lower |> to_unsigned_bigint |> Z.add (Z.of_int 1))

  let compare_size s t = Z.compare (cardinality s) (cardinality t)

  let complement { w; v } =
    match v with
    | Bot -> { w; v = Top }
    | Top -> { w; v = Bot }
    | Interval { lower; upper } ->
        let new_lower = Bitvec.(add upper (of_int ~size:(size upper) 1)) in
        let new_upper = Bitvec.(sub lower (of_int ~size:(size lower) 1)) in
        interval new_lower new_upper

  let member t e =
    match t with
    | Bot -> false
    | Top -> true
    | Interval { lower; upper } ->
        Bitvec.size_is_equal lower e;
        Bitvec.size_is_equal upper e;
        Bitvec.(ule (sub e lower) (sub upper lower))

  let compare_l a b =
    match (a, b) with
    | a, b when equal_l a b -> 0
    | Top, _ -> 1
    | Bot, _ -> -1
    | _, Top -> -1
    | _, Bot -> 1
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        if
          member b al && member b au
          && ((not (member a bl)) || not (member a bu))
        then -1
        else 1

  let compare s t = compare_l s.v t.v

  let join s t =
    let s, t = infer s t in
    let { v = a; _ } = s in
    let { v = b; _ } = t in
    if compare s t <= 0 then t
    else if compare t s <= 0 then s
    else
      match (a, b) with
      | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
        ->
          let al_mem = member b al in
          let au_mem = member b au in
          let bl_mem = member a bl in
          let bu_mem = member a bu in
          if al_mem && au_mem && bl_mem && bu_mem then
            { w = Some (Bitvec.size al); v = Top }
          else if au_mem && bl_mem then interval al bu
          else if al_mem && bu_mem then interval bl au
          else
            let inner_span = cardinality (interval au bl) in
            let outer_span = cardinality (interval bu al) in
            if
              Z.lt inner_span outer_span
              || (Z.equal inner_span outer_span && Bitvec.ule al bl)
            then interval al bu
            else interval bl au
      | _, _ -> failwith "unreachable"

  (* Join for multiple intervals to increase precision (join is not monotone) *)
  let lub (ints : t list) =
    let bigger a b = if compare_size a b < 0 then b else a in
    let gap a b =
      match (a.v, b.v) with
      | Interval { upper = au; _ }, Interval { lower = bl; _ }
        when (not (member b.v au)) && not (member a.v bl) ->
          complement (interval bl au)
      | _, _ -> bottom
    in
    (* APLAS12 mentions "last cases are omitted", does not specify which cases. *)
    let extend a b = join a b in
    let sorted =
      List.sort
        (fun s t ->
          match (s.v, t.v) with
          | Interval { lower = al; _ }, Interval { lower = bl; _ } ->
              Bitvec.compare al bl
          | _, _ -> compare_l s.v t.v)
        ints
    in
    let f1 =
      List.fold_left
        (fun acc t ->
          match t.v with
          | Interval { lower; upper } when Bitvec.ule upper lower ->
              extend acc t
          | _ -> acc)
        bottom sorted
    in
    let g, f =
      List.fold_left
        (fun (g, f) t -> (bigger g (gap f t), extend f t))
        (bottom, f1) sorted
    in
    complement (bigger g (complement f))

  let widening s t =
    let s, t = infer s t in
    let { v = a; _ } = s in
    let { v = b; _ } = t in
    match (a, b) with
    | _, Bot -> s
    | Bot, _ -> t
    | _, Top -> s
    | Top, _ -> t
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        Bitvec.size_is_equal al bl;
        Bitvec.size_is_equal au bu;
        let width = Bitvec.size al in
        if compare t s <= 0 then s
        else if Z.geq (cardinality s) (Z.pow (Z.of_int 2) width) then
          { w = Some width; v = Top }
        else
          let joined = join s t in
          if equal joined (interval al bu) then
            join joined
              (interval al
                 Bitvec.(
                   sub (mul au (of_int ~size:width 2)) al
                   |> add (of_int ~size:width 1)))
          else if equal joined (interval bl au) then
            join joined
              (interval
                 Bitvec.(
                   sub
                     (sub (mul al (of_int ~size:width 2)) au)
                     (of_int ~size:width 1))
                 au)
          else if member b al && member b au then
            join t
              (interval bl
                 Bitvec.(
                   sub
                     (bl
                     |> add (mul au (of_int ~size:width 2))
                     |> add (of_int ~size:width 1))
                     (mul al (of_int ~size:width 2))))
          else { w = Some width; v = Top }

  let intersect s t =
    let s, t = infer s t in
    let { v = a; _ } = s in
    let { v = b; _ } = t in
    match (a, b) with
    | Bot, _ -> []
    | _, Bot -> []
    | Top, _ -> [ t ]
    | a, b when equal_l a b -> [ t ]
    | _, Top -> [ s ]
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        let al_mem = member b al in
        let au_mem = member b au in
        let bl_mem = member a bl in
        let bu_mem = member a bu in
        let a_in_b = al_mem && au_mem in
        let b_in_a = bl_mem && bu_mem in
        if a_in_b && b_in_a then [ interval al bu; interval bl au ]
        else if a_in_b then [ s ]
        else if b_in_a then [ t ]
        else if al_mem && (not au_mem) && (not bl_mem) && bu_mem then
          [ interval al bu ]
        else if (not al_mem) && au_mem && bl_mem && not bu_mem then
          [ interval bl au ]
        else []

  let nsplit t =
    match t.v with
    | Bot -> []
    | Top -> (
        match t.w with
        | Some w -> [ interval (umin w) (smax w); interval (smin w) (umax w) ]
        | None -> failwith "Cannot determine nsplit for Top without width")
    | Interval { lower; upper } ->
        let width = Bitvec.size lower in
        let np = np width in
        if compare np t <= 0 then
          [ interval lower (smax width); interval (smin width) upper ]
        else [ t ]

  let ssplit t =
    match t.v with
    | Bot -> []
    | Top -> (
        match t.w with
        | Some w -> [ interval (umin w) (smax w); interval (smin w) (umax w) ]
        | None -> failwith "Cannot determine nsplit for Top without width")
    | Interval { lower; upper } ->
        let width = Bitvec.size lower in
        let sp = sp width in
        if compare sp t <= 0 then
          [ interval lower (umax width); interval (umin width) upper ]
        else [ t ]

  let cut t = List.concat_map ssplit (nsplit t)
end

module WrappingIntervalsLatticeOps = struct
  include WrappingIntervalsLattice

  (*
  TODO: 
  - Unary:
    - [x] Negate
    - [x] Not
    - [ ] Sign extend
    - [ ] Zero extend
    - [ ] Extract 
  - Binary:
    - [x] Addition
    - [x] Subtraction
    - [x] Multiplication
    - [ ] Bitwise Or/And/Xor
    - [ ] Left Shift
    - [ ] Logical Right Shift
    - [ ] Arithmetic Right Shift
    - [x] (Un)signed Div (see Crab for impl, paper does not provide)
  - 
  *)

  let bind1 f t =
    {
      w = t.w;
      v =
        (match t.v with
        | Bot -> Bot
        | Top -> Top
        | Interval { lower; upper } -> f lower upper);
    }

  let neg =
    bind1 (fun l u -> Interval { lower = Bitvec.neg u; upper = Bitvec.neg l })

  let bitnot =
    bind1 (fun l u ->
        Interval { lower = Bitvec.bitnot u; upper = Bitvec.bitnot l })

  let add s t =
    let top = infer s top |> snd in
    match (s.v, t.v) with
    | Bot, _ -> s
    | _, Bot -> t
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        if Z.(leq (add (cardinality s) (cardinality t)) (cardinality top)) then
          interval (Bitvec.add al bl) (Bitvec.add au bu)
        else top
    | _, _ -> top

  let sub s t =
    let top = infer s top |> snd in
    match (s.v, t.v) with
    | Bot, _ -> s
    | _, Bot -> t
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        if Z.(leq (add (cardinality s) (cardinality t)) (cardinality top)) then
          interval (Bitvec.sub al bu) (Bitvec.sub au bl)
        else top
    | _, _ -> top

  let mul s t =
    let rusmul s t =
      let top = infer s top |> snd in
      let w =
        match s.w with
        | Some w -> w
        | None -> failwith "Cannot multiply without known width"
      in
      let umul =
        match (s.v, t.v) with
        | ( Interval { lower = al; upper = au },
            Interval { lower = bl; upper = bu } ) ->
            let cond =
              let al = Bitvec.to_unsigned_bigint al in
              let au = Bitvec.to_unsigned_bigint au in
              let bl = Bitvec.to_unsigned_bigint bl in
              let bu = Bitvec.to_unsigned_bigint bu in
              Z.(lt (sub (mul au bu) (mul al bl)) (pow (of_int 2) w))
            in
            if cond then interval (Bitvec.mul al bl) (Bitvec.mul au bu) else top
        | _, _ -> top
      in
      let smul =
        match (s.v, t.v) with
        | ( Interval { lower = al; upper = au },
            Interval { lower = bl; upper = bu } ) ->
            let msb_hi b =
              Bitvec.(equal (extract ~hi:w ~lo:(w - 1) b) (ones ~size:1))
            in
            let cond (a, b) (c, d) =
              let a = Bitvec.to_unsigned_bigint a in
              let b = Bitvec.to_unsigned_bigint b in
              let c = Bitvec.to_unsigned_bigint c in
              let d = Bitvec.to_unsigned_bigint d in
              Z.(lt (sub (mul a b) (mul c d)) (pow (of_int 2) w))
            in
            if
              msb_hi al && msb_hi au && msb_hi bl && msb_hi bu
              && cond (au, bu) (al, bl)
            then interval (Bitvec.mul al bl) (Bitvec.mul au bu)
            else if
              msb_hi al && msb_hi au
              && (not (msb_hi bl))
              && (not (msb_hi bu))
              && cond (au, bl) (al, bu)
            then interval (Bitvec.mul al bu) (Bitvec.mul au bl)
            else if
              (not (msb_hi al))
              && (not (msb_hi au))
              && msb_hi bl && msb_hi bu
              && cond (al, bu) (au, bl)
            then interval (Bitvec.mul au bl) (Bitvec.mul al bu)
            else top
        | _, _ -> top
      in
      intersect umul smul
    in
    lub
      (List.concat_map
         (fun a -> List.concat_map (fun b -> rusmul a b) (cut t))
         (cut s))

  (* Division implementation derived from Crab *)
  let trim_zeroes t =
    let w =
      match t.w with
      | Some w -> w
      | None -> failwith "Cannot trim zeroes without known width"
    in
    let zero = Bitvec.zero ~size:w in
    match t.v with
    | Bot -> []
    | Top -> [ interval (Bitvec.of_int ~size:w 1) (umax w) ]
    | Interval { lower; upper } ->
        if Bitvec.equal lower zero && Bitvec.equal upper zero then []
        else if Bitvec.equal lower zero then
          [ interval (Bitvec.of_int ~size:w 1) upper ]
        else if Bitvec.equal upper zero then [ interval lower (umax w) ]
        else if member t.v zero then
          [ interval lower (umax w); interval (Bitvec.of_int ~size:w 1) upper ]
        else [ t ]

  let udiv s t =
    let divide s t =
      let top = infer s top |> snd in
      match (s.v, t.v) with
      | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
        ->
          interval (Bitvec.udiv al bu) (Bitvec.sdiv au bl)
      | _, _ -> top
    in
    lub
      (List.concat_map
         (fun a ->
           List.concat_map
             (fun bs -> List.map (fun b -> divide a b) (trim_zeroes bs))
             (nsplit t))
         (nsplit s))

  let sdiv s t =
    let divide s t =
      let top = infer s top |> snd in

      match (s.v, t.v) with
      | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
        -> (
          let w =
            match s.w with
            | Some w -> w
            | None -> failwith "Cannot signed divide without known width"
          in
          let msb_hi b =
            Bitvec.(equal (extract ~hi:w ~lo:(w - 1) b) (ones ~size:1))
          in
          let ( = ) = Bitvec.equal in
          let smin, neg1 = (smin w, umax w) in
          match (msb_hi al, msb_hi bl) with
          | true, true
            when not ((au = smin && bl = neg1) || (al = smin && bu = neg1)) ->
              interval (Bitvec.sdiv au bl) (Bitvec.sdiv al bu)
          | false, false
            when not ((al = smin && bu = neg1) || (au = smin && bl = neg1)) ->
              interval (Bitvec.sdiv al bu) (Bitvec.sdiv au bl)
          | true, false
            when not ((al = smin && bl = neg1) || (au = smin && bu = neg1)) ->
              interval (Bitvec.sdiv al bl) (Bitvec.sdiv au bu)
          | false, true
            when not ((au = smin && bu = neg1) && al = smin && bl = neg1) ->
              interval (Bitvec.sdiv au bu) (Bitvec.sdiv al bl)
          | _, _ -> top)
      | _, _ -> top
    in
    lub
      (List.concat_map
         (fun a ->
           List.concat_map
             (fun bs -> List.map (fun b -> divide a b) (trim_zeroes bs))
             (cut t))
         (cut s))
end

module WrappingIntervalsValueAbstraction = struct
  include WrappingIntervalsLattice
  include WrappingIntervalsLatticeOps

  let eval_const (op : Lang.Ops.AllOps.const) =
    match op with
    | `Bool _ -> { w = Some 1; v = Top }
    | `Integer _ -> top
    | `Bitvector bv ->
        if Bitvec.size bv = 0 then { w = Some 0; v = Top } else interval bv bv

  let eval_unop (op : Lang.Ops.AllOps.unary) a =
    match op with
    | `BVNEG -> neg a
    | `BVNOT -> bitnot a
    | _ -> infer a top |> snd

  let eval_binop (op : Lang.Ops.AllOps.binary) a b =
    let a, b = infer a b in
    match op with
    | `BVADD -> add a b
    | `BVSUB -> sub a b
    | `BVMUL -> mul a b
    | `BVUDIV -> udiv a b
    | `BVSDIV -> sdiv a b
    | _ -> infer a top |> snd

  let eval_intrin (op : Lang.Ops.AllOps.intrin) args = top
end

module StateAbstraction = Intra_analysis.MapState (WrappingIntervalsLattice)

module WrappingIntervalsValueAbstractionBasil = struct
  include WrappingIntervalsValueAbstraction
  module E = Lang.Expr.BasilExpr
end

include
  Dataflow_graph.EasyForwardAnalysisPack (WrappingIntervalsValueAbstractionBasil)
