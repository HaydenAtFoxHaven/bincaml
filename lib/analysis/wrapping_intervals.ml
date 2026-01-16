open Bincaml_util.Common

module WrappingIntervalsLattice = struct
  let name = "wrappingIntervals"

  type t = Top | Interval of { lower : Bitvec.t; upper : Bitvec.t } | Bot
  [@@deriving eq, show { with_path = false }]

  let interval lower upper =
    Bitvec.size_is_equal lower upper;
    Interval { lower; upper }

  let bottom = Bot
  let pretty t = Containers_pp.text (show t)

  (*  TODO: Rewrite as compare_size to avoid storing widths for Top and Bot *)
  let cardinality t =
    match t with
    | Bot -> Z.of_int 0
    | Top -> Z.pow (Z.of_int 2) 64
    | Interval { lower; upper } ->
        Bitvec.(
          sub upper lower
          |> add (of_int ~size:(size lower) 1)
          |> to_unsigned_bigint)

  let compare_size a b =
    match (a, b) with
    | a, b when equal a b -> 0
    | Top, _ -> 1
    | Bot, _ -> -1
    | _, Top -> -1
    | _, Bot -> 1
    | Interval _, Interval _ -> Z.compare (cardinality a) (cardinality b)

  let complement t =
    match t with
    | Bot -> Top
    | Top -> Bot
    | Interval { lower; upper } ->
        let new_lower = Bitvec.(add upper (of_int ~size:(size upper) 1)) in
        let new_upper = Bitvec.(sub lower (of_int ~size:(size lower) 1)) in
        interval new_lower new_upper

  let member t e =
    match t with
    | Bot -> false
    | Top -> true
    | Interval { lower; upper } -> Bitvec.(ule (sub e lower) (sub upper lower))

  let compare a b =
    match (a, b) with
    | a, b when equal a b -> 0
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

  let join a b =
    if compare a b <= 0 then b
    else if compare a b >= 0 then a
    else
      match (a, b) with
      | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
        ->
          let al_mem = member b al in
          let au_mem = member b au in
          let bl_mem = member a bl in
          let bu_mem = member a bu in
          if al_mem && au_mem && bl_mem && bu_mem then Top
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
      match (a, b) with
      | Interval { upper = au; _ }, Interval { lower = bl; _ }
        when (not (member b au)) && not (member a bl) ->
          complement (interval bl au)
      | _, _ -> Bot
    in
    (* APLAS12 mentions "last cases are omitted", does not specify which cases. *)
    let extend a b = join a b in
    let sorted =
      List.sort
        (fun a b ->
          match (a, b) with
          | Interval { lower = al; _ }, Interval { lower = bl; _ } ->
              Bitvec.compare al bl
          | _, _ -> compare a b)
        ints
    in
    let f1 =
      List.fold_right
        (fun t acc ->
          match t with
          | Interval { lower; upper } when Bitvec.ule upper lower ->
              extend acc t
          | _ -> acc)
        sorted Bot
    in
    let g, f =
      List.fold_right
        (fun t (g, f) -> (bigger g (gap f t), extend f t))
        sorted (Bot, f1)
    in
    complement (bigger g (complement f))

  let widening a b =
    match (a, b) with
    | a, Bot -> a
    | Bot, b -> b
    | a, Top -> a
    | Top, b -> b
    | Interval { lower = al; upper = au }, Interval { lower = bl; upper = bu }
      ->
        Bitvec.size_is_equal al bl;
        Bitvec.size_is_equal au bu;
        let width = Bitvec.size al in
        if compare b a <= 0 then a
        else if Z.geq (cardinality a) (Z.pow (Z.of_int 2) 64) then Top
        else
          let joined = join a b in
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
            join b
              (interval bl
                 Bitvec.(
                   sub
                     (bl
                     |> add (mul au (of_int ~size:width 2))
                     |> add (of_int ~size:width 1))
                     (mul al (of_int ~size:width 2))))
          else Top
end

module WrappingIntervalsValueAbstraction = struct
  include WrappingIntervalsLattice

  let eval_const op = Top
  let eval_unop op a = Top
  let eval_binop op a b = Top
  let eval_intrin op args = Top
end

module StateAbstraction = Intra_analysis.MapState (WrappingIntervalsLattice)

module WrappingIntervalsValueAbstractionBasil = struct
  include WrappingIntervalsValueAbstraction
  module E = Lang.Expr.BasilExpr
end
