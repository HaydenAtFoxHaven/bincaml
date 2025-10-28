open Expr
open Containers
open CCSexp
open Value

module SMTLib2 = struct
  type logic = Int | Prop | BV | Array | DT [@@deriving ord]

  module LSet = Set.Make (struct
    type t = logic

    let compare = compare_logic
  end)

  module VMap = Map.Make (Var)

  type var_decl = { decl_cmd : CCSexp.t; var : CCSexp.t }

  type builder = {
    commands : CCSexp.t list;
    var_decls : var_decl VMap.t;
    logics : LSet.t;
  }

  let init = { commands = []; var_decls = VMap.empty; logics = LSet.empty }

  type 'e t = builder -> 'e * builder

  let return e = fun s -> (e, s)

  let get (e : 'a t) =
   fun s ->
    let v, s = e s in
    s

  let bind (t : 'f t) (f : 'a -> 'g t) s =
    let v, s = t s in
    let bv, bs = f v s in
    (bv, bs)

  let ( let* ) = bind

  let sequence (args : 'a t list) : 'a list t =
    List.fold_left
      (fun (a : CCSexp.t list t) i ->
        let* a = a in
        let* i = i in
        return (i :: a))
      (return []) args

  let rec of_typ (ty : Types.BType.t) =
    match ty with
    | Integer -> (atom "Int", LSet.singleton Int)
    | Boolean -> (atom "Bool", LSet.singleton Prop)
    | Bitvector i ->
        ( list [ atom "_"; atom "BitVec"; atom @@ Int.to_string i ],
          LSet.singleton BV )
    | Types.BType.Unit -> (atom "Unit", LSet.singleton DT)
    | Types.BType.Top -> (atom "Any", LSet.singleton DT)
    | Types.BType.Nothing -> (atom "Nothing", LSet.singleton DT)
    | Types.BType.Map (l, r) ->
        let tl, ll = of_typ l in
        let tr, lr = of_typ r in
        let log = LSet.union (LSet.singleton Array) (LSet.union ll lr) in
        (list [ atom "Array"; tl; tr ], log)

  let gen_decl v =
    let n = Var.name v in
    let ty = Var.typ v in
    let ty, logics = of_typ ty in
    let v = atom n in
    ({ decl_cmd = list [ atom "declare-const"; v; ty ]; var = v }, logics)

  let decl_var (v : Var.t) s =
    VMap.find_opt v s.var_decls |> function
    | Some { decl_cmd; var } -> (var, s)
    | None ->
        let decl, logics = gen_decl v in
        ( decl.var,
          {
            s with
            var_decls = VMap.add v decl s.var_decls;
            logics = LSet.union logics s.logics;
          } )

  let get_var v = fun s -> decl_var v s

  let replace_unsupp_ops_alg
      (e : (BasilExpr.t * Types.BType.t) BasilExpr.abstract_expr) : BasilExpr.t
      =
    let open AbstractExpr in
    let open BasilExpr in
    let orig s = fix @@ map fst s in
    let repeat bit bits body =
      let l = List.init bits (fun i -> bit) in
      List.fold_left (fun acc e -> binexp ~op:`BVConcat acc e) body l
    in
    match e with
    | UnaryExpr (`ZeroExtend bits, (e, t)) -> (
        match t with
        | Bitvector size -> repeat (bvconst @@ PrimQFBV.zero ~size) bits e
        | _ -> failwith "type error")
    | UnaryExpr (`SignExtend bits, (body, t)) -> (
        match t with
        | Bitvector size ->
            repeat (extract ~hi_incl:size ~lo_excl:(size - 1) body) bits body
        | _ -> failwith "type error")
    | o -> orig o

  (* TODO: Factor this out into BasilExpr; it might be better to structure this more; since we are doing type-inference
     along the way maybe it makes sense to check the substituted expression is type-correct for its context?
     ALSO really need to factor out the identity function on each subexpr.
  *)
  let rewrite_smt_constructs (e : BasilExpr.t) : BasilExpr.t =
    BasilExpr.fold_with_type replace_unsupp_ops_alg e

  let of_op
      (op :
        [< Ops.AllOps.const
        | Ops.AllOps.unary
        | Ops.AllOps.binary
        | Ops.AllOps.intrin ]) =
    match op with
    | `Extract (hi, lo) ->
        list [ atom "_"; atom "extract"; of_int (hi - 1); of_int lo ]
    | `BVConcat -> atom "concat"
    | `Integer i -> atom (PrimInt.to_string i)
    | `Bitvector i ->
        list
          [
            atom "_";
            atom @@ "bv" ^ (PrimQFBV.value i |> Z.to_string);
            atom @@ Int.to_string @@ PrimQFBV.width i;
          ]
    | #Ops.AllOps.unary as o -> atom @@ Ops.AllOps.to_string o
    | #Ops.AllOps.const as o -> atom @@ Ops.AllOps.to_string o
    | #Ops.AllOps.binary as o -> atom @@ Ops.AllOps.to_string o
    | #Ops.AllOps.intrin as o -> atom @@ Ops.AllOps.to_string o

  let smt_alg (e : sexp t BasilExpr.abstract_expr) =
    match e with
    | Constant o -> return (of_op o)
    | RVar e -> get_var e
    | UnaryExpr (o, e) ->
        let* e = e in
        return @@ list [ of_op o; e ]
    | BinaryExpr (o, l, r) ->
        let* l = l in
        let* r = r in
        return @@ list [ of_op o; l; r ]
    (* TODO: bool2bv1 *)
    | ApplyIntrin (o, args) ->
        let* args = sequence args in
        return (list (of_op o :: args))
    (* TODO: fundecls*)
    | ApplyFun (n, args) ->
        let* args = sequence args in
        return @@ list (atom n :: args)
    (* TODO: bindings *)
    | Binding (_, _) -> failwith "unsupp"

  let of_bexpr e =
    let e : BasilExpr.t = rewrite_smt_constructs e in
    (BasilExpr.cata smt_alg e) init

  let%expect_test _ =
    let open BasilExpr in
    let e =
      binexp ~op:`EQ
        (unexp ~op:(`SignExtend 10) (bvconst (PrimQFBV.ones ~size:3)))
        (bvconst @@ PrimQFBV.of_int ~width:13 100)
    in
    print_endline (to_string e);
    let smt = fst @@ of_bexpr e in
    print_endline (CCSexp.to_string smt);
    [%expect
      {|
      eq(sign_extend_10(0x7:bv3), 0x64:bv13)
      (eq (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (_ bv7 3) ((_ extract 2 2) (_ bv7 3))) ((_ extract 2 2) (_ bv7 3))) ((_ extract 2 2) (_ bv7 3))) ((_ extract 2 2) (_ bv7 3))) ((_ extract 2 2) (_ bv7 3))) ((_ extract 2 2) (_ bv7 3))) ((_ extract 2 2) (_ bv7 3))) ((_ extract 2 2) (_ bv7 3))) ((_ extract 2 2) (_ bv7 3))) ((_ extract 2 2) (_ bv7 3))) (_ bv100 13)) |}]
end
