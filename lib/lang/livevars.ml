open Containers
open Expr
open Prog
open Types
module V = Set.Make (Var)
module B = Map.Make (Var)

let show_b show_v b =
  B.to_list b
  |> List.map (fun (k, v) -> Printf.sprintf "%s -> %s" (Var.show k) (show_v v))
  |> String.concat ", "

let substitute_expr (sub : Var.t -> 't) e =
  let open AbstractExpr in
  let binding acc e =
    match e with Binding (b, e) -> V.union acc (V.of_list b) | o -> acc
  in
  let subst binding e =
    match e with
    | RVar e when V.find_opt e binding |> Option.is_none -> sub e
    | o -> BasilExpr.fix o
  in
  BasilExpr.map_fold ~f:binding ~alg:subst V.empty e

let%expect_test _ =
  let open BasilExpr in
  let v1 = Var.create "v1" (BType.bv 5) in
  let v2 = Var.create "v2" (BType.bv 5) in
  let exp =
    BasilExpr.forall ~bound:[ v1 ] (binexp ~op:`BVADD (rvar v1) (rvar v2))
  in
  print_endline (to_string exp);
  let sub v = bvconst (Value.PrimQFBV.of_int ~width:5 150) in
  let e2 = substitute_expr sub exp in
  print_endline (to_string e2);
  [%expect
    {|
    forall(v1:bv5 :: bvadd(v1:bv5, v2:bv5))
    forall(v1:bv5 :: bvadd(v1:bv5, 0x16:bv5)) |}]

let%expect_test _ =
  print_endline "beans";
  [%expect {| beans |}]

let fv_expr (e : ('a, Var.t, 'b, 'c, 'd, V.t) AbstractExpr.t) =
  let open AbstractExpr in
  match e with
  | RVar e -> V.singleton e
  | Binding (b, e) -> V.diff e (V.of_list b)
  | o -> fold (fun acc a -> V.union a acc) V.empty o

let fv_expr e = BasilExpr.cata fv_expr e

let assigned_stmt (init : V.t) s : V.t =
  let id a v = a in
  let f_lvar a v = V.add v a in
  Stmt.fold ~f_lvar ~f_rvar:id ~f_expr:id ~init s

let fv_stmt (init : V.t) s : V.t =
  let id a v = a in
  let f_rvar a v = V.add v a in
  let f_expr a v = V.union (fv_expr v) a in
  Stmt.fold ~f_lvar:id ~f_rvar ~f_expr ~init s

let tf_block (init : V.t) b =
  let tf_stmt init s =
    let assigns = V.diff init (assigned_stmt V.empty s) in
    fv_stmt assigns s
  in
  Block.fold_stmt_backwards ~f:tf_stmt ~phi:(fun f _ -> f) ~init b

module G = Procedure.G

module LV =
  Graph.Fixpoint.Make
    (G)
    (struct
      type vertex = G.E.vertex
      type edge = G.E.t
      type g = G.t
      type data = V.t

      let direction = Graph.Fixpoint.Backward
      let equal = V.equal
      let join = V.union

      let analyze (e : edge) d =
        match G.E.label e with Block b -> tf_block d b | _ -> d
    end)
