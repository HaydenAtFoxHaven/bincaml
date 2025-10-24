open Containers
open Expr
open Prog

let fv_expr e =
  let open AbstractExpr in
  let children a = fold (fun acc a -> a :: acc) [] a in
  match e with
  | RVar e -> [ e ]
  | o ->
      let c = children o in
      List.concat c

module V = Set.Make (Var)

let fv_expr e = BasilExpr.cata fv_expr e |> V.of_list

let assigned_stmt (init : V.t) s : V.t =
  let f_rvar = fun (acc : V.t) v -> acc in
  let f_lvar = fun (acc : V.t) v -> V.add v acc in
  let f_expr = fun (acc : V.t) v -> acc in
  Stmt.fold ~f_lvar ~f_rvar ~f_expr ~init s

let fv_stmt (init : V.t) s : V.t =
  let f_lvar = fun (acc : V.t) v -> acc in
  let f_rvar = fun (acc : V.t) v -> V.add v acc in
  let f_expr = fun (acc : V.t) v -> V.union (fv_expr v) acc in
  Stmt.fold ~f_lvar ~f_rvar ~f_expr ~init s

let tf_stmt init s =
  V.union (V.diff init (assigned_stmt V.empty s)) (fv_stmt V.empty s)

let tf_block (init : V.t) b =
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
