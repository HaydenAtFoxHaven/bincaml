open Value
open Common
open Types

type assocop = [ `EQ | `NEQ | `BOOLAND | `BOOLOR ]
[@@deriving show { with_path = false }, eq]

type predicatebinop =
  [ `EQ
  | `NEQ
  | `BVULT
  | `BVULE
  | `BVSLT
  | `BVSLE
  | `INTLT
  | `INTLE
  | `BOOLAND
  | `BOOLOR
  | `BOOLIMPLIES ]
[@@deriving show { with_path = false }, eq]

type bitbinop =
  [ `BVAND
  | `BVOR
  | `BVADD
  | `BVMUL
  | `BVUDIV
  | `BVUREM
  | `BVSHL
  | `BVLSHR
  | `BVNAND
  | `BVNOR
  | `BVXOR
  | `BVXNOR
  | `BVCOMP
  | `BVSUB
  | `BVSDIV
  | `BVSREM
  | `BVSMOD
  | `BVASHR ]
[@@deriving show { with_path = false }, eq]

type intbinop = [ `INTADD | `INTMUL | `INTSUB | `INTDIV | `INTMOD ]
[@@deriving show { with_path = false }, eq]

type unop = [ `BITNOT | `LOGNOT | `NEG ]
[@@deriving show { with_path = false }, eq]

type binop = [ predicatebinop | intbinop | bitbinop ]
[@@deriving show { with_path = false }, eq]

type intrin_op = [ `RepeatBits ] [@@deriving eq]

type intrin = { op : intrin_op; ty_args : BType.t list; ty_return : BType.t }
[@@deriving eq]

let intrin_name i = match i.op with `RepeatBits -> "repeat_bits"

module ExprType = struct
  (* could maybe use ppx_deriving enum for this, unsure if it supports polymorphic variants though*)
  let hash_op = Hashtbl.hash

  type ('v, 'e) expr_node =
    | RVar of 'v
    | AssocExpr of assocop * 'e list
    | BinaryExpr of binop * 'e * 'e
    | UnaryExpr of unop * 'e
    | BVZeroExtend of int * 'e
    | BVSignExtend of int * 'e
    | BVExtract of { hi : int; lo : int; arg : 'e }
    | BVConcat of 'e * 'e
    | BVConst of PrimQFBV.t
    | IntConst of Z.t
    | BoolConst of bool
    | Old of 'e
    | Binding of { bound : 'v list; body : 'e }
    | FApplyIntrin of {
        name : intrin;
        args : 'e list;
        ty_return : BType.t option;
      }
    | FApply of { name : string; args : 'e list }
  [@@deriving eq, map, fold, iter]

  let equal eq_var eq_subexpr e1 e2 = equal_expr_node eq_var eq_subexpr e1 e2
  let map f e = map_expr_node identity f e
  let iter f e = iter_expr_node (fun i -> ()) f e
  let fold f i e = fold_expr_node (fun i a -> i) f i e

  let hash hash_var hash e1 : int =
    let open HashHelper in
    match e1 with
    | RVar i -> hash_var i
    | Binding { bound; body } -> combinel (hash body) (List.map hash_var bound)
    | AssocExpr (bop, es) -> combinel (hash_op bop) (List.map hash es)
    | BinaryExpr (bop, e1, e2) -> combine2 (hash_op bop) (hash e1) (hash e2)
    | UnaryExpr (uop, e1) ->
        combine2 (hash_op `SignExtend) (hash e1) (hash_op uop)
    | BVZeroExtend (i, e) ->
        combine2 (hash_op `ZeroExtend) (hash e) (Hashtbl.hash i)
    | BVSignExtend (i, e) ->
        combine2 (hash_op `SignExtend) (hash e) (Hashtbl.hash i)
    | BVExtract { hi; lo; arg } ->
        combine3 (hash_op `BVExtract) (hash arg) (Hashtbl.hash hi)
          (Hashtbl.hash lo)
    | BVConcat (e1, e2) -> combine2 (hash_op `BVConcat) (hash e1) (hash e2)
    | BVConst bv -> PrimQFBV.hash bv
    | IntConst i -> combine (hash_op `IntConst) (Hashtbl.hash i)
    | BoolConst b -> combine (hash_op `BoolConst) (Hashtbl.hash b)
    | Old b -> hash b
    | FApply { name; args } -> combinel (Hashtbl.hash name) (List.map hash args)
    | FApplyIntrin { name; args; ty_return } ->
        combine (Hashtbl.hash name)
          (combinel (Hashtbl.hash ty_return) (List.map hash args))

  module Final (F : sig
    type v
    type e
    type f

    val fix : (v, e) expr_node -> f
  end) =
  struct
    (* smart constrs*)
    let intconst v = F.fix (IntConst v)
    let bvconst ~(width : int) v = F.fix (BVConst (PrimQFBV.of_int ~width v))
    let assocexp ~op ls = F.fix (AssocExpr (op, ls))
    let binexp ~op l r = F.fix (BinaryExpr (op, l, r))
    let unexp ~op arg = F.fix (UnaryExpr (op, arg))

    let zero_extend ~n_prefix_bits arg =
      F.fix (BVZeroExtend (n_prefix_bits, arg))

    let sign_extend ~n_prefix_bits arg =
      F.fix (BVSignExtend (n_prefix_bits, arg))

    let old e = F.fix (Old e)
    let fapply name args = F.fix (FApply { name; args })

    let bvextract ~hi_incl ~lo_excl arg =
      F.fix (BVExtract { hi = hi_incl; lo = lo_excl; arg })

    let bvconcat arg1 arg2 = F.fix (BVConcat (arg1, arg2))
    let bvconst bv = F.fix (BVConst bv)
    let intconst i = F.fix (IntConst i)
    let boolconst b = F.fix (BoolConst b)
    let variable v = F.fix (RVar v)
  end
end

module Recursion (E : sig
  type 'e node

  val fix : 'e node -> 'e
  val unfix : 'a -> 'a node
  val map : ('a -> 'b) -> 'a node -> 'b node
end) =
struct
  let ( >> ) = fun f g x -> g (f x)

  let rec cata : 'b. ('b E.node -> 'b) -> 'e -> 'b =
   fun alg -> E.unfix >> E.map (cata alg) >> alg
end

module Expr (V : ORD_TYPE) = struct
  open ExprType

  type expr = expr_node_v Fix.HashCons.cell
  and expr_node_v = E of (V.t, expr) ExprType.expr_node [@@unboxed]

  module ExprHashType = struct
    type t = expr_node_v

    let equal (e1 : t) (e2 : t) =
      match (e1, e2) with
      | E e1, E e2 -> ExprType.equal V.equal Fix.HashCons.equal e1 e2

    let hash = function E e -> ExprType.hash V.hash Fix.HashCons.hash e
  end

  module M = Fix.HashCons.ForHashedTypeWeak (ExprHashType)

  let fix (e : (V.t, expr) ExprType.expr_node) = M.make (E e)

  let unfix (e : expr) : (V.t, expr) ExprType.expr_node =
    match e.data with E e -> e

  (* this map definition embeds unfix *)
  let map f e = ExprType.map f e
  let ( >> ) = fun f g x -> g (f x)
  let rec cata alg e = (unfix >> map (cata alg) >> alg) e

  module Memoiser = Fix.Memoize.ForHashedType (struct
    type t = expr

    let equal = Fix.HashCons.equal
    let hash = Fix.HashCons.hash
  end)

  let cata_memo (alg : (V.t, 'a) expr_node -> 'a) =
    let g r t = map r (unfix t) |> alg in
    Memoiser.fix g

  let printer_alg show_v e =
    match (e : ('v, 'a) expr_node) with
    | RVar id -> show_v id
    | AssocExpr (op, args) ->
        Format.sprintf "%s(%s)" (show_assocop op) (String.concat ", " args)
    | BinaryExpr (op, l, r) -> Format.sprintf "%s(%s, %s)" (show_binop op) l r
    | UnaryExpr (op, a) -> Format.sprintf "%s(%s)" (show_unop op) a
    | BVZeroExtend (n, a) -> Format.sprintf "zero_extend(%d, %s)" n a
    | BVSignExtend (n, a) -> Format.sprintf "sign_extend(%d, %s)" n a
    | BVConcat (l, r) -> Format.sprintf "concat(%s, %s)" l r
    | BVConst i -> PrimQFBV.show i
    | IntConst i -> Value.show_integer i
    | BoolConst true -> "true"
    | BoolConst false -> "false"
    | Old e -> Format.sprintf "old(%s)" e
    | FApply { name; args } ->
        Format.sprintf "%s(%s)" name (String.concat "," args)
    | FApplyIntrin { name; args } ->
        Format.sprintf "%s(%s)" (intrin_name name) (String.concat "," args)
    | BVExtract { hi; lo; arg } ->
        Format.sprintf "extract(%d, %d, %s)" hi lo arg
    | Binding { bound; body } ->
        Format.sprintf "(%s) . %s"
          (String.concat ", " (List.map show_v bound))
          body

  let to_string =
    let alg e = printer_alg V.show e in
    cata alg

  module S = Set.Make (V)

  let free_vars e =
    let alg = function
      | RVar id -> S.singleton id
      | o -> ExprType.fold S.union S.empty o
    in
    cata alg e

  include ExprType.Final (struct
    type v = V.t
    type e = expr
    type f = expr_node_v Fix.HashCons.cell

    let fix = fix
  end)

  let%expect_test _ =
    print_string @@ to_string
    @@ binexp ~op:`INTADD (intconst (Z.of_int 50)) (intconst (Z.of_int 100));
    [%expect "\n      `INTADD(50, 100)"]

  let exp () =
    binexp ~op:`INTADD
      (intconst (Z.of_int 50))
      (binexp ~op:`INTADD
         (intconst (Z.of_int 50))
         (binexp ~op:`INTADD
            (intconst (Z.of_int 50))
            (binexp ~op:`INTADD
               (intconst (Z.of_int 50))
               (intconst (Z.of_int 5)))))

  let%expect_test _ =
    let alg e =
      let s = printer_alg V.show e in
      print_endline s;
      s
    in
    let p = cata alg in
    ignore (p @@ exp ());
    [%expect
      "\n\
      \      5\n\
      \      50\n\
      \      `INTADD(50, 5)\n\
      \      50\n\
      \      `INTADD(50, `INTADD(50, 5))\n\
      \      50\n\
      \      `INTADD(50, `INTADD(50, `INTADD(50, 5)))\n\
      \      50\n\
      \      `INTADD(50, `INTADD(50, `INTADD(50, `INTADD(50, 5))))"]

  let%expect_test _ =
    let alg e =
      let s = printer_alg V.show e in
      print_endline s;
      s
    in
    let p = cata_memo alg in
    ignore (p @@ exp ());
    [%expect
      "\n\
      \      5\n\
      \      50\n\
      \      `INTADD(50, 5)\n\
      \      `INTADD(50, `INTADD(50, 5))\n\
      \      `INTADD(50, `INTADD(50, `INTADD(50, 5)))\n\
      \      `INTADD(50, `INTADD(50, `INTADD(50, `INTADD(50, 5))))"]
end

let () = Printexc.record_backtrace true
