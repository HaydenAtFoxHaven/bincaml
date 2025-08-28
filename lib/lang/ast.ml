open Common
open Value

module AbstractExpr = struct
  type ('const, 'var, 'unary, 'binary, 'intrin, 'e) t =
    | RVar of 'var  (** variables *)
    | Constant of 'const
        (** constants; a pure intrinsic function with zero arguments *)
    | UnaryExpr of 'unary * 'e
        (** application of a pure intrinsic function with one arguments *)
    | BinaryExpr of 'binary * 'e * 'e
        (** application of a pure intrinsic function with two arguments *)
    | ApplyIntrin of 'intrin * 'e list
        (** application of a pure intrinsic function with n arguments *)
    | ApplyFun of string * 'e list
        (** application of a pure runtime-defined function with n arguments *)
    | Binding of 'var list * 'e  (** syntactic binding in a nested scope *)
  [@@deriving eq, fold, map, iter]

  let id a b = a
  let ofold = fold
  let fold f b o = ofold id id id id id f b o
  let omap = map

  let map f e =
    let id a = a in
    omap id id id id id f e

  let hash hash e1 =
    let hash_const = Hashtbl.hash in
    let hash_var = Hashtbl.hash in
    let hash_unary = Hashtbl.hash in
    let hash_binary = Hashtbl.hash in
    let hash_intrin = Hashtbl.hash in
    let open HashHelper in
    match e1 with
    | RVar r -> combine 1 (hash_var r)
    | UnaryExpr (op, a) -> combine2 3 (hash_unary op) (hash a)
    | BinaryExpr (op, l, r) -> combine3 5 (hash_binary op) (hash l) (hash r)
    | Constant c -> combine 7 (hash_const c)
    | ApplyIntrin (i, args) ->
        combine 11 (combinel (hash_intrin i) (List.map hash args))
    | ApplyFun (n, args) ->
        combine 13 (combinel (String.hash n) (List.map hash args))
    | Binding (args, body) ->
        combine 17 (combinel (hash body) (List.map hash_var args))

  module Final (F : sig
    type e
    type f

    val fix : ('a, 'b, 'c, 'd, 'e, e) t -> f
  end) =
  struct
    (* smart constrs*)

    let bvconst ~(width : int) v =
      F.fix (Constant (`Bitvector (PrimQFBV.of_int ~width v)))

    let assocexp ~op ls = F.fix (ApplyIntrin (op, ls))
    let binexp ~op l r = F.fix (BinaryExpr (op, l, r))
    let unexp ~op arg = F.fix (UnaryExpr (op, arg))
    let boolconst b = F.fix (Constant (`Boolean b))
    let variable v = F.fix (RVar v)
  end
end

module Var = struct
  type t = Int.t

  let equal = Int.equal
  let hash = Int.hash
  let show = Int.to_string
  let compare = Int.compare
end

module Unary = struct
  type unary = [ `BITNOT | `LOGNOT | `NEG ]
  [@@deriving show { with_path = false }, eq, enum]

  let hash_unary = unary_to_enum
end

module LogicalOps = struct
  type const = [ `Bool of bool ] [@@deriving show { with_path = false }, eq]
  type unary = [ `LNOT ] [@@deriving show { with_path = false }, eq]
  type binary = [ `EQ | `NEQ ] [@@deriving show { with_path = false }, eq]
  type assoc = [ `BitAND | `BitOR ]
  type intrin = [ `BVConcat ]

  let show = function
    | #const as c -> show_const c
    | #unary as u -> show_unary u
    | #binary as b -> show_binary b

  let hash_boolop = Hashtbl.hash
end

module BVOps = struct
  type const = [ `Bitvector of PrimQFBV.t | LogicalOps.const ]
  [@@deriving show { with_path = false }, eq]

  type unary = [ LogicalOps.unary | `BITNOT | `BVNEG ]
  [@@deriving show { with_path = false }, eq]

  type binary =
    [ LogicalOps.binary
    | `BVAND
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
    | `BVASHR
    | `BVULT
    | `BVULE
    | `BVSLT
    | `BVSLE ]
  [@@deriving show { with_path = false }, eq]

  type intrin =
    [ `ZeroExtend of int | `SignExtend of int | `Extract of int * int ]
  [@@deriving show { with_path = false }, eq]

  let show = function
    | #const as c -> show_const c
    | #unary as u -> show_unary u
    | #binary as b -> show_binary b
end

module IntOps = struct
  type const = [ `Integer of PrimInt.t ]
  [@@deriving show { with_path = false }, eq]

  type unary = [ `INTNEG ] [@@deriving show { with_path = false }, eq]

  type binary = [ `INTADD | `INTMUL | `INTSUB | `INTDIV | `INTMOD ]
  [@@deriving show { with_path = false }, eq]

  let show = function
    | #const as c -> show_const c
    | #unary as u -> show_unary u
    | #binary as b -> show_binary b
end

module Spec = struct
  type unary = [ `Forall | `Old | `Exists ]
  [@@deriving show { with_path = false }, eq]

  let hash_intrin a = Hashtbl.hash a
end

module AllLogics = struct
  type const = [ IntOps.const | BVOps.const ]
  type unary = [ IntOps.unary | BVOps.unary ]
  type binary = [ IntOps.binary | BVOps.binary ]
  type intrin = BVOps.intrin
  type ('var, 'e) t = (const, 'var, unary, binary, intrin, 'e) AbstractExpr.t
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

module Expr = struct
  module EX = AbstractExpr

  type ('a, 'b, 'c, 'd, 'e) expr = ('a, 'b, 'c, 'd, 'e) expr_node_v

  and ('a, 'b, 'c, 'd, 'e) expr_node_v =
    | E of ('a, 'b, 'c, 'd, 'e, ('a, 'b, 'c, 'd, 'e) expr) EX.t

  let fix (e : ('a, 'b, 'c, 'd, 'e, ('a, 'b, 'c, 'd, 'e) expr) EX.t) = E e

  let unfix (e : ('a, 'b, 'c, 'd, 'e) expr) :
      ('a, 'b, 'c, 'd, 'e, ('a, 'b, 'c, 'd, 'e) expr) EX.t =
    match e with E e -> e

  (* smart constructors *)
  let const v = fix (Constant v)
  let intconst v = fix (Constant (BValue.Integer v))
  let binexp ~op l r = fix (BinaryExpr (op, l, r))
  let unexp ~op arg = fix (UnaryExpr (op, arg))
  let fapply id params = fix (ApplyFun (id, params))
  let applyintrin id params = fix (ApplyIntrin (id, params))
  let identity x = x

  (* this map definition embeds unfix *)
  let map f e = EX.map f e
  let ( >> ) = fun f g x -> g (f x)
  let rec cata alg e = (unfix >> map (cata alg) >> alg) e

  module S = Set.Make (Var)

  let idf a b = a

  let free_vars e =
    let alg = function
      | EX.RVar id -> S.singleton id
      | o -> EX.fold S.union S.empty o
    in
    cata alg e

  let substitute e =
    let open EX in
    let alg = function RVar i -> fix (RVar 0) | t -> fix t in
    cata alg e
end

let printer_alg e =
  let open AbstractExpr in
  match e with
  | RVar id -> Var.show id
  | BinaryExpr (op, l, r) -> Format.sprintf "%s(%s, %s)" (show_binop op) l r
  | UnaryExpr (op, a) -> Format.sprintf "%s(%s)" (Unary.show_unary op) a
  | Constant i -> BValue.show i
  | ApplyIntrin (intrin, args) ->
      Format.sprintf "%s(%s)"
        (Intrin.show_intrin intrin)
        (String.concat ", " args)
  | ApplyFun (n, args) -> Format.sprintf "%s(%s)" n (String.concat ", " args)
  | Binding (vars, body) ->
      Format.sprintf "((%s) -> %s)"
        (String.concat ", " (List.map Var.show vars))
        body

let log_alg =
  let alg e =
    let s = printer_alg e in
    print_endline s;
    s
  in
  alg

let%expect_test _ =
  let open AbstractExpr in
  let open Expr in
  let to_string =
    let alg e = printer_alg e in
    cata alg
  in
  let e = fix @@ Constant (BValue.Integer (Z.of_int 50)) in
  print_string @@ to_string @@ binexp ~op:`INTADD e e;
  [%expect {|`INTADD(50, 50) |}]

let exp_bool () =
  let open Expr in
  binexp ~op:`BOOLAND
    (intconst (Z.of_int 50))
    (binexp ~op:`BOOLAND
       (intconst (Z.of_int 50))
       (binexp ~op:`BOOLAND
          (intconst (Z.of_int 50))
          (binexp ~op:`BOOLAND (intconst (Z.of_int 50)) (intconst (Z.of_int 5)))))

let exp_all () =
  let open Expr in
  binexp ~op:`INTADD
    (intconst (Z.of_int 50))
    (binexp ~op:`INTADD
       (intconst (Z.of_int 50))
       (binexp ~op:`INTADD
          (intconst (Z.of_int 50))
          (binexp ~op:`INTADD (intconst (Z.of_int 50)) (intconst (Z.of_int 5)))))

let%expect_test _ =
  let alg = log_alg in
  let open Expr in
  let p = cata alg in
  ignore (p @@ exp_all ());
  [%expect
    {|
  5
  50
  `INTADD(50, 5)
  50
  `INTADD(50, `INTADD(50, 5))
  50
  `INTADD(50, `INTADD(50, `INTADD(50, 5)))
  50
  `INTADD(50, `INTADD(50, `INTADD(50, `INTADD(50, 5))))|}]

let%expect_test _ =
  let alg = log_alg in
  let open Expr in
  let p = cata alg in
  ignore (p @@ exp_bool ());
  [%expect
    {| 
      5
      50
      `BOOLAND(50, 5)
      50
      `BOOLAND(50, `BOOLAND(50, 5))
      50
      `BOOLAND(50, `BOOLAND(50, `BOOLAND(50, 5)))
      50
      `BOOLAND(50, `BOOLAND(50, `BOOLAND(50, `BOOLAND(50, 5))))
    |}]

let () = Printexc.record_backtrace true
