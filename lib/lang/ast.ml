open Common
open Containers
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

  type ('const, 'var, 'unary, 'binary, 'intrin, 'e) abs =
    ('const, 'var, 'unary, 'binary, 'intrin, 'e) t

  module Final (F : sig
    type 'v t
    type const
    type unary
    type binary
    type intrin

    val fix : (const, 'v, unary, binary, intrin, 'v t) abs -> 'v t
    val unfix : 'v t -> (const, 'v, unary, binary, intrin, 'v t) abs
  end) =
  struct
    let ( >> ) = fun f g x -> g (f x)
    let rec cata alg e = (F.unfix >> map (cata alg) >> alg) e
  end
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

module type Ops = sig
  type const
  type unary
  type binary
  type intrin

  val hash_const : const -> int
  val hash_unary : unary -> int
  val hash_binary : binary -> int
  val hash_intrin : intrin -> int
  val pp_const : Format.formatter -> const -> unit
  val show_const : const -> string
  val equal_const : const -> const -> bool
  val pp_unary : Format.formatter -> unary -> unit
  val show_unary : unary -> string
  val equal_unary : unary -> unary -> bool
  val pp_binary : Format.formatter -> binary -> unit
  val show_binary : binary -> string
  val equal_binary : binary -> binary -> bool
  val pp_intrin : Format.formatter -> intrin -> unit
  val show_intrin : intrin -> string
  val equal_intrin : intrin -> intrin -> bool

  type ('var, 'e) t = (const, 'var, unary, binary, intrin, 'e) AbstractExpr.t
end

module AllOps : Ops = struct
  type const = [ IntOps.const | BVOps.const ]
  [@@deriving show { with_path = false }, eq]

  type unary = [ IntOps.unary | BVOps.unary ]
  [@@deriving show { with_path = false }, eq]

  type binary = [ IntOps.binary | BVOps.binary ]
  [@@deriving show { with_path = false }, eq]

  let hash_const = Hashtbl.hash
  let hash_unary = Hashtbl.hash
  let hash_binary = Hashtbl.hash
  let hash_intrin = Hashtbl.hash

  type intrin = BVOps.intrin [@@deriving show { with_path = false }, eq]
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
  let intconst v = fix (Constant v)
  let binexp ~op l r = fix (BinaryExpr (op, l, r))
  let unexp ~op arg = fix (UnaryExpr (op, arg))
  let fapply id params = fix (ApplyFun (id, params))
  let applyintrin id params = fix (ApplyIntrin (id, params))
  let identity x = x

  (* this map definition embeds unfix *)
  let map f e = EX.map f e
  let ( >> ) = fun f g x -> g (f x)
  let rec cata alg e = (unfix >> map (cata alg) >> alg) e
  let idf a b = a
end

module FixExpr (O : Ops) = struct
  module F = struct
    type const = O.const
    type unary = O.unary
    type binary = O.binary
    type intrin = O.intrin

    type 'v t = 'v expr_node_v

    and 'v expr_node_v =
      | E of (const, 'v, unary, binary, intrin, 'v t) AbstractExpr.t

    let fix e = E e
    let unfix e = match e with E e -> e
  end

  include F
  include AbstractExpr.Final (F)

  (* smart constructors*)
  let const v = fix (Constant v)
  let intconst v = fix (Constant v)
  let binexp ~op l r = fix (BinaryExpr (op, l, r))
  let unexp ~op arg = fix (UnaryExpr (op, arg))
  let fapply id params = fix (ApplyFun (id, params))
  let applyintrin id params = fix (ApplyIntrin (id, params))
  let identity x = x
end

module BasilExpr = struct
  include FixExpr (AllOps)
end
