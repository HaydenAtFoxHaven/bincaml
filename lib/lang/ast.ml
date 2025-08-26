module HashHelper = struct
  let combine acc n = (acc * 65599) + n
  let combine2 acc n1 n2 = combine (combine acc n1) n2
  let combine3 acc n1 n2 n3 = combine (combine (combine acc n1) n2) n3

  let rec combinel acc n1 =
    match n1 with [] -> acc | h :: tl -> combinel (combine acc h) tl
end

module Value = struct
  type integer = Z.t

  let pp_integer = Z.pp_print
  let show_integer i = Z.to_string i
  let equal_integer i j = Z.equal i j

  type bitvector = int * integer [@@deriving eq]

  let bv_size b = fst b
  let bv_val b = snd b

  let show_bitvector (b : bitvector) =
    Printf.sprintf "0x%s:bv%d" (Z.format "%x" @@ bv_val b) (bv_size b)

  let pp_bitvector fmt b = Format.pp_print_string fmt (show_bitvector b)

  type t =
    | Integer of integer
    | Bitvector of bitvector
    | Boolean of bool
    | Unit
  [@@deriving show, eq]

  let hash a =
    let open HashHelper in
    match a with
    | Unit -> 1
    | Integer i -> combine 2 (Z.hash i)
    | Boolean true -> combine 5 1
    | Boolean false -> combine 7 2
    | Bitvector (sz, i) -> combine2 11 (Int.hash sz) (Z.hash i)
end

module type TYPE = sig
  type t

  val show : t -> string
  val equal : t -> t -> bool
  val hash : t -> int
end

module BType = struct
  type t = Boolean | Integer | Bitvector of int | Unit | Top | Nothing
  [@@deriving eq]

  (*
  Nothing < Unit < {boolean, integer, bitvector} < Top
  *)
  let compare (a : t) (b : t) =
    match (a, b) with
    | Top, Top -> 0
    | Top, _ -> 1
    | _, Top -> -1
    | Nothing, Nothing -> 0
    | Nothing, _ -> -1
    | _, Nothing -> 1
    | Unit, _ -> -1
    | _, Unit -> 1
    | Boolean, Integer -> 0
    | Integer, Boolean -> 0
    | Boolean, Bitvector _ -> 0
    | Bitvector _, Boolean -> 0
    | Boolean, Boolean -> 0
    | Integer, Bitvector _ -> 0
    | Bitvector _, Integer -> 0
    | Bitvector a, Bitvector b -> Int.compare a b
    | Integer, Integer -> 0

  type lambda = Leaf of t | Lambda of (lambda * lambda)

  let rec curry ?(acc = []) (l : lambda) : lambda list * lambda =
    match l with
    | Leaf _ as l -> (List.rev acc, l)
    | Lambda (l, ts) -> curry ~acc:(l :: acc) ts

  let uncurry (args : lambda list) (v : lambda) =
    List.fold_left (fun a p -> Lambda (a, p)) v

  let leaf_to_string = function
    | Boolean -> "bool"
    | Integer -> "int"
    | Bitvector i -> "bv" ^ Int.to_string i
    | Unit -> "()"
    | Top -> "⊤"
    | Nothing -> "⊥"

  let rec lambda_to_string = function
    | Lambda ((Lambda _ as a), Leaf b) ->
        "(" ^ lambda_to_string a ^ ")" ^ "->" ^ leaf_to_string b
    | Lambda ((Lambda _ as a), (Lambda _ as b)) ->
        "(" ^ lambda_to_string a ^ ")" ^ "->" ^ "(" ^ lambda_to_string b ^ ")"
    | Lambda (Leaf a, (Lambda _ as b)) ->
        "(" ^ leaf_to_string a ^ ")" ^ "->" ^ lambda_to_string b
    | Lambda (Leaf a, Leaf b) -> leaf_to_string a ^ "->" ^ leaf_to_string b
    | Leaf l -> leaf_to_string l
end

module ExprType
    (PrimConst : TYPE)
    (V : TYPE)
    (PrimUnary : TYPE)
    (PrimBinary : TYPE)
    (PrimFun : TYPE) =
struct
  open Value

  (* may need to ppx_import these types?
  type vartype = V.t
  type constop = PrimConst.t
  type unaryop = PrimUnary.t
  type binaryop = PrimBinary.t
  type funop = PrimFun.t
  *)

  (* expression ops with an explicit variant, this is used just for hash consing *)

  type 'e expr_node =
    | RVar of V.t  (** variables *)
    | Constant of PrimConst.t
        (** constants; a pure intrinsic function with zero arguments *)
    | UnaryExpr of PrimUnary.t * 'e
        (** application of a pure intrinsic function with one arguments *)
    | BinaryExpr of PrimBinary.t * 'e * 'e
        (** application of a pure intrinsic function with two arguments *)
    | ApplyIntrin of PrimFun.t * 'e list
        (** application of a pure intrinsic function with n arguments *)
    | ApplyFun of string * 'e list
        (** application of a pure runtime-defined function with n arguments *)
    | Binding of V.t list * 'e  (** syntactic binding in a nested scope *)
  [@@deriving eq, fold, map, iter]
  (* store, load *)

  let equal eq_var eq_expr = equal_expr_node eq_var eq_expr

  let hash : ('e -> int) -> 'e expr_node -> int =
   fun hash e1 ->
    let open HashHelper in
    match e1 with
    | RVar r -> combine 1 (V.hash r)
    | UnaryExpr (op, a) -> combine2 3 (PrimUnary.hash op) (hash a)
    | BinaryExpr (op, l, r) -> combine3 5 (PrimBinary.hash op) (hash l) (hash r)
    | Constant c -> combine 7 (PrimConst.hash c)
    | ApplyIntrin (i, args) ->
        combine 11 (combinel (PrimFun.hash i) (List.map hash args))
    | ApplyFun (n, args) ->
        combine 13 (combinel (String.hash n) (List.map hash args))
    | Binding (args, body) ->
        combine 17 (combinel (hash body) (List.map V.hash args))
end

module Var = struct
  type t = Int.t

  let equal = Int.equal
  let hash = Int.hash
  let show = Int.to_string
  let compare = Int.compare
end

module Unary = struct
  type t = [ `BITNOT | `LOGNOT | `NEG ]
  [@@deriving show { with_path = false }, eq, enum]

  let hash = to_enum
end

module BoolBinOp = struct
  type t =
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
  [@@deriving show { with_path = false }, eq, enum]

  let hash = to_enum
end

module BVBinOp = struct
  type t =
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
  [@@deriving show { with_path = false }, eq, enum]

  let hash = to_enum
end

module IntBinOp = struct
  type t = [ `INTADD | `INTMUL | `INTSUB | `INTDIV | `INTMOD ]
  [@@deriving show { with_path = false }, eq, enum]

  let hash = to_enum
end

module Binary = struct
  type t = [ BVBinOp.t | IntBinOp.t | BoolBinOp.t ]
  [@@deriving show { with_path = false }, eq]

  let hash a =
    match a with
    | #BVBinOp.t as a -> BVBinOp.hash a
    | #BoolBinOp.t as a -> BoolBinOp.hash a
    | #IntBinOp.t as a -> IntBinOp.hash a
end

module Intrin = struct
  type t =
    [ `ZeroExtend of int
    | `SignExtend of int
    | `BITConcat
    | `Old
    | `BitExtract of int * int
    | `EQ
    | `NEQ
    | `BOOLAND
    | `BOOLOR ]
  [@@deriving show { with_path = false }, eq]

  let hash a = Hashtbl.hash a
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

module AllExpr = ExprType (Value) (Var) (Unary) (Binary) (Intrin)

module Expr = struct
  module EX = AllExpr

  type expr = expr_node_v Fix.HashCons.cell
  and expr_node_v = E of expr EX.expr_node [@@unboxed]

  module ExprHashType = struct
    type t = expr_node_v

    let equal (e1 : t) (e2 : t) =
      match (e1, e2) with
      | E e1, E e2 -> EX.equal_expr_node Fix.HashCons.equal e1 e2

    let hash = function E e -> EX.hash Fix.HashCons.hash e
  end

  module M = Fix.HashCons.ForHashedTypeWeak (ExprHashType)

  let fix (e : expr EX.expr_node) = M.make (E e)
  let unfix (e : expr) : expr EX.expr_node = match e.data with E e -> e

  (* smart constructors *)
  let const v = fix (Constant v)
  let intconst v = fix (Constant (Integer v))
  let boolconst v = fix (Constant (Boolean v))
  let bvconst v = fix (Constant (Bitvector v))
  let binexp ~op l r = fix (BinaryExpr (op, l, r))
  let unexp ~op arg = fix (UnaryExpr (op, arg))
  let fapply id params = fix (ApplyFun (id, params))
  let applyintrin id params = fix (ApplyIntrin (id, params))

  (* this map definition embeds unfix *)
  let map f e = EX.map_expr_node f e
  let ( >> ) = fun f g x -> g (f x)
  let rec cata alg e = (unfix >> map (cata alg) >> alg) e

  module Memoiser = Fix.Memoize.ForHashedType (struct
    type t = expr

    let equal = Fix.HashCons.equal
    let hash = Fix.HashCons.hash
  end)

  let cata_memo (alg : 'a EX.expr_node -> 'a) =
    let g r t = map r (unfix t) |> alg in
    Memoiser.fix g

  module S = Set.Make (Var)

  let printer_alg e =
    match (e : 'a EX.expr_node) with
    | RVar id -> Var.show id
    | BinaryExpr (op, l, r) -> Format.sprintf "%s(%s, %s)" (Binary.show op) l r
    | UnaryExpr (op, a) -> Format.sprintf "%s(%s)" (Unary.show op) a
    | Constant i -> Value.show i
    | ApplyIntrin (intrin, args) ->
        Format.sprintf "%s(%s)" (Intrin.show intrin) (String.concat ", " args)
    | ApplyFun (n, args) -> Format.sprintf "%s(%s)" n (String.concat ", " args)
    | Binding (vars, body) ->
        Format.sprintf "((%s) -> %s)"
          (String.concat ", " (List.map Var.show vars))
          body

  let to_string =
    let alg e = printer_alg e in
    cata alg

  let free_vars e =
    let alg = function
      | EX.RVar id -> S.singleton id
      | o -> EX.fold_expr_node S.union S.empty o
    in
    cata alg e

  let substitute e =
    let alg = function EX.RVar i -> fix (RVar 0) | t -> fix t in
    cata alg e

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
      let s = printer_alg e in
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
      let s = printer_alg e in
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
