open Types
open Common
open Value

module type A = sig
  type 'a t

  val add : 'a t -> 'a t -> 'a t
  val sub : 'a t -> 'a t -> 'a t
  val mul : 'a t -> 'a t -> 'a t
  val div : 'a t -> 'a t -> 'a t
end

module BV = struct
  type bvbinop = BVAADD | BVSUB | BVOR | BVAND | BVXOR
  type intbinop = INTADD | INTSUB
  type intunop = BVNEG | BVNOT
  type bvunop = INTNEG | INTNOT

  type bvcompop =
    | BVULE
    | BVUGE
    | BVSGE
    | BVSLE
    | BVULT
    | BVUGT
    | BVSGT
    | BVSLT

  type intcompop = LE | GE | LT | GT

  type 'e intexpr =
    | BVConst of Z.t
    | BVBinary of intbinop * 'e * 'e
    | BVUnary of intunop * 'e

  type 'e bvexpr =
    | BVConst of PrimQFBV.t
    | BVBinary of bvbinop * 'e * 'e
    | BVUnary of bvunop * 'e

  type 'e predicate =
    | BoolConst of bool
    | BoolOr of 'e list
    | BoolAnd of 'e list
    | BoolEq of 'e * 'e
    | BoolBVComp of bvcompop * 'e * 'e
    | BoolIntComp of intcompop * 'e * 'e

  type 'e expr =
    | Int of 'e expr intexpr
    | BV of 'e expr bvexpr
    | Bool of 'e expr predicate
end
