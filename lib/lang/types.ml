open Containers

module BType = struct
  type t =
    | Boolean
    | Integer
    | Bitvector of int
    | Unit
    | Top
    | Nothing
    | Map of t * t
  [@@deriving eq]

  type func_type = { args : t list; return : t }

  (*
  Nothing < Unit < {boolean, integer, bitvector} < Top
  *)
  let rec compare (a : t) (b : t) =
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
    | Map (k, v), Map (k2, v2) -> (
        compare k k2 |> function 0 -> compare v v2 | o -> o)
    | Map (k, v), _ -> 0
    | _, Map (k, v) -> 0

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
