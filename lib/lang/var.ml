open Common
open ContainersLabels
open Value
open Types

module V = struct
  type t = { name : string; typ : Types.BType.t; pure : bool }
  [@@deriving eq, ord]

  let show (v : t) : string = Printf.sprintf "%s:%s" v.name (BType.show v.typ)
  let pp fmt (b : t) : unit = Format.pp_print_string fmt (show b)
  let var name ?(pure = true) typ = { name; typ; pure }
  let hash v = Hashtbl.hash v
end

module H = Fix.HashCons.ForHashedTypeWeak (V)

type t = V.t Fix.HashCons.cell

let show v =
  Printf.sprintf "{id=%d ; data=%s}" (Fix.HashCons.id v)
    (V.show (Fix.HashCons.data v))

let pp fmt v = Format.pp_print_string fmt (show v)
let to_string v = V.show (Fix.HashCons.data v)
let create name ?(pure = false) typ = H.make { name; typ; pure }
let name (e : t) = (Fix.HashCons.data e).name
let typ (e : t) = (Fix.HashCons.data e).typ
let pure (e : t) = (Fix.HashCons.data e).pure
let compare (a : t) (b : t) = Fix.HashCons.compare a b
let equal (a : t) (b : t) = Fix.HashCons.equal a b
let hash (a : t) = Fix.HashCons.hash a

module Set = CCHashSet.Make (V)
(**FIXME: these do not use the hash-consign*)

module Bindings = CCHashTrie.Make (V)

module Decls = struct
  type 'v t = (string, 'v) Hashtbl.t

  let find_opt m name = Hashtbl.find_opt m name
  let empty () : 'v t = Hashtbl.create 30

  let add m (v : 'v) =
    let d = find_opt m (name v) in
    match d with
    | Some e when equal e v -> ()
    | Some e -> failwith "Already declared diff var with that name: "
    | None -> Hashtbl.add m (name v) v
end
