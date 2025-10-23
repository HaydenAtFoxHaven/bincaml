open Value
open Common
module ID = Int
open Types
open Ast
open ContainersLabels

module Stmt = struct
  type endian = Big | Litle [@@deriving eq, ord]
  type ident = string

  type ('var, 'expr) t =
    | Instr_Assign of ('var * 'expr) list
    | Instr_Load of { lhs : 'var; addr : 'expr; endian : endian }
    | Instr_Store of {
        lhs : 'var;
        addr : 'expr;
        value : 'expr;
        endian : endian;
      }
    | Instr_Call of { lhs : 'var list; procid : ID.t; args : 'expr list }
    | Instr_IntrinCall of { lhs : 'var list; name : string; args : 'expr list }
    | Instr_IndirectCall of { target : 'expr }
  [@@deriving eq, ord]
end

module Block = struct
  type 'var phi = Phi of { lhs : 'var; rhs : (ID.t * 'var) list }
  [@@deriving eq, ord]

  type ('var, 'expr) t = {
    id : ID.t;
    phis : 'var phi list;
    stmts : ('var, 'expr) Stmt.t list;
  }
  [@@deriving eq, ord]
end

module Var = struct
  module V = struct
    type t = { name : string; typ : BType.t; pure : bool } [@@deriving eq, ord]

    let var name ?(pure = true) typ = { name; typ; pure }
    let hash v = Hashtbl.hash v
  end

  module H = Fix.HashCons.ForHashedTypeWeak (V)

  type t = V.t Fix.HashCons.cell

  let create name ?(pure = false) typ = H.make { name; typ; pure }
  let name (e : t) = (Fix.HashCons.data e).name
  let typ (e : t) = (Fix.HashCons.data e).typ
  let pure (e : t) = (Fix.HashCons.data e).pure
  let equal (a : t) (b : t) = Fix.HashCons.equal a b
  let hash (a : t) = Fix.HashCons.hash a

  module Set = CCHashSet.Make (V)
  module Bindings = CCHashTrie.Make (V)

  module Decls = struct
    type var = t
    type t = (string, var) Hashtbl.t

    let find_opt m name = Hashtbl.find_opt m name

    let add m (v : var) =
      let d = find_opt m (name v) in
      match d with
      | Some e when equal e v -> ()
      | Some e -> failwith "Already declared diff var with that name: "
      | None -> Hashtbl.add m (name v) v
  end
end

module Procedure = struct
  type ident = Proc of int [@@unboxed]

  module Vert = struct
    type t = Begin of ID.t | End of ID.t
    [@@deriving show { with_path = false }, eq, ord]

    let hash (v : t) =
      let h = Hash.pair Hash.int Hash.int in
      Hash.map (function Begin i -> (31, i) | End i -> (37, i)) h v
  end

  module Edge = struct
    type t = Block of ID.t | Jump [@@deriving eq, ord]

    let default = Jump
  end

  module Loc = Int
  module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)

  type 'e t = {
    id : ID.t;
    name : string;
    formal_in_params : Var.t list;
    formal_out_params : Var.t list;
    captures_globs : Var.Decls.t;
    modifies_globs : Var.Decls.t;
    requires : 'e list;
    ensures : 'e list;
    locals : Var.Decls.t;
    blocks : ((Var.t, 'e) Block.t, Vector.rw) Vector.t;
    block_i : (int, int) Hashtbl.t;
    graph : G.t;
    gensym : Fix.Gensym.gensym;
    gensym_bloc : Fix.Gensym.gensym;
  }

  let update_block_by_index p (b : ('a, 'b) Block.t) =
    let i =
      Hashtbl.get p.block_i b.id |> Option.get_exn_or "update nonexistent block"
    in
    Vector.set p.blocks i b

  let fresh_block p ?(phis = []) ~(stmts : ('var, 'expr) Stmt.t list) () =
    let open Block in
    let id = p.gensym_bloc () in
    let b = { id; phis; stmts } in
    Vector.push p.blocks b;
    id

  let fresh_var p ?(pure = true) typ =
    let n = "v" ^ Int.to_string (p.gensym ()) in
    let v = Var.create n typ in
    Var.Decls.add p.locals v;
    v

  let copy e = { e with graph = G.copy e.graph }
end

module Program = struct
  module IDMap = Map.Make (ID)

  type e = Var.t BasilExpr.t
  type proc = e Procedure.t
  type bloc = (Var.t, e) Block.t
  type t = { globals : Var.Decls.t; procs : proc IDMap.t }

  (*type t = { procedure_name : string IDMap.t; block_label : string IDMap.t }*)
end
