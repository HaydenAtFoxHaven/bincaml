open Value
open Common
open Types
open Ast
open ContainersLabels
module ID = Int

module Stmt = struct
  type endian = [ `Big | `Little ] [@@deriving eq, ord]
  type ident = string

  type ('var, 'expr) t =
    | Instr_Assign of ('var * 'expr) list
    | Instr_Load of { lhs : 'var; rvar : Var.t; addr : 'expr; endian : endian }
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

  type t = {
    id : ID.t;
    phis : Var.t list;
    stmts : (Var.t, BasilExpr.t) Stmt.t list;
  }
  [@@deriving eq, ord]
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
    type block = Block.t [@@deriving eq, ord]
    type t = Block of block | Jump [@@deriving eq, ord]

    let default = Jump
  end

  module Loc = Int
  module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)

  type t = {
    id : ID.t;
    name : string;
    formal_in_params : Var.t list;
    formal_out_params : Var.t list;
    captures_globs : Var.Decls.t;
    modifies_globs : Var.Decls.t;
    requires : BasilExpr.t list;
    ensures : BasilExpr.t list;
    locals : Var.Decls.t;
    graph : G.t;
    gensym : Fix.Gensym.gensym;
    gensym_bloc : Fix.Gensym.gensym;
  }

  let add_goto p ~(from : ID.t) ~(targets : ID.t list) =
    let open Vert in
    let g = p.graph in
    let fr = End from in
    List.iter ~f:(fun t -> G.add_edge g fr (Begin t)) targets

  let create p id name ?(formal_in_params = []) ?(formal_out_params = [])
      ?(captures_globs = Var.Decls.empty ())
      ?(modifies_globs = Var.Decls.empty ()) ?(requires = []) ?(ensures = [])
      ?(locals = Var.Decls.empty ()) ?(blocks = Vector.create ()) () =
    {
      id;
      name;
      formal_in_params;
      formal_out_params;
      captures_globs;
      modifies_globs;
      requires;
      ensures;
      locals;
      graph = G.create ();
      gensym = Fix.Gensym.make ();
      gensym_bloc = Fix.Gensym.make ();
    }

  (*
  let update_block_by_index p (b : ('a, 'b) Block.t) =
    let i =
      Hashtbl.get p.block_i b.id |> Option.get_exn_or "update nonexistent block"
    in
    Vector.set p.blocks i b
    *)

  let fresh_block p ?(phis = []) ~(stmts : ('var, 'expr) Stmt.t list)
      ?(successors = []) () =
    let open Block in
    let id = p.gensym_bloc () in
    let b = Edge.(Block { id; phis; stmts }) in
    let open Vert in
    G.add_vertex p.graph (Begin id);
    G.add_vertex p.graph (Begin id);
    G.add_edge_e p.graph (Begin id, b, End id);
    List.iter ~f:(fun i -> G.add_edge p.graph (End id) (Begin i)) successors;
    id

  let get_block p id =
    let open Edge in
    let open G in
    try
      let _, e, _ = G.find_edge p.graph (Begin id) (End id) in
      match e with Block b -> Some b | Jump -> None
    with Not_found -> None

  let fresh_var p ?(pure = true) typ =
    let n = "v" ^ Int.to_string (p.gensym ()) in
    let v = Var.create n typ in
    Var.Decls.add p.locals v;
    v

  let copy e = { e with graph = G.copy e.graph }
end

module Program = struct
  module IDMap = Map.Make (ID)

  type e = BasilExpr.t
  type proc = Procedure.t
  type bloc = Block.t
  type stmt = (Var.t, e) Stmt.t
  type t = { modulename : string; globals : Var.Decls.t; procs : proc IDMap.t }

  let decl_glob p = Var.Decls.add p.globals

  let empty ?name () =
    let modulename = Option.get_or ~default:"<module>" name in
    { modulename; globals = Var.Decls.empty (); procs = IDMap.empty }

  (*type t = { procedure_name : string IDMap.t; block_label : string IDMap.t }*)
end
