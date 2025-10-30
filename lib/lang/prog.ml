open Value
open Common
open Types
open Expr
open Containers

module Params = struct
  module M = Map.Make (String) [@@deriving show]

  type formal = Var.t M.t [@@deriving eq, ord]
  type actual = BasilExpr.t M.t [@@deriving eq, ord]
  type lhs = Var.t M.t [@@deriving eq, ord]

  let show_actual a =
    M.to_list a
    |> List.map (function k, v ->
        Printf.sprintf "%s -> %s" k (BasilExpr.to_string v))
    |> String.concat ", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_actual fmt a = Format.pp_print_string fmt (show_actual a)

  let show_formal (a : formal) =
    M.to_list a
    |> List.map (function k, v -> Printf.sprintf "%s -> %s" k (Var.to_string v))
    |> String.concat ", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_formal fmt a = Format.pp_print_string fmt (show_formal a)

  let show_lhs (a : lhs) =
    M.to_list a
    |> List.map (function k, v -> Printf.sprintf "%s <- %s" (Var.to_string v) k)
    |> String.concat ", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_lhs fmt a = Format.pp_print_string fmt (show_lhs a)
end

module Stmt = struct
  type endian = [ `Big | `Little ] [@@deriving eq, ord]
  type ident = string

  let show_endian = function `Big -> "be" | `Little -> "le"
  let pp_endian fmt e = Format.pp_print_string fmt (show_endian e)

  type ('lvar, 'var, 'expr) t =
    | Instr_Assign of ('lvar * 'expr) list  (** simultaneous assignment *)
    | Instr_Assert of { body : 'expr }  (** assertions *)
    | Instr_Assume of { body : 'expr; branch : bool }  (** load from memory *)
    | Instr_Load of { lhs : 'lvar; mem : 'var; addr : 'expr; endian : endian }
        (** effectful operation calling a named intrinsic*)
    | Instr_IntrinCall of {
        lhs : 'lvar Params.M.t;
        name : string;
        args : 'expr Params.M.t;
      }  (** a store to memory *)
    | Instr_Store of {
        mem : 'var;
        addr : 'expr;
        value : 'expr;
        endian : endian;
      }
    | Instr_Return of { args : 'expr Params.M.t }
    | Instr_Call of {
        lhs : 'lvar Params.M.t;
        procid : ID.t;
        args : 'expr Params.M.t;
      }
    | Instr_IndirectCall of { target : 'expr }
  [@@deriving eq, ord, map]

  let map ~f_lvar ~f_expr ~f_rvar e = map f_lvar f_rvar f_expr e

  (** return an iterator over any memory field in the statement (read or
      written) *)
  let iter_mem_access stmt =
    match stmt with
    | Instr_Load { lhs; mem; addr; endian } -> Iter.singleton mem
    | Instr_Store { mem; addr; value; endian } -> Iter.singleton mem
    | _ -> Iter.empty

  (** return an iterator containing the memory written to by the statement *)
  let iter_mem_store stmt =
    match stmt with
    | Instr_Store { mem; addr; value; endian } -> Iter.singleton mem
    | _ -> Iter.empty

  (** get an iterator over the expresions in the RHS of the statement *)
  let iter_rexpr stmt =
    let open Iter.Infix in
    match stmt with
    | Instr_Assign ls -> List.to_iter ls >|= snd
    | Instr_Assert { body } -> Iter.singleton body
    | Instr_Assume { body } -> Iter.singleton body
    | Instr_Load { lhs; mem; addr; endian } -> Iter.singleton addr
    | Instr_Store { mem; addr; value; endian } ->
        Iter.singleton value <+> Iter.singleton addr
    | Instr_IntrinCall { lhs; name; args } -> Params.M.to_iter args >|= snd
    | Instr_IndirectCall { target } -> Iter.singleton target
    | Instr_Call { lhs; procid; args } -> Params.M.to_iter args >|= snd
    | Instr_Return { args } -> Params.M.to_iter args >|= snd

  (** get an iterator over the variables in the LHS of the statement *)
  let iter_lvar stmt =
    let open Iter.Infix in
    match stmt with
    | Instr_Assign ls -> List.to_iter ls >|= fst
    | Instr_Assert { body } -> Iter.empty
    | Instr_Assume { body } -> Iter.empty
    | Instr_Load { lhs; mem; addr; endian } -> Iter.singleton lhs
    | Instr_Store { mem; addr; value; endian } -> Iter.singleton mem
    | Instr_IntrinCall { lhs; name; args } -> Params.M.to_iter lhs >|= snd
    | Instr_IndirectCall { target } -> Iter.empty
    | Instr_Call { lhs; procid; args } -> Params.M.to_iter lhs >|= snd
    | Instr_Return { args } -> Iter.empty

  (** Get pretty-printer for il format*)
  let pretty show_var show_expr s =
    let open Containers_pp in
    let open Containers_pp.Infix in
    let param_list l =
      if Params.M.is_empty l then text "()"
      else
        let l = Params.M.to_list l |> List.map (fun (i, t) -> t) in
        bracket "(" (nest 2 (fill (text "," ^ newline_or_spaces 1) l)) ")"
    in
    let show_var v = text @@ show_var v in
    let show_expr e = text @@ show_expr e in
    let e = map ~f_lvar:show_var ~f_expr:show_expr ~f_rvar:show_var s in
    match e with
    | Instr_Assign ls ->
        let ls = List.map (function lhs, rhs -> lhs ^ text " := " ^ rhs) ls in
        fill (text " ,") ls
    | Instr_Assert { body } -> text "assert " ^ body
    | Instr_Assume { body; branch = false } -> text "assume " ^ body
    | Instr_Assume { body; branch = true } -> text "guard " ^ body
    | Instr_Load { lhs; mem; addr; endian } ->
        lhs ^ text " := " ^ text "load "
        ^ text (show_endian endian)
        ^ text " " ^ addr
    | Instr_Store { mem; addr; value; endian } ->
        text "store "
        ^ text (show_endian endian)
        ^ text " " ^ addr ^ text " " ^ value
    | Instr_IntrinCall { lhs; name; args } ->
        fill nil
          [
            param_list lhs;
            newline ^ text " := call ";
            text name;
            param_list args;
          ]
    | Instr_Call { lhs; procid; args } ->
        let n = ID.to_string procid in
        fill nil
          [
            param_list lhs; newline ^ text " := call "; text n; param_list args;
          ]
    | Instr_Return { args } -> text "return " ^ param_list args
    | Instr_IndirectCall { target } -> text "indirect_call " ^ target

  (** Pretty print to il format*)
  let to_string ?width show_var show_expr (s : (Var.t, Var.t, BasilExpr.t) t) =
    let width = Option.get_or ~default:80 width in
    let d = pretty show_var show_expr s in
    Containers_pp.Pretty.to_string ~width d
end

module Block = struct
  type 'var phi = { lhs : 'var; rhs : (ID.t * 'var) list }
  [@@deriving eq, ord, show]
  (** a phi node representing the join of incoming edges assigned to a lhs
      variable*)

  let pretty_phi show_var v =
    let open Containers_pp in
    let open Containers_pp.Infix in
    let lhs = text (show_var v.lhs) in
    let rhs =
      List.map
        (function
          | bid, v ->
              (text @@ ID.to_string bid) ^ text " -> " ^ text (show_var v))
        v.rhs
    in
    lhs ^ text " := phi" ^ (bracket "(" (fill (text ", ") rhs)) ")"

  type ('v, 'e) stmt_list = ('v, 'v, 'e) Stmt.t Vector.ro_vector

  type ('v, 'e) t = {
    id : ID.t;  (** the block identfier *)
    phis : 'v phi list;
        (** List of phi nodes simultaneously assigning each input variable *)
    stmts : ('v, 'e) stmt_list;  (** statement list *)
  }

  let equal _ _ a b = ID.equal a.id b.id
  let compare _ _ a b = ID.compare a.id b.id

  let pretty show_var show_expr ?(succ = []) b =
    let open Containers_pp in
    let open Containers_pp.Infix in
    let phi =
      match b.phis with
      | [] -> []
      | o ->
          let phi = List.map (pretty_phi show_var) o in
          [ bracket "(" (fill (text ",") phi) ")" ]
    in
    let jump =
      match succ with
      | [] -> text "unreachable"
      | succ ->
          text "goto " ^ (fun s -> bracket "(" (fill (text ",") s) ")") succ
    in
    let stmts =
      Vector.to_list b.stmts |> List.map (Stmt.pretty show_var show_expr)
    in
    let stmts = phi @ stmts @ [ jump ] in
    let stmts =
      bracket "["
        (nest 2 @@ newline ^ append_l ~sep:(text ";" ^ newline) stmts)
        "]"
    in
    text "block " ^ text (ID.to_string b.id) ^ text " " ^ stmts

  let to_string b =
    let stmts =
      Vector.map
        (fun stmt -> Stmt.to_string Var.to_string BasilExpr.to_string stmt)
        b.stmts
      |> Vector.to_iter
      |> String.concat_iter ~sep:";\n  "
    in
    Printf.sprintf "block %s [\n  %s]\n" (ID.to_string b.id) stmts

  let fold_stmt_forwards ~(phi : 'acc -> 'v phi list -> 'acc)
      ~(f : 'acc -> ('v, 'v, 'e) Stmt.t -> 'acc) (i : 'a) (b : ('v, 'e) t) :
      'acc =
    Iter.fold f (phi i b.phis) (Vector.to_iter b.stmts)

  let fold_stmt_backwards ~(f : 'acc -> ('v, 'v, 'e) Stmt.t -> 'acc)
      ~(phi : 'acc -> 'v phi list -> 'acc) ~(init : 'a) (b : ('v, 'e) t) : 'acc
      =
    Iter.fold f init (Vector.to_iter_rev b.stmts) |> fun e -> phi e b.phis
end

module Procedure = struct
  type ident = Proc of int [@@unboxed]

  module Vert = struct
    type t = Begin of ID.t | End of ID.t | Entry | Return | Exit
    [@@deriving show { with_path = false }, eq, ord]

    let hash (v : t) =
      let h = Hash.pair Hash.int Hash.int in
      Hash.map
        (function
          | Entry -> (1, 1)
          | Return -> (3, 1)
          | Exit -> (5, 1)
          | Begin i -> (31, ID.hash i)
          | End i -> (37, ID.hash i))
        h v

    let block_id_string = function
      | Begin i -> ID.to_string i
      | End i -> ID.to_string i
      | Entry -> "proc_entry"
      | Return -> "return"
      | Exit -> "exit"
  end

  module Edge = struct
    type block = (Var.t, BasilExpr.t) Block.t [@@deriving eq, ord]
    type t = Block of block | Jump [@@deriving eq, ord]

    let show = function Block b -> Block.to_string b | Jump -> "goto"
    let to_string = function Block b -> Block.to_string b | Jump -> "goto"
    let default = Jump
  end

  module Loc = Int

  module G = struct
    include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)
  end

  type ('v, 'e) proc_spec = {
    requires : BasilExpr.t list;
    ensures : BasilExpr.t list;
    captures_globs : 'v list;
    modifies_globs : 'v list;
  }

  type ('v, 'e) t = {
    id : ID.t;
    formal_in_params : 'v Params.M.t;
    formal_out_params : 'v Params.M.t;
    graph : G.t;
    locals : 'v Var.Decls.t;
    local_ids : ID.generator;
    block_ids : ID.generator;
    specification : ('v, 'e) proc_spec option;
  }

  let pretty show_var show_expr p =
    let open Containers_pp in
    let open Containers_pp.Infix in
    let params m =
      Params.M.to_list m
      |> List.map (function i, p -> show_var p)
      |> List.map text
      |> fun s -> bracket "(" (fill (text "," ^ newline_or_spaces 1) s) ")"
    in
    let header =
      text "proc "
      ^ text (ID.to_string p.id)
      ^ nest 2
          (fill
             (newline ^ text " -> ")
             [ params p.formal_in_params; params p.formal_out_params ])
    in
    let collect_edge b ende acc =
      let edge = G.E.label (G.find_edge p.graph b ende) in
      match edge with
      | Edge.(Block b) ->
          let succ = G.succ p.graph ende in
          let succ = List.map (fun v -> text (Vert.block_id_string v)) succ in
          let b = Block.pretty show_var show_expr ~succ b in
          b :: acc
      | _ -> acc
    in
    let blocks = G.fold_edges collect_edge p.graph [] in
    let blocks =
      surround (text "[")
        (nest 2 @@ newline
        ^ append_l ~sep:(text ";" ^ newline) (List.rev blocks))
        (newline ^ text "]")
    in
    header ^ nl ^ blocks

  let add_goto p ~(from : ID.t) ~(targets : ID.t list) =
    let open Vert in
    let g = p.graph in
    let fr = End from in
    List.iter (fun t -> G.add_edge g fr (Begin t)) targets

  let create id ?(formal_in_params = Params.M.empty)
      ?(formal_out_params = Params.M.empty) ?(captures_globs = [])
      ?(modifies_globs = []) ?(requires = []) ?(ensures = []) () =
    let graph = G.create () in
    let specification =
      Some { captures_globs; modifies_globs; requires; ensures }
    in
    G.add_vertex graph Entry;
    G.add_vertex graph Exit;
    G.add_vertex graph Return;
    {
      id;
      formal_in_params;
      formal_out_params;
      graph;
      locals = Var.Decls.empty ();
      local_ids = ID.make_gen ();
      block_ids = ID.make_gen ();
      specification;
    }

  let add_block p id ?(phis = []) ~(stmts : ('var, 'var, 'expr) Stmt.t list)
      ?(successors = []) () =
    let stmts = Vector.of_list stmts in
    let b = Edge.(Block { id; phis; stmts }) in
    let open Vert in
    G.add_vertex p.graph (Begin id);
    G.add_vertex p.graph (Begin id);
    G.add_edge_e p.graph (Begin id, b, End id);
    List.iter (fun i -> G.add_edge p.graph (End id) (Begin i)) successors

  let decl_block_exn p name ?(phis = [])
      ~(stmts : ('var, 'var, 'expr) Stmt.t list) ?(successors = []) () =
    let open Block in
    let id = p.block_ids.decl_exn name in
    add_block p id ~phis ~stmts ~successors ();
    id

  let fresh_block p ?name ?(phis = [])
      ~(stmts : ('var, 'var, 'expr) Stmt.t list) ?(successors = []) () =
    let open Block in
    let name = Option.get_or ~default:"block" name in
    let id = p.block_ids.fresh ~name () in
    add_block p id ~phis ~stmts ~successors ();
    id

  let add_return p ~(from : ID.t) ~(args : BasilExpr.t Params.M.t) =
    let open Vert in
    let fr = End from in
    let id = p.block_ids.fresh ~name:"retbl" () in
    let b =
      Edge.(
        Block
          {
            id;
            phis = [];
            stmts = Vector.of_list [ Stmt.(Instr_Return { args }) ];
          })
    in
    G.add_edge_e p.graph (fr, b, Return)

  let get_entry_block p id =
    let open Edge in
    let open G in
    try
      let id = G.find_edge p.graph Entry (Begin id) in
      Some id
    with Not_found -> None

  let get_block p id =
    let open Edge in
    let open G in
    try
      let _, e, _ = G.find_edge p.graph (Begin id) (End id) in
      match e with Block b -> Some b | Jump -> None
    with Not_found -> None

  let update_block p (block : (Var.t, BasilExpr.t) Block.t) =
    let open Edge in
    let open G in
    let id = block.id in
    G.remove_edge p.graph (Begin id) (End id);
    G.add_edge_e p.graph (Begin id, Block block, End id)

  let fresh_var p ?(pure = true) typ =
    let n, _ = p.local_ids.fresh ~name:"v" () in
    let v = Var.create n typ ~pure in
    Var.Decls.add p.locals v;
    v

  let copy e = { e with graph = G.copy e.graph }
end

module Program = struct
  type e = BasilExpr.t
  type proc = (Var.t, BasilExpr.t) Procedure.t
  type bloc = (Var.t, BasilExpr.t) Block.t
  type stmt = (Var.t, Var.t, e) Stmt.t

  type t = {
    modulename : string;
    globals : Var.t Var.Decls.t;
    procs : proc ID.Map.t;
    proc_names : ID.generator;
  }

  let decl_glob p = Var.Decls.add p.globals

  let empty ?name () =
    let modulename = Option.get_or ~default:"<module>" name in
    {
      modulename;
      globals = Var.Decls.empty ();
      procs = ID.Map.empty;
      proc_names = ID.make_gen ();
    }
end
