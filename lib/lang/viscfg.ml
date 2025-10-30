open Prog
open Containers

module type Labelling = sig
  val labelling : Procedure.Vert.t -> string option
end

module type ProcPrinter = sig
  val fprint_graph : Format.formatter -> Procedure.G.t -> unit
  val output_graph : out_channel -> Procedure.G.t -> unit
end

module Make (L : Labelling) = Graph.Graphviz.Dot (struct
  open Procedure
  include G
  include Graph.Pack

  let addind ind = if ind <= 4 then 4 else 2

  let safe_label (s : string) =
    let wrap = 100 in
    let slack = 30 in
    let wrap_p = [ ';'; ')'; '('; ' ' ] in
    "\\l"
    ^ (String.to_list s
      |> List.fold_left_map
           (fun (l, ind) c ->
             match c with
             | '\n' -> ((0, 0), "\\l")
             | '"' -> ((l, ind), "\\\"")
             | c
               when l >= wrap - slack
                    && List.find_opt (function y -> Char.equal y c) wrap_p
                       |> Option.is_some ->
                 let ind = addind ind in
                 ((0, ind), String.of_char c ^ "\\l" ^ String.make ind ' ')
             | c when l >= wrap ->
                 let ind = addind ind in
                 ((0, ind), "\\l" ^ String.make ind ' ' ^ String.of_char c)
             | c -> ((l + 1, ind), String.make 1 c))
           (0, 0)
      |> snd |> String.concat "")
    ^ "\\l"

  let edge_attributes (e : E.t) =
    [ `Label (safe_label @@ Edge.to_string (E.label e)); `Fontname "Mono" ]

  let default_edge_attributes _ = []
  let get_subgraph _ = None

  let vertex_name (v : Vert.t) =
    let open Vert in
    let n =
      match v with
      | Begin v -> Printf.sprintf "beg%d" (ID.index v)
      | End v -> Printf.sprintf "end%d" (ID.index v)
      | Entry -> "entry"
      | Exit -> "exit"
      | Return -> "return"
    in
    n

  let vertex_attributes v =
    let n = vertex_name v in
    let l =
      match L.labelling v with
      | Some x ->
          let l = n ^ "\\l :     " ^ x ^ "\\l" in
          [ `Label l ]
      | _ -> []
    in
    [ `Shape `Box; `Fontname "Mono" ] @ l

  let default_vertex_attributes _ = []
  let graph_attributes _ = []
end)

let dot_labels label_fun =
  (module Make (struct
    let labelling = label_fun
  end) : ProcPrinter)

module Dot = Make (struct
  let labelling v = None
end)
