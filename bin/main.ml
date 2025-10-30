open Cmdliner
open Lang.Prog
open Containers
open Lang

let () = Printexc.record_backtrace true

let check fname proc =
  let p = Ocaml_of_basil.Loadir.ast_of_fname fname in
  let procs prog =
    let open Program in
    Lang.ID.Map.iter (fun i _ -> Printf.printf "%s\n" (ID.show i)) prog.procs
  in
  if not @@ String.equal proc "" then
    let id = p.prog.proc_names.get_id proc in
    let p = Lang.ID.Map.find id p.prog.procs in
    Lang.Livevars.print_live_vars_dot Format.std_formatter p
    (*let p =
      Lang.Prog.Procedure.pretty Lang.Var.to_string
        Lang.Expr.BasilExpr.to_string p
    in
    print_endline @@ Containers_pp.Pretty.to_string ~width:80 p*)
  else procs p.prog

let fname =
  let doc = "Input file name (filename.il)" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FNAME" ~doc)

let proc =
  let doc = "proc to output" and docv = "PROC" in
  Arg.(value & opt string "" & info [ "p"; "proc" ] ~doc ~docv)

let check_f = Term.(const check $ fname $ proc)

let cmd =
  let doc = "obasil" in
  let info = Cmd.info "obasil" ~version:"alpha" ~doc in
  Cmd.v info check_f

let main () = exit (Cmd.eval cmd)
let () = main ()
