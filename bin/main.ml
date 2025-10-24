open Cmdliner

let check fname = Ocaml_of_basil.Loadir.ast_of_fname fname |> ignore

let fname =
  let doc = "Input file name (filename.il)" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FNAME" ~doc)

let check_f = Term.(const check $ fname)

let cmd =
  let doc = "obasil" in
  let info = Cmd.info "obasil" ~version:"alpha" ~doc in
  Cmd.v info check_f

let main () = exit (Cmd.eval cmd)
let () = main ()
