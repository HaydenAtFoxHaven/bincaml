(** Loads a initial IR from the semi-concrete AST *)

open Lang.Types
open Lang.Value
open Lang.Prog
open Lang.Ast
open Containers

type load_st = { prog : Program.t; blockmap : (string, int) Hashtbl.t }

let map_prog f l = { l with prog = f l.prog }

type textRange = (int * int) option [@@deriving show { with_path = false }, eq]

module BasilASTLoader = struct
  open BasilIR.AbsBasilIR

  let failure x = failwith "Undefined case." (* x discarded *)
  let stripquote s = String.sub s 1 (String.length s - 2)

  let rec transBVTYPE (x : bVTYPE) : BType.t =
    match x with
    | BVTYPE (_, string) ->
        let sz =
          String.split_on_char 'v' string |> function
          | h :: l :: _ -> int_of_string l
          | _ -> failwith "bad bv format"
        in
        Bitvector sz

  and transBIdent (x : bIdent) : string =
    match x with BIdent (_, id) -> stripquote id

  and transStr (x : str) : string =
    match x with Str string -> stripquote string

  and transProgram ?(name = "<module>") (x : moduleT) : load_st =
    let prog =
      { prog = Program.empty ~name (); blockmap = Hashtbl.create 30 }
    in
    match x with
    | Module1 declarations -> List.fold_left transDeclaration prog declarations

  and transDeclaration prog (x : decl) : load_st =
    match x with
    | Decl_SharedMem (bident, type') ->
        map_prog
          (fun p ->
            Program.decl_glob p
              (Var.create
                 (unsafe_unsigil (`Global bident))
                 ~pure:false (transType type'));
            p)
          prog
    | Decl_UnsharedMem (bident, type') ->
        map_prog
          (fun p ->
            Program.decl_glob p
              (Var.create
                 (unsafe_unsigil (`Global bident))
                 ~pure:true (transType type'));
            p)
          prog
    | Decl_Var (bident, type') ->
        map_prog
          (fun p ->
            Program.decl_glob p
              (Var.create
                 (unsafe_unsigil (`Global bident))
                 ~pure:true (transType type'));
            p)
          prog
    | Decl_UninterpFun (attrDefList, glident, argtypes, rettype) -> prog
    | Decl_Fun (attrList, glident, params, rt, body) -> prog
    | Decl_Axiom _ -> prog
    | Decl_ProgEmpty _ -> prog
    | Decl_ProgWithSpec _ -> prog
    | Decl_Proc (id, inparam, ourparam, attrib, spec, ProcDef_Empty) -> prog
    | Decl_Proc
        ( ProcIdent (id_pos, id),
          in_params,
          out_params,
          attrs,
          spec_list,
          ProcDef_Some (bl, blocks, el) ) ->
        let formal_in_params = List.map param_to_lvar in_params in
        let formal_out_params = List.map param_to_lvar out_params in
        let p = Procedure.create 0 0 id () in
        let blocks = List.map transBlock blocks in
        let blocks = List.map(function `Block (name, stmts, goto) ->
            (name, Procedure.fresh_block)
        let name = id in
        prog

  and transMapType (x : mapType) : BType.t =
    match x with MapType1 (t0, t1) -> Map (transType t0, transType t1)

  and transType (x : typeT) : BType.t =
    match x with
    | TypeIntType inttype -> Integer
    | TypeBoolType booltype -> Boolean
    | TypeMapType maptype -> transMapType maptype
    | TypeBVType (BVType1 bvtype) -> transBVTYPE bvtype

  and transIntVal (x : intVal) : PrimInt.t =
    match x with
    | IntVal_Hex (IntegerHex (_, ihex)) -> Z.of_string ihex
    | IntVal_Dec (IntegerDec (_, i)) -> Z.of_string i

  and transEndian (x : BasilIR.AbsBasilIR.endian) =
    match x with Endian_Little -> `Big | Endian_Big -> `Little

  and transStatement (x : BasilIR.AbsBasilIR.stmtWithAttrib) : Program.stmt list
      =
    let stmt = match x with StmtWithAttrib1 (stmt, _) -> stmt in
    match stmt with
    | Stmt_SingleAssign (Assignment1 (lvar, expr)) ->
        [ Instr_Assign [ (transLVar lvar, transExpr expr) ] ]
    | Stmt_MultiAssign assigns ->
        [
          Instr_Assign
            (assigns
            |> List.map (function Assignment1 (l, r) ->
                   (transLVar l, transExpr r)));
        ]
    | Stmt_Load (lvar, endian, bident, expr, intval) -> []
    | Stmt_Store (endian, bident, expr0, expr, intval) -> []
    | Stmt_DirectCall (calllvars, bident, exprs) -> []
    | Stmt_IndirectCall expr -> []
    | Stmt_Assume expr -> []
    | Stmt_Guard expr -> []
    | Stmt_Assert expr -> []

  and transCallLVars (x : lVars) : lVar list =
    match x with
    | LVars_Empty -> []
    | LVars_LocalList lvars -> []
    | LVars_List lvars -> []

  and unpackLVars lvs =
    List.map
      (function
        | LocalVar1 (i, t) ->
            Var.create (unsafe_unsigil (`Local i)) (transType t))
      lvs

  and transJump (x : BasilIR.AbsBasilIR.jumpWithAttrib) =
    let jump = match x with JumpWithAttrib1 (jump, _) -> jump in
    match jump with
    | Jump_GoTo bidents -> `GoTo bidents
    | Jump_Unreachable -> `None
    | Jump_Return exprs -> `Return (List.map transExpr exprs)

  and transLVar (x : BasilIR.AbsBasilIR.lVar) : Var.t =
    match x with
    | LVar_Local (LocalVar1 (bident, type')) ->
        Var.create (unsafe_unsigil (`Local bident)) (transType type')
    | LVar_Global (GlobalVar1 (bident, type')) ->
        Var.create (unsafe_unsigil (`Global bident)) (transType type')

  and list_begin_end_to_textrange beginlist endlist : textRange =
    let beg = match beginlist with BeginList ((i, j), l) -> i in
    let ed = match endlist with EndList ((i, j), l) -> j in
    Some (beg, ed)

  and rec_begin_end_to_textrange beginlist endlist : textRange =
    let beg = match beginlist with BeginRec ((i, j), l) -> i in
    let ed = match endlist with EndRec ((i, j), l) -> j in
    Some (beg, ed)

  and transBlock (x : BasilIR.AbsBasilIR.block) =
    match x with
    | Block1
        ( BlockIdent (text_range, name),
          addrattr,
          beginlist,
          statements,
          jump,
          endlist ) ->
        let stmts = List.map transStatement statements in
        let succ = transJump jump in
        `Block (name, stmts, succ)

  and param_to_lvar (pp : params) : Var.t =
    match pp with
    | Params1 (LocalIdent (pos, id), t) -> Var.create id (transType t)

  and transParams (x : params) : Var.t = param_to_lvar x

  and unsafe_unsigil g : string =
    match g with
    | `Global (GlobalIdent (pos, g)) -> g
    | `Local (LocalIdent (pos, g)) -> g
    | `Proc (ProcIdent (pos, g)) -> g
    | `Block (BlockIdent (pos, g)) -> g

  and transExpr (x : BasilIR.AbsBasilIR.expr) : BasilExpr.t =
    match x with
    | Expr_Global (GlobalVar1 (g, type')) ->
        BasilExpr.rvar
        @@ Var.create (unsafe_unsigil (`Global g)) (transType type')
    | Expr_Local (LocalVar1 (g, type')) ->
        BasilExpr.rvar
        @@ Var.create (unsafe_unsigil (`Local g)) (transType type')
    | Expr_Assoc (binop, rs) -> (
        match transBoolBinOp binop with
        | #AllOps.intrin as op ->
            BasilExpr.applyintrin ~op (List.map transExpr rs)
        | _ -> failwith "non-associative operator")
    | Expr_Binary (binop, expr0, expr) -> (
        let op = transBinOp binop in
        match op with
        | #AllOps.binary as op ->
            BasilExpr.binexp ~op (transExpr expr0) (transExpr expr)
        | #AllOps.intrin as op ->
            BasilExpr.applyintrin ~op [ transExpr expr0; transExpr expr ]
        | `BVUGT ->
            BasilExpr.unexp ~op:`LNOT
              (BasilExpr.binexp ~op:`BVULE (transExpr expr0) (transExpr expr))
        | `BVUGE ->
            BasilExpr.unexp ~op:`LNOT
              (BasilExpr.binexp ~op:`BVULT (transExpr expr0) (transExpr expr))
        | `BVSGT ->
            BasilExpr.unexp ~op:`LNOT
              (BasilExpr.binexp ~op:`BVSLE (transExpr expr0) (transExpr expr))
        | `BVSGE ->
            BasilExpr.unexp ~op:`LNOT
              (BasilExpr.binexp ~op:`BVSLT (transExpr expr0) (transExpr expr))
        | `INTGT -> failwith "usupported up : intgt"
        | `INTGE -> failwith "unsupported op: intge")
    | Expr_Unary (unop, expr) ->
        BasilExpr.unexp ~op:(transUnOp unop) (transExpr expr)
    | Expr_ZeroExtend (intval, expr) ->
        BasilExpr.zero_extend
          ~n_prefix_bits:(Z.to_int @@ transIntVal intval)
          (transExpr expr)
    | Expr_SignExtend (intval, expr) ->
        BasilExpr.sign_extend
          ~n_prefix_bits:(Z.to_int @@ transIntVal intval)
          (transExpr expr)
    | Expr_Extract (ival0, intval, expr) ->
        BasilExpr.extract
          ~hi_incl:(transIntVal ival0 |> Z.to_int)
          ~lo_excl:(transIntVal intval |> Z.to_int)
          (transExpr expr)
    | Expr_Concat (expr0, expr) ->
        BasilExpr.concat (transExpr expr0) (transExpr expr)
    | Expr_Literal (Value_BV (BVVal1 (intval, BVType1 bvtype))) ->
        BasilExpr.bvconst
          (match transBVTYPE bvtype with
          | Bitvector width -> PrimQFBV.create ~width (transIntVal intval)
          | _ -> failwith "unreachable")
    | Expr_Literal (Value_Int intval) -> BasilExpr.intconst (transIntVal intval)
    | Expr_Literal Value_True -> BasilExpr.boolconst true
    | Expr_Literal Value_False -> BasilExpr.boolconst false
    | Expr_Old e -> BasilExpr.unexp ~op:`Old (transExpr e)
    | Expr_Forall (LambdaDef1 (lv, _, e)) ->
        BasilExpr.forall ~bound:(unpackLVars lv) (transExpr e)
    | Expr_Exists (LambdaDef1 (lv, _, e)) ->
        BasilExpr.exists ~bound:(unpackLVars lv) (transExpr e)
    | Expr_FunctionOp (gi, args) ->
        BasilExpr.apply_fun
          ~name:(unsafe_unsigil (`Global gi))
          (List.map transExpr args)

  and transBinOp (x : BasilIR.AbsBasilIR.binOp) =
    match x with
    | BinOpBVBinOp bvbinop -> transBVBinOp bvbinop
    | BinOpBVLogicalBinOp bvlogicalbinop -> transBVLogicalBinOp bvlogicalbinop
    | BinOpBoolBinOp boolbinop -> transBoolBinOp boolbinop
    | BinOpIntLogicalBinOp intlogicalbinop ->
        transIntLogicalBinOp intlogicalbinop
    | BinOpIntBinOp intbinop -> transIntBinOp intbinop
    | BinOpEqOp equop -> transEqOp equop

  and transUnOp (x : BasilIR.AbsBasilIR.unOp) =
    match x with
    | UnOpBVUnOp bvunop -> transBVUnOp bvunop
    | UnOp_boolnot -> `LNOT
    | UnOp_intneg -> `INTNEG
    | UnOp_booltobv1 -> `BOOL2BV1

  and transBVUnOp (x : bVUnOp) =
    match x with BVUnOp_bvnot -> `BVNOT | BVUnOp_bvneg -> `BVNEG

  and transBVBinOp (x : BasilIR.AbsBasilIR.bVBinOp) =
    match x with
    | BVBinOp_bvand -> `BVAND
    | BVBinOp_bvor -> `BVOR
    | BVBinOp_bvadd -> `BVADD
    | BVBinOp_bvmul -> `BVMUL
    | BVBinOp_bvudiv -> `BVUDIV
    | BVBinOp_bvurem -> `BVUREM
    | BVBinOp_bvshl -> `BVSHL
    | BVBinOp_bvlshr -> `BVLSHR
    | BVBinOp_bvnand -> `BVNAND
    | BVBinOp_bvnor -> `BVNOR
    | BVBinOp_bvxor -> `BVXOR
    | BVBinOp_bvxnor -> `BVXNOR
    | BVBinOp_bvcomp -> `BVCOMP
    | BVBinOp_bvsub -> `BVSUB
    | BVBinOp_bvsdiv -> `BVSDIV
    | BVBinOp_bvsrem -> `BVSREM
    | BVBinOp_bvsmod -> `BVSMOD
    | BVBinOp_bvashr -> `BVASHR

  and transBVLogicalBinOp (x : bVLogicalBinOp) =
    match x with
    | BVLogicalBinOp_bvule -> `BVULE
    | BVLogicalBinOp_bvult -> `BVULT
    | BVLogicalBinOp_bvslt -> `BVSLT
    | BVLogicalBinOp_bvsle -> `BVSLE
    | BVLogicalBinOp_bvugt -> `BVUGT
    | BVLogicalBinOp_bvuge -> `BVUGE
    | BVLogicalBinOp_bvsgt -> `BVSGT
    | BVLogicalBinOp_bvsge -> `BVSGE

  and transEqOp (x : eqOp) = match x with EqOp_eq -> `EQ | EqOp_neq -> `NEQ

  and transIntBinOp (x : intBinOp) =
    match x with
    | IntBinOp_intadd -> `INTADD
    | IntBinOp_intmul -> `INTMUL
    | IntBinOp_intsub -> `INTSUB
    | IntBinOp_intdiv -> `INTDIV
    | IntBinOp_intmod -> `INTMOD

  and transIntLogicalBinOp (x : intLogicalBinOp) =
    match x with
    | IntLogicalBinOp_intlt -> `INTLT
    | IntLogicalBinOp_intle -> `INTLE
    | IntLogicalBinOp_intgt -> `INTGT
    | IntLogicalBinOp_intge -> `INTGE

  and transBoolBinOp (x : boolBinOp) =
    match x with
    | BoolBinOp_booland -> `AND
    | BoolBinOp_boolor -> `OR
    | BoolBinOp_boolimplies -> `IMPLIES
end

let ast_of_concrete_ast m = BasilASTLoader.transProgram m

let ast_of_channel fname c =
  let m = Basilloader.Cast_loader.concrete_ast_of_channel c in
  BasilASTLoader.transProgram ~name:fname m

let ast_of_fname fname = IO.with_in fname (fun c -> ast_of_channel fname c)
