open Value
open Common
module ID = Int
open Types
open Cexpr

module Stmt = struct
  type endian = Big | Litle
  type ident = string

  module BlockID = ID
  module ProcID = ID

  type ('var, 'expr) instr =
    | Instr_Assign of ('var * 'expr) list
    | Instr_Load of { lhs : 'var; addr : 'expr; endian : endian }
    | Instr_Store of {
        lhs : 'var;
        addr : 'expr;
        value : 'expr;
        endian : endian;
      }
    | Instr_Call of { lhs : 'var list; procid : ProcID.t; args : 'expr list }
    | Instr_IntrinCall of { lhs : 'var list; name : string; args : 'expr list }
    | Instr_IndirectCall of 'expr

  type ('var, 'expr) t =
    | Stmt_Instr of ('var, 'expr) instr
    | Stmt_Assume of 'expr
    | Stmt_Assert of 'expr
    | Stmt_If of 'expr * ('var, 'expr) t
    | Stmt_While of 'expr * ('var, 'expr) t
    | Stmt_Goto of string list
    | Block of {
        label : string;
        phis_in : ('var * 'var) list;
        guard : 'expr option;
        stmts : ('var, 'expr) instr list;
        phis_out : ('var * 'var) list;
        succ : ('var, 'expr) t;
      }
end

module Block = struct
  type ident = Block of int [@@unboxed]
end

module Procedure = struct
  type ident = Proc of int [@@unboxed]

  type ('var, 'e) t = {
    name : string;
    requires : 'e list;
    ensures : 'e list;
    body : 'e list;
  }
end

module Program = struct
  module IDMap = Map.Make (ID)

  type t = { procedure_name : string IDMap.t; block_label : string IDMap.t }
end
