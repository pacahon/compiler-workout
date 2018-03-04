open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval c p =
  match (c, p) with
  | (c, []) -> c
  | ((y::x::st, c), BINOP op::p') -> eval (Language.Expr.eval_binop op x y::st, c) p'
  | ((st, c), CONST x::p') -> eval (x::st, c) p'
  | ((st, (s, z::i, o)), READ::p') -> eval (z::st, (s, i ,o)) p'
  | ((x::st, (s, i, o)), WRITE::p') -> eval (st, (s, i, o @ [x])) p'
  | ((st, (s, i, o)), LD x::p') -> eval (s x::st, (s, i, o)) p'
  | ((v::st, (s, i, o)), ST x::p') -> eval (st, (Language.Expr.update x v s, i, o)) p'
  | _ -> failwith "Undefined Behavior"

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt =
  let rec compile_e e =
    match e with
    | Language.Expr.Const n -> [CONST n]
    | Language.Expr.Var x -> [LD x]
    | Language.Expr.Binop (op, e1, e2) -> compile_e e1 @ compile_e e2 @ [BINOP op]
  in
  match stmt with
  | Language.Stmt.Read x -> [READ; ST x]
  | Language.Stmt.Write e -> compile_e e @ [WRITE]
  | Language.Stmt.Assign (x, e) -> compile_e e @ [ST x]
  | Language.Stmt.Seq (st1, st2) -> compile st1 @ compile st2
  | _ -> failwith "Undefined Behavior"

                         
