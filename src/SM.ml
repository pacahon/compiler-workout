open GT       
       
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
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval c p =
  let int_of_bool b = if b then 1 else 0 in
  let bool_of_int i = if i != 0 then true else false in
  let eval_op op v1 v2 =
    match op with
    | "*" -> v1 * v2
    | "/" -> v1 / v2
    | "%" -> v1 mod v2
    | "+" -> v1 + v2
    | "-" -> v1 - v2
    | "==" -> int_of_bool (v1 == v2)
    | "!=" -> int_of_bool (v1 != v2)
    | "<=" -> int_of_bool (v1 <= v2)
    | "<"  -> int_of_bool (v1 < v2)
    | ">=" -> int_of_bool (v1 >= v2)
    | ">"  -> int_of_bool (v1 > v2)
    | "!!" -> int_of_bool (bool_of_int v1 || bool_of_int v2)
    | "&&" -> int_of_bool (bool_of_int v1 && bool_of_int v2)
    | _ -> failwith ("Unknown operator " ^ op)
  in
  match (c, p) with
  | (c, []) -> c
  | ((y::x::st, c), BINOP op::p') -> eval (eval_op op x y::st, c) p'
  | ((st, c), CONST x::p') -> eval (x::st, c) p'
  | ((st, (s, z::i, o)), READ::p') -> eval (z::st, (s, i ,o)) p'
  | ((x::st, (s, i, o)), WRITE::p') -> eval (st, (s, i, o @ [x])) p'
  | ((st, (s, i, o)), LD x::p') -> eval (s x::st, (s, i, o)) p'
  | ((v::st, (s, i, o)), ST x::p') -> eval (st, (Syntax.Expr.update x v s, i, o)) p'
  | _ -> failwith "Undefined Behavior"

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile stmt =
  let rec compile_e e =
    match e with
    | Syntax.Expr.Const n -> [CONST n]
    | Syntax.Expr.Var x -> [LD x]
    | Syntax.Expr.Binop (op, e1, e2) -> compile_e e1 @ compile_e e2 @ [BINOP op]
  in
  match stmt with
  | Syntax.Stmt.Read x -> [READ; ST x]
  | Syntax.Stmt.Write e -> compile_e e @ [WRITE]
  | Syntax.Stmt.Assign (x, e) -> compile_e e @ [ST x]
  | Syntax.Stmt.Seq (st1, st2) -> compile st1 @ compile st2
  | _ -> failwith "Undefined Behavior"
