(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Binary operation evaluator
          val eval_binop : string -> int -> int -> int
    *)
    let eval_binop op v1 v2 =
      let int_of_bool b = if b then 1 else 0 in
      let bool_of_int i = if i != 0 then true else false in
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

    (* Expression evaluator
          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval st expr =
      match expr with
      | Const x -> x
      | Var x -> st x
      | Binop (op, e1, e2) -> eval_binop op (eval st e1) (eval st e2)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)

    let binop_specifiers_helper operators =
      List.map (fun op -> ostap (- $(op)), fun x y -> Binop (op, x, y)) operators

    ostap (
      parse:
        !(Ostap.Util.expr
             (fun x -> x)
             [|  (* --- an array of binary operator specifiers, ordered by the priority in increasing order *)
               `Lefta, binop_specifiers_helper ["!!"];
               `Lefta, binop_specifiers_helper ["&&"];
               `Nona , binop_specifiers_helper [">="; ">"; "<="; "<"; "=="; "!="];
               `Lefta, binop_specifiers_helper ["+"; "-"];
               `Lefta, binop_specifiers_helper ["*"; "/"; "%"];
             |]
             primary
           );

      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t  with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((st, i, o) as conf) stmt =
      match stmt with
      | Read    x       -> (match i with z::i' -> (Expr.update x z st, i', o) | _ -> failwith "Unexpected end of input")
      | Write   e       -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e)   -> (Expr.update x (Expr.eval st e) st, i, o)
      | Seq    (s1, s2) -> eval (eval conf s1) s2
      | Skip -> conf
      | If (e, t, f) -> (match Expr.eval st e with 0 -> eval conf f | _ -> eval conf t)
      | While (e, s) -> (match Expr.eval st e with 0 -> conf | _ -> eval conf (Seq (s, stmt)))  (* TODO: reduce Seq? *)
      | Repeat (s, e) -> (match Expr.eval st e with 0 -> eval conf s | _ -> eval conf (Seq (s, stmt)))

    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;
      stmt:
        %"skip"                             {Skip}
      | %"if" e:!(Expr.parse)
        %"then" t:parse 
        elifStmts:(%"elif" !(Expr.parse) %"then" parse)*
        elseStmt:(%"else" f:parse)?
        %"fi"                               {If (e, t, List.fold_right (fun (e, s) b -> If (e, s, b)) elifStmts (match elseStmt with Some x -> x | None -> Skip) )} 
      | %"while" e:!(Expr.parse) 
        %"do" s:parse 
        %"od"                               {While (e, s)}
      | %"repeat" s:parse 
        %"until" e:!(Expr.parse)            {Repeat (s, e)}
      | %"for" s1:parse -","
                e:!(Expr.parse) -","
                s2:parse
        %"do" s3:parse 
        %"od"                               {Seq (s1, While (e, Seq(s2, s3)))}  (* FIXME: how to undo s1 after loop? *)
      | "read" -"(" x:IDENT -")"            {Read x}
      | "write" -"(" e:!(Expr.parse) -")"   {Write e}
      | x:IDENT -":=" e:!(Expr.parse)        {Assign (x, e)}
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse
