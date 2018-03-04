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
    let rec eval env expr =
      match expr with
      | Const x -> x
      | Var x -> env x
      | Binop (op, e1, e2) ->
        let v1 = eval env e1 in
        let v2 = eval env e2 in
        eval_binop op v1 v2

    let binop_specifiers_helper operators =
      List.map (fun op -> ostap ($(op)), fun x y -> Binop (op, x, y)) operators

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      parse: expr;
      expr:
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

        primary: x:IDENT {Var x} | c:DECIMAL {Const c} | -"(" expr -")"
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval conf stmt =
      match (conf, stmt) with
      | ((s, i, o), Assign (x, e)) -> let v = Expr.eval s e in (Expr.update x v s, i, o)
      | ((s, z::i, o), Read x) -> (Expr.update x z s, i, o)
      | ((s, i, o), Write e) -> let v = Expr.eval s e in (s, i, o @ [v])
      | (c, Seq (st1, st2)) -> let c' = eval c st1 in eval c' st2
      | _ -> failwith "Undefined statement"

    (* Statement parser *)
    ostap (
      stmt:
        x:IDENT -":=" e:!(Expr.parse)        {Assign (x, e)}
        | -"read" -"(" s:IDENT -")"          {Read s}
        | -"write" -"(" v:!(Expr.parse) -")" {Write v};
      parse: <s::ss> : !(Ostap.Util.listBy)[ostap (";")][stmt] {List.fold_left (fun x y -> Seq (x, y)) s ss}
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
