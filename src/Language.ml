(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let fail = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)
      in
      { g = fail; l = fail; scope = [] }

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      if List.mem x s.scope
      then { s with l = (fun y -> if x = y then v else s.l y) }
      else { s with g = (fun y -> if x = y then v else s.g y) }
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if List.mem x s.scope then s.l x else s.g x

    (* Creates a new scope, based on a given state *)
    let enter st xs = { g = st.g; l = empty.l; scope = xs }

    (* Drops a scope *)
    let leave st st' = { st' with g = st.g }

  end
    
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
      | Var x -> State.eval st x
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((st, i, o) as conf) stmt =
      match stmt with
      | Read    x       -> (match i with z::i' -> (State.update x z st, i', o) | _ -> failwith "Unexpected end of input")
      | Write   e       -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e)   -> (State.update x (Expr.eval st e) st, i, o)
      | Seq    (s1, s2) -> eval env (eval env conf s1) s2
      | Skip -> conf
      | If (e, t, f) -> (match Expr.eval st e with 0 -> eval env conf f | _ -> eval env conf t)
      | While (e, s) -> (match Expr.eval st e with 0 -> conf | _ -> eval env (eval env conf s) stmt)
      | Repeat (s, e) -> (
        let conf' = eval env conf s in
        let (st', _, _) = conf' in
        match Expr.eval st' e with
        0 -> eval env conf' stmt
        | _ -> conf'
      )
      | Call (fun_name, params) -> (
        let (arg_names, locals, body) = env#definition fun_name in
        let arg_values = List.map (Expr.eval st) params in
        let unbound_state = State.enter st (arg_names @ locals) in
        let bindings = List.combine arg_names arg_values in
        let fun_state = List.fold_right (fun (x, v) st -> State.update x v st) bindings unbound_state in
        let (st', i', o') = eval env (fun_state, i, o) body in
        (State.leave st' st, i', o')
      )
                                
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
        %"od"                               {Seq (s1, While (e, Seq(s3, s2)))}
      | "read" -"(" x:IDENT -")"            {Read x}
      | "write" -"(" e:!(Expr.parse) -")"   {Write e}
      | x:IDENT -":=" e:!(Expr.parse)       {Assign (x, e)}
      | fun_name:IDENT -"(" args:!(Util.list0)[Expr.parse] -")" {Call (fun_name, args)}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg: IDENT;
      parse:
        %"fun" fun_name:IDENT -"(" args:!(Util.list0 arg) -")" locals:(%"local" !(Util.list arg))?
        -"{" s:!(Stmt.parse) -"}" { (fun_name, (args, (match locals with None -> [] | Some xs -> xs), s)) }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (fun_name, def) :: tl -> make_map (M.add fun_name def m) tl
  in
  let m = make_map M.empty defs in
  let _, _, o = Stmt.eval (object method definition fun_name = M.find fun_name m end) (State.empty, i, []) body in o
                                   
(* Top-level parser *)
let parse = ostap (
  !(Definition.parse)* !(Stmt.parse)
)
