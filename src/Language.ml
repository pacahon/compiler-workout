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
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

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


    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let rec eval env ((st, i, o, r) as conf) expr =
      match expr with
      | Const x -> (st, i, o, Some x)
      | Var x -> let v = State.eval st x in (st, i, o, Some v)
      | Binop (op, e1, e2) ->
        let (_, _, _, Some v1) as conf' = eval env conf e1 in
        let (st', i', o', Some v2) = eval env conf' e2 in
        let v = eval_binop op v1 v2 in
        (st', i', o', Some v)
      | Call (fun_name, args_e) ->
        let eval_arg (conf, acc) arg_expr =
          let (_,  _,  _, Some v) as conf' = eval env conf arg_expr in
          (conf', (v :: acc))
        in
        let (conf', args_v) = List.fold_left eval_arg (conf, []) args_e in
        env#definition env fun_name (List.rev args_v) conf'
         
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
      | fun_name:IDENT -"(" args:!(Util.list0)[parse] -")" {Call (fun_name, args)}
      | x:IDENT {Var x}
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration, a continuation and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt =
      let diamond st k =
        match k with
        | Skip -> st
        | _ -> Seq (st, k)
      in
      match stmt with
      | Read x -> (
        match i with
        | z::i' -> eval env (State.update x z st, i', o, r) Skip k
        | _ -> failwith "Unexpected end of input"
      )
      | Write e -> (
        let (st', i', o', Some r') = Expr.eval env conf e in
        eval env (st', i', o' @ [r'], r) Skip k
      )
      | Assign (x, e) -> (
        let (st', i', o', Some r') = Expr.eval env conf e in
        eval env (State.update x r' st', i', o', r) Skip k
      )
      | Seq (s1, s2) -> eval env conf (diamond s2 k) s1
      | Skip -> (
        match k with
        | Skip -> conf
        | _ -> eval env conf Skip k
      )
      | If (e, t, f) -> (
        let (st', i', o', Some r') = Expr.eval env conf e in
        eval env (st', i', o', r) k (match r' with 0 -> f | _ -> t)
      )
      | While (e, s) -> (
        let (st', i', o', Some r') = Expr.eval env conf e in
        match r' with
        | 0 -> eval env (st', i', o', r) Skip k
        | _ -> eval env (st', i', o', r) (diamond stmt k) s
      )
      | Repeat (s, e) -> (
        let cycle = While (Expr.Binop ("==", e, Expr.Const 0), s) in
        eval env conf (diamond cycle k) s
      )
      | Return e -> (
        match e with
        | None -> (st, i, o, None)
        | Some expr -> Expr.eval env conf expr
      )
      | Call (fun_name, args) -> (
        let conf' = Expr.eval env conf (Expr.Call (fun_name, args)) in
        eval env conf' Skip k
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
      | %"return" e:!(Expr.parse)?          {Return e}
      | fun_name:IDENT
        -"(" args:!(Expr.parse)* -")"       {Call(fun_name, args)}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
