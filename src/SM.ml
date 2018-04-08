open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | insn :: prg' ->
    match insn with
    | BINOP op    -> let y::x::stack' = stack in eval env (cstack, Expr.eval_binop op x y :: stack', c) prg'
    | READ        -> let z::i' = i in eval env (cstack, z::stack, (st, i', o)) prg'
    | WRITE       -> let z::stack' = stack in eval env (cstack, stack', (st, i, o @ [z])) prg'
    | CONST i     -> eval env (cstack, i::stack, c) prg'
    | LD x        -> eval env (cstack, State.eval st x :: stack, c) prg'
    | ST x        -> let z::stack' = stack in eval env (cstack, stack', (State.update x z st, i, o)) prg'
    | LABEL _     -> eval env conf prg'
    | JMP l       -> eval env conf (env#labeled l)
    | CJMP (s, l) ->
      let x::stack' = stack in
      let prg'' =
        if (x = 0 && s = "z") || (x != 0 && s = "nz")
        then env#labeled l
        else prg'
      in
      eval env (cstack, stack', c) prg''
    | CALL fun_name ->
      let cstack' = ((prg', st)::cstack) in eval env (cstack', stack, c) (env#labeled fun_name)
    | BEGIN (args, locals) -> (
      let bind x ((v :: stack), state) = (stack, State.update x v state) in
      let (stack', st') = List.fold_right bind args (stack, State.enter st (args @ locals)) in
      eval env (cstack, stack', (st', i, o)) prg'
    )
    | END -> (
      match cstack with
      | [] -> conf
      | (p, s)::cstack' -> eval env (cstack', stack, (Language.State.leave st s, i, o)) p
    )
    | _ -> failwith "Undefined behavior"

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) =
  let labelGenerator = object
    val mutable counter = 0

    method next =
      counter <- counter + 1;
      "label_" ^ string_of_int counter
    end
  in
  let rec compile_e e =
    match e with
    | Language.Expr.Const n -> [CONST n]
    | Language.Expr.Var x -> [LD x]
    | Language.Expr.Binop (op, e1, e2) -> compile_e e1 @ compile_e e2 @ [BINOP op]
    | Language.Expr.Call (fun_name, args) ->
      List.concat (List.map compile_e (List.rev args)) @ [CALL fun_name]
  in
  let rec compile' p =
    match p with
    | Language.Stmt.Read x -> [READ; ST x]
    | Language.Stmt.Write e -> compile_e e @ [WRITE]
    | Language.Stmt.Assign (x, e) -> compile_e e @ [ST x]
    | Language.Stmt.Seq (st1, st2) -> compile' st1 @ compile' st2
    | Language.Stmt.Skip -> []
    | Language.Stmt.If (e, t, f) ->
      let else_label = labelGenerator#next in
      let fi_label = labelGenerator#next in
      compile_e e @ [CJMP ("z", else_label)] @ compile' t @ [JMP fi_label] @ [LABEL else_label] @ compile' f @ [LABEL fi_label]
    | Language.Stmt.While (e, s) ->
      let cond_label = labelGenerator#next in
      let loop_label = labelGenerator#next in
      [JMP cond_label] @ [LABEL loop_label] @ compile' s @ [LABEL cond_label] @ compile_e e @ [CJMP ("nz", loop_label)]
    | Language.Stmt.Repeat (s, e) ->
      let loop_label = labelGenerator#next in
      [LABEL loop_label] @ compile' s @ compile_e e @ [CJMP ("z", loop_label)]
    | Language.Stmt.Call (fun_name, args) ->
      List.concat (List.map compile_e (List.rev args)) @ [CALL fun_name]
    | Stmt.Return e -> (
      match e with
      | None -> [END]
      | Some expr -> compile_e expr @ [END]
    )
    | _ -> failwith "Undefined Behavior"
  in
  let compile_def (fun_name, (args, locals, body)) =
    [LABEL fun_name; BEGIN (args, locals)] @ compile' body @ [END]
  in
  [LABEL "main"] @ compile' p @ [END] @ List.concat (List.map compile_def defs)
