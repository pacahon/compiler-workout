open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | insn :: prg' ->
    match insn with
    | BINOP op     -> let y::x::stack' = stack in eval env (cstack, Value.of_int (Expr.eval_binop op (Value.to_int x) (Value.to_int y)) :: stack', c) prg'
    | CONST i      -> eval env (cstack, (Value.of_int i)::stack, c) prg'
    | STRING s     -> eval env (cstack, (Value.of_string s)::stack, c) prg'
    | LD x         -> eval env (cstack, State.eval st x :: stack, c) prg'
    | ST x         -> let v::stack' = stack in eval env (cstack, stack', (State.update x v st, i, o)) prg'
    (* FIXME: List.rev indexes ? *)
    | STA (x, len) -> let v::indexes, stack' = split (len + 1) stack in eval env (cstack, stack', (Language.Stmt.update st x v indexes, i, o)) prg'
    | LABEL _      -> eval env conf prg'
    | JMP l        -> eval env conf (env#labeled l)
    | CJMP (s, l)  ->
      let x::stack' = stack in
      let prg'' =
        if (Value.to_int x = 0 && s = "z") || (Value.to_int x != 0 && s = "nz")
        then env#labeled l
        else prg'
      in
      eval env (cstack, stack', c) prg''
    | CALL (fun_name, _, _) ->
      let cstack' = ((prg', st)::cstack) in eval env (cstack', stack, c) (env#labeled fun_name)
    | BEGIN (_, args, locals) -> (
      let bind ((v :: stack), state) x = (stack, State.update x v state) in
      let (stack', st') = List.fold_left bind (stack, State.enter st (args @ locals)) args in
      eval env (cstack, stack', (st', i, o)) prg'
    )
    | END | RET _ -> (
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
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

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
    (* TODO: List.rev? *)
    | Language.Expr.Array es -> (List.concat (List.map compile_e es)) @ [CALL ("$array", List.length es, true)]
    | Language.Expr.String s -> [STRING s]
    | Language.Expr.Var x -> [LD x]
    | Language.Expr.Binop (op, e1, e2) -> compile_e e1 @ compile_e e2 @ [BINOP op]
    (* TODO: List.rev? *)
    | Language.Expr.Elem (xs_e, index_e) -> compile_e xs_e @ compile_e index_e @ [CALL ("$elem", 2, false)]
    (* TODO: List.rev? *)
    | Language.Expr.Length xs_e -> compile_e xs_e @ [CALL ("$length", 1, false)]
    | Language.Expr.Call (fun_name, args) ->
      List.concat (List.map compile_e (List.rev args)) @ [CALL (fun_name, List.length args, false)]
  in
  let rec compile' p =
    match p with
    | Language.Stmt.Assign (x, [], e) -> compile_e e @ [ST x]
    | Language.Stmt.Assign (x, indexes, e) -> List.concat (List.map compile_e (indexes @ [e])) @ [STA (x, List.length indexes)]
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
      List.concat (List.map compile_e (List.rev args)) @ [CALL (fun_name, List.length args, true)]
    | Language.Stmt.Return e -> (
      match e with
      | None -> [RET false]
      | Some expr -> compile_e expr @ [RET true]
    )
    | _ -> failwith "Undefined Behavior"
  in
  let compile_def (fun_name, (args, locals, body)) =
    [LABEL fun_name; BEGIN (fun_name, args, locals)] @ compile' body @ [END]
  in
  compile' p @ [END] @ List.concat (List.map compile_def defs)
