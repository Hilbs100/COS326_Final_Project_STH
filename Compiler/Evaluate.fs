(*************************************************)
(* An environment-based evaluator for Dynamic ML *)
(*************************************************)

module Compiler.Evaluate

open Compiler.Syntax
open Compiler.Printing
open Compiler.EvalUtil

(* Defines the subset of expressions considered values
   Notice that closures are values but the rec form is not -- this is
   slightly different from the way values are defined in the 
   substitution-based interpreter.  Rhetorical question:  Why is that?
   Notice also that Cons(v1,v2) is a value (if v1 and v2 are both values).
*) 
let rec is_value (e:exp) : bool = 
  match e with
      Constant _ -> true  
    | Pair (e1, e2) -> is_value e1 && is_value e2
    | EmptyList -> true
    | EmptySet -> true
    | Cons (e1, e2) -> is_value e1 && is_value e2
    | OCons (e1, e2) -> is_value e1 && is_value e2
    | SetCons (e1, e2) -> is_value e1 && is_value e2
    | Closure _ -> true
    | _ -> false
(* ----------------------------------------- *)
(* Free variable analysis and env pruning    *)
(* ----------------------------------------- *)

(* variable set as list without duplicates *)
let rec var_mem (x:variable) (vs:variable list) : bool =
  match vs with
  | [] -> false
  | y::ys -> if var_eq x y then true else var_mem x ys

let rec var_add (x:variable) (vs:variable list) : variable list =
  if var_mem x vs then vs else x :: vs

let rec var_union (a:variable list) (b:variable list) : variable list =
  match a with
  | [] -> b
  | x::xs -> var_union xs (var_add x b)

let rec var_remove (x:variable) (vs:variable list) : variable list =
  match vs with
  | [] -> []
  | y::ys -> if var_eq x y then ys else y :: var_remove x ys

let rec var_remove_many (to_remove:variable list) (vs:variable list) : variable list =
  match to_remove with
  | [] -> vs
  | x::xs -> var_remove_many xs (var_remove x vs)

(* free variables of an expression under a set of bound variables *)
let rec free_vars_with_bound (bound:variable list) (e:exp) : variable list =
  match e with
  | Var v | TypedVar (_, v) -> if var_mem v bound then [] else [v]
  | Constant _ -> []
  | Op (e1, _, e2) -> var_union (free_vars_with_bound bound e1) (free_vars_with_bound bound e2)
  | If (e1, e2, e3) ->
      let f1 = free_vars_with_bound bound e1 in
      let f2 = free_vars_with_bound bound e2 in
      let f3 = free_vars_with_bound bound e3 in
      var_union f1 (var_union f2 f3)
  | Let (x, e1, e2) ->
      let f1 = free_vars_with_bound bound e1 in
      let f2 = free_vars_with_bound (x :: bound) e2 in
      var_union f1 f2
  | Pair (e1, e2) -> var_union (free_vars_with_bound bound e1) (free_vars_with_bound bound e2)
  | Fst e1 -> free_vars_with_bound bound e1
  | Snd e1 -> free_vars_with_bound bound e1
  | EmptyList -> []
  | EmptySet -> []
  | Cons (e1, e2) | OCons(e1, e2) | SetCons (e1, e2) -> var_union (free_vars_with_bound bound e1) (free_vars_with_bound bound e2)
  | Match (e1, e2, hd, tl, e3) ->
      let f1 = free_vars_with_bound bound e1 in
      let f2 = free_vars_with_bound bound e2 in
      let f3 = free_vars_with_bound (hd :: tl :: bound) e3 in
      var_union f1 (var_union f2 f3)
  | Rec (f, x, b) -> free_vars_with_bound (f :: x :: bound) b
  | RecTyped (f, x, _, b) -> free_vars_with_bound (f :: x :: bound) b
  (* A closure literal is already closed by its env; treat as having no free vars. *)
  | Closure _ -> []
  | App (e1, e2) -> var_union (free_vars_with_bound bound e1) (free_vars_with_bound bound e2)
  | Raise e1 -> free_vars_with_bound bound e1
  | TryWith (e1, x, e2) ->
      let f1 = free_vars_with_bound bound e1 in
      let f2 = free_vars_with_bound (x :: bound) e2 in
      var_union f1 f2

let free_vars_fun (f:variable) (x:variable) (b:exp) : variable list =
  free_vars_with_bound [f; x] b

(* prune env to only the first (most recent) bindings for the variables in fvs *)
let prune_env (env:env) (fvs:variable list) : env =
  let rec loop (acc_env:env) (seen:variable list) (rest:env) : env =
    match rest with
    | [] -> acc_env
    | (y, v) :: tl ->
        if var_mem y fvs && not (var_mem y seen)
        then loop ((y, v) :: acc_env) (y :: seen) tl
        else loop acc_env seen tl
  in
  (* We collected in reverse order; reverse to preserve original order with most-recent first *)
  let pr = loop [] [] env in
  List.rev pr

(* Simple wrapper: prune the current env for a Rec(f,x,body) closure *)
let prune (env:env) (f:variable) (x:variable) (body:exp) : env =
  prune_env env (free_vars_fun f x body)

(* Type Checking *)
let rec check (ctx:ctx) (e:exp) : typ =
  match e with
  | Constant c -> type_of_constant c
  | Op (e1, op, e2) ->
    let (t1, t2, t) = type_of_op op in 
    let t1' = check ctx e1 in
    let t2' = check ctx e2 in
    if (t1 = t1' || t1' = AlphaT) && (t2 = t2' || t2' = AlphaT) then t
    else raise (TypeError (string_of_exp e))
  | Var x | TypedVar (_, x) -> 
    match lookup_ctx ctx x with
    | Some t -> t
    | None -> raise (TypeError x)
  | Rec (f, x, body) -> 
    check (update_ctx (update_ctx ctx f AlphaT) x AlphaT) body
  | RecTyped (f, x, t_arg, body) ->
    let t_body = check (update_ctx (update_ctx ctx f (ArrT (t_arg, AlphaT))) x t_arg) body in
    ArrT (t_arg, t_body)
  | App (e1, e2) ->
    let tf = check ctx e1 in
    let ta = check ctx e2 in
    (match tf with
     | ArrT (t1, t2) -> 
      if t1 = ta || ta = AlphaT then t2
      else raise (TypeError (string_of_exp e))
     | _ -> tf)
  | If (e1, e2, e3) ->
    let t1 = check ctx e1 in
    if t1 <> BoolT then raise (TypeError (string_of_exp e1))
    else 
      let t2 = check ctx e2 in
      let t3 = check ctx e3 in
      t2 // Branches don't need to match for this, because we don't have Options to have None cases
  | Let (x, e1, e2) ->
    let t1 = check ctx e1 in
    check (update_ctx ctx x t1) e2
  | Pair (e1, e2) ->
      let t1 = check ctx e1 in
      let t2 = check ctx e2 in
      ArrT (t1, t2) // Using array type to represent pair type for Fst and Snd
  | Fst e1 -> 
      (match check ctx e1 with
      | ArrT (t1, t2) -> t1
      | AlphaT -> AlphaT
      | _ -> raise (TypeError (string_of_exp e1)))
  | Snd e1 -> 
      (match check ctx e1 with
      | ArrT (t1, t2) -> t2
      | AlphaT -> AlphaT
      | _ -> raise (TypeError (string_of_exp e1)))
  | EmptyList -> AlphaT // polymorphic list type
  | EmptySet -> AlphaT // polymorphic set type
  | Cons (e1, e2) | OCons (e1, e2) | SetCons (e1, e2) ->
      let t1 = check ctx e1 in
      let t2 = check ctx e2 in
      t2
  | Match (e1, e2, hd, tl, e3) -> 
      let t1 = check ctx e1 in
      let t2 = check ctx e2 in
      let t3 = check (update_ctx (update_ctx ctx hd AlphaT) tl t1) e3 in
      t2 // Again, don't have Options, so branches don't need to match
  | Closure (envc, f, x, body) ->
      raise (TypeError (string_of_exp e))
  | Raise e1 -> 
      let t1 = check ctx e1 in
      t1
  | TryWith (e1, x, e2) ->
      let t1 = check ctx e1 in
      let t2 = check (update_ctx ctx x AlphaT) e2 in
      t2
  

(* ----------------------------------------- *)
(* The evaluator                            *)
(* ----------------------------------------- *)


(* evaluation; use eval_loop to recursively evaluate subexpressions *)
let eval_body (env:env) (eval_loop:env -> exp -> exp) (e:exp) : exp = 
  match e with
    | Var x | TypedVar (_, x)-> 
      (match lookup_env env x with 
        | None -> raise (UnboundVariable x)
        | Some v -> v)
    | Constant _ -> e
    | Op (e1, op, e2) -> 
      let v1 = eval_loop env e1 in
      let v2 = eval_loop env e2 in
      apply_op v1 op v2
    | If (e1, e2, e3) ->
      (match eval_loop env e1 with
         | Constant (Bool true) -> eval_loop env e2
         | Constant (Bool false) -> eval_loop env e3
         | _ -> raise (BadIf e1))
    | Let (x, e1, e2) ->
      let v1 = eval_loop env e1 in
      eval_loop ((x,v1)::env) e2
    | Rec (f, x, e1) | RecTyped (f, x, _, e1) ->
      let env' = prune env f x e1 in
      Closure (env', f, x, e1)
    | Closure (envc, f, x, e1) -> Closure (envc, f, x, e1)
    | App (e1, e2) ->
      let vf = eval_loop env e1 in
      let va = eval_loop env e2 in
      (match vf with
       | Closure (cenv, f, x, body) ->
           let call_env = (x, va) :: (f, vf) :: cenv in
           eval_loop call_env body
       | _ -> raise (BadApplication vf))
    | Pair (e1, e2) ->
        let v1 = eval_loop env e1 in
        let v2 = eval_loop env e2 in
        Pair (v1, v2)
    | Fst e1 -> 
        (match eval_loop env e1 with
        | Pair (v1,v2) -> v1
        | p -> raise (BadPair p))
    | Snd e1 -> 
        (match eval_loop env e1 with
        | Pair (v1,v2) -> v2
        | p -> raise (BadPair p))
    | EmptyList -> EmptyList
    | Cons (e1, e2) ->
        let v1 = eval_loop env e1 in
        let v2 = eval_loop env e2 in
        Cons (v1, v2)
    // Ordered Cons - took a lot of code because had to handle var and constant cases and mixtures of them
    | OCons (e1, e2) ->
        match eval_loop env e1 with
        | Constant x -> 
          match eval_loop env e2 with
          | EmptyList -> OCons(Constant x, EmptyList)
          | OCons(Constant hd, tl) -> 
            if x < hd then OCons(Constant x, OCons(Constant hd, tl)) 
            else eval_loop env (OCons(Constant hd, OCons(Constant x, tl)))
          | OCons(Var hd, tl) -> 
            (match eval_loop env (Var hd) with
                | Constant hdv -> 
                  if x < hdv then OCons(Constant x, OCons(Constant hdv, tl)) 
                  else eval_loop env (OCons(Constant hdv, OCons(Constant x, tl)))
                | _ -> raise (BadInput (Var hd)))
          | _ -> raise (BadInput e2)
        | Var x -> 
          (match eval_loop env (Var x) with
            | Constant xv ->
              match eval_loop env e2 with
              | EmptyList -> OCons(Constant xv, EmptyList)
              | OCons(Constant hd, tl) -> 
                if xv < hd then OCons(Constant xv, OCons(Constant hd, tl)) 
                else eval_loop env (OCons(Constant hd, OCons(Constant xv, tl)))
              | OCons(Var hd, tl) ->
                (match eval_loop env (Var hd) with
                | Constant hdv -> 
                  if xv < hdv then OCons(Constant xv, OCons(Constant hdv, tl)) 
                  else eval_loop env (OCons(Constant hdv, OCons(Constant xv, tl)))
                | _ -> raise (BadInput (Var hd)))
              | _ -> raise (BadInput e2)
            | _ -> raise (BadInput (Var x)))
        | _ -> raise (BadInput e1)
    | EmptySet -> EmptySet
    // A set that inherently disallows duplicate keys
    | SetCons (e1, e2) ->
        match eval_loop env e1 with
        | Pair (v1, v2) -> 
          match eval_loop env e2 with
          | EmptySet -> SetCons (Pair (v1, v2), EmptySet)
          | SetCons (Pair (hd1, hd2), tl) ->
            if (v1 = hd1) then SetCons (Pair (hd1, hd2), tl) // no duplicate keys
            else SetCons (Pair (hd1, hd2), eval_loop env (SetCons (Pair (v1, v2), tl)))
          | _ -> raise (BadInput e2)
        | _ -> raise (BadInput e1)      
    | Match (e1, e2, hd, tl, e3) -> 
        (match eval_loop env e1 with
        | EmptyList -> eval_loop env e2
        | Cons(v1, v2) -> eval_loop ((hd, v1)::(tl, v2)::env) e3
        | OCons(v1, v2) -> eval_loop ((hd, v1)::(tl, v2)::env) e3
        | SetCons(v1, v2) -> eval_loop ((hd, v1)::(tl, v2)::env) e3
        | v -> raise (BadMatch v))
    | Raise e1 -> 
        let v1 = eval_loop env e1 in
        Raise v1
    | TryWith (e1, x, e2) ->
        try 
          let v = eval_loop env e1 in
          match v with
          | Raise e1 -> eval_loop ((x, e1) :: env) e2
          | _ -> v
        with
        | ex -> eval_loop ((x, Var ex.Message) :: env) e2
    
// (* evaluate closed, top-level expression e *)

let eval e =
  try
    check empty_ctx e |> ignore;  // Type check before evaluating
    let rec loop env e = eval_body env loop e in
    loop empty_env e
  with 
    | TypeError msg -> 
      Constant (String ("Type error: " + msg)); 
    | ex -> 
      Constant (String ("Runtime error: " + ex.Message)); 


// (* print out subexpression after each step of evaluation *)
let debug_eval e = 
    let rec loop env e =
        if is_value e then e  (* don't print values *)
        else begin
            printfn "Evaluating %s\n" (string_of_exp e); 
            let v = eval_body env loop e in 
            printfn "%s evaluated to %s\n" (string_of_exp e) (string_of_exp v); 
            v
        end
    in loop empty_env e
