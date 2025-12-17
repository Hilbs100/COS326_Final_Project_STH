(* Testing *)

(* In this file, we build abstract syntax trees representing various
   functions for the purpose of testing our evaluators.

   You will have to construct some additional functions yourself.
 *)

module Compiler.Testing

open Compiler.Syntax
open Compiler.Printing

(************)
(* INTEGERS *)
(************)

(* Useful Constants *)
let zero = Constant (Int 0) 
let one = Constant (Int 1) 
let two = Constant (Int 2) 
let three = Constant (Int 3) 
let four = Constant (Int 4)

(***********************)
(* RECURSIVE FUNCTIONS *)
(***********************)

(* let z = 2 in (let x = 3 in fun y -> x + y + z) (let x = 4 in x + z) *)
let clo =  
  Let ("z", two,
       App (Let ("x", three, 
         Rec ("f", "y", 
              Op (Var "x", Plus, Op (Var "y", Plus, Var "z")))
                ),
        Let ("x", four, Op (Var "x", Plus, Var "z"))
           )
      )

(* rec fact n = if n < 1 then 1 else n * fact (n - 1) *)
let fact = 
  Rec ("fact", "n", 
       If (Op (Var "n", Less, one),
           one,
           Op (Var "n", Times, 
               App (Var "fact", 
                        Op (Var "n", Minus, one)))))

(* fact 4 *)
let fact4 = App (fact, four)

(*********)
(* PAIRS *)
(*********)

(* the pair (1,2) *)
let p1 = Pair (one, two)

(* the function swap below is equivalent to:
       let swap p = let (x,y) = p in (y,x)
*)
let swap = 
  Rec ("swap", "p",
       Let ("x", Fst (Var "p"),
       Let ("y", Snd (Var "p"),
       Pair(Var "y", Var "x"))))

(* use swap to swap the elements of p1 *)
let swap_p1 = App (swap, p1)

(*********)
(* LISTS *)
(*********)

(* takes an OCaml list of expressions and generates a single expression
   representing the list
*)
let rec listify (l:exp list) : exp =
  match l with
      [] -> EmptyList
    | hd::tl -> Cons(hd,listify tl)

(* a list of 4 numbers *)
let list4 = listify [one;two;three;four] 

let rec ordered_listify (l:exp list) : exp =
  match l with
      [] -> EmptyList
    | hd::tl -> OCons(hd,ordered_listify tl)

(* a ordered list of 4 numbers *)
let ol4 = ordered_listify [one;two;three;four]

let ol3 = ordered_listify [four; three; two]

(* rec sublist l = 
 *   match l with
 *     [] -> 0
 *   | hd::tl -> hd - sublist tl *)
 (* Did sublist because order matters for testing ordered lists *)
let sublist = 
  Rec ("sublist", "l", 
       Match (Var "l",
           zero,
           "hd", "tl", Op (Var "hd", Minus, 
               App (Var "sublist", Var "tl"))))

let sl4 = App (sublist, list4)
let sol3 = App (sublist, ol3)

(******************************)
(* SETS    *)
(******************************)

let rec setify (l:exp list) : exp =
  match l with
    | [] -> EmptySet
    | hd::tl -> SetCons(hd,setify tl)

(* a set of 4 pairs *)
let test_set4 = setify [Pair(one,two); Pair(three,four); Pair(two,three); Pair(one,four)] 
// Should only get 3 elements when evaluated

let rec get_from_dict = 
  Rec("get_from_dict", "l" , Rec("dict_loop", "key",
    Match (Var "l", 
      Constant (String "None"), "hd", "tl", 
      If(Op (Var "key", Eq, Fst (Var "hd")), 
        Snd (Var "hd"), App (App (Var "get_from_dict", Var "tl"), Var "key")))))

let get_set4 = App (App(get_from_dict, test_set4), two)

let test_set = setify [one; two; three] // Throws BadInput as it's supposed to

(*******************************)
(* QUESTIONS FOR YOU TO ANSWER *)
(*******************************)

(* Define a function fact_tail that computes the factorial of a number
   using tail recursion. You may define helper functions as needed.
   Example: fact_tail 4 == 24*)

(*******************************)
(* QUESTIONS FOR YOU TO ANSWER *)
(*******************************)

(* NOTE: NONE OF THE FUNCTIONS YOU WRITE BELOW SHOULD INCLUDE
 * Closure (env,f,x,e)
 *
 * Define recursive functions using the Rec(f,x,body) form
 *)

(* Replace the constant "one" below with your implementation of 
   the function map : ('a -> 'b) -> 'a list -> 'b list 
   Note: do not implement this as map: (('a -> 'b)*'a list) -> 'b list
 *)
let map = Rec ("map", "f",
            Rec ("map_loop", "ls",
              Match (Var "ls",
                EmptyList,
                "hd", "tl",
                Cons (App (Var "f", Var "hd"),
                      App (App (Var "map", Var "f"), Var "tl"))
              )
            )
          )
    
(* Replace the constant "one" below with your implementation of 
   the function plus1 that adds one to an integer *)
let plus1 = Rec ("plus1", "x",
            Op (Var "x", Plus, one))

(* Use plus1 and map, defined above, to implement the function 
   incr_all, which adds 1 to every element of a list. Examples:

   incr_all [] == []
   incr_all [1;2;3] == [2;3;4]
*)
let incr_all = Rec("incr_all", "l", App(App (map, plus1), Var "l"))
let incr_all4 = App (incr_all, list4)

(* Replace the constant one below by implementing a function that 
 * takes a list of pairs of integers and returns a list of integers 
 * where each element of the list is the sum of the elements of the 
 * pairs.  Examples:

  sum_pairs [] == []
  sum_pairs [(1,2); (3,4)] == [3; 7]
 *)

let sum_pairs = Rec("sum_pairs", "l", App(
  App(map, Rec("sum_pair", "p", Op(Fst(Var "p"), Plus, Snd(Var "p")))), Var "l"
))


(**********************)
(* EXCEPTION HANDLING *)
(**********************)

// Test bad operation
let bad_op = TryWith(Op (Constant (Bool true), Plus, Constant (Int 1)), "e", Raise (Var "e"))
// Now throws type error before evaluation, removing from tests to see other tests

let fact_safe =
  Rec("fact_safe", "n",
    If(Op(Var "n", Less, one),
       Raise (Constant (String "Negative argument to factorial")),
       If(Op(Var "n", LessEq, one), one, Op(Var "n", Times, App(Var "fact_safe", Op(Var "n", Minus, one))))
    )
  )

let arg_err_safe =
  TryWith(App(fact_safe, Constant (Int (-1))), "e", Constant (Int 1))


let no_arg_err =
  TryWith(App(fact_safe, Constant (Int (3))), "e", Constant (Int 1))

let arg_err = App(fact_safe, Constant (Int (-5)))

(***********************)
(* Type Checking *)
(***********************)

let add = RecTyped("add", "x", IntT,
              RecTyped("add_loop", "y", IntT,
                Op(Var "x", Plus, Var "y")
              )
            )

let add_error = App (App(add, two), (Constant (Bool true)))

(*********)
(* TESTS *)
(*********)

(* Feel free to add many more tests of your own to the list *)

// Labels
let lists = ("Lists", [list4; ol4; ol3; sl4; sol3])
let sets = ("Sets", [test_set4; get_set4; test_set])
let functions = ("Functions", [clo; incr_all; incr_all4; sum_pairs])
let exceptions = ("Exceptions", [arg_err_safe; no_arg_err; arg_err])
let type_checks = ("Type Checking", [bad_op; add_error])

let tests = [zero; fact4; list4; ol4; ol3; sl4; sol3; test_set4; get_set4; test_set;
  clo; incr_all; incr_all4; sum_pairs; bad_op; arg_err_safe; no_arg_err; arg_err; add_error]

let labeled_tests = [lists; sets; functions; exceptions; type_checks]

(***********************)
(* TEST RUNNERS        *)
(***********************)

let run_test eval exp =
  Printf.printf "========\n";
  Printf.printf "%s\n" (string_of_exp exp);
  Printf.printf "Evaluates to:\n";
  Printf.printf "%s\n" (string_of_exp (eval exp));
  Printf.printf "========\n"


let run_tests eval tests =
  List.iter (run_test eval) tests

let run_labeled_test eval ls =
  match ls with 
    (label, tests) ->
      Printf.printf "===== %s =====\n" label;
      run_tests eval tests

let run_labeled_tests eval lss = 
  List.iter (run_labeled_test eval) lss