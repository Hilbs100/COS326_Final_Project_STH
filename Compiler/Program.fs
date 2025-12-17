// For more information see https://aka.ms/fsharp-console-apps
open Compiler.Testing
open Compiler.Evaluate

printfn "Everything compiled"

let main = run_labeled_tests eval labeled_tests

printfn "Everything ran"