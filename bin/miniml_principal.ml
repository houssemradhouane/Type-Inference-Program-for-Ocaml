(* ouverture de la "library" definie dans lib/dune *)
open Miniml

(* ouverture de modules de la library Miniml *)
open Miniml_lexer
open Miniml_parser
open Miniml_typer

(* ******** à compléter ********* *)
let inferType fichier =
   let f =  read_miniml_tokens_from_file fichier  in 
   let exp = match Flux.uncons (parseExpr f) with
            | Some((a,_),_) -> a
            | None -> failwith "parsing error" in 
   makeEquations exp []

let main () =      
   let s =
      if Array.length Sys.argv > 1 then
         Sys.argv.(1)
      else
         ""
   in 
      inferType s
;;

main();;
