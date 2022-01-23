(* ouverture de la "library" definie dans lib/dune *)
open Miniml

(* ouverture de modules de la library Miniml *)
open Miniml_lexer
open Miniml_parser
open Miniml_typer
open Miniml_printer

(* ******** à compléter ********* *)
let inferType fichier =
   let f =  read_miniml_tokens_from_file fichier  in 
   let exp = match Flux.uncons (parseExpr f) with
            | Some((a,_),_) -> a
            | None -> failwith "parsing error" in 
   let l = makeEquations exp []
   in
  let (_,l2) = solve l in
  let (ty,_) = getType [] exp in finalizeType ty l2 []

let main () =      
   let s =
      if Array.length Sys.argv > 1 then
         Sys.argv.(1)
      else
         ""
   in 
     let fty = inferType s in print_typ TypeVariable.fprintf Format.std_formatter fty;
;;

main();;
