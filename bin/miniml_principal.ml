(* ouverture de la "library" definie dans lib/dune *)
open Miniml

(* ouverture de modules de la library Miniml *)
open Miniml_lexer
open Miniml_parser
open Miniml_typer

(* ******** à compléter ********* *)
 let inferType chaine =
      let f =  read_miniml_tokens_from_file chaine  in 
      let exp = parseExpr f in 
      let l = makeEquations exp [] in
      solv