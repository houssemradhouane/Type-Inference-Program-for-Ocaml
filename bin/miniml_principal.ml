(*Le travail a été fait par:
Houssem Radhouane
Mohamed Hamza Kadri
Mahmoud Laanaiya
Pierre-Louis de Villers


-----------------------------------
Le script fonctionne correctement sur quelques exemples mais pas d'autres.
On a essayé de corriger l'erreur dans notre code qui cause ceci, mais on a 
une faute probablement dans notre fonction injectDefinition dans miniml_typer.

1)Les parties qui donnent les résultats attendus :
- Parser
- Formation des équations de typage
- Normalisation des équations de typage
- Résolution du système d'équations
- Levée d'erreur s'il y a un mauvais typage
- affichage des résultats

2)La partie qui ne donne pas le résultat attendu dans certain cas :
- Injection du résultat final dans le type général pour l'affichage

Les tests pour la formation du système d'équations et pour leur résolution passent
(vous pouvez utiliser les fonctions de tests à la fin du fichier miniml_typer)
Donc la seule partie qui semble poser problème est l'injection des résultats dans le
type final.*)

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
     let fty = inferType s in print_typ TypeVariable.fprintf Format.std_formatter fty
;;

main();;
