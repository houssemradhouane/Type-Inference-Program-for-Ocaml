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


open Miniml_types
open Miniml_lexer
open Miniml_parser
open Miniml_printer

(* signature minimale pour définir des variables *)
module type VariableSpec =
  sig
    (* type abstrait des variables      *)
    type t

    (* création d'une variable fraîche  *)
    val fraiche : unit -> t

    (* fonctions de comparaison         *)
    (* permet de définir des conteneurs *)
    (* (hash-table, etc) de variables   *)
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int

    (* fonction d'affichage             *)
    (* on utilise Format.std_formatter  *)
    (* comme premier paramètre          *)
    (* pour la sortie standard          *) 
    val fprintf : Format.formatter -> t -> unit
  end

(* implantation de la spécification     *)
module TypeVariable : VariableSpec =
  struct
    type t = int

    let fraiche =
      let cpt = ref 0 in
      (fun () -> incr cpt; !cpt)

    let compare a b = a - b
    let equal a b = a = b
    let hash a = Hashtbl.hash a
    let fprintf fmt a = Format.fprintf fmt "t{%d}" a
  end


(* Définition du type environnement *)
type  'a env =  (ident * 'a typ) list

(* fonction qui met à jour un environnement *)
(* à partir d'une expression *)
(* Sortie : environnement mis à jour*)
let update_env exp e =
    match exp with
    | ELetrec(i,_,_) -> let alpha = TVar(TypeVariable.fraiche ()) in
                                  (i,alpha)::e
    | EFun(i,_) -> let alpha = TVar(TypeVariable.fraiche ()) in
                                  (i,alpha)::e
    | _ -> e
(* Fonction qui à partir d'un identifiant de variable *)
(* renvoie son type s'il existe dans l'environnement *)
let rec getTypeFromEnv env ident =
      match env with
      | [] -> None
      | (v,t)::q -> if v=ident then Some(t)
                               else getTypeFromEnv q ident

(*********************************************************************FORMATION DES EQUATIONS DE TYPE************************************************************************** *)

(* Fonction qui renvoie le type d'une expression *)
(* entrée : une expression *)
(* sortie : son type avec les variables fraîches *)
let rec getType e exp =
      let ne = (update_env exp e) in
      let typ =match exp with
      | EProd(e1,e2) -> let (t1,_) = getType ne e1 in
                        let (t2,_) = getType ne e2 in 
                        TProd(t1,  t2)
      | ECons (_,e2) -> let (t2,_) = getType ne e2 in t2
      | EFun(i,e1) -> let alpha = match getTypeFromEnv ne i with
                           |Some(t) ->t
                           |None -> failwith "Non-existing-variable"
                          in let (t1,_) = getType ne e1 in 
                          TFun(alpha, t1)
      | EIf(_,e2,_) -> let (t2,_) = getType ne e2 in t2
      | EApply(_,_) ->TVar(TypeVariable.fraiche ())
      | EBinop(_) -> TVar(TypeVariable.fraiche ())
      | ELet(i,e1,e2) -> let (t1,_) = getType ne e1 in
                         let (t2,_) = getType ((i,t1)::ne) e2 in 
                            t2
      | ELetrec(_,_,e2) -> let (t2,_) = getType ne e2 in t2
      | EConstant(c) -> let cons = 
                          match c with
                        | CBooleen(_) -> TBool
                        | CEntier(_) -> TInt
                        | CNil -> TList(TUnit)
                        | CUnit -> TUnit
                        in cons
      | EIdent(i) -> match getTypeFromEnv e i with
                    | Some(t) -> t
                    | None -> failwith "undefined variable"
      in (typ,ne)

(* Fonction qui donne une équation de type *)
(* à partir d'une expression *)
(* entrée : expression, environnement *)
(* sortie : liste d'equation de type (peut re vide)*)
let makeEquation exp e = 
    match exp with
    | ECons (e1,e2) -> let (t1,_) = getType e e1 in
                        let (t2,_) = getType e e2 in 
                        [(t2,TList(t1))]
    | EIf(e1,e2,e3) -> let (t1,_) = getType e e1 in
                        let (t2,_) = getType e e2 in 
                        let (t3,_) = getType e e3 in
                         [(t1, TBool);(t2, t3)]
    | ELetrec(i,e1,_) -> let (t1,_) = getType e e1 in
                         let (_,ne) = getType e exp in
                            let t =
                            match (getTypeFromEnv ne i) with
                            |Some(c) ->[(c, t1)]
                            |None -> failwith "variable is not defined"
                          in t
    | EApply(e1,e2) -> let (t1,_) = getType e e1 in
                       let (t2,_) = getType e e2 in 
                       let (t,_) = getType e exp in
                        [(t1, TFun(t2, t))]
    | _ -> []

(* Fonction qui donne un système d'équation de type *)
(* à partir d'une expression. Elle parcourt l'expression récurissevement *)
(* entrée : expression , environnement*)
(* sortie : liste d'equation de type (peut être vide)*)
let rec makeEquations exp en =
    let e = update_env exp en in
    match exp with
      | EProd(e1,e2) -> (makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)
      | ECons (e1,e2) -> (makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)
      | EFun(_,e1) -> (makeEquation exp e)@(makeEquations e1 e)
      | EIf(e1,e2,e3) -> (makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)@(makeEquations e3 e)
      | EApply(e1,e2) ->(makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)
      | EBinop(_) -> makeEquation exp e
      | ELet(i,e1,e2) -> let (t,_) = getType e e1 in
                          let en = (i,t)::e in
                      (makeEquation exp en)@(makeEquations e1 en)@(makeEquations e2 en)
      | ELetrec(_,e1,e2) -> (makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)
      | EConstant(_) ->[]
      | EIdent(_) -> []
(************************************************************NORMALISATION DES EQUATIONS DE TYPE*******************************************************************************)

(* fonction qui remplace une variable fraîche *)
(* par le type equivalent dans un système d'équations *)
(* entrée : variable de type, type equivalent, liste d'equations*)
(* sortie : nouveau système d'equations*)
let rec replace alpha tau l =
    match l with 
    | [] -> []
    | (t1,t2)::q -> let new_eq =
                if t1 == alpha
                then (tau,t2)
                else (t1,t2)
                in new_eq::(replace alpha tau q)

(* Fonction qui résout un système d'équations de type *)
(* entrée : liste d'equations*)
(* sortie : liste normalisée des équations*)
let solveEquations l =
  let rec solveEquationsAcc l res = 
    match l with
    | [] -> res
    | (t1,t2)::q -> let add =
                    match (t1,t2) with
                    | TUnit, TUnit -> solveEquationsAcc q res
                    | TInt, TInt -> solveEquationsAcc q res
                    | TBool, TBool -> solveEquationsAcc q res
                    | TList(typ1), TList(typ2) -> solveEquationsAcc q ((typ1,typ2)::res)
                    | TFun(to1,to2),TFun(sig1,sig2) -> solveEquationsAcc q ((to1,sig1)::(to2,sig2)::res)
                    | TProd(to1,to2),TProd(sig1,sig2) -> solveEquationsAcc q ((to1,sig1)::(to2,sig2)::res)
                    | TVar(a), TVar(b) -> if TypeVariable.equal a b
                                          then solveEquationsAcc q res
                                          else failwith "failed to type"
                    | ty, TVar(a) -> solveEquationsAcc q ((TVar(a),ty)::res)
                    | TVar(a) ,ty -> solveEquationsAcc (replace (TVar(a)) ty q) (replace (TVar(a)) ty res)
                    | _ -> failwith " failed to type"
                    in add
  in solveEquationsAcc l []

(*******************************************************************INJECTION DES RESULTATS DANS LE TYPE GENERAL*************************************************************** *)

(* Fonction qui extrait une défintion de variable de type*)
(* Entrée : Liste d'équations*)
(* Sortie : (VariabledeType,TypeEquivalent*)
let getDefinitions l =
    let rec getDefinitionsAcc l res = 
    match l with
    | [] -> res
    | (t1,t2)::q -> let add =
                    match (t1,t2) with
                    | TVar(_), TVar(_) -> getDefinitionsAcc q res
                    | TVar(_) ,_ -> (t1,t2)::(getDefinitionsAcc q res)
                    | _ -> getDefinitionsAcc q res
                    in add
    in getDefinitionsAcc l []

(*Fonction qui remplace une Variable de type *)
(* par son type equivalent dans le type general *)
(* d'une expression*)
(* entrée : type de l'expression, type equivalent, environnement *)
(* sortie : nouveau type mis à jour *)
let rec injectDefinition exprty def e=
    let (alpha,ty) = def in
    match exprty with
    | TUnit -> TUnit
    (* type bool                   *)
    | TBool -> TBool
    (* type int                    *)
    | TInt -> TInt
    (* variable de type            *)
    | TVar(a) -> if TVar(a) == alpha then ty else TVar(a)
    (* type produit: (t1 * t2)     *)
    | TProd(e1,e2) -> TProd(injectDefinition e1 def e,injectDefinition e2 def e)
    (* type fonction: (t1 -> t2)   *)
    | TFun(e1,e2) -> TFun(injectDefinition e1 def e,injectDefinition e2 def e)
    (* type liste: t1 list         *)
    | TList(t) -> TList(injectDefinition t def e)

(*Fonction qui remplace toutes les Variable de type *)
(* par leurs type equivalent dans le type general *)
(* d'une expression*)
(* entrée : type de l'expression, types equivalents, environnement *)
(* sortie : type final de l'expression *)
let rec finalizeType exprTy defs e =
    match defs with
    | [] -> exprTy
    | def::q -> let nexprTy = injectDefinition exprTy def e in
                    finalizeType nexprTy q e

(* fonction qui résout un système d'équation en itérant *)
(* sur le système jusqu'à ce qu'il n'y plus de travail à faire *)
(* et renvoie les couples (variabledetype, typeEquivalent)*)
(* entrée : liste d'equations *)
(* sortie : (résultat d'application des règles(doit être vide si bon typage), liste des couples (VariabledeType,TypeEquivalent))*)    
let solve l =
    let rec solverec l def =
        let l2 = getDefinitions l in
        let l1 = solveEquations l in
          if l=l1 then (l,l2@def)
          else solverec l1 (l2@def)
    in solverec l []

(**************************************************************************FONCTIONS DE TESTS***********************************************************************************)

(* fonction utile pour tester makeEquations*)
let test_makeEquations chaine =
  let f =  read_miniml_tokens_from_string chaine  in 
  let  exp = match Flux.uncons (parseExpr f) with
           | Some((a,_),_) -> a
           | None -> failwith "parsing error" in 
   makeEquations exp []

(* fonction utile pour tester solve*)
 let test_solve chaine =
  let f =  read_miniml_tokens_from_string chaine  in 
  let  exp = match Flux.uncons (parseExpr f) with
           | Some((a,_),_) -> a
           | None -> failwith "parsing error" in 
  let l = makeEquations exp [] in solve l

(* fonction utile pour tester injectDefinition*)
 let test_injectDefinition chaine =
  let f =  read_miniml_tokens_from_string chaine  in 
  let  exp = match Flux.uncons (parseExpr f) with
           | Some((a,_),_) -> a
           | None -> failwith "parsing error" in 
  let l = makeEquations exp [] in let (_,l2)=solve l in
  let def = match l2 with
      |t::_ ->t
      |_ ->(TUnit,TUnit) in
  let (t,_) = getType [] exp in
  injectDefinition t def []
   (* in
  let (_,l2) = solve l in
  let (ty,_) = getType [] exp in let fty =finalizeType ty l2 [] in print_typ TypeVariable.fprintf Format.std_formatter fty *)






