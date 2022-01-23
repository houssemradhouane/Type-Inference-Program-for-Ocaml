open Miniml_types
open Miniml_lexer
open Miniml_parser

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

(* Fonction qui renvoie le type d'une expression *)
let rec getType e exp =
      let ne = (update_env exp e) in
      match exp with
      | EProd(e1,e2) -> TProd(getType e e1, getType e e2)
      | ECons (_,e2) -> getType e e2
      | EFun(i,e1) -> 
                        let alpha = match getTypeFromEnv ne i with
                           |Some(t) ->t
                           |None -> failwith "Non-existing-variable"
                          in TFun(alpha, getType ne e1)
      | EIf(_,e2,_) -> getType e e2
      | EApply(_,_) ->TVar(TypeVariable.fraiche ())
      | EBinop(_) -> TVar(TypeVariable.fraiche ())
      | ELet(i,e1,e2) -> getType ((i,getType e e1)::e) e2
      | ELetrec(_,_,e2) -> let ne = (update_env exp e) in 
                                getType ne e2
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

(* Fonction qui forme une liste d'équations de type *)
(* à partir d'une expression *)
let makeEquation exp e = 
    match exp with
    | ECons (e1,e2) -> [((getType e e2),TList(getType e e1))]
    | EIf(e1,e2,e3) ->  [(getType e e1, TBool);(getType e e2, getType e e3)]
    | ELetrec(i,e1,_) ->  let alpha = TVar(TypeVariable.fraiche ()) in 
                            let t =
                            match (getTypeFromEnv ((i,alpha)::e) i) with
                            |Some(c) ->[(c, getType ((i,alpha)::e) e1)]
                            |None -> failwith "variable is not defined"
                          in t
    | EApply(e1,e2) -> [(getType e e1, TFun(getType e e2, getType e exp))]
    | _ -> []

let rec makeEquations exp e =
    match exp with
      | EProd(e1,e2) -> (makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)
      | ECons (e1,e2) -> (makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)
      | EFun(_,e1) -> (makeEquation exp e)@(makeEquations e1 e)
      | EIf(e1,e2,e3) -> (makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)@(makeEquations e3 e)
      | EApply(e1,e2) ->(makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)
      | EBinop(_) -> makeEquation exp e
      | ELet(_,e1,e2) -> (makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)
      | ELetrec(_,e1,e2) -> (makeEquation exp e)@(makeEquations e1 e)@(makeEquations e2 e)
      | EConstant(_) ->[]
      | EIdent(_) -> []

(* fonction qui remplace une variable fraîche *)
(* par le type equivalent dans un système d'équations *)
let rec replace alpha tau l =
    match l with 
    | [] -> []
    | (t1,t2)::q -> let new_eq =
                if t1 == alpha
                then (tau,t2)
                else (t1,t2)
                in new_eq::(replace alpha tau q)

(* Fonction qui résout un système d'équations de type *)
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

let rec injectDefinition exprty def e=
    let (alpha,ty) = def in
    match exprty with
    | TUnit -> TUnit
    (* type bool                   *)
    | TBool -> TBool
    (* type int                    *)
    | TInt -> TInt
    (* variable de type            *)
    | TVar(a) -> if TVar(a) = alpha then ty else TVar(a)
    (* type produit: (t1 * t2)     *)
    | TProd(e1,e2) -> TProd(injectDefinition e1 def e,injectDefinition e2 def e)
    (* type fonction: (t1 -> t2)   *)
    | TFun(e1,e2) -> TFun(injectDefinition e1 def e,injectDefinition e2 def e)
    (* type liste: t1 list         *)
    | TList(t) -> TList(injectDefinition t def e)
    
let solve l =
    let rec solverec l def =
        let l2 = getDefinitions l in
        let l1 = solveEquations l in
          if l=l1 then (l,l2@def)
          else solverec l1 (l2@def)
    in solverec l []

 let inferType chaine =
  let f =  read_miniml_tokens_from_string chaine  in 
  let  exp = match Flux.uncons (parseExpr f) with
           | Some((a,_),_) -> a
           | None -> failwith "parsing error" in 
  makeEquations exp []





