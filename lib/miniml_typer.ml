open Miniml_types

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
type env = (ident * 'a typ) list

(* Définition du type equation : couple de deux types *)
type equation = 'a typ * 'b typ

(* Fonction qui à partir d'un identifiant de variable *)
(* renvoie son type s'il existe dans l'environnement *)
let rec getTypeFromEnv env ident =
      match env with
      | [] -> None
      | (v,t)::q -> if v=ident then Some(t)
                               else getType q ident

(* Fonction qui renvoie le type d'une expression *)
let rec getType env exp =
      match exp with
      | EConstant(c) -> match c with
                        | CBooleen(b) -> Tbool
                        | CEntier(e) -> TInt
                        | CNil -> TList(TUnit)
                        | CUnit -> TUnit
      | EIdent(i) -> match getTypeFromEnv env i with
                    | Some(t) -> t
                    | None -> failwith "undefined variable"
      | EProd(e1,e2) -> TProd(getType env e1, getType env e2)
      | ECons (e1,e2) -> getType env e2
      | EFun(i,e) -> let alpha = TVar(TypeVariable.fraiche ()) in
                          Tfun(alpha, getType (i,alpha)::env e)
      | EIf(e,e1,e2) -> getType e1
      | EApply(e1,e2) ->TVar(TypeVariable.fraiche ())
      | EBinop(t) -> TVar(TypeVariable.fraiche ())
      | ELet(i,e1,e2) -> getType (i,getType env e1)::env e2
      | ELetrec(i,e1,e2) -> let alpha = TVar(TypeVariable.fraiche ()) in
                         getType (i,alpha)::env e2

(* Fonction qui forme une liste d'équations de type *)
(* à partir d'une expression *)
let makeEquations exp env =
  let makeEquationsAcc exp eq_liste env = 
    match exp with
    | ECons (e1,e2) -> (getType e2,TList(getType e1))::eq_liste
    | EIf(e,e1,e2) ->  (getType e, TBool)::(getType e1, getType e2)::eq_liste
    | ELetrec(i,e1,e2) -> (getType i, getType e1)::eq_liste 
    | EApply(e1,e2) -> (getType e1, TFun(getType e2, getType exp))::eq_liste
    | _ -> eq_liste
  in makeEquationsAcc exp []


