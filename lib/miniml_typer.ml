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
type  'a env =  (ident * 'a typ) list

(* Fonction qui à partir d'un identifiant de variable *)
(* renvoie son type s'il existe dans l'environnement *)
let rec getTypeFromEnv env ident =
      match env with
      | [] -> None
      | (v,t)::q -> if v=ident then Some(t)
                               else getTypeFromEnv q ident

(* Fonction qui renvoie le type d'une expression *)
let rec getType e exp =
      match exp with
      
      | EProd(e1,e2) -> TProd(getType e e1, getType e e2)
      | ECons (_,e2) -> getType e e2
      | EFun(i,e1) -> let alpha = TVar(TypeVariable.fraiche ()) in
                          TFun(alpha, getType ((i,alpha)::e) e1)
      | EIf(e1,_,_) -> getType e e1
      | EApply(_,_) ->TVar(TypeVariable.fraiche ())
      | EBinop(_) -> TVar(TypeVariable.fraiche ())
      | ELet(i,e1,e2) -> getType ((i,getType e e1)::e) e2
      | ELetrec(i,_,e2) -> let alpha = TVar(TypeVariable.fraiche ()) in
                         getType ((i,alpha)::e) e2
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
let makeEquations exp e =
  let makeEquationsAcc exp eq_liste e = 
    match exp with
    | ECons (e1,e2) -> (getType e e2,TList(getType e e1))::eq_liste
    | EIf(e1,e2,e3) ->  (getType e e1, TBool)::(getType e e2, getType e e3)::eq_liste
    | ELetrec(i,e1,_) -> let t =
                          match (getTypeFromEnv e i) with
                          |Some(c) ->(c, getType e e1)::eq_liste 
                          |None -> failwith "variable is not defined"
                          in t
    | EApply(e1,e2) -> (getType e e1, TFun(getType e e2, getType e exp))::eq_liste
    | _ -> eq_liste
  in makeEquationsAcc exp [] e





