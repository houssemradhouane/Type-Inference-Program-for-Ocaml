open Miniml_types
open Miniml_lexer
open Lazyflux

module Flux = Lazyflux.Flux;;
module Solution = Lazyflux.Flux;;

(* types des parsers généraux *)
type ('a, 'b) result = ('b * 'a Flux.t) Solution.t;;
type ('a, 'b) parser = 'a Flux.t -> ('a, 'b) result;;

(* interface des parsers: combinateurs de parsers et parsers simples *)
module type Parsing =
  sig
    val map : ('b -> 'c) -> ('a, 'b) parser -> ('a, 'c) parser

    val return : 'b -> ('a, 'b) parser

    val ( >>= ) : ('a, 'b) parser -> ('b -> ('a, 'c) parser) -> ('a, 'c) parser

    val zero : ('a, 'b) parser

    val ( ++ ) : ('a, 'b) parser -> ('a, 'b) parser -> ('a, 'b) parser

    val run : ('a, 'b) parser -> 'a Flux.t -> 'b Solution.t

    val pvide : ('a, unit) parser

    val ptest : ('a -> bool) -> ('a, 'a) parser

    val ( *> ) : ('a, 'b) parser -> ('a, 'c) parser -> ('a, 'b * 'c) parser
  end

(* implantation des parsers, comme vu en TD. On utilise les opérations *)
(* du module Flux et du module Solution                                *)
module Parser : Parsing =
  struct
    let map fmap parse f = Solution.map (fun (b, f') -> (fmap b, f')) (parse f);; 

    let return b f = Solution.return (b, f);;

    let (>>=) parse dep_parse = fun f -> Solution.(parse f >>= fun (b, f') -> dep_parse b f');;

    let zero f = Solution.zero;;

    let (++) parse1 parse2 = fun f -> Solution.(parse1 f ++ parse2 f);;

    let run parse f = Solution.(map fst (filter (fun (b, f') -> Flux.uncons f' = None) (parse f)));;

    let pvide f =
      match Flux.uncons f with
      | None   -> Solution.return ((), f)
      | Some _ -> Solution.zero;;

    let ptest p f =
      match Flux.uncons f with
      | None        -> Solution.zero
      | Some (t, q) -> if p t then Solution.return (t, q) else Solution.zero;;

    let ( *> ) parse1 parse2 = fun f ->
      Solution.(parse1 f >>= fun (b, f') -> parse2 f' >>= fun (c, f'') -> return ((b, c), f''));;
  end

(* Fonction de lecture d'un fichier.    *)
(* Produit le flux des lexèmes reconnus *)
let read_miniml_tokens_from_file filename : token Flux.t =
  try
    let chan = open_in filename in
    let buf = Lexing.from_channel chan in
    line_g := 1;
    let next_token () =
      try
        let next = token buf in
        if next = EOF
        then
          begin
            close_in chan;
            None
          end
        else
          Some (next, ())
   with
   | ErreurLex msg ->
      begin
        close_in chan;
        raise (ErreurLecture (Format.sprintf "ERREUR : ligne %d, lexème '%s' : %s" !line_g (Lexing.lexeme buf) msg))
      end in
    Flux.unfold next_token ()
 with
    | Sys_error _ -> raise (ErreurLecture (Format.sprintf "ERREUR : Impossible d'ouvrir le fichier '%s' !" filename))
;;

(* Fonction de lecture d'un buffer.   *)
(* Similaire à la fonction précédente *)
let read_miniml_tokens_from_lexbuf buf : token Flux.t =
  line_g := 1;
  let next_token () =
    try
      let next = token buf in
      if next = EOF
      then
        begin
          None
        end
      else
        Some (next, ())
    with
    | ErreurLex msg ->
       begin
         raise (ErreurLecture (Format.sprintf "ERREUR : ligne %d, lexème '%s' : %s" !line_g (Lexing.lexeme buf) msg))
       end in
  Flux.unfold next_token ()
;;

open Parser

(* Fonction de lecture d'une chaîne.  *)
(* Similaire à la fonction précédente *)
let read_miniml_tokens_from_string chaine : token Flux.t =
  read_miniml_tokens_from_lexbuf (Lexing.from_string chaine)
;;

(* Fonctions auxiliaires de traitement des lexèmes *)
(* contenant une information: IDENT, BOOL et INT   *)
let isident =
  function IDENT _     -> true
         | _           -> false
let isbool =
  function BOOL _      -> true
         | _           -> false
let isint =
  function INT _       -> true
         | _           -> false

let unident =
  function
  | IDENT id    -> id
  | _           -> assert false
let unbool =
  function
  | BOOL b      -> b
  | _           -> assert false   
let unint =
  function
  | INT i       -> i
  | _           -> assert false


(* Fonctions de parsing de MiniML *)
(* ******** à compléter ********* *)

let istoken : token -> token -> bool = fun a t ->
  match t with
  | t when (t = a) -> true
  | _ -> false


let parseIdent = ptest isident >>= fun (t) -> return (unident t)
let parseInt = ptest isint >>= fun (t) -> return (unint t)
let parseBool = ptest isbool >>= fun (t) -> return (unbool t)
let parseToken a = ptest (istoken a) >>= fun (_) -> return ()


let rec parseExpr : (token, expr) parser = fun flux ->
  (
    (parseToken LET >>= fun () -> parseLiaison >>= fun (i, e) -> parseToken IN >>= fun () -> parseExpr >>= fun (e2) -> return (ELet (i, e, e2))) ++
    (parseToken LET >>= fun () -> parseToken REC >>= fun () -> parseLiaison >>= fun (i, e) ->
       parseToken IN >>= fun () -> parseExpr >>= fun (e2) -> return (ELetrec (i, e, e2))) ++
    (parseToken PARO >>= fun () -> parseExpr >>= fun (e1) -> parseBinop >>= fun (binop) ->
      parseExpr >>= fun (e2) -> parseToken PARF >>= fun () -> return (EApply (EApply (binop, e1), e2))) ++
    (parseToken PARO >>= fun () -> parseExpr >>= fun (e1) -> parseToken CONS >>= fun () ->
      parseExpr >>= fun (e2) -> parseToken PARF >>= fun () -> return (ECons (e1, e2))) ++
    (parseToken PARO >>= fun () -> parseExpr >>= fun (e1) -> parseToken VIRG >>= fun () ->
      parseExpr >>= fun (e2) -> parseToken PARF >>= fun () -> return (EProd (e1, e2))) ++
    (parseToken PARO >>= fun () -> parseExpr >>= fun (e1) -> parseBinop >>= fun (binop) ->
      parseExpr >>= fun (e2) -> parseToken PARF >>= fun () -> return (EApply (EApply (binop, e1), e2))) ++
    (parseToken PARO >>= fun () -> parseExpr >>= fun (e) -> parseToken PARF >>= fun () -> return (e)) ++
    (parseToken PARO >>= fun () -> parseExpr >>= fun (e1) -> parseExpr >>= fun (e2) -> parseToken PARF >>= fun () -> return (EApply (e1, e2))) ++
    (parseToken IF >>= fun () -> parseExpr >>= fun (e1) -> parseToken THEN >>= fun () -> parseExpr >>= fun (e2) ->
      parseToken ELSE >>= fun () -> parseExpr >>= fun (e3) -> return (EIf (e1, e2, e3))) ++
    (parseToken PARO >>= fun () -> parseToken FUN >>= fun () -> parseIdent >>= fun (i) ->
      parseToken TO >>= fun () -> parseExpr >>= fun (e) -> parseToken PARF >>= fun () -> return (EFun (i, e))) ++
    (parseIdent >>= fun (i) -> return (EIdent i)) ++
    (parseConst >>= fun (c) -> return (EConstant c))
  ) flux


and parseLiaison : (token, (ident * expr)) parser = fun flux ->
  (
    (parseIdent >>= fun (i) -> parseToken EQU >>= fun () -> parseExpr >>= fun (e) -> return ((i, e)))
  ) flux


and parseBinop : (token, expr) parser = fun flux ->
  (
    (parseToken EQU >>= fun () -> return (EBinop EQU)) ++
    (parseToken NOTEQ >>= fun () -> return (EBinop NOTEQ)) ++
    (parseToken INFEQ >>= fun () -> return (EBinop INFEQ)) ++
    (parseToken INF >>= fun () -> return (EBinop INF)) ++
    (parseToken SUPEQ >>= fun () -> return (EBinop SUPEQ)) ++
    (parseToken SUP >>= fun () -> return (EBinop SUP)) ++
    (parseToken AND >>= fun () -> return (EBinop AND)) ++
    (parseToken OR >>= fun () -> return (EBinop OR)) ++
    (parseToken PLUS >>= fun () -> return (EBinop PLUS)) ++
    (parseToken MOINS >>= fun () -> return (EBinop MOINS)) ++
    (parseToken MULT >>= fun () -> return (EBinop MULT)) ++
    (parseToken DIV >>= fun () -> return (EBinop DIV)) ++
    (parseToken CONCAT >>= fun () -> return (EBinop CONCAT))
  ) flux
  

and parseConst : (token, constant) parser = fun flux ->
  (
    (parseInt >>= fun (i) -> return (CEntier i)) ++
    (parseBool >>= fun (b) -> return (CBooleen b)) ++
    (parseToken CROO >>= fun () -> parseToken CROF >>= fun () -> return (CNil)) ++
    (parseToken PARO >>= fun () -> parseToken PARF >>= fun () -> return (CUnit))
  ) flux