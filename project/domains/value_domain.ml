(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Antoine Miné 2015
  Marc Chevalier 2018
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Signature of abstract domains representing sets of integers
  (for instance: constants or intervals).
 *)

(* L : on ajoute Bot à n'importe quel type 'a avec le type t add_bot *)
type 'a add_bot =
  |Nb of 'a
  |Bot
type 'a add_bot_top = (* top : n'importe quelle valeur définie ou non *)
  |Nb of 'a
  |Bot
  |Top

open Abstract_syntax_tree

module type VALUE_DOMAIN =
  sig

    (* type of abstract elements *)
    (* an element of type t abstracts a set of integers *)
    type t

    (* unrestricted value: [-oo,+oo] *)
    val top: t

    (* bottom value: empty set *)
    val bottom: t

    (* constant: {c} *)
    val const: Z.t -> t

    (* interval: [a,b] *)
    val rand: Z.t -> Z.t -> t


    (* unary operation *)
    val unary: t -> int_unary_op -> t

    (* binary operation *)
    val binary: t -> t -> int_binary_op -> t

    val eval_expr: int_expr -> t


    (* comparison *)
    (* [compare x y op] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is true for some v' in y
       - y' abstracts the set of v' in y such that v op v' is true for some v  in x
       i.e., we filter the abstract values x and y knowing that the test is true

       a safe, but not precise implementation, would be:
       compare x y op = (x,y)
     *)
    val compare: t -> t -> compare_op -> (t * t)


    (* backards unary operation *)
    (* [bwd_unary x op r] return x':
       - x' abstracts the set of v in x such as op v is in r
       i.e., we fiter the abstract values x knowing the result r of applying
       the operation on x
     *)
    val bwd_unary: t -> int_unary_op -> t -> t

     (* backward binary operation *)
     (* [bwd_binary x y op r] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is in r for some v' in y
       - y' abstracts the set of v' in y such that v op v' is in r for some v  in x
       i.e., we filter the abstract values x and y knowing that, after
       applying the operation op, the result is in r
      *)
    val bwd_binary: t -> t -> int_binary_op -> t -> (t * t)


    (* set-theoretic operations *)
    val join: t -> t -> t
    val meet: t -> t -> t

    (* widening *)
    val widen: t -> t -> t

    (* subset inclusion of concretizations *)
    val subset: t -> t -> bool

    (* check the emptiness of the concretization *)
    val is_bottom: t -> bool

    (* print abstract element *) (* L : On utilise un formatter *)
    val print: Format.formatter -> t -> unit

end

(* L : Implémentation d'un domaine de valeurs concret *)

module ConcreteValues : VALUE_DOMAIN =
  struct
    
    (* type des entiers concrets : Z.t *)
    type t = Z.t add_bot_top

    (* unrestricted value: [-oo,+oo] *)
    let top : t = (Top : t)

    (* bottom value: empty set *)
    let bottom : t = (Bot : t)

    (* constant: {c} *)
    let const : Z.t -> t = fun n -> Nb n

    (* interval: [a,b] *)
    let rand: Z.t -> Z.t -> t = fun a b ->
      if Z.gt a b then Bot
      else 
        begin
          if Z.equal a b then const a
          else Top
        end


    (* unary operation *)
    let unary: t -> int_unary_op -> t = assert false

    (* binary operation *)
    let binary: t -> t -> int_binary_op -> t = assert false

    let eval_expr: int_expr -> t = assert false

    (* comparison *)
    (* [compare x y op] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is true for some v' in y
       - y' abstracts the set of v' in y such that v op v' is true for some v  in x
       i.e., we filter the abstract values x and y knowing that the test is true

       a safe, but not precise implementation, would be:
       compare x y op = (x,y)
     *)
    let compare: t -> t -> compare_op -> (t * t) = fun _ _ _ -> Top, Top

    (* backards unary operation *)
    (* [bwd_unary x op r] return x':
       - x' abstracts the set of v in x such as op v is in r
       i.e., we fiter the abstract values x knowing the result r of applying
       the operation on x
     *)
    let bwd_unary: t -> int_unary_op -> t -> t = fun _ _ _ -> Top

     (* backward binary operation *)
     (* [bwd_binary x y op r] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is in r for some v' in y
       - y' abstracts the set of v' in y such that v op v' is in r for some v  in x
       i.e., we filter the abstract values x and y knowing that, after
       applying the operation op, the result is in r
      *)
    let bwd_binary: t -> t -> int_binary_op -> t -> (t * t) = fun _ _ _ _ -> Top, Top


    (* set-theoretic operations *)
    let join: t -> t -> t = fun a b -> match a,b with
        | Bot, Bot -> Bot
        | Bot, _| _, Bot -> Top
        | Top, _| _, Top -> Top
        | (Nb x), (Nb y) when Z.equal x y -> Nb x
        | _ -> Top

    let meet: t -> t -> t = fun a b -> match a,b with
        | Bot,_ |_, Bot -> Bot
        | Top, _ -> b
        | _, Top -> a
        | (Nb x), (Nb y) when Z.equal x y -> Nb x
        | _ -> Bot
        

    (* widening *)
    let widen: t -> t -> t = fun _ _ -> Top

    (* subset inclusion of concretizations *)
    let subset: t -> t -> bool = fun a b -> match a,b with
        | Bot, _ -> true
        | (Nb x), (Nb y) when x = y -> true
        | (Nb _), Top -> true
        | Top, Top -> true
        | _ -> false

    (* check the emptiness of the concretization *)
    let is_bottom : t -> bool = function
      | Bot -> true
      | _ -> false

    (* print abstract element *)
    let print : Format.formatter -> t -> unit = fun fmt x -> match x with
      | Bot -> Format.fprintf fmt "Bot"
      | Top -> Format.fprintf fmt "Top" 
      | Nb x -> Z.pp_print fmt x

  end

let print_test () =
  let _ = print_newline() in
  let _ = print_string ("hello world") in
  let _ = print_newline() in
  ()
