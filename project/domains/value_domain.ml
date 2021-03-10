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
  | Nb of 'a
  | Bot

(*
type bool_abst = (* Abstraction pour les booléens*)
  | BOOLTrue
  | BOOLFalse
  | BOOLBot (* non défini *)
  | BOOLTop (* True ou False *)
  | BOOLAny (* n'importe quoi, défini ou non *)
*)

type bool_bot =
  | BOOLTrue
  | BOOLFalse
  | BOOLBot

module Bool = Set.Make (struct type t = bool_bot let compare = compare end)
type bool_abst = Bool.t

open Abstract_syntax_tree

module type VALUE_DOMAIN =
  sig

    (* type of abstract elements *)
    (* an element of type t abstracts a set of integers *)
    type t

    (* L : n'importe quoi : défini ou non *)
    val any: t

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

    val compare_op: t -> t -> compare_op -> bool_abst
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

(* L : Implémentation globale de l'abstraction pour les booléens *)

(* constant: {c} *)
let bool_const : bool -> bool_abst = fun b ->
  if b then Bool.singleton BOOLTrue else Bool.singleton BOOLFalse

let bool_top = Bool.of_list [BOOLTrue; BOOLFalse]

let bool_any = Bool.add BOOLBot bool_top

let bool_bot = Bool.singleton BOOLBot

let can_be_true : bool_abst -> bool = Bool.mem BOOLTrue

let can_be_false : bool_abst -> bool = Bool.mem BOOLFalse

(* random in true/false *)
let bool_rand : unit -> bool_abst = fun () -> bool_top

let bool_not : bool_bot -> bool_bot = fun b -> match b with
  | BOOLTrue -> BOOLFalse
  | BOOLFalse -> BOOLTrue
  | BOOLBot -> BOOLBot

(* unary operation *)
let bool_unary : bool_abst -> bool_unary_op -> bool_abst = fun b iuo ->
  let op = match iuo with
    | AST_NOT -> bool_not
  in Bool.map op b

let bool_and : bool_bot -> bool_bot -> bool_bot = fun b0 b1 -> match b0,b1 with
  | BOOLFalse, _ -> BOOLFalse
  | BOOLTrue, BOOLTrue -> BOOLTrue
  | BOOLTrue, BOOLFalse -> BOOLFalse
  | BOOLTrue, BOOLBot -> BOOLBot
  | BOOLBot, _ -> BOOLBot

let bool_or : bool_bot -> bool_bot -> bool_bot = fun b0 b1 -> match b0,b1 with
  | BOOLTrue, _ -> BOOLTrue
  | BOOLFalse, BOOLFalse -> BOOLFalse
  | BOOLFalse, BOOLTrue -> BOOLTrue
  | BOOLFalse, BOOLBot -> BOOLBot
  | BOOLBot, _ -> BOOLBot

(* binary operation *)
let bool_binary : bool_abst -> bool_abst -> bool_binary_op -> bool_abst = fun b0 b1 iuo ->
  let op = match iuo with
    | AST_AND -> bool_and
    | AST_OR -> bool_or
  in 
  Bool.fold
    (
      fun b b2 ->
        Bool.union (Bool.map (op b) b1) b2
    )
    b0
    Bool.empty

(* set-theoretic operations *)
let bool_join : bool_abst -> bool_abst -> bool_abst = Bool.union

let bool_meet : bool_abst -> bool_abst -> bool_abst = Bool.inter

(* subset inclusion of concretizations *)
let bool_subset : bool_abst -> bool_abst -> bool = Bool.subset

(* L : Implémentation d'un domaine de valeurs concret *)

module ConcreteValues : VALUE_DOMAIN =
  struct
    
    (* type des entiers concrets : Z.t *)
    type t =
      | VALBot (* non définie *)
      | VALTop (* n'importe quelle valeur définie *)
      | VALAny (* toutes les possibilité, y compris indéfini *)
      | VALNb of Z.t (* un entier bien déterminé *)

    (* unrestricted value: [-oo,+oo] *)
    let top : t = (VALTop : t)

    let any : t = (VALAny : t)

    (* bottom value: empty set *)
    let bottom : t = (VALBot : t)

    (* constant: {c} *)
    let const : Z.t -> t = fun n -> VALNb n

    (* interval: [a,b] *)
    let rand : Z.t -> Z.t -> t = fun a b ->
      if Z.gt a b then VALBot
      else 
        begin
          if Z.equal a b then const a
          else VALTop
        end

    let unary_plus : t -> t = fun a -> a

    let unary_minus : t -> t = fun a -> match a with
        | VALBot -> VALBot
        | VALNb x -> VALNb (Z.neg x)
        | VALTop -> VALTop
        | VALAny -> VALAny

    (* unary operation *)
    let unary : t -> int_unary_op -> t = fun a iuo -> 
      let op = match iuo with
        | AST_UNARY_PLUS -> unary_plus
        | AST_UNARY_MINUS -> unary_minus
      in
      op a

    let binary_plus : t -> t -> t = fun a b ->
      match a,b with
        | VALBot, _ | _, VALBot -> VALBot
        | VALAny, _ | _, VALAny -> VALAny
        | VALTop, _ | _, VALTop -> VALTop
        | (VALNb x), (VALNb y) -> VALNb (Z.add x y)

    let binary_minus : t -> t -> t = fun a b ->
      match a,b with
      | VALBot, _ | _, VALBot -> VALBot
      | VALAny, _ | _, VALAny -> VALAny
      | VALTop, _ | _, VALTop -> VALTop
      | (VALNb x), (VALNb y) -> VALNb (Z.sub x y)

    let binary_mult : t -> t -> t = fun a b ->
      match a,b with
      | VALBot, _ | _, VALBot -> VALBot
      | VALAny, _ | _, VALAny -> VALAny
      | VALTop, _ | _, VALTop -> VALTop
      | (VALNb x), (VALNb y) -> VALNb (Z.mul x y)

    let binary_div : t -> t -> t = fun a b ->
      match a,b with
        | VALBot, _ | _, VALBot -> VALBot
        | _, VALAny -> VALAny
        | VALAny, (VALNb y) when (Z.equal y Z.zero) -> VALBot
        | VALAny, _ -> VALAny
        | VALTop, (VALNb y) when (Z.equal y Z.zero) -> VALBot
        | VALTop, VALTop -> VALAny
        | (VALNb x), (VALNb y) when not (Z.equal y Z.zero)-> VALNb (Z.div x y)
        | _ -> VALBot

    let binary_mod : t -> t -> t = fun a b ->
      match a,b with
        | VALBot, _ | _, VALBot -> VALBot
        | _, VALAny -> VALAny
        | VALAny, (VALNb y) when (Z.equal y Z.zero) -> VALBot
        | VALAny, _ -> VALAny
        | VALTop, (VALNb y) when (Z.equal y Z.zero) -> VALBot
        | VALTop, VALTop -> VALAny
        | (VALNb x), (VALNb y) when not (Z.equal y Z.zero)-> VALNb (Z.rem x y)
        | _ -> VALBot

    (* binary operation *)
    let binary : t -> t -> int_binary_op -> t = fun a b ibo ->
      let op = match ibo with
        | AST_PLUS -> binary_plus
        | AST_MINUS -> binary_minus
        | AST_MULTIPLY -> binary_mult
        | AST_DIVIDE -> binary_div
        | AST_MODULO -> binary_mod
      in
      op a b

    let eq : t -> t -> bool_abst = fun n m -> match n,m with
      | VALBot, _ | _, VALBot -> bool_bot
      | VALAny, _ | _, VALAny -> bool_any
      | VALTop, _ | _, VALTop -> bool_top
      | (VALNb m), (VALNb n) -> bool_const (Z.equal m n)

    let neq : t -> t -> bool_abst = fun n m -> match n,m with
      | VALBot, _ | _, VALBot -> bool_bot
      | VALAny, _ | _, VALAny -> bool_any
      | VALTop, _ | _, VALTop -> bool_top
      | (VALNb m), (VALNb n) -> bool_const (not (Z.equal m n))

    let leq : t -> t -> bool_abst = fun n m -> match n,m with
      | VALBot, _ | _, VALBot -> bool_bot
      | VALAny, _ | _, VALAny -> bool_any
      | VALTop, _ | _, VALTop -> bool_top
      | (VALNb m), (VALNb n) -> bool_const (Z.leq m n)

    let geq : t -> t -> bool_abst = fun n m -> match n,m with
      | VALBot, _ | _, VALBot -> bool_bot
      | VALAny, _ | _, VALAny -> bool_any
      | VALTop, _ | _, VALTop -> bool_top
      | (VALNb m), (VALNb n) -> bool_const (Z.geq m n)

    let lt : t -> t -> bool_abst = fun n m -> match n,m with
      | VALBot, _ | _, VALBot -> bool_bot
      | VALAny, _ | _, VALAny -> bool_any
      | VALTop, _ | _, VALTop -> bool_top
      | (VALNb m), (VALNb n) -> bool_const (Z.lt m n)

    let gt : t -> t -> bool_abst = fun n m -> match n,m with
      | VALBot, _ | _, VALBot -> bool_bot
      | VALAny, _ | _, VALAny -> bool_any
      | VALTop, _ | _, VALTop -> bool_top
      | (VALNb m), (VALNb n) -> bool_const (Z.gt m n)

    let compare_op : t -> t -> compare_op -> bool_abst = fun m n co ->
      let op = match co with
        | AST_EQUAL -> eq
        | AST_NOT_EQUAL -> neq
        | AST_LESS -> lt
        | AST_LESS_EQUAL -> leq
        | AST_GREATER -> gt
        | AST_GREATER_EQUAL -> geq
      in
      op m n

    (* comparison *)
    (* [compare x y op] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is true for some v' in y
       - y' abstracts the set of v' in y such that v op v' is true for some v  in x
       i.e., we filter the abstract values x and y knowing that the test is true

       a safe, but not precise implementation, would be:
       compare x y op = (x,y)
     *)
    let compare: t -> t -> compare_op -> (t * t) = fun _ _ _ -> VALTop, VALTop

    (* backards unary operation *)
    (* [bwd_unary x op r] return x':
       - x' abstracts the set of v in x such as op v is in r
       i.e., we fiter the abstract values x knowing the result r of applying
       the operation on x
     *)
    let bwd_unary: t -> int_unary_op -> t -> t = fun _ _ _ -> VALTop

     (* backward binary operation *)
     (* [bwd_binary x y op r] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is in r for some v' in y
       - y' abstracts the set of v' in y such that v op v' is in r for some v  in x
       i.e., we filter the abstract values x and y knowing that, after
       applying the operation op, the result is in r
      *)
    let bwd_binary: t -> t -> int_binary_op -> t -> (t * t) = fun _ _ _ _ -> VALTop, VALTop


    (* set-theoretic operations *)
    let join : t -> t -> t = fun a b -> match a,b with
        | VALBot, VALBot -> VALBot
        | VALBot, _ | _, VALBot -> VALAny
        | VALAny, _ | _, VALAny -> VALAny
        | VALTop, _ | _, VALTop -> VALTop
        | (VALNb x), (VALNb y) when Z.equal x y -> VALNb x
        | _ -> VALTop

    let meet : t -> t -> t = fun a b -> match a,b with
        | VALBot,_ |_, VALBot -> VALBot
        | VALAny, c | c, VALAny -> c
        | VALTop, c | c, VALTop -> c
        | (VALNb x), (VALNb y) when Z.equal x y -> VALNb x
        | _ -> VALBot
        

    (* widening *)
    let widen : t -> t -> t = join

    (* subset inclusion of concretizations *)
    let subset : t -> t -> bool = fun a b -> match a,b with
        | VALBot, _ -> true
        | _, VALBot -> false
        | _, VALAny -> true
        | VALAny, _ -> false
        | _, VALTop -> true
        | VALTop, _ -> false
        | (VALNb x), (VALNb y) when Z.equal x y -> true
        | _ -> false

    (* check the emptiness of the concretization *)
    let is_bottom : t -> bool = function
      | VALBot -> true
      | _ -> false

    (* print abstract element *)
    let print : Format.formatter -> t -> unit = fun fmt x -> match x with
      | VALBot -> Format.fprintf fmt "Bot"
      | VALTop -> Format.fprintf fmt "Top" 
      | VALAny -> Format.fprintf fmt "Any"
      | VALNb x -> Format.fprintf fmt "{%a}" 
        Z.pp_print x

  end
