(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Antoine Miné 2015
  Marc Chevalier 2018
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Signature of abstract domains representing sets of envrionments
  (for instance: a map from variable to their bounds).
 *)

open! Cfg
(* open Value_domain *) (* L *)
(*module V = ConcreteValues (* L *)*)

module type DOMAIN =
  sig

    (* type of abstract elements *)
    (* an element of type t abstracts a set of mappings from variables
       to integers -> ensemble de mémoires/environnements
     *)
    type env_set

    (* L : type représentant un unique environnement/mémoire *)
    type env

    (* L : type représentant les valeurs prisent par les variables *)
    type v

    (* initial environment (singleton), with all variables initialized to 0 *)
    val init: var list -> env_set

    (* empty set of environments *)
    val bottom: env_set

    (* assign an integer expression to a variable *)
    val assign: env_set -> var -> int_expr -> env_set

    (* filter environments to keep only those satisfying the boolean expression *)
    val guard: env_set -> bool_expr -> env_set

    (* abstract join *)
    val join: env_set -> env_set -> env_set

    (* widening *)
    val widen: env_set -> env_set -> env_set

    (* whether an abstract element is included in another one *)
    val subset: env_set -> env_set -> bool

    (* whether the abstract element represents the empty set *)
    val is_bottom: env_set -> bool

    (* prints *)
    val print: out_channel -> env_set -> unit

  end

(* L : domaine "concret"; les objets de type t sont des ensembles d'applications des variables dans les valeurs *)
(* Convention : tant que possible, je match les variables avec x,y,z,... et les valeurs avec n,m,... *)

(*
module Concrete =
  struct

    type v = V.t

    module Env = Map.Make(struct type t = var let compare = compare end)
    type env = v Env.t

    module EnvSet = Set.Make(struct type t = env let compare = compare end)
    type env_set = EnvSet.t

    (* initial environment (singleton), with all variables initialized to 0 *)
    let init : var list -> env_set = fun l ->
      EnvSet.singleton
        (
          List.fold_left
            (
              fun (env : env) (x : var) ->
                Env.add x (V.const Z.zero) env
            )
            Env.empty
            l
        )

    (* empty set of environments *)
    let bottom : env_set = EnvSet.empty

    let assign_env: env -> var -> int_expr -> env_set = assert false

    (* assign an integer expression to a variable *)
    let assign: env_set -> var -> int_expr -> env_set = assert false


    (* filter environments to keep only those satisfying the boolean expression *)
    let guard: env_set -> bool_expr -> env_set = assert false

    (* abstract join *)
    let join: env_set -> env_set -> env_set = assert false

    (* widening *)
    let widen: env_set -> env_set -> env_set = assert false

    (* whether an abstract element is included in another one *)
    let subset: env_set -> env_set -> bool = assert false

    (* whether the abstract element represents the empty set *)
    let is_bottom: env_set -> bool = assert false

    (* prints *)
    let print: out_channel -> env_set -> unit = assert false
  end

*)