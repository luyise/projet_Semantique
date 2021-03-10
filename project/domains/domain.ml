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
open Value_domain (* L *)
module V = ConcreteValues (* L *)

module type DOMAIN =
  sig

    (* type of abstract elements *)
    (* an element of type t abstracts a set of mappings from variables
       to integers -> ensemble de mémoires/environnements
     *)
    type t

    (* initial environment (singleton), with all variables initialized to 0 *)
    val init: var list -> t

    (* empty set of environments *)
    val bottom: t

    (* assign an integer expression to a variable *)
    val assign: t -> var -> int_expr -> t

    (* filter environments to keep only those satisfying the boolean expression *)
    val guard: t -> bool_expr -> t

    (* abstract join *)
    val join: t -> t -> t

    (* widening *)
    val widen: t -> t -> t

    (* whether an abstract element is included in another one *)
    val subset: t -> t -> bool

    (* whether the abstract element represents the empty set *)
    val is_bottom: t -> bool

    (* prints *)
    val print: Format.formatter -> t -> unit

  end

(* L : domaine "concret"; les objets de type t sont des ensembles d'applications des variables dans les valeurs *)
(* Convention : tant que possible, je match les variables avec x,y,z,... et les valeurs avec n,m,... *)

module Concrete : DOMAIN =
  struct

    type v = V.t

    module Env = Map.Make(struct type t = var let compare = compare end)
    
    type t = v Env.t

    (* initial environment (singleton), with all variables initialized to 0 *)
    let init : var list -> t = fun l ->
      List.fold_left
        (
          fun (env : t) (x : var) ->
            Env.add x (V.const Z.zero : v) env
        )
        Env.empty
        l      

    (* empty set of environments *)
    let bottom : t = Env.empty

    (* évalue une int_expr étant donné un environnement *)
    let rec eval_int_expr : int_expr -> t -> v = fun e env ->
      match e with
        (* unary operation *)
        | CFG_int_unary ((iuo : Abstract_syntax_tree.int_unary_op), (e0 : int_expr)) -> 
          V.unary (eval_int_expr e0 env) iuo
        (* binary operation *)
        | CFG_int_binary ((ibo : Abstract_syntax_tree.int_binary_op), (e0 : int_expr), (e1 : int_expr)) ->
          V.binary (eval_int_expr e0 env) (eval_int_expr e1 env) ibo
        (* variable use *)
        | CFG_int_var x ->
          begin
            try Env.find x env
            with Not_found -> failwith "Undifined_variable (Analysis fatal error)"
          end
        | CFG_int_const (n : Z.t) -> V.const n
        | CFG_int_rand ((n : Z.t), (m : Z.t)) -> V.rand n m

    (* assigne une abstraction de valeur à une variable dans une abstraction d'environnements *)
    let update : t -> var -> v -> t = fun env x s ->
      Env.add x s env

    (* assign an integer expression to a variable *)
    let assign : t -> var -> int_expr -> t = fun env x e ->
      update env x (eval_int_expr e env)

    let rec eval_bool_expr : bool_expr -> t -> bool_abst = fun e env ->
      match e with
        (* unary operation *)
        | CFG_bool_unary ((buo : Abstract_syntax_tree.bool_unary_op), (e0 : bool_expr)) -> 
          bool_unary (eval_bool_expr e0 env) buo
        (* binary operation *)
        | CFG_bool_binary ((bbo : Abstract_syntax_tree.bool_binary_op), (e0 : bool_expr), (e1 : bool_expr)) ->
          bool_binary (eval_bool_expr e0 env) (eval_bool_expr e1 env) bbo
        | CFG_compare ((co : Abstract_syntax_tree.compare_op), (e0 : int_expr), (e1 : int_expr)) ->
          V.compare_op (eval_int_expr e0 env) (eval_int_expr e1 env) co
        (* constants *)
        | CFG_bool_const b -> bool_const b
        (* non-deterministic choice *)
        | CFG_bool_rand -> bool_rand ()
    
    (* filter environments to keep only those satisfying the boolean expression *)
    let guard : t -> bool_expr -> t = fun env e ->
      let b = eval_bool_expr e env in
      if can_be_true b then env
      else bottom

    let guard_opt : t -> bool_expr -> t * t = fun env e ->
      let b = eval_bool_expr e env in
      match (can_be_true b), (can_be_false b) with
        | true, true -> env, env
        | true, false -> env, bottom
        | false, true -> bottom, env
        | false, false -> bottom, bottom

    let merge_fun : var -> v option -> v option -> v option = fun _ v0 v1 ->
      match v0,v1 with
        | None, _ | _, None -> None
        | Some v0, Some v1 when V.subset v0 v1 -> Some v1
        | Some v1, Some v0 when V.subset v0 v1 -> Some v1
        | _ -> Some V.top

    (* abstract join *)
    let join : t -> t -> t = fun env0 env1 -> Env.merge merge_fun env0 env1

    (* widening *)
    let widen : t -> t -> t = join

    (* whether an abstract element is included in another one *)
    let subset : t -> t -> bool = fun env0 env1 ->
      Env.for_all
        (
          fun (x : var) (n : v) ->
            match Env.find_opt x env1 with
              | None -> false
              | Some m -> V.subset n m
        )
        env0

    (* whether the abstract element represents the empty set *)
    let is_bottom : t -> bool = Env.is_empty

    let binding_printer : Format.formatter -> var -> v -> unit = fun fmt x n ->
      Format.fprintf fmt " %s = %a \n"
       ((x.var_name)^"("^(string_of_int (x.var_id))^")")
       (V.print) n
    (* prints *)
    let print : Format.formatter -> t -> unit = fun fmt env ->
      let _ = Format.fprintf fmt "état de l'environnement : \n" in
      let _ = Env.iter (binding_printer fmt) env in
      Format.fprintf fmt "\n"

  end
