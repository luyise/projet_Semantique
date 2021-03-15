(* L : itérateur sur le cfg *)

open! Cfg
open Domain
let display = ref true         (* mettre à true pour une description du calcul lors de l'itération, false pour n'afficher que le résultat de l'analyse *)

(* trouve une optionnelle entrée vers une fonction main *)
let main_entry : cfg -> node option = fun cfg ->
  match (List.find_opt (fun f -> f.func_name = "main") cfg.cfg_funcs) with
    |None -> None
    |Some f -> Some f.func_entry

(* rajoute un arc de la fiin de l'init vers le main si la fonction main existe *)
let add_arc_to_main : cfg -> cfg = fun cfg ->
  match main_entry cfg with
    | None -> cfg
    | Some n ->
      begin
        let cfg_arcs0 = cfg.cfg_arcs in
        let nb_arcs = List.length cfg_arcs0 in
        let arc_to_main = 
          { arc_id = nb_arcs + 1;    (* unique identifier *)
            arc_src = cfg.cfg_init_exit ;   (* source node *)
            arc_dst = n;   (* destination node *)
            arc_inst = CFG_skip "Appel du main après l'initialisation";  (* instruction *)
          }
        in
        let update_entry_and_exit : node -> unit = fun node ->
          if node.node_id = cfg.cfg_init_exit.node_id then
            node.node_out <- arc_to_main :: node.node_out
          else if node.node_id = n.node_id then 
            node.node_in <- arc_to_main :: node.node_in
        in
        let _ = List.iter update_entry_and_exit cfg.cfg_nodes in
        let cfg_arcs1 = arc_to_main :: cfg_arcs0 in
        { 
          cfg_vars = cfg.cfg_vars;    (* list of all the variables *)
          cfg_funcs = cfg.cfg_funcs;  (* list of all the functions *)
          cfg_nodes = cfg.cfg_nodes;  (* list of all the nodes in the program *)
          cfg_arcs = cfg_arcs1;    (* list of all the arcs in the program *)
          cfg_init_entry = cfg.cfg_init_entry;  (* first node of code initializing global variables *)
          cfg_init_exit = cfg.cfg_init_exit;   (* last node of initialization code *)
        }
      end


module type ITERATOR = 
  sig

    module D : DOMAIN
    type env = D.t
    type t (* estimation pour les environnements possibles en tout noeud du cfg *)

    (* prety-printer pour une famille d'environnement indexée par les noeuds d'un CFG *)
    val pp_est : Format.formatter -> unit

    (* fonction principale d'itération sur le graphe de flot de controle,
    elle maintien une abstraction d'environnement en chaque noeud du CFG et les met à jour jusqu'à ce que chaque noeud possède un environnement invariant *)
    val iterate_cfg : Format.formatter -> cfg -> unit

  end

module ConcreteIterator =
  struct
    
    module D = Concrete
    type env = D.t
    module Est = Map.Make(struct type t = node let compare = compare end)
    type t = env Est.t

    (* fonction auxiliaire qui initialise un environnement "Bot" pour chaque noeud autre que le noeud d'entré du CFG,
     et qui initialise toutes les variables à zéro au noeud d'entrée *)
    let init_bot : node list -> node -> var list -> t = fun n_list init_node x_list ->
      Est.add
        init_node
        (D.init x_list)
        (
          List.fold_left
            (
              fun (est : t) (x : node) ->
                Est.add x (D.init_bot x_list) est
            )
            Est.empty
            n_list
        )

    (* fonction qui imprime pour chaque noeud l'envirronnement associé *)
    let binding_printer : Format.formatter -> node -> env -> unit = fun fmt n env ->
      Format.fprintf fmt " environnement au noeud %i : \n %a"
        n.node_id
        D.print env
    
    (* prety-printer pour une famille d'environnement indexée par les noeuds d'un CFG *)
    let pp_est : Format.formatter -> t -> unit = fun fmt est ->
      let _ = Format.fprintf fmt "Estimation globale du GFC : \n" in
      let _ = Est.iter (binding_printer fmt) est in
      Format.fprintf fmt "\n"

    
    (* fonction principale d'itération sur le graphe de flot de controle,
    elle maintien une abstraction d'environnement en chaque noeud du CFG et les met à jour jusqu'à ce que chaque noeud possède un environnement invariant *)
    let iterate_cfg = fun fmt graph ->
      
      let dirty = Queue.create() in   (* file d'attente des noeuds à mettre à jour *)
      let init_node = graph.cfg_init_entry in
      let _ = if !display then Format.fprintf fmt "initialisation des noeuds à traiter : \n" in
      let graph_nodes = graph.cfg_nodes in
      let _ = List.iter 
        (fun n ->
          let _ = if !display then Format.fprintf fmt "noeud %i \n" n.node_id in
          Queue.push n dirty)
        graph_nodes
      in
      let _ = if !display then Format.fprintf fmt "\n" in

      (* tableau indiquant si une variable est dans la file ou non, qui permet d'éviter de push plusieurs fois un même noeud *) 
      let is_dirty = Array.make (List.length graph_nodes + 1) true in (* par défaut, dans le CFG, les noeuds sont numérotés de 1 à (List.length graph_nodes) *)

      let is_reachable = Array.make (List.length graph_nodes + 1) true in (* indique si un noeud est accessible ou non afin de ne pas élargir des environnement inutilement *)

      let rec clean (est : t) : (t) = (* fonction récursive qui va mettre à jour l'estimation *)
        if Queue.is_empty dirty then est else begin

          let current_node = Queue.take dirty in            (* noeud qui va être mis à jour *)
          let _ = is_dirty.(current_node.node_id) <- false in (* on indique que l'on a sorti le noeud courant de la file *)
          let current_env = Est.find current_node est in    (* environnement du noeud qui va être mis-à-jour *)
          let _ = if !display then Format.fprintf fmt "noeud courant : %i : \n" current_node.node_id in

          match current_node.node_in with (* on regarde si le neouds possède des arcs entrants, et on met à jour l'environnement en fonction *)

            | [] -> 
              let _ = if !display then Format.fprintf fmt "pas d'entrée, état de l'environnement sur le noeud courant : \n" in
              let _ = if !display then D.print fmt current_env in
              clean est

            | arcs -> 
              begin

                (* fonction qui renvoie l'environnement sur le noeud courant calculé en passant par un arc arc0, et un booléen indiquent si il est possible d'emprunter cet arc *)
                let compute_env_with_arc : arc -> env * bool = fun arc0 ->

                  let _ = if !display then Format.fprintf fmt "Traitement de l'arc %i \n" arc0.arc_id in
                  if not (is_reachable.(arc0.arc_src.node_id)) then begin
                    let _ = if !display then Format.fprintf fmt "le noeud source n'est pas accessible. \n" in
                    D.bottom, false
                  end else begin
                    let previous_env = Est.find arc0.arc_src est in (* environnement du noeud source de l'arc *)
                    let _ = if !display then Format.fprintf fmt "environnement du noeud source : \n" in
                    let _ = if !display then D.print fmt previous_env in

                    let new_current_env = match arc0.arc_inst with (* nouvel environnement obtenu au noeud courant *)
                      | CFG_assign ((x : var), (e : int_expr)) -> D.assign previous_env x e, true
                      | CFG_skip _ -> previous_env, true
                      | CFG_guard (e : bool_expr) -> D.guard previous_env e
                      | _ -> assert false
                    in
                    let _ = if !display then Format.fprintf fmt "environnement calculé au noeud courant avec l'arc %i : \n" arc0.arc_id in
                    let _ = if !display then D.print fmt (fst new_current_env) in
                    new_current_env
                  end
                    
                in

                (* nouvel environnement au noeud courant après traitement de tous les arcs entrant. *)
                let new_current_env, is_it_reachable = List.fold_left
                  (fun (env, is_it_reachable) arc0 ->
                    let env0, is_it_reachable0 = compute_env_with_arc arc0 in
                    (D.join env0 env), (is_it_reachable0 || is_it_reachable)  )
                  (D.bottom, false)
                  arcs
                in
                 (* on vérifie que le noeud courant est accessible *)
                let updated = ref false in
                let _ = if not is_it_reachable then begin
                  let _ = if is_reachable.(current_node.node_id) then updated := true in
                  let _ = is_reachable.(current_node.node_id) <- false in
                  let _ = if !display then Format.fprintf fmt "le noeud courant est innaccessible \n" in ()
                end else begin
                  let _ = if not is_reachable.(current_node.node_id) then updated := true in
                  let _ = is_reachable.(current_node.node_id) <- true in ()
                end in

                (* si l'environnement à été mis à jour et que le noeud courant possède des arcs sortant, on les met dans la file des noeuds à traiter. *)
                let _ =
                  if D.is_equal current_env new_current_env && not (!updated) then begin
                    let _ = if !display then Format.fprintf fmt "l'environnement n'a pas été mis à jour \n" in ()
                  end else begin 
                    let _ = if !display then Format.fprintf fmt "l'environnement à été mis à jour \n" in
                    let _ = if !display then Format.fprintf fmt "noeuds salis : \n" in
                    let _ = List.iter 
                      (
                        fun arc ->
                          let dst = arc.arc_dst in
                          let _ = if !display then Format.fprintf fmt "  -> %i \n" dst.node_id in
                          if not is_dirty.(dst.node_id) then Queue.push arc.arc_dst dirty
                      )
                      current_node.node_out
                    in
                    let _ = if !display then Format.fprintf fmt "\n" in ()
                  end
                in
                let _ = if !display then Format.fprintf fmt "état de l'environnement sur le noeud courant : \n" in
                let _ = if !display then D.print fmt new_current_env in

                clean (Est.add current_node new_current_env est) (* On continue d'itérer sur les autres noeuds de la file *)
              end

        end
      in

      (* On met à jour l'estimation sur le CFG en partant d'un environnement "Any" en tout noeud du graphe, excepté en le noeud d'entrée ou les variables ont par défaut la valeur 0 *)
      let final_est = clean (init_bot graph.cfg_nodes init_node graph.cfg_vars) in 
      let _ = Format.fprintf fmt "- fin de l'execution : - \n \n" in
      let _ = pp_est fmt final_est in ()

  end