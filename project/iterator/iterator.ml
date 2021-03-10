(* L : itérateur sur le cfg *)

open! Cfg
open Domain

module type ITERATOR = 
  sig

    module D : DOMAIN
    type env = D.t

    val iterate_cfg : Format.formatter -> cfg -> unit

  end

module ConcreteIterator =
  struct
    
    module D = Concrete
    type env = D.t

    let main_entry : cfg -> node option = fun cfg ->
      match (List.find_opt (fun f -> f.func_name = "main") cfg.cfg_funcs) with
        |None -> None
        |Some f -> Some f.func_entry

    let iterate_cfg = fun fmt graph ->
      let dirty = Queue.create() in
      let init_node = graph.cfg_init_entry in
      let _ = Queue.push init_node dirty in
      let rec clean env =
        if Queue.is_empty dirty then env else
        begin
          let current = Queue.take dirty in
          match current.node_out with
            | [] -> env
            | [arc0] ->
              begin
                match arc0.arc_inst with
                  | CFG_assign ((x : var), (e : int_expr)) ->
                    let _ = Queue.push arc0.arc_dst dirty in
                    let _ = D.print fmt env in
                    clean (D.assign env x e)
                  | _ -> assert false
              end
            | _ -> assert false
        end
      in
      let initialized_env = clean (D.init graph.cfg_vars) in
      let _ = D.print fmt initialized_env in
      let _ = Format.fprintf fmt "- fin de l'initialisation - \n" in
      let final_env = match main_entry graph with
        | None -> initialized_env
        | Some main_entry_node ->
          begin
            let _ = Queue.push main_entry_node dirty in
            (clean initialized_env)
          end
      in
      let _ = D.print fmt final_env in
      Format.fprintf fmt "- fin de l'execution - \n"

  end