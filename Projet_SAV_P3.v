Require Import Lia.

Inductive lambdaTerme :=
  | var : nat -> lambdaTerme
  | lambda : lambdaTerme -> lambdaTerme
  | app : lambdaTerme -> lambdaTerme -> lambdaTerme.

Fixpoint linkDepth (t : lambdaTerme) : nat :=
  match t : lambdaTerme return nat with
    | var _ => 0
    | lambda t_0 => 1 + (linkDepth t_0)
    | app t_0 t_1 => max (linkDepth t_0) (linkDepth t_1)
 end.

Definition id : lambdaTerme := lambda (var 0).

Eval compute in (linkDepth id).


(* Définition du code de la machine de Krivine *)
CoInductive instruction :=
    | access : nat -> instruction
    | grab : instruction
    | push : codeBloc -> instruction
with codeBloc := 
    | emptyBloc : codeBloc
    | ins : instruction -> codeBloc -> codeBloc.

(* Définition de la pile de la machine de Krivine *)
Inductive stack := 
    | empty : stack
    | element : (codeBloc * stack) -> stack -> stack.

(* Définition de l'état de la machine de Krivine*)
Definition krivineState: Type := (codeBloc * stack * stack).

(* Définition de la fonction transition *)
Definition transitionFunction : krivineState -> option krivineState :=
  fun ks => match ks return option krivineState with 
    | (ins (access 0) _, element (c_0, e_0) _, s) => Some (c_0, e_0, s)
    | (ins (access (S n)) c, element _ tl, s) =>  Some (ins (access n) c, tl, s)
    | (ins (push c_2) c, e, s) => Some (c, e, element (c_2, e) s)
    | (ins grab c, e, element (c_0, e_0) s) => Some (c, element (c_0, e_0) e, s)
    | _ => None
end.

Fixpoint comp (t: lambdaTerme) : codeBloc :=
  match t: lambdaTerme return codeBloc with
    | var n => ins (access n) emptyBloc
    | lambda t_0 => ins grab (comp t_0)
    | app t_0 t_1 => ins (push (comp t_1)) (comp t_0)
end.

Print comp.

Fixpoint tau_code (code : codeBloc) : lambdaTerme :=
  match code return lambdaTerme with
    | ins (access n) _ => var n
    | ins (push c_2) c_1 => app (tau_code c_1) (tau_code c_2)
    | ins grab c => lambda (tau_code c)
end.

Fixpoint 


Print tau_code.