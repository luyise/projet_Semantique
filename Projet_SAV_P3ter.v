Add LoadPath "C:\Users\Hp\Documents\Coq" as CoqDirectory.
Add LoadPath "/Users/samuel/Documents/Documents-L3/PolyCours/S2/Sem/projet_Semantique" as CoqDirectory.
Load Projet_SAV_Lemmas.



(* Définition du code de la machine de Krivine *)
Inductive codeBloc :=
    | Access : nat -> codeBloc
    | grab : codeBloc -> codeBloc
    | push : codeBloc -> codeBloc -> codeBloc.

(* Définition de la pile de la machine de Krivine *)
Inductive stack := 
    | empty_stack : stack
    | const_stack : (codeBloc * stack) -> stack -> stack.

Notation "'Grab' ; tl " := (grab tl) (at level 20).
Notation "'Push' c ; tl " := (push c tl) (at level 20).
Notation " p # s " := (const_stack p s) (at level 19).


Fixpoint size (e: stack) : nat :=
  match e return nat with
    | empty_stack => 0
    | _ # tl => S (size tl)
end.

(* Définition de l'état de la machine de Krivine*)
Definition krivineState: Type := (codeBloc * stack * stack).

(* Définition de la fonction transition *)
Definition transitionFunction : krivineState -> option krivineState :=
  fun ks => match ks return option krivineState with 
    | (Access 0, (c_0, e_0) # _, s) => Some (c_0, e_0, s)
    | (Access (S n), _ # tl, s)     => Some (Access n, tl, s)
    | (Push c_2; c, e, s)           => Some (c, e, (c_2, e) # s)
    | (Grab; c, e, t # s)           =>  Some (c, t # e, s)
    | _ => None
end.

Fixpoint comp (t: lambdaTermeN) : codeBloc :=
  match t: lambdaTermeN return codeBloc with
    | var n => Access n
    | lambda t_0 => Grab; (comp t_0)
    | app t_0 t_1 => Push (comp t_1); (comp t_0)
end.

Definition comp_glob : lambdaTermeN -> krivineState := 
  fun t => (comp t, empty_stack, empty_stack).


Fixpoint tau_code (code: codeBloc) : lambdaTermeN :=
  match code return lambdaTermeN with
    | Access n => var n
    | Push c_2; c_1 => app (tau_code c_1) (tau_code c_2)
    | Grab; c => lambda (tau_code c)
end.

Fixpoint tau_stack (s: stack) : list lambdaTermeN :=
  match s with
    | empty_stack => nil
    | (c_0, e_0) # e_1 => (subst_list (tau_code c_0) 0 (tau_stack e_0)) :: (tau_stack e_1)
end.

Lemma tau_stack_formula: forall (c_0: codeBloc), forall (e_0 e_1 : stack),
    tau_stack ((c_0, e_0) # e_1) = List.cons (subst_list (tau_code c_0) 0 (tau_stack e_0)) (tau_stack e_1).
Proof.
  move => c_0 e_0 e_1.
  simpl.
  auto.
Qed.

Lemma tau_stack_length: forall s : stack, List.length (tau_stack s) = size s.
Proof.
  intro s.
  induction s.
  simpl.
  trivial.
  simpl.
  case p.
  intro c.
  intro s0.
  simpl.
  rewrite IHs.
  trivial.
Qed.

Definition tau_tuple : codeBloc -> stack -> lambdaTermeN :=
  fun c e => subst_list (tau_code c) 0 (tau_stack e).

Fixpoint tau_inner (s: stack) (n: lambdaTermeN): lambdaTermeN :=
  match s return lambdaTermeN with
    | (c, e) # tl => tau_inner tl (app n (tau_tuple c e))
    | empty_stack => n
end.

Definition tau : krivineState -> lambdaTermeN := 
  fun ks =>  
    match ks return lambdaTermeN with 
      | (c, e, s) => tau_inner s (tau_tuple c e)
end.

Lemma comp_is_comp_glob: forall t: lambdaTermeN, tau (comp_glob t) = tau_code (comp t).
Proof.
  move => t.
  induction t.
  all : simpl.
  all : unfold tau_tuple.
  all : simpl.
  2-3 : repeat rewrite prop0.
  all : trivial.
Qed.

Lemma comp_and_tau: forall t: lambdaTermeN, tau (comp_glob t) = t.
Proof.
  induction t.
  all : simpl.
  all : unfold tau_tuple.
  all : simpl.
  trivial.
  all : repeat rewrite prop0.
  all : repeat rewrite <- comp_is_comp_glob.
  rewrite IHt.
  trivial.
  rewrite IHt1 IHt2.
  trivial.
Qed.

Lemma grab_beta_red : forall c c1 : codeBloc, forall s s1 : stack,
  List.Forall (fun t => C[0](t)) (tau_stack s) -> (app (tau_tuple (grab c) s) (tau_tuple c1 s1)) beta-> (tau_tuple c ((c1, s1) # s)).
Proof.
  move => c c1 s s1 Hl.
  unfold tau_tuple.
  simpl.
  suff: List.map incr_free (tau_stack s) = tau_stack s.
  + intro H.
    rewrite H.
    suff : ((tau_code c) [0 <-- (tau_code c1) [0 <-- tau_stack s1] :: tau_stack s])
        = (tau_code c) [1 <-- tau_stack s] [0 <- (tau_code c1) [0 <-- tau_stack s1]].
      intro H0; rewrite H0.
    apply (evaluation (tau_code c) [1 <-- tau_stack s] (tau_code c1) [0 <-- tau_stack s1]).

    apply prop2.
    simpl.
    trivial.
  + apply lemma23; trivial.
Qed.
