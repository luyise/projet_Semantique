Require Import Lia.
Require Import ssreflect.

(* Partie 1 : Indices de De Bruijn et manipulation de lambdaTerme *)

(* - 1 - *)

(* type pour les lambda-termes avec indices de De Bruijn *)
Inductive lambdaTermeN :=
  | var : nat -> lambdaTermeN
  | lambda : lambdaTermeN -> lambdaTermeN
  | app : lambdaTermeN -> lambdaTermeN -> lambdaTermeN.

(* - 2 - *)

(* une fonction test calulant la profondeur d'un terme *)
Fixpoint linkDepth (t : lambdaTermeN) : nat :=
  match t : lambdaTermeN return nat with
    | var _ => 0
    | lambda t_0 => 1 + (linkDepth t_0)
    | app t_0 t_1 => max (linkDepth t_0) (linkDepth t_1)
  end.

Definition id : lambdaTermeN := lambda (var 0).

(* [ prop_aux_with_linkDepth n d t ] renvoie la proposition correspondant à
  "dans le sous-terme t, apparaissant sous d lambdas dans un terme, toutes les variables libres sont d'indice <= n" *)
Fixpoint prop_aux_with_linkDepth (n : nat) (d : nat) (t : lambdaTermeN) : Prop :=
  match t return Prop with
    | var x => (x>n -> x<d)
    | lambda t_0 => (prop_aux_with_linkDepth n (d+1) t_0)
    | app t_0 t_1 => (prop_aux_with_linkDepth n d t_0) /\ (prop_aux_with_linkDepth n d t_1)
  end.

(* hasAllFreeVarUnder n t renvoie la proposition correspondant à 
  "dans le terme t, toutes les variables libres sont d'indice <= n" *)
Definition hasAllFreeVarUnder : nat -> lambdaTermeN -> Prop :=
  fun n => prop_aux_with_linkDepth n 0.

(* la notation proposée par le sujet : *)
Notation "C[ n ]( t  )" := (hasAllFreeVarUnder (n : nat) (t : lambdaTermeN)).

Lemma lemma0 : forall t : lambdaTermeN, forall n d : nat,
  prop_aux_with_linkDepth n d t -> prop_aux_with_linkDepth (n+1) d t.
Proof.
  move => t.
  induction t.
  simpl; lia.
  simpl; move => n d.
  apply IHt.
  simpl; move => n d.
  case.
  move => Ht1 Ht2.
  split; [apply IHt1 | apply IHt2]; trivial.
Qed.

Lemma lemma1 : forall t : lambdaTermeN, forall n : nat, C[n](t) -> C[n+1](t).
Proof.
  move => t n; apply lemma0.
Qed.

(* isClosed t donne la proposition correspondant à "t est un terme clos" *)
Definition isClosed t := C[0](t).

(*
Ici, on définit une convention sur l'interprétation des termes.
A priori, pour le terme app (var 1) (lambda (var 1)) ou app (var 1) (lambda (var 2)) rien ne permet d'identifier les variables 1 et/ou 2.
Cependant, lorsque l'on éffectue une beta-réduction sur app (lambda (app (var 1) (lambda (var 1)))) (var 2),
on n'identifie pas les deux occurrences de 1 à une même variable (celle à substituer par 2)
et dans app (lambda (lambda (app (var 1) (lambda (var 2))))) (var 2) lors d'une beta-reduction, on veut identifier les occurences de 1 et de 2 à la même variable que l'on substitue.
Donc on choisit la convention que chaque lambda incrémente de 1 les valeurs représentant les variables libres auquelles elles font référence.
Par exemple lambda (app (lambda (var 2)) (var 1)) s'interprète comme le lambda-Terme lambdaX.((lambdaY. Z) Z) 
*)

(* remarque : dans la suite on utilise Nat.eqb, Nat.leb pour obtenir un résultat booléen et non propositionnel pour (3 = 4) *)

(* incr_free_with_linkDepth d u ncrémente toutes les variables libres de u en tant que sous terme d'un
  autre terme, apparaissant sous une profondeur de d lambdas. *)

Fixpoint incr_free_with_linkDepth (d : nat) (u : lambdaTermeN) :=
 match u return lambdaTermeN with
    | var x => if (Nat.leb d x) then (var (S x)) else u
    | lambda u_0 => lambda (incr_free_with_linkDepth (S d) u_0)
    | app u_0 u_1 => app (incr_free_with_linkDepth d u_0) (incr_free_with_linkDepth d u_1)
  end.

Definition incr_free t := incr_free_with_linkDepth 0 t. 

(* On définit la fonction de substitution :
subst t y u renvoie le terme t dans lequel on a substitué la variable y (au sens discuté précédemment par le terme u *)
Fixpoint subst (t : lambdaTermeN) (y : nat) (u : lambdaTermeN) : lambdaTermeN := 
  match t return lambdaTermeN with
    | var x =>
      if (Nat.eqb x y) then u else t
    | lambda t_0 =>
      lambda (subst t_0 (y+1) (incr_free u))
    | app t_0 t_1 =>
      app (subst t_0 y u) (subst t_1 y u)
  end.

Notation "t [ y <- u ]" := (subst t y u) (at level 0).

(*
Eval compute in id.
Eval compute in ( ((app (lambda (var 1)) (var 1))) [ 0 <- id ] ).
*)





(* Définition du code de la machine de Krivine *)
Inductive codeBloc :=
    | access : nat -> codeBloc
    | grab : codeBloc -> codeBloc
    | push : codeBloc -> codeBloc -> codeBloc.

(* Définition de la pile de la machine de Krivine *)
Inductive stack := 
    | empty : stack
    | element : (codeBloc * stack) -> stack -> stack.

(* Définition de l'état de la machine de Krivine*)
Definition krivineState: Type := (codeBloc * stack * stack).

(* Définition de la fonction transition *)
Definition transitionFunction : krivineState -> option krivineState :=
  fun ks => match ks return option krivineState with 
    | (access 0, element (c_0, e_0) _, s) => Some (c_0, e_0, s)
    | (access (S n), element _ tl, s) =>  Some (access n, tl, s)
    | (push c_2 c, e, s) => Some (c, e, element (c_2, e) s)
    | (grab c, e, element (c_0, e_0) s) => Some (c, element (c_0, e_0) e, s)
    | _ => None
end.

Fixpoint comp (t: lambdaTermeN) : codeBloc :=
  match t: lambdaTermeN return codeBloc with
    | var n => access n
    | lambda t_0 => grab (comp t_0)
    | app t_0 t_1 => push (comp t_1) (comp t_0)
end.

Definition comp_glob : lambdaTermeN -> krivineState := 
  fun t => (comp t, empty, empty).

Print comp.

Fixpoint tau_code (code: codeBloc) : lambdaTermeN :=
  match code return lambdaTermeN with
    | access n => var n
    | push c_2 c_1 => app (tau_code c_1) (tau_code c_2)
    | grab c => lambda (tau_code c)
end.

Fixpoint tau_tuple (c: codeBloc) (e: stack) (prof: nat) : lambdaTermeN :=
  match e with
    | empty => tau_code c
    | element (c_0, e_0) e_1 => subst (tau_tuple c e_1 (S prof)) prof (tau_tuple c_0 e_0 0)
end.

Fixpoint tau_inner (c: codeBloc) (e: stack) (s: stack) : lambdaTermeN :=
  match s return lambdaTermeN with
    | element (c_0, e_0) tl => app (tau_tuple c e 0) (tau_inner c_0 e_0 tl)
    | empty => tau_tuple c e 0
end.

Print tau_code.
Print tau_tuple.
Print tau_inner.



Definition tau : krivineState -> lambdaTermeN := 
  fun ks =>  
    match ks return lambdaTermeN with 
      | (c, e, s) => tau_inner c e s
end.

Lemma comp_is_comp_glob: forall t: lambdaTermeN, tau (comp_glob t) = tau_code (comp t).
Proof.
  move => t.
  simpl.
  trivial.
Qed.

Lemma comp_and_tau: forall t: lambdaTermeN, tau (comp_glob t) = t.
Proof.
  induction t; simpl.
  trivial.
  suff : (tau_code (comp t)) = t.
  move => H; rewrite H; trivial.
  rewrite <- comp_is_comp_glob.
  trivial.
  rewrite <- comp_is_comp_glob.
  rewrite IHt1.
  rewrite <- comp_is_comp_glob.
  rewrite IHt2.
  trivial.
Qed.

Fixpoint size (e: stack) : nat :=
  match e return nat with
    | empty => 0
    | element _ tl => S (size tl)
end.

Definition code_correctness: codeBloc -> stack -> Prop := 
  fun c e => C[ size e]( tau_code c).

Fixpoint stack_correctness (s: stack): Prop :=
  match s with
    | empty => True 
    | element (c_0, e_0) tl => (code_correctness c_0 e_0) /\ stack_correctness e_0 /\ stack_correctness tl
end.

Definition state_correctness: krivineState -> Prop := 
  fun ks => match ks with 
    | (c, e, s) => code_correctness c e /\ stack_correctness e /\ stack_correctness s
end.

Lemma option_equality_lemma: forall A : Type, forall (a1 a2: A), Some a1 = Some a2 -> a1 = a2.
Proof.
  move => A a1 a2.
  case.
  trivial.
Qed.

Lemma tuple_eq_is_eq: forall (A B : Type) (a1 a2 : A) (b1 b2 : B),
      (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
Proof.
  move => A B.
  split. move => H . split.
  replace a1 with (fst (a1, b1)); replace a2 with (fst (a2, b2)); trivial.
  rewrite H.
  trivial.
  replace b1 with (snd (a1, b1)); replace b2 with (snd (a2, b2)); trivial.
  rewrite H; trivial.
  move => H. destruct H.
  rewrite H. rewrite H0.
  trivial.
Qed.

Lemma triple_eq_is_eq: forall (A B C: Type) (a1 a2 : A) (b1 b2 : B) (c1 c2 : C),
  (a1, b1, c1) = (a2, b2, c2) <-> a1 = a2 /\ b1 = b2 /\ c1 = c2.
  move => A B C.
  split.
  move => H.
  split.
  replace a1 with (fst (fst ((a1, b1), c1))); replace a2 with (fst (fst ((a2, b2), c2))); trivial.
  rewrite H; trivial.
  split.
  replace b1 with (snd (fst ((a1, b1), c1))); replace b2 with (snd (fst ((a2, b2), c2))); trivial.
  rewrite H; trivial.
  replace c1 with (snd ((a1, b1), c1)); replace c2 with (snd ((a2, b2), c2)); trivial.
  rewrite H; trivial.
  move => H. destruct H; destruct H0.
  rewrite H; rewrite H0; rewrite H1.
  trivial.
Qed.

Lemma correctness_preserved: forall ks: krivineState, forall nks: krivineState, state_correctness ks -> (transitionFunction ks = Some nks) -> state_correctness nks.
Proof.
  unfold krivineState.
  move => ks nks.
  case ks.
  move => p_0 s_0.
  case p_0.
  move => c_0 e_0.
  case nks; move => p_1 s_1; case p_1; move => c_1 e_1.
  case c_0; simpl.
  case e_0; simpl.
  move => n _.
  case n; discriminate.
  move => p_2 s n.
  case n; simpl.
  case p_2.
  move => c s0 H1 Eq.
  destruct H1 as [cc_1 [[cc_c_s0 [sc_s0 sc_s]] sc_s_0]].
  suff: (c = c_1) /\ (s0 = e_1) /\ (s_0 = s_1).
  move => [c_is_c1 [s0_is_e1 s_0_is_s_1]].
  rewrite <- c_is_c1; rewrite <- s0_is_e1; rewrite <- s_0_is_s_1.
  split; trivial; split; trivial.
  apply triple_eq_is_eq.
  apply option_equality_lemma.
  trivial.
  
  case p_2.
  move => c s0 n0 H Eq.
  destruct H; destruct H0; destruct H0; destruct H2.
  suff: (access n0 = c_1) /\ (s = e_1) /\ (s_0 = s_1).
  move => [c_is_acc [s0_is_e1 s_0_is_s_1]].
  rewrite <- c_is_acc; rewrite <- s0_is_e1; rewrite <- s_0_is_s_1.
  split.
  unfold code_correctness; simpl.
  unfold code_correctness in H; simpl in H.
  unfold hasAllFreeVarUnder; unfold hasAllFreeVarUnder in H.
  simpl; simpl in H.
  lia.
  split; trivial.
  apply triple_eq_is_eq.
  apply option_equality_lemma.
  trivial.


  case s_0.
  discriminate.

  move => p s c.
  case p.
  move => c0 s0.
  simpl.
  unfold code_correctness; simpl.
  (*unfold hasAllFreeVarUnder; simpl.*)
  move => H Eq.
  destruct H; destruct H0; destruct H1; destruct H2.
  suff: (c = c_1) /\ (element (c0, s0) e_0 = e_1) /\ (s = s_1).
  move => [c_is_c1 [e0_is_e1 s_is_s1]].
  rewrite <- c_is_c1; rewrite <- e0_is_e1; rewrite <- s_is_s1.
  split; trivial.
  simpl.


  move => H_correct.
  destruct H_correct as [H_1 H_temp].
  destruct H_temp as [H_2 H_3].
  case c_0.
  move => n.
  case n.
  case e_0.
  discriminate.
  move => p_2.
  move => tl.
  assert (element p_2 tl = e_0).
  case p_2.
  move => c_2 e_2.
  move => unknown.
  move => option_eq.
  split.
  
  split.
  simpl.

  move n_0; discriminate.



  move => H_trans.
  unfold state_correctness.
  move => H1.
  compute in H1.
  move => H2.
  unfold state_correctness.
  decompose H1.
  simpl.
Admitted.

