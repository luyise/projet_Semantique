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
  "dans le sous-terme t, apparaissant sous d lambdas dans un terme, toutes les variables libres sont d'indice < n" *)
Fixpoint prop_aux_with_linkDepth (n : nat) (d : nat) (t : lambdaTermeN) : Prop :=
  match t return Prop with
    | var x => (x < n+d)
    | lambda t_0 => (prop_aux_with_linkDepth n (d+1) t_0)
    | app t_0 t_1 => (prop_aux_with_linkDepth n d t_0) /\ (prop_aux_with_linkDepth n d t_1)
  end.

(* hasAllFreeVarUnder n t renvoie la proposition correspondant à 
  "dans le terme t, toutes les variables libres sont d'indice < n" *)
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

(* - 3 - *)

(*
Ici, on définit une convention sur l'interprétation des termes.
A priori, pour le terme app (var 1) (lambda (var 1)) ou app (var 1) (lambda (var 2)) rien ne permet d'identifier les variables 1 et/ou 2.
Cependant, lorsque l'on éffectue une beta-réduction sur app (lambda (app (var 1) (lambda (var 1)))) (var 2),
on n'identifie pas les deux occurrences de 1 à une même variable (celle à substituer par 2)
et dans app (lambda (lambda (app (var 1) (lambda (var 2))))) (var 2) lors d'une beta-reduction, on veut identifier les occurences de 1 et de 2 à la même variable que l'on substitue.
Donc on choisit la convention que chaque lambda incrémente de 1 les valeurs représentant les variables libres auquelles elles font référence.
Par exemple lambda (app (lambda (var 2)) (var 1)) s'interprète comme le lambda-Terme lambdaX.((lambdaY. Z) Z) 
*)

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
subst t y u renvoie le terme t dans lequel on a substitué la variable y (au sens discuté précédemment) par le terme u *)
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

(* On va montrer le résultat attendu, pour cela, on a besoin de quelques lemmes techniques *)

Lemma lemma2 : forall n m : nat, n < m -> Nat.eqb n m = false.
Proof.
  move => n m.
  move => Ltnm.
  destruct (PeanoNat.Nat.eqb_neq n m).
  apply H0.
  lia.
Qed.

Lemma lemma3 :
  forall t : lambdaTermeN, forall n d : nat,
    (prop_aux_with_linkDepth n (d+1) t) -> prop_aux_with_linkDepth (n+1) d t.
Proof.
  induction t. rename n into x.
  simpl.
  move => n d.
  lia.
  move => n d.
  simpl.
  apply IHt.
  simpl.
  split; destruct H as [H_1 H_2]. apply IHt1. trivial.
  apply IHt2; trivial.
Qed.

(* Un des lemmes les plus important conceptuellement : *)

Lemma lemma4 : forall t : lambdaTermeN, forall n : nat, C[n]( lambda t ) -> C[n+1]( t ).
Proof.
  unfold hasAllFreeVarUnder.
  induction t. rename n into x.
  move => n.
  simpl. lia.
  move => n.
  simpl. exact (lemma3 t n 1).
  move => n.
  simpl; split;
  destruct H as [H_1 H_2];
  apply lemma3; simpl; trivial.
Qed.

Lemma lemma5 : 
  forall t : lambdaTermeN, forall n : nat, C[ n ]( t ) -> forall u : lambdaTermeN, t [ n <- u ] = t.
Proof.
  induction t. rename n into x.
  move => n.
  unfold hasAllFreeVarUnder.
  simpl.
  move => Ltxn.
  assert (x < n).
  lia. clear Ltxn. rename H into Ltxn.
  move => u.
  rewrite (lemma2 x n Ltxn); reflexivity.
  move => n Cnlambdat u.
  simpl. assert ((t) [n + 1 <- incr_free u] = t).
  pose CSnt := lemma4 t n Cnlambdat.
  apply IHt. exact CSnt.
  rewrite H; reflexivity.
  move => n.
  unfold hasAllFreeVarUnder.
  simpl.
  case; move => Ht1 Ht2.
  assert (hasAllFreeVarUnder n t1); unfold hasAllFreeVarUnder. assumption.
  assert (hasAllFreeVarUnder n t2); unfold hasAllFreeVarUnder. assumption.
  move => u. 
  assert ((t1) [ n <- u ] = t1) as Eqt1.
  apply IHt1. assumption.
  assert ((t2) [ n <- u ] = t2) as Eqt2.
  apply IHt2. assumption.
  rewrite Eqt1 Eqt2; reflexivity.
Qed.

Lemma lemma6 :
  forall t : lambdaTermeN, isClosed t -> forall n : nat, C[n](t).
Proof.
  move => t.
  induction n.
  unfold isClosed in H; assumption.
  replace (S n) with (n + 1).
  apply lemma1; assumption.
  lia.
Qed.

Theorem theorem0 : 
  forall t : lambdaTermeN, isClosed t -> (forall y : nat, forall u : lambdaTermeN, t [ y <- u ] = t).
Proof.
  move => t.
  unfold isClosed.
  move => Ht.
  move => y.
  assert C[y](t) as Cyt.
  apply lemma6.
  unfold isClosed; assumption.
  apply lemma5; assumption.
Qed.

Print List.map.
Print List.nth.

(* On définit la fonction de substitution en parallèle :
subst t i [u_0, u_1, ..., u_n] renvoie le terme t dans lequel on a substitué les variable i, i+1, ..., i+n par les termes respectifs u_0, u_1, ..., u_n *)
Fixpoint subst_list (t : lambdaTermeN) (i : nat) (l : list lambdaTermeN) : lambdaTermeN :=
  match t return lambdaTermeN with
    | var x =>
      if ((Nat.leb i x) && (Nat.leb x (i+(length l)))) then (List.nth (x-i) l t) else t
    | lambda t_0 =>
      lambda (subst_list t_0 (i+1) (List.map incr_free l))
    | app t_0 t_1 =>
      app (subst_list t_0 i l) (subst_list t_1 i l)
  end.

Print list.
Locate " :: ".

Eval compute in ( subst_list (lambda (lambda (app (var 1) (var 4)))) 1 ((var 2) :: (id) :: nil)).
