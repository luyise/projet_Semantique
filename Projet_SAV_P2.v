Add LoadPath "C:\Users\Hp\Documents\Coq\projet_Semantique" as CoqDirectory.
Add LoadPath "/Users/samuel/Documents/Documents-L3/PolyCours/S2/Sem/projet_Semantique" as CoqDirectory.
Load Projet_SAV_P1.

(* - 1 - *)

Reserved Notation  " t beta-> u " (at level 0).

Inductive beta_sred : lambdaTermeN -> lambdaTermeN -> Prop :=
  | evaluation : forall t u : lambdaTermeN, ((app (lambda t) u) beta-> (t [0 <- u]))
  | context_red_l : forall t u v : lambdaTermeN, (t beta-> u) -> ((app t v) beta-> (app u v))
  | context_red_r : forall t u v : lambdaTermeN, (t beta-> u) -> ((app v t) beta-> (app v u))
  | context_red_lambda : forall t u : lambdaTermeN, (t beta-> u) -> ((lambda t) beta-> (lambda u))
where " t beta-> u " := (beta_sred t u).

(* - 2 - *)

Reserved Notation " t beta->* u " (at level 0). 

Inductive beta_red : lambdaTermeN -> lambdaTermeN -> Prop :=
  | Brefl : forall t : lambdaTermeN, ( t beta->* t )
  | Bsingle : forall t u : lambdaTermeN, ( t beta-> u ) -> ( t beta->* u )
  | Bconcat : forall t u v : lambdaTermeN, ( t beta->* u ) -> ( u beta->* v ) -> ( t beta->* v )
where " t beta->* u " := (beta_red t u).  

(* - 3 - *)

Lemma lemma17 :
  forall v t u : lambdaTermeN, (t beta->* u) -> ((app t v) beta->* (app u v)).
Proof.
  move => w.
  apply beta_red_ind.
    constructor 1.
    move => t u Reds_0.
    apply Bsingle. apply context_red_l. trivial.
    move => t u v BRed_0 BRed_1 BRed_2 Bred_3.
    apply (Bconcat (app t w) (app u w) (app v w)); trivial.
Qed.

Proposition beta_red_context_red_l :
  forall t u v : lambdaTermeN, (t beta->* u) -> ((app t v) beta->* (app u v)).
Proof.
  move => t u v.
  exact (lemma17 v t u).
Qed.

Lemma lemma18 :
  forall v t u : lambdaTermeN, (t beta->* u) -> ((app v t) beta->* (app v u)).
Proof.
  move => w.
  apply beta_red_ind.
    constructor 1.
    move => t u Red_0.
    apply Bsingle. apply context_red_r. trivial.
    move => t u v _ BRed_0 _ BRed_1.
    apply (Bconcat (app w t) (app w u) (app w v)); trivial.
Qed. 

Proposition beta_red_context_red_r :
  forall t u v : lambdaTermeN, (t beta->* u) -> ((app v t) beta->* (app v u)).
Proof.
  move => t u v.
  exact (lemma18 v t u).
Qed.

Proposition beta_red_context_red_lambda :
  forall t u : lambdaTermeN, (t beta->* u) -> ((lambda t) beta->* (lambda u)).
Proof.
  apply beta_red_ind.
    constructor 1.
    move => t u Red_0.
    apply Bsingle. apply context_red_lambda. trivial.
    move => t u v _ Red_0 _ Red_1.
    apply (Bconcat (lambda t) (lambda u) (lambda v)); trivial.
Qed.

(** On définit ici une relation plus fine que la beta_reduction,
  qui correspond au pendant du fonctionnement de la machine de krivine sur des lambdas termes
  ceci servira à prouver un théorème de correction de la compilation en partie 5 *)

Reserved Notation " A s-> B " (at level 0).

Inductive krivine_sred : lambdaTermeN -> lambdaTermeN -> Prop :=
  | Kevaluation : forall t u : lambdaTermeN, ((app (lambda t) u) s-> (t [0 <- u]))
  | Kcontext_red_l : forall t u v : lambdaTermeN, (t s-> u) -> ((app t v) s-> (app u v))
where " t_0 s-> t_1 " := (krivine_sred t_0 t_1).

Reserved Notation " A s->* B " (at level 0).

Inductive krivine_red : lambdaTermeN -> lambdaTermeN -> Prop :=
  | Krefl : forall t : lambdaTermeN, (t s->* t)
  | Ksingle : forall t u : lambdaTermeN, (t s-> u) -> (t s->* u)
  | Kconcat : forall t u v : lambdaTermeN, (t s->* u) -> (u s->* v) -> (t s->* v)
where " t_0 s->* t_1 " := (krivine_red t_0 t_1).

Lemma only_app_may_be_kv_reduced :
  forall t u : lambdaTermeN, (t s-> u) -> exists v w : lambdaTermeN, t = app v w.
Proof.
  move => t u KvRed. inversion KvRed as [t_0 t_1 Eqt Equ | t_0 t_1 t_2 KvRed' Eqt Equ].
  exists (lambda t_0), t_1. trivial.
  exists t_0, t_2. trivial.
Qed.

Lemma kv_red_is_functionnal :
  forall t_0 t_1 t_2 : lambdaTermeN, (t_0 s-> t_1) /\ (t_0 s-> t_2) -> t_1 = t_2.
Proof.
  move => t_0.
  induction t_0.
  all : move => t_1 t_2. all : move => H. all : destruct H as [KvRed_1 KvRed_2].
    + inversion KvRed_1.
    + pose Ht_0 := (only_app_may_be_kv_reduced (lambda t_0) t_1 KvRed_1).
      destruct Ht_0. destruct H as [y Eq]. congruence.
    + case_eq t_0_1.
        - move => x. move => Eq. rewrite Eq in KvRed_1. inversion KvRed_1. inversion H2.
        - move => u. move => Eq. rewrite Eq in KvRed_1 KvRed_2. inversion KvRed_1. all : inversion KvRed_2.
          all : trivial. apply False_ind. pose Abs := (only_app_may_be_kv_reduced (lambda u) u1 H5).
          destruct Abs. destruct H6. congruence. 
          pose Abs := (only_app_may_be_kv_reduced (lambda u) u0 H2). destruct Abs. destruct H6. congruence.
          pose Abs := (only_app_may_be_kv_reduced (lambda u) u0 H2). destruct Abs. destruct H7. congruence.
        - move => u_1 u_2. move => Eq. inversion KvRed_1. congruence.
          inversion KvRed_2. congruence. suff : (u = u0). move => Equ. rewrite Equ. reflexivity.
          apply IHt_0_1. split; auto.
Qed. 

Lemma kv_sred_included_in_beta_sred :
  forall t_0 t_1 : lambdaTermeN, (t_0 s-> t_1) -> (t_0 beta-> t_1).
Proof.
  move => t_0 t_1 KvRed.
  induction KvRed.
  apply evaluation.
  apply context_red_l. trivial.
Qed.

Lemma kv_red_included_in_beta_red :
  forall t_0 t_1 : lambdaTermeN, (t_0 s->* t_1) -> (t_0 beta->* t_1).
Proof.
  move => t_0 t_1 KvRed.
  induction KvRed.
    + constructor 1.
    + constructor 2. apply kv_sred_included_in_beta_sred. trivial.
    + apply (Bconcat t u v); trivial.
Qed.