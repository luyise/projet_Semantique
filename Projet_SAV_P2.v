Add LoadPath "C:\Users\Hp\Documents\Coq" as CoqDirectory.
Load Projet_SAV_P1.

(* - 1 - *)

Inductive beta_sred : lambdaTermeN -> lambdaTermeN -> Prop :=
  | evaluation : forall t u : lambdaTermeN, (beta_sred (app (lambda t) u) (t [0 <- u]))
  | context_red_l : forall t u v : lambdaTermeN, (beta_sred t u) -> (beta_sred (app t v) (app u v))
  | context_red_r : forall t u v : lambdaTermeN, (beta_sred t u) -> (beta_sred (app v t) (app v u))
  | context_red_lambda : forall t u : lambdaTermeN, (beta_sred t u) -> (beta_sred (lambda t) (lambda u)).

Notation  " t beta-> u " := (beta_sred t u) (at level 0).

(* - 2 - *)

Inductive beta_red : lambdaTermeN -> lambdaTermeN -> Prop :=
  | refl : forall t : lambdaTermeN, beta_red t t
  | sred : forall t u v : lambdaTermeN, beta_sred t u -> beta_red u v -> beta_red t v.

Notation " t beta->* u " := (beta_red t u) (at level 0).  

(* - 3 - *)

Lemma lemma17 :
  forall v t u : lambdaTermeN, (t beta->* u) -> ((app t v) beta->* (app u v)).
Proof.
  move => w.
  apply beta_red_ind.
    constructor 1.
    move => t u v Reds_0 Red_0.
    apply sred. apply context_red_l. trivial.
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
    move => t u v Reds_0 Red_0.
    apply sred. apply context_red_r. trivial.
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
    move => t u v Reds_0 Red_0.
    apply sred. apply context_red_lambda. trivial.
Qed. 
