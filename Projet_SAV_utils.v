
Lemma option_equality_lemma: forall A : Type, forall (a1 a2: A), Some a1 = Some a2 <-> a1 = a2.
Proof.
  move => A a1 a2.
  split.
  case.
  trivial.
  move => H.
  rewrite H.
  trivial.
Qed.

Lemma tuple_eq_is_eq: forall (A B : Type) (a1 a2 : A) (b1 b2 : B),
      (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
Proof.
  intros.
  split; intro H . split.
  1 : replace a1 with (fst (a1, b1)); replace a2 with (fst (a2, b2)); trivial.
  2 : replace b1 with (snd (a1, b1)); replace b2 with (snd (a2, b2)); trivial.
  1-2: rewrite H.
  1-2: trivial.
  destruct H.
  rewrite H H0.
  trivial.
Qed.

Lemma triple_eq_is_eq: forall (A B C: Type) (a1 a2 : A) (b1 b2 : B) (c1 c2 : C),
  (a1, b1, c1) = (a2, b2, c2) <-> a1 = a2 /\ b1 = b2 /\ c1 = c2.
  intros.
  split.
  intro H.
  repeat split.
  1 : replace a1 with (fst (fst ((a1, b1), c1))); replace a2 with (fst (fst ((a2, b2), c2))); trivial.
  2 : replace b1 with (snd (fst ((a1, b1), c1))); replace b2 with (snd (fst ((a2, b2), c2))); trivial.
  3 : replace c1 with (snd ((a1, b1), c1)); replace c2 with (snd ((a2, b2), c2)); trivial.
  1-3: rewrite H; trivial.
  intro H. destruct H; destruct H0.
  rewrite H H0 H1.
  trivial.
Qed.

Lemma some_triple_to_eq: forall (A B C: Type) (a1 a2: A) (b1 b2: B) (c1 c2: C),
  Some (a1, b1, c1) = Some (a2, b2, c2) <-> a1 = a2 /\ b1 = b2 /\ c1 = c2.
Proof.
  intros.
  split.
  all: intro H.
  + apply triple_eq_is_eq.
    apply option_equality_lemma.
    trivial.

  + apply option_equality_lemma.
    apply triple_eq_is_eq.
    trivial.
Qed.
