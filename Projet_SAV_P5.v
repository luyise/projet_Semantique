Add LoadPath "C:\Users\Hp\Documents\Coq\projet_Semantique" as CoqDirectory.
Add LoadPath "/Users/samuel/Documents/Documents-L3/PolyCours/S2/Sem/projet_Semantique" as CoqDirectory.
Load Projet_SAV_P3bis.

Definition code_correctness: codeBloc -> stack -> Prop := 
  fun c e => C[ size e]( tau_code c).

  (*
Fixpoint stack_correctness (s: stack): Prop :=
  match s with
    | empty => True 
    | element (c_0, e_0) tl => (code_correctness c_0 e_0) /\ stack_correctness e_0 /\ stack_correctness tl
end.*)

Inductive stack_correctness : stack -> Prop :=
    | empty_is_correct : stack_correctness empty_stack
    | top_is_correct : forall c_0 : codeBloc, forall e_0 tl : stack,
        (code_correctness c_0 e_0) -> (stack_correctness e_0) -> (stack_correctness tl)
        -> stack_correctness ((c_0, e_0) # tl).

Theorem stack_correctness_is_no_free: forall e: stack,
    stack_correctness e ->  List.Forall (fun t => C[ 0 ]( t )) (tau_stack e).
Proof.
    intro e; intro H. 
    induction H.
    all: simpl.
    auto.
    
    apply List.Forall_cons.
    2: trivial.

    unfold code_correctness in H.

    rewrite <- tau_stack_length in H.

    apply lemma28.
    all: trivial.
Qed.


Definition state_correctness: krivineState -> Prop := 
  fun ks => match ks with 
    | (c, e, s) => code_correctness c e /\ stack_correctness e /\ stack_correctness s
end.

Lemma correctness_propagation:
  forall (c1 c2: codeBloc), forall (e1 e2 s1 s2: stack),
    code_correctness c1 e1 /\ stack_correctness e1 /\ stack_correctness s1 /\ Some (c1, e1, s1) = Some (c2, e2, s2) -> code_correctness c2 e2 /\ stack_correctness e2 /\ stack_correctness s2.
Proof.
  move => c1 c2 e1 e2 s1 s2 H.
  destruct H; destruct H0; destruct H1.
  suff: c1 = c2 /\ e1 = e2 /\ s1 = s2.
  move => [E1 [E2 E3]].
  rewrite <- E1; rewrite <- E2; rewrite <- E3.
  auto.
  apply some_triple_to_eq.
  trivial.
Qed.

Lemma stack_correctness_propagation:
  forall c: codeBloc, forall (e s : stack),
    stack_correctness s /\ stack_correctness e /\ code_correctness c e -> stack_correctness ((c, e) # s).
Proof.
  move => c e s H.
  destruct H; destruct H0.
  apply top_is_correct.
  all : trivial.
Qed.

Lemma code_correctness_propagation_access:
  forall n: nat, forall s: stack, forall p: codeBloc * stack,
    code_correctness (Access (S n)) (p # s) -> code_correctness (Access n) s.
Proof.
  intro n; intro s; intro p.
  unfold code_correctness; simpl.
  unfold hasAllFreeVarUnder; simpl.
  lia.
Qed.

Lemma code_correctness_propagation_grab:
  forall (c c0: codeBloc), forall (e s: stack),
    code_correctness (Grab; c) s -> code_correctness c ((c0, e) # s).
Proof.
  move => c c0 e s.
  unfold code_correctness; simpl.
  intro H.
  replace (S (size s)) with (size s + 1).
  2: lia.
  apply lemma4.
  trivial.
Qed.

Lemma code_correctness_propagation_push1:
  forall (c1 c2: codeBloc), forall (e: stack),
    code_correctness (Push c1; c2) e -> code_correctness c1 e.
Proof.
  unfold code_correctness.
  unfold hasAllFreeVarUnder.
  simpl.
  intro c1; intro c2; intro e; intro H.
  elim H.
  auto.
Qed.

Lemma code_correctness_propagation_push2:
  forall (c1 c2: codeBloc), forall (e: stack),
    code_correctness (Push c1; c2) e -> code_correctness c2 e.
Proof.
  unfold code_correctness.
  unfold hasAllFreeVarUnder.
  simpl.
  intro c1; intro c2; intro e; intro H.
  elim H.
  auto.
Qed.

Lemma correctness_preserved: forall ks: krivineState, forall nks: krivineState, state_correctness ks -> (transitionFunction ks = Some nks) -> state_correctness nks.
Proof.
  unfold krivineState.
  intro ks; intro nks.
  case ks; clear ks.
  intro p; intro s.
  case p; clear p.
  intro c; intro e.
  case nks; clear nks; intro p; intro s_1; case p; intro c0; intro e0.
  case c; clear c.
  + intro n.
    simpl.
    case e; clear e.
    case n; discriminate.
    intro p0; intro s0.
    case n; clear n; simpl.
    case p0; clear p0.
    intro c; intro s1.
    move => H1 Eq.
    destruct H1 as [H0 [H1 H2]].
    inversion H1.
    apply (correctness_propagation c c0 s1 e0 s s_1).
    auto.
    
    case p0; clear p0.
    move => c s1 n H Eq.
    destruct H; destruct H0.
    apply (correctness_propagation (Access n) c0 s0 e0 s s_1).
    split.
    pose H4 := code_correctness_propagation_access n s0 (c, s1) H.
    trivial.
    inversion H0.
    auto.

  + intro c.
    case s; clear s.
    simpl. 
    discriminate.

    move => p0 s.
    case p0; clear p0.
    move => c1 s0.
    simpl.
    move => [H [H0 H1]] Eq.
    apply (correctness_propagation c c0 ((c1, s0) # e) e0 s s_1).
    split.

    apply code_correctness_propagation_grab; trivial.
    inversion H1.
    split; auto.
    apply top_is_correct; trivial.

  + simpl.
    move => c c1 [H [H0 H1]] Eq.
    apply (correctness_propagation c1 c0 e e0 ((c, e) # s) s_1).
    split.
    apply (code_correctness_propagation_push2 c c1 e); trivial.
    repeat split.
    all : trivial.
  
    apply stack_correctness_propagation.
    repeat split.
    all : trivial.
    apply (code_correctness_propagation_push1 c c1 e H).
Qed.

(*
Lemma tau_inner_processing_access_0 : forall c0: codeBloc, forall s s2 s3 : stack,
  (tau_inner (access 0) (element (c0, s2) s3) s) = tau_inner c0 s2 s.
*)

Lemma tau_inner_beta_red: forall s : stack, forall u v : lambdaTermeN, beta_sred u v -> beta_sred (tau_inner s u) (tau_inner s v).
Proof.
    induction s.
    simpl.
    trivial.
    simpl.
    case p.
    intro c; intro s0; intro u; intro v; intro H.
    apply IHs.
    apply context_red_l.
    trivial.
Qed.


(*
Lemma app_red: forall v u t : lambdaTermeN, (beta_sred (app u v) (app t v)) ->  (beta_sred u t) \/ (beta_sred v v /\ u = t).
Proof.
    intro v.
    induction v; intro u; intro t; intro H.
Admitted.




Lemma beta_red_tau_inner: forall s : stack, forall u v : lambdaTermeN, beta_sred (tau_inner s u) (tau_inner s v) -> beta_sred u v.
Proof.
    intro s.
    induction s.
    simpl.
    trivial.

    simpl.
    case p; clear p.
    intro c; intro s0; intro u; intro v.
    pose t := tau_tuple c s0; fold t; fold t.
    induction t.
    intro H.
    pose H0 := IHs (app u (var n)) (app v (var n)) H.
    inversion H0.
    simpl.
    induction t.
    simpl in H0.
    inversion H0.
    rewrite <- H2 in H0; rewrite <- H2 in H.
    clear H2; clear u.
    rewrite <- H3 in *; clear H3; clear s0; clear c.
    rewrite <- H4 in H0.

    Focus 2.
    trivial.
    Focus 2.
    rewrite <- H3 in *; clear H3; clear c; clear s0.
    clear H5; clear u0.
    rewrite <- H4 in *; clear H4; clear v.
    rewrite <- H1 in *; clear H1; clear u.
    case H0.
    
    pose H5 := evaluation t u0.
    rewrite H4 in H5.
    rewrite evaluation in H4.
    case_eq H0.
    apply (context_red_l u v (tau_tuple c s0)) in H0.
    elim H0; trivial.
    destruct H0.
    inversion H0.
    suff: beta_red (app (lambda t) (tau_tuple c s0) ) 
    trivial.
Qed.
*)

Require Import Arith.
Theorem trans_is_beta_reduce: forall ks1 ks2 : krivineState, transitionFunction ks1 = Some ks2 -> state_correctness ks1 -> beta_sred (tau ks1) (tau ks2) \/ tau ks1 = tau ks2.
Proof.
  move => ks1 ks2.
  case ks1; clear ks1.
  case ks2; clear ks2.
  move => p s p0 s0.
  case p; clear p.
  case p0; clear p0.
  move => c s1 c0 s2.
  case c; clear c.
  move => n.
  simpl.
  case n; clear n.
  case s1; clear s1.
  discriminate.
  move => p1 s3.
  case p1; clear p1.
  move => c1 s4.

  move => Correct Eq.

  suff: c1 = c0 /\ s4 = s2 /\ s0 = s.
  2: apply some_triple_to_eq; trivial.

  move => H.
  destruct H; destruct H0.
  rewrite H; rewrite H0; rewrite H1.


    induction s.
    simpl.


    case s3.
    auto.
    move => p2 s.
    unfold tau_tuple.
    simpl.
    auto.
    auto.

  move => n0; case s1; clear s1.
  discriminate.
  move => p1 s3; case p1; clear p1.
  move => c1 s4.
  unfold code_correctness.
  simpl.
  unfold hasAllFreeVarUnder.
  simpl.
  move => Eq [Correct1 [Correct2 Correct3]].
  suff: Access n0 = c0 /\ s3 = s2 /\ s0 = s.
  2: apply some_triple_to_eq; trivial.
  move => H.
  destruct H; destruct H0.
  rewrite <- H; rewrite <- H0; rewrite <- H1.
  induction s0.
  simpl.
  unfold tau_tuple.
  unfold tau_code.
  rewrite (lemma11 (S n0) 0 (tau_stack ((c1, s4) # s3))).
  lia.
  rewrite tau_stack_length.
  simpl.
  lia.
  rewrite (lemma11 (n0) 0 (tau_stack s3)).
  lia.
  rewrite tau_stack_length.
  lia.
  replace (n0 - 0) with n0; try lia.
  replace (S n0 - 0) with (S n0); try lia.

  simpl.
  right.
  apply List.nth_indep.
  rewrite tau_stack_length.
  lia.

  simpl in Correct3.
  case p in Correct3.
  inversion Correct3.

  simpl.
  case p.
  move => c3 s6.

  unfold tau_tuple.
  simpl.
  suff : n0 < length (tau_stack s3).
  move => Ineg.
  assert (n0 <? length (tau_stack s3) = true) as Eq2.
  rewrite (PeanoNat.Nat.ltb_lt); trivial.
  rewrite Eq2.
  suff : S n0 < S (length (tau_stack s3)).
  move => Ineg2.
  assert (S n0 <? S (length (tau_stack s3)) = true) as Eq3.
  rewrite (PeanoNat.Nat.ltb_lt); trivial.
  rewrite Eq3.
  replace (n0 - 0) with n0.
  right.
  pose Eq4 := List.nth_indep (tau_stack s3) (var (S n0)) (var n0).
  suff : n0 < length (tau_stack s3).
  move => H9.
  pose Eq5 := Eq4 n0 H9.
  rewrite Eq5.
  trivial.
  trivial.
  lia.
  lia.
  rewrite tau_stack_length.
  lia.

  move => c.
  simpl.
  case s0; clear s0.
  discriminate.
  move => p s0.
  case p; clear p.
  move => c1 s3.
  simpl.
  move => SomeEq H.
  destruct H; destruct H0.

  suff : c = c0 /\ (c1, s3) # s1 = s2 /\ s0  = s.
  2: apply some_triple_to_eq; auto.
  move => [Eq1 [Eq2 Eq3]].
  rewrite <- Eq1; rewrite <- Eq2; rewrite <- Eq3.
  clear SomeEq Eq1 Eq2 Eq3.
  clear c0; clear s; clear s2.

  unfold code_correctness in H.
  simpl in H.

  left.

  apply tau_inner_beta_red.
  apply grab_beta_red.

  apply stack_correctness_is_no_free.
  trivial.

  move => c c1 Eq.
  suff : c1 = c0 /\ s1 = s2 /\ (c, s1) # s0 = s.
  2: apply some_triple_to_eq; auto.
  move => [Eq1 [Eq2 Eq3]] [H [H0 H1]].
  rewrite <- Eq1 in *; clear Eq1; clear c0.
  rewrite <- Eq2 in *; clear Eq2; clear s2.
  rewrite <- Eq3 in *; clear Eq3; clear s.
  simpl.
  right.
  suff : tau_tuple (push c c1) s1 = app (tau_tuple c1 s1) (tau_tuple c s1).
  auto.
  unfold tau_tuple.
  simpl.
  trivial.
Qed.

Lemma lambdaTerme_code_correctness : forall u : lambdaTermeN, isClosed u <-> state_correctness (comp_glob u).
    split.
    unfold comp_glob.
    simpl.
    unfold code_correctness.
    simpl.
    unfold isClosed.
    rewrite <- comp_is_comp_glob.
    rewrite comp_and_tau.
    intro H.
    split; auto.
    split; apply empty_is_correct.

    unfold state_correctness.
    case_eq (comp_glob u).
    intro p; intro s; case p.
    intro c; intro s0.
    unfold comp_glob.
    intro H.
    suff: (comp u = c) /\ empty_stack = s0 /\ empty_stack = s.
    move => [Eq1 [Eq2 Eq3]]. clear H.
    rewrite <- Eq2; clear Eq2; clear s0.
    rewrite <- Eq3; clear Eq3; clear s.
    rewrite <- Eq1 in *; clear Eq1; clear c.
    move => [H0 [H1 H2]].
    unfold code_correctness in H0.
    simpl in H0.
    unfold isClosed.
    rewrite <- (comp_is_comp_glob u) in H0.
    rewrite (comp_and_tau u) in H0.
    trivial.
    apply triple_eq_is_eq.
    trivial.
Qed.