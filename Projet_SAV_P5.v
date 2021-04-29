Add LoadPath "C:\Users\Hp\Documents\Coq\projet_Semantique" as CoqDirectory.
Add LoadPath "/Users/samuel/Documents/Documents-L3/PolyCours/S2/Sem/projet_Semantique" as CoqDirectory.
Load Projet_SAV_P3ter.

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


Lemma tau_inner_krivine_sred: forall s : stack, forall u v : lambdaTermeN, krivine_sred u v -> krivine_sred (tau_inner s u) (tau_inner s v).
Proof.
    induction s.
    simpl.
    trivial.
    simpl.
    case p.
    intro c; intro s0; intro u; intro v; intro H.
    apply IHs.
    apply Kcontext_red_l.
    trivial.
Qed.

Require Import Arith.
Theorem trans_is_krivine_reduce: forall ks1 ks2 : krivineState, transitionFunction ks1 = Some ks2 -> state_correctness ks1 -> krivine_sred (tau ks1) (tau ks2) \/ tau ks1 = tau ks2.
Proof.
  intro ks1; case ks1; clear ks1.
  intro p; case p; clear p.
  intro c; intro s; intro s0.
  intro ks2; case ks2; clear ks2.
  intro p; case p; clear p.
  intro c0; intro s1; intro s2.
  case c; clear c.
  all : simpl.
  + intro n.
    case n; clear n.
    2: intro n.
    all : case s.
    all : try discriminate.
    all : intro p; case p; clear p.
    all : intro c; intro s3; intro s4.
    all : intro Eq.
    suff : c = c0 /\ s3 = s1 /\ s0 = s2.
    2 : apply some_triple_to_eq; trivial.
    2 : suff : Access n = c0 /\ s4 = s1 /\ s0 = s2.
    3 : apply some_triple_to_eq; trivial.
    all : move => [Eq1 [Eq2 Eq3]].
    all : rewrite <- Eq1, <- Eq2, <- Eq3.
    all : clear Eq Eq1 Eq2 Eq3 c0 s1 s2.
    all : intro H.
    all : right.
    all : unfold tau_tuple.
    all : simpl.
    reflexivity.

    elim H.
    intro H0; intro H1.
    unfold code_correctness in H0.
    simpl in H0.
    unfold hasAllFreeVarUnder in H0.
    simpl in H0.

    rewrite <- tau_stack_length in H0.
    Check PeanoNat.Nat.ltb_lt.

    assert (n <? length (tau_stack s4) = true) as Eq.
    rewrite (PeanoNat.Nat.ltb_lt); trivial.
    lia.
    rewrite Eq; clear Eq.

    assert (S n <? S (length (tau_stack s4)) = true) as Eq.
    rewrite (PeanoNat.Nat.ltb_lt); trivial.
    lia.
    rewrite Eq; clear Eq.

    replace (n - 0) with n.
    2 : lia.
    
    assert (List.nth n (tau_stack s4) (var (S n)) = List.nth n (tau_stack s4) (var n)).
    apply List.nth_indep.
    lia.

    rewrite H2.
    reflexivity.

  + intro c.
    case s0; clear s0.
    discriminate.
    intro p; case p; clear p.
    intro c1; intro s0; intro s3.
    simpl.
    intro SomeEq.
    suff : c = c0 /\ (c1, s0) # s = s1 /\ s3 = s2.
    2: apply some_triple_to_eq; auto.
    move => [Eq1 [Eq2 Eq3]].
    rewrite <- Eq1; rewrite <- Eq2; rewrite <- Eq3.
    clear SomeEq Eq1 Eq2 Eq3 c0 s1 s2.

    move => [_ [H2 _]].
    left.

    apply tau_inner_krivine_sred.
    apply grab_krivine_sred.

    apply stack_correctness_is_no_free.
    trivial.

  + intro c; intro c1; intro Eq.
    suff : c1 = c0 /\ s = s1 /\ (c, s) # s0 = s2.
    2: apply some_triple_to_eq; auto.
    move => [Eq1 [Eq2 Eq3]].
    rewrite <- Eq1, <- Eq2, <- Eq3.
    clear Eq1 Eq2 Eq3 Eq c0 s1 s2.
    move => [H [H0 H1]].
    right.
    simpl.

    suff : tau_tuple (Push c; c1) s = app (tau_tuple c1 s) (tau_tuple c s).
    intro Eq; rewrite Eq.
    reflexivity.
    
    unfold tau_tuple.
    simpl.
    reflexivity.
Qed.

Lemma lambdaTerme_code_correctness : forall u : lambdaTermeN, isClosed u <-> state_correctness (comp_glob u).
    split.
    unfold comp_glob.
    simpl.
    unfold isClosed.
    unfold code_correctness.
    rewrite <- comp_is_comp_glob.
    rewrite comp_and_tau.
    simpl.
    split; auto.
    split; apply empty_is_correct.

    intro H.
    rewrite <- comp_and_tau.
    elim H.
    rewrite comp_is_comp_glob.
    pose c := comp u.
    fold c.
    unfold code_correctness.
    unfold isClosed.
    simpl.
    auto.
Qed.