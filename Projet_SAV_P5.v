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
        -> stack_correctness ($ (c_0, e_0) # tl).

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
    stack_correctness s /\ stack_correctness e /\ code_correctness c e -> stack_correctness ($ (c, e) # s).
Proof.
  move => c e s H.
  destruct H; destruct H0.
  apply top_is_correct.
  all : trivial.
Qed.

Lemma code_correctness_propagation_access:
  forall n: nat, forall c : codeBloc, forall  e s: stack,
    code_correctness (Access (S n)) ($ (c, e) # s) -> code_correctness (Access n) s.
Proof.
  intro n; intro c; intro e; intro s.
  unfold code_correctness; simpl.
  unfold hasAllFreeVarUnder; simpl.
  lia.
Qed.

Lemma code_correctness_propagation_grab:
  forall c c2: codeBloc, forall e2 s: stack,
    code_correctness (Grab; c) s -> code_correctness c ($ (c2, e2) # s).
Proof.
  move => c c2 e2 s.
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

Lemma correctness_preserved:
  forall ks_0 ks_1: krivineState,
    (ks_0 km-> ks_1) -> state_correctness ks_0 -> state_correctness ks_1.
Proof.
  intro ks; case ks; clear ks.
  intro p; case p; clear p.
  intro c0; intro e0; intro s0.

  intro ks; case ks; clear ks.
  intro p; case p; clear p.
  intro c1; intro e1; intro s1.
  intro H.
  inversion H.
  + simpl.
    intro H7.
    destruct H7; destruct H7. 
    inversion H7.
    auto.

  + simpl.

    unfold code_correctness.
    simpl.
    unfold hasAllFreeVarUnder.
    simpl.

    intro H7.
    destruct H7; destruct H7.
    inversion H7.
    split; auto.
    lia.
    
  + intro H7.

    destruct H7; destruct H7.

    unfold state_correctness.
    split.
    apply (code_correctness_propagation_push2 c_0 c1 e1).
    trivial.
    
    split; trivial.

    apply top_is_correct.
    
    all : trivial.

    apply (code_correctness_propagation_push1 c_0 c1 e1).
    trivial.

  + unfold state_correctness.

    (*case p; intro c2; intro e2.*)

    intro H7.
    destruct H7; destruct H7.
    inversion H8.

    repeat split.

    apply code_correctness_propagation_grab.
    trivial.

    apply top_is_correct.
    all : trivial.
Qed.


Lemma tau_inner_krivine_sred:
  forall s : stack, forall u v : lambdaTermeN,
    u s-> v -> (tau_inner s u) s-> (tau_inner s v).
Proof.
    induction s.
    simpl.
    trivial.
    simpl.
    intro u; intro v; intro H.
    apply IHs2.
    apply Kcontext_red_l.
    trivial.
Qed.

Theorem trans_is_krivine_reduce:
  forall ks1 ks2 : krivineState,
    ks1 km-> ks2 -> state_correctness ks1 -> ((tau ks1) s-> (tau ks2)) \/ tau ks1 = tau ks2.
Proof.
  intro ks1; case ks1; clear ks1.
  intro p; case p; clear p.
  intro c; intro s; intro s0.
  intro ks2; case ks2; clear ks2.
  intro p; case p; clear p.
  intro c0; intro s1; intro s2.
  intro H.
  inversion H.
  + 

    intro SC.
    right.
    simpl.
    unfold tau_tuple.
    simpl.
    reflexivity.

  + clear H H1 H2 H3 H4 H5 H6 s_0 s_1 s0 c s c0.

    intro SC.
    inversion SC.
    destruct H0.
    right.

    unfold tau.
    unfold tau_tuple.
    simpl.

    unfold code_correctness in H.
    unfold hasAllFreeVarUnder in H.
    simpl in H.

    rewrite <- tau_stack_length in H.


    suff : (Nat.ltb n (length (tau_stack s1)) = true).
    intro Eq; rewrite Eq; clear Eq.

    suff : (Nat.ltb (S n) (S (length (tau_stack s1))) = true).
    intro Eq; rewrite Eq; clear Eq.
    
    replace (n - 0) with n.

    3-4: rewrite (PeanoNat.Nat.ltb_lt); trivial.
    2-4: lia.
    
    assert (List.nth n (tau_stack s1) (var (S n)) = List.nth n (tau_stack s1) (var n)).
    apply List.nth_indep.
    lia.

    rewrite H2.
    reflexivity.

  + 
    intro H7.
    inversion H7.

    right.
    unfold tau.
    simpl.
    suff : tau_tuple (Push c_0; c0) s1 = app (tau_tuple c0 s1) (tau_tuple c_0 s1).
    intro Eq; rewrite Eq; trivial.


    unfold tau_tuple.
    simpl.
    reflexivity.

  + intro H7.
    inversion H7.
    left.

    unfold tau.
    simpl.

    apply tau_inner_krivine_sred.
    apply grab_krivine_sred.

    apply stack_correctness_is_no_free.
    elim H8.
    trivial.
Qed.

Lemma lambdaTerme_code_correctness : forall u : lambdaTermeN, isClosed u <-> state_correctness (comp_glob u).
Proof.
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