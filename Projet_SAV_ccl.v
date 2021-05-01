Add LoadPath "C:\Users\Hp\Documents\Coq\projet_Semantique" as CoqDirectory.
Add LoadPath "/Users/samuel/Documents/Documents-L3/PolyCours/S2/Sem/projet_Semantique" as CoqDirectory.
Load Projet_SAV_P5.

Theorem krivine_trans_is_stategy :
    forall ks_0 ks_1 : krivineState,
        state_correctness ks_0 -> (ks_0 km->* ks_1) -> (tau ks_0) s->* (tau ks_1) /\ state_correctness ks_1.
Proof.
    move => ks_0 ks_1 StateC H.
    induction H.
    + split.
        apply Krefl.
        trivial.
    + split.
        pose Formula := trans_is_krivine_reduce ks_0 ks_1 H StateC.
        case Formula.
        intro H0.
        exact (Ksingle (tau ks_0) (tau ks_1) H0).

        intro H0; rewrite H0; apply Krefl.

        exact (correctness_preserved ks_0 ks_1 H StateC).

    + split.

        apply (Kconcat (tau ks_0) (tau ks_1) (tau ks_2)).
        all : pose H1 := IHtransitionRelationExt1 StateC.
        all : elim H1; intro H2; intro StateC2.
        trivial.
        all : pose H3 := IHtransitionRelationExt2 StateC2.
        all : elim H3.
        all : trivial.
Qed.

Theorem compilation_correctness_stategy :
    forall t : lambdaTermeN, forall ks : krivineState,
        isClosed t -> ((comp_glob t) km->* ks) -> (t s->* (tau ks)).
Proof.
    move => t ks_1 iC H.
    pose ks_0 := comp_glob t.
    rewrite <- (comp_and_tau t).
    apply krivine_trans_is_stategy.
    2: trivial.

    apply lambdaTerme_code_correctness.
    trivial.
Qed.

Theorem compilation_correctness :
    forall t : lambdaTermeN, forall ks : krivineState,
        isClosed t -> ((comp_glob t) km->* ks) -> (t beta->* (tau ks)).
Proof.
    intro t; intro ks; intro H; intro H0.
    apply kv_red_included_in_beta_red.
    apply compilation_correctness_stategy.
    all : trivial.
Qed.

Fixpoint concat (s : stack) (p : codeBloc * stack) : stack :=
    match s with
        |empty_stack => p # empty_stack
        | p_2 # s_2 => p_2 # concat s_2 p
end.

Lemma tau_inner_concat :
    forall s0 s1 : stack, forall c1 : codeBloc, forall u : lambdaTermeN,
        tau_inner (concat s0 (c1, s1)) u = app (tau_inner s0 u) (tau_tuple c1 s1).
Proof.
    intro s; induction s.
    simpl.
    trivial.

    case p; clear p.
    simpl.
    intro c; intro s0; intro s1; intro c1; intro u.
    rewrite IHs.
    reflexivity.
Qed.

Lemma not_interacting_with_stack : 
    forall ks_0 ks_1 : krivineState,
    ks_0 km->* ks_1 -> 
    let (p0, s0) := ks_0 in let (p1, s1) := ks_1 in
    let (c0, e0) := p0   in let (c1, e1) := p1   in 
    forall p : codeBloc * stack, (c0, e0, concat s0 p) km->* (c1, e1, concat s1 p).
Proof.
    apply transitionRelationExt_ind.
    all : intro ks_0; case ks_0; clear ks_0.
    all : intro p; case p; clear p.
    all : intro c0; intro e0; intro s0.
    intro p; apply refl_km.
    all : intro ks_1; case ks_1; clear ks_1.
    all : intro p; case p; clear p.
    all : intro c1; intro e1; intro s1.
    intro H.
    inversion H.
    1-4 : intro p0.
    1-4 : apply single_km.
    apply TAccess_O.
    apply TAccess_S.
    apply TPush.
    apply TGrab.

    intro ks_2; case ks_2; clear ks_2.
    intro p; case p; clear p.
    intro c2; intro e2; intro s2.
    intro T1; intro P1; intro T2; intro P2; intro p.
    pose P1' := P1 p.
    pose P2' := P2 p.
    apply (concat_km (c0, e0, concat s0 p) (c1, e1, concat s1 p) (c2, e2, concat s2 p)).
    all : trivial.
Qed.


Theorem otherside:
    forall t_0 t_1: lambdaTermeN,
        (t_0 s-> t_1) -> exists ks : krivineState, (comp_glob t_0) km->* ks /\ t_1 = tau ks.
Proof.
    apply krivine_sred_ind.
    move => t u.
    (*induction H.*)
    unfold comp_glob.
    simpl.
    pose ks_1 := (comp t, (comp u, empty_stack) # empty_stack, empty_stack) : krivineState.
    exists ks_1.
    unfold ks_1.
    simpl.
    unfold tau_tuple.
    unfold tau_stack.
    rewrite prop0.
    assert (tau_code (comp u) = u).
    2 : assert (tau_code (comp t) = t).
    1-2 : rewrite <- comp_is_comp_glob.
    1-2 : rewrite <- comp_and_tau.
    1-2 : trivial.
    rewrite H.
    rewrite H0.
    split.
    2 : rewrite lemma8.
    2 : trivial.

    apply (concat_km
        (Push comp u; (Grab ; comp t), empty_stack, empty_stack)
        (Grab; comp t, empty_stack, (comp u, empty_stack) # empty_stack)
        (comp t, (comp u, empty_stack) # empty_stack, empty_stack)).
    1-2 : apply single_km.
    apply TPush.
    apply TGrab.

    unfold comp_glob.
    simpl.
    move => t u v H IHkrivine_sred.
    inversion IHkrivine_sred.
    case_eq x.
    intro p; case p; clear p.
    intro c; intro s; intro s0.
    intro Eq.
    rewrite Eq in H0.
    clear Eq x.
    pose ks_1 := (c, s, concat s0 (comp v, empty_stack)).
    exists ks_1.
    unfold ks_1.
    simpl.
    destruct H0.
    rewrite H1.
    unfold tau.
    
    split.
    2 : rewrite tau_inner_concat.
    2 : unfold tau_tuple.
    2 : simpl.
    2 : rewrite prop0.
    2 : rewrite <- comp_is_comp_glob.
    2 : rewrite comp_and_tau.
    2 : reflexivity.

    apply (concat_km
        (Push comp v; comp t, empty_stack, empty_stack)
        (comp t, empty_stack, (comp v, empty_stack) # empty_stack)
        (c, s, concat s0 (comp v, empty_stack))).
    apply single_km.
    apply TPush.

    pose c0 := comp t.
    fold c0; fold c0 in IHkrivine_sred.
    fold c0 in H0. 

    apply (not_interacting_with_stack (c0, empty_stack, empty_stack) (c, s, s0)).
    trivial.
Qed.

Lemma propagation_1: forall ks_0 ks_1 : krivineState
    (ks_0 km-> ks_1) -> tau ks_0 = tau ks_1 \/ tau ks_0 s-> ks_1. 

Lemma propagation_2: forall ks_0 ks_1: krivineState,
    (ks_0 km->* ks_1) -> 
        let (p0, s0) := ks_0 in let (c0, e0) := p0 in
        forall ks_2 : krivineState, comp_glob (tau ks_0) = ks_2 ->
    exists ks_3, (ks_2 km->* ks_3) /\ tau ks_3 = tau ks_1.
Proof.
    apply transitionRelationExt_ind.
    all : intro ks_0; case ks_0; clear ks_0.
    all : intro p; case p; clear p.
    all : intro c0; intro e0; intro s0.
    all : intro ks_1; case ks_1; clear ks_1.
    all : intro p; case p; clear p.
    all : intro c1; intro e1; intro s1.
    intro H.
    rewrite <- H.
    exists (c1, e1, s1).
    split.
    apply refl_km.
    rewrite comp_and_tau.
    reflexivity.

    intro H.
    all : intro ks_2; case ks_2; clear ks_2.
    all : intro p; case p; clear p.
    all : intro c2; intro e2; intro s2.

    unfold comp_glob.
    intro Eq.
    inversion Eq.
    rewrite <- H1, <- H2, <- H3 in H.
    clear Eq H1 H2 H3 c0 e0 s0.
    inversion H.
    rewrite <- H5, <- H4, <- H6 in H.
    rewrite <- H4.
    clear H5 e1 H4 c1 H6 s1.
    clear H2 H3 e s.

    exists (c2, e2, s2).
    split.
    apply refl_km.
    rewrite <- (comp_and_tau (tau (c2, e2, s2))).
    simpl.
    rewrite <- H1.
    unfold tau_tuple.
    simpl.
    reflexivity.

    unfold comp_glob.
    simpl.

    intro TH1; intro IH1.
    intro TH2; intro IH2.

    intro ks_3; case ks_3; clear ks_3.
    intro p; case p; clear p.
    intro c3; intro e3; intro s3.

    intro H; inversion H.
    rewrite <- H1, <- H2, <- H3 in TH1.
    rewrite <- H1, <- H2, <- H3 in IH1.
    clear H H1 H2 H3 c0 e0 s0.
    pose H0 := IH2 (comp_glob (tau (c1, e1, s1))).
    assert ((comp (tau (c1, e1, s1)), empty_stack, empty_stack) =
    (c1, e1, s1)) as H.

Qed.
