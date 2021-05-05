Add LoadPath "C:\Users\Hp\Documents\Coq\projet_Semantique" as CoqDirectory.
Add LoadPath "/Users/samuel/Documents/Documents-L3/PolyCours/S2/Sem/projet_Semantique" as CoqDirectory.
Load Projet_SAV_P5.
Load Projet_SAV_DecidableEquality.

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

Fixpoint concat (s : stack) (c : codeBloc) (e : stack) : stack :=
    match s with
        | empty_stack => $ (c, e) # empty_stack
        | $ (c2, e2) # s_2 => $ (c2, e2) # concat s_2 c e
end.

Lemma tau_inner_concat :
    forall s0 s1 : stack, forall c1 : codeBloc, forall u : lambdaTermeN,
        tau_inner (concat s0 c1 s1) u = app (tau_inner s0 u) (tau_tuple c1 s1).
Proof.
    intro s; induction s.
    simpl.
    trivial.

    simpl.
    intro s0; intro c1; intro u.
    rewrite IHs2.
    reflexivity.
Qed.

Lemma not_interacting_with_stack : 
    forall ks_0 ks_1 : krivineState,
    ks_0 km->* ks_1 -> 
    let (p0, s0) := ks_0 in let (p1, s1) := ks_1 in
    let (c0, e0) := p0   in let (c1, e1) := p1   in 
    forall c : codeBloc, forall e: stack, (c0, e0, concat s0 c e) km->* (c1, e1, concat s1 c e).
Proof.
    apply transitionRelationExt_ind.
    all : intro ks_0; case ks_0; clear ks_0.
    all : intro p; case p; clear p.
    all : intro c0; intro e0; intro s0.
    intro c; intro e; apply refl_km.
    all : intro ks_1; case ks_1; clear ks_1.
    all : intro p; case p; clear p.
    all : intro c1; intro e1; intro s1.
    intro H.
    inversion H.
    1-4 : intro c3; intro e3.
    1-4 : apply single_km.
    apply TAccess_O.
    apply TAccess_S.
    apply TPush.
    apply TGrab.

    intro ks_2; case ks_2; clear ks_2.
    intro p; case p; clear p.
    intro c2; intro e2; intro s2.
    intro T1; intro P1; intro T2; intro P2.
    pose P1' := P1 c2 e2.
    intro c3; intro e3.
    pose P2' := P2 c2 e2.
    apply (concat_km (c0, e0, concat s0 c3 e3) (c1, e1, concat s1 c3 e3) (c2, e2, concat s2 c3 e3)).
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
    pose ks_1 := (comp t, $ (comp u, empty_stack) # empty_stack, empty_stack) : krivineState.
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
        (Grab; comp t, empty_stack, $ (comp u, empty_stack) # empty_stack)
        (comp t, $ (comp u, empty_stack) # empty_stack, empty_stack)).
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
    pose ks_1 := (c, s, concat s0 (comp v) empty_stack).
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
        (comp t, empty_stack, $ (comp v, empty_stack) # empty_stack)
        (c, s, concat s0 (comp v) empty_stack)).
    apply single_km.
    apply TPush.

    pose c0 := comp t.
    fold c0; fold c0 in IHkrivine_sred.
    fold c0 in H0. 

    apply (not_interacting_with_stack (c0, empty_stack, empty_stack) (c, s, s0)).
    trivial.
Qed.

Lemma opposed: forall A B : Prop, (A -> B) -> (not B -> not A).
Proof. auto. Qed.


Lemma terminaison_state :
    forall ks_0 : krivineState, forall t t_1 : lambdaTermeN,
        state_correctness ks_0 ->
        t = tau ks_0 ->
        (t s-> t_1) -> (t <> t_1) ->
       (* (forall ks_1 : krivineState, ks_0 km->* ks_1 -> t = tau ks_1) -> *)
        (forall ks_1 ks_2 : krivineState,
            ks_0 km->* ks_1 -> ks_1 km-> ks_2 ->
            (tau ks_0 = tau ks_1) ->
            let (p_1, s_1) := ks_1 in
            let (c_1, e_1) := p_1 in
            (forall n : nat, c_1 <> Access n) -> match c_1 with
                | (Push _; _) => True
                | (Grab; _) => (t <> tau ks_2)
                | Access n => True
                end
            ).
Proof.
    intro ks_0; intro t; intro t_1; intro SC; intro Eq.
    rewrite Eq; clear Eq.
    intro TisPossible; intro TbutNotEq.
(*    intro H.*)
    intro ks_1; case ks_1; clear ks_1.
    intro p; case p; clear p.
    intro c; intro e; intro s.
    intro ks_2; case ks_2; clear ks_2.
    intro p; case p; clear p.
    intro c2; intro e2; intro s2.
    case c; clear c.
    intro Trans.
    all : auto.
    intro c.
    intro H0.
    intro H1.
    case_eq s.
    intro StackEq.
    rewrite StackEq in H1.
    inversion H1.

    intro c0; intro e0; intro s0.
    intro EqS.

    intro Eq.
    rewrite EqS in H1.
    inversion H1.
    rewrite Eq.
    intro H10; clear H10.
    rewrite <- H; rewrite <-H in H1; clear H c2.
    rewrite <- H9; rewrite <-H9 in H1; clear H9 s2.
    rewrite <- H8 in H1; clear H8 e2.
    move : TbutNotEq.
    rewrite Eq.
    suff : t_1 = tau (c, $ (c0, e0)# e, s0).
    intro Eq2; rewrite Eq2.
    trivial.
    suff : (tau ks_0) s-> (tau (c, $ (c0, e0)# e, s0)).
    intro H.
    exact (kv_red_is_functionnal (tau ks_0) t_1 (tau (c, $ (c0, e0)# e, s0)) (conj TisPossible H)).

    rewrite Eq.
    unfold tau.
    simpl.
    apply tau_inner_krivine_sred.
    unfold tau_tuple.
    simpl.
    suff : state_correctness (Grab ; c, e, s).
    intro sC2.
    inversion sC2.
    destruct H7.
    suff : List.Forall (fun t => C[ 0 ]( t )) (tau_stack e).
    2 : apply stack_correctness_is_no_free; assumption.
    intro ListForall_isCorrect.
    rewrite (lemma23 (tau_stack e) ListForall_isCorrect).
    rewrite (lemma16 (tau_code c) 0 (tau_stack e) ListForall_isCorrect ((tau_code c0) [0 <-- tau_stack e0])).
    simpl.
    apply (Kevaluation 
        (tau_code c) [1 <-- tau_stack e]
        (tau_code c0) [0 <-- tau_stack e0]
    ).

    pose H7 := krivine_trans_is_stategy ks_0 (Grab ; c, e, s) SC H0.
    elim H7.
    trivial.
Qed.

Lemma grab_is_reachable : forall ks_0 : krivineState, 
    state_correctness ks_0 ->
    exists ks_1, ks_0 km->* ks_1 /\ 
        (let (p0, _) := ks_1 in let (c0, _) := p0 in 
            match c0 with
                | Grab; _ => True
                | _ => False
            end
        ).
Proof.
    intro ks_0; case ks_0; clear ks_0.
    intro p; case p; clear p.
    intro c; intro e.
    move : c.
    induction e.
    intro c.
    simpl.
    induction c; intro s.
    unfold code_correctness.
    unfold hasAllFreeVarUnder.
    simpl.
    lia.
    intro H.
    exists (Grab ; c, empty_stack, s).
    split; trivial.
    apply refl_km.

    simpl.
    intro H.
    destruct H; destruct H0.
    pose H2 := code_correctness_propagation_push2 c1 c2 empty_stack H.
    suff : stack_correctness ($ (c1, empty_stack) # s).
    intro H3.
    pose H4 := IHc2 ($ (c1, empty_stack) # s) (conj H2 (conj H0 H3)).
    inversion H4.
    destruct H5.
    exists x.
    split; trivial.
    apply (concat_km (Push c1; c2, empty_stack, s) (c2, empty_stack, $ (c1, empty_stack) # s) x).
    apply single_km.
    apply TPush.
    trivial.
    apply top_is_correct; try assumption.
    apply (code_correctness_propagation_push1 c1 c2 empty_stack H).

    intro c0.


    induction c0; intro s; intro sC.
    induction n.
    pose ks_2 := (c, e1, s).
    inversion sC.
    destruct H0.
    inversion H0.
    clear H2 H3 H4 c_0 e_0 tl.
    assert (state_correctness (c, e1, s)).
    unfold state_correctness.
    auto.

    pose ks_1 := IHe1 c s H2.
    inversion ks_1.
    exists x.
    destruct H3.
    split; trivial.
    apply (concat_km (Access 0, $ (c, e1) # e2, s) (c, e1, s) x); trivial.
    apply single_km.
    apply TAccess_O.

    inversion sC.
    destruct H0.



    pose IHe := IHe2 (Access n) s.

    assert (state_correctness (Access n, e2, s)).
    unfold state_correctness. 

    inversion H0.
    split; auto.
    apply (code_correctness_propagation_access n c e1 e2).
    assumption.

    pose IH := IHe H2.
    inversion IH.
    destruct H3.
    exists x.
    split; trivial.

    apply (concat_km (Access (S n), $ (c, e1) # e2, s) (Access n, e2, s), x); trivial.
    apply single_km.
    apply TAccess_S.

    exists (Grab ; c0, $ (c, e1) # e2, s).
    split; trivial.
    apply refl_km.

    pose H3 := IHc0_2 ($ (c0_1, $ (c, e1) # e2) # s).
    suff : state_correctness (c0_2, $ (c, e1) # e2, $ (c0_1, $ (c, e1) # e2) # s).
    intro H4.
    pose H5 := H3 H4.
    inversion H5.
    destruct H.
    exists x.
    split; trivial.
    apply (concat_km
        (Push c0_1; c0_2, $ (c, e1) # e2, s) 
        (c0_2, $ (c, e1) # e2, $ (c0_1, $ (c, e1) # e2) # s)
        x); trivial.
    apply single_km.
    apply TPush.

    inversion sC.
    destruct H0.
    unfold state_correctness.
    split.
    2 : split; trivial.
    Check code_correctness_propagation_push2.
    apply (code_correctness_propagation_push2 c0_1); trivial.

    inversion H0.
    apply top_is_correct; trivial.
    apply (code_correctness_propagation_push1 c0_1 c0_2); trivial.
Qed.

Lemma propagation_1: forall ks: krivineState,
    state_correctness ks -> 
    (forall t_1 : lambdaTermeN, ((tau ks) s->* t_1) -> tau ks = t_1)
    ->
    (forall ks_1 : krivineState, (ks km->* ks_1) -> (tau ks = tau ks_1)).
Proof.
    intro ks.
    intro sC.
    intro H.
    intro ks_1.
    intro H0.
    Check krivine_trans_is_stategy.
    pose t := krivine_trans_is_stategy ks ks_1 sC H0.
    destruct t.
    pose H3 := H (tau ks_1) H1.
    trivial.
Qed.

Lemma lemma00 : 
    forall t : lambdaTermeN,
    (forall t_1 : lambdaTermeN, t s->* (t_1) -> t = t_1) <->
    ~ (exists t_1 : lambdaTermeN, t s->* (t_1) /\ t<> t_1).
Proof.
    split.
    intro H.
    intro H0.
    inversion H0.
    destruct H1.
    pose Abs := H x H1.
    congruence.
    intro H1.
    intro t1.
    intro H2.
    suff : not (t <> t1) -> t = t1.
    intro H3.
    elim H3; trivial.
    contradict H1.
    exists t1.
    auto.

    pose Cases := decidable_lambda_terme_equality t t1.
    case Cases.
    all : move=>//.
Qed.

Lemma lemma00bis : 
    forall t : lambdaTermeN,
    (exists t_1 : lambdaTermeN, t s->* (t_1) /\ t<> t_1)
    ->
    not (forall t_1 : lambdaTermeN, t s->* (t_1) -> t = t_1).
Proof.
    intro t.
    intro Exist.
    inversion Exist.
    destruct H.
    intro Forall.
    pose Eq := Forall x H.
    congruence.
Qed.

Lemma lemma01 :
    forall ks: krivineState,
        (forall ks_1 : krivineState, ks km->* ks_1 -> tau ks = tau ks_1)
        <->
        ~ (exists ks_1 : krivineState, ks km->* ks_1 /\ tau ks <> tau ks_1).
Proof.
    split.
    intro H; intro H0.
    inversion H0.
    destruct H1.
    pose Abs := H x H1.
    congruence.

    intro NegH.
    intro ks_1.
    intro Trans.
    suff : not (tau ks <> tau ks_1) -> tau ks = tau ks_1.
    intro H3.
    elim H3; trivial.
    contradict NegH.
    exists ks_1.
    auto.

    pose Cases := decidable_lambda_terme_equality (tau ks) (tau ks_1).
    case Cases.
    all : move => //.
Qed.

Lemma lemma01bis :
    forall ks : krivineState,
        (exists ks_1 : krivineState, ks km->* ks_1 /\ tau ks <> tau ks_1)
        ->
        not (forall ks_1 : krivineState, ks km->* ks_1 -> tau ks = tau ks_1).
Proof.
    intro ks.
    intro Exist.
    intro Forall.
    inversion Exist.
    destruct H.
    pose Abs := Forall x H.
    congruence.
Qed.

Lemma propagation_2: forall ks: krivineState,
    state_correctness ks ->
    (forall ks_1 : krivineState, (ks km->* ks_1) -> (tau ks = tau ks_1))
    ->
    (forall t_1 : lambdaTermeN, ((tau ks) s->* t_1) -> tau ks = t_1).
Proof.
    intro ks; intro sC.
    intro H.
    assert (~ (exists ks_1 : krivineState, ks km->* ks_1 /\ tau ks <> tau ks_1)).
    apply (lemma01 ks).
    assumption.


    apply (lemma00 (tau ks)).
    contradict H0.
    exfalso.

    inversion H0.
    destruct H1.
    induction H1.
    congruence.

    all : swap 1 2.
    pose Cases := (decidable_lambda_terme_equality t u).
    case Cases.
    intro Eq.
    rewrite Eq in H1_ H1_0 IHkrivine_red1 IHkrivine_red2 H2 H H0.
    clear Eq Cases t.
    apply IHkrivine_red2; trivial.
    
    intro NotEq.
    apply IHkrivine_red1; trivial.

    pose self := refl_km ks.
    pose Eq := H ks self.
    assert (forall ks_1 ks_2 : krivineState,
        ks km->* ks_1 ->
        (ks_1) km-> (ks_2) ->
        tau ks = tau ks_1 ->
        let (p_1, _) := ks_1 in
        let (c_1, _) := p_1 in
        (forall n : nat, c_1 <> Access n) ->
        match c_1 with
        | Grab ; _ => t <> tau ks_2
        | _ => True
    end).
    exact (terminaison_state ks t u sC Eq H1 H2).
    rewrite Eq in H1 H0 H2 H3.

    pose H4 := grab_is_reachable ks sC.
    inversion H4.
    destruct H5.
    assert (tau ks = tau x).
    rewrite <- Eq.
    exact (H x H5).

    pose next := transitionFunction x.
    case_eq next.

    all : swap 1 2.

    unfold next.
    induction x.
    induction a.
    case_eq a.
    1-3 : intro c.
    3 : intro c0.
    1,3 : intro eq; rewrite eq in H6; trivial.
    case_eq b.
    2 : simpl.
    2 : discriminate.
    
    intro Eq2.
    rewrite <-Eq in H7.
    rewrite Eq2 in H7.
    intro Eq3; rewrite Eq3 in H7.
    unfold tau in H7.
    unfold tau_tuple in H7.
    simpl in H7.
    rewrite <-Eq in H1.

    pose Abs := only_app_may_be_kv_reduced t u H1.
    inversion Abs.
    inversion H8.
    rewrite H9 in H7.
    discriminate.

    intro k; intro Transition.
    suff : ((tau x) s-> (tau k)).
    intro TransS.
    unfold next in Transition.
    apply transitionRelation_is_transitionFunction in Transition.
    pose transition_ks_0_k := concat_km ks x k H5 (single_km x k Transition).
    pose Absurdity_Eq := H k transition_ks_0_k.
    rewrite <-H7 in TransS.
    rewrite <-Eq in TransS; rewrite <-Eq in H1; rewrite <-Eq in H2.
    pose LastEq := kv_red_is_functionnal t u (tau k) (conj H1 TransS).
    rewrite LastEq in H2.
    rewrite Absurdity_Eq in H2.
    auto.
    
    induction x.
    induction a.
    rename a into c; rename b0 into e; rename b into s.
    case_eq c.
    1-3: intro c0.
    3: intro c1.
    1-3: intro Eq2.
    1-3: rewrite Eq2 in H6.
    1, 3: exfalso; trivial.

    case_eq s.
    intro Eq3; rewrite Eq2 in H7; rewrite Eq3 in H7.

    rewrite <- Eq in H1; rewrite <- Eq in H2; rewrite <-Eq in H7.
    unfold tau in H7.
    unfold tau_tuple in H7.
    simpl in H7.
    pose Abs := only_app_may_be_kv_reduced t u H1.
    inversion Abs.
    inversion H8.
    rewrite H9 in H7.
    discriminate.

    intro c1; intro e1; intro s1.
    intro Eq3.
    move : Transition.
    unfold next.
    rewrite Eq2; rewrite Eq3.
    simpl.
    case k.
    intro p; case p; clear p.
    intro c2; intro e2; intro s2.
    intro SomeEq.
    inversion SomeEq.
    simpl.
    apply tau_inner_krivine_sred.
    unfold tau_tuple.
    simpl.

    suff : (List.Forall isClosed (tau_stack e)).
    intro LFiC.
    rewrite (lemma23 (tau_stack e) LFiC).
    rewrite (lemma16 (tau_code c2) 0 (tau_stack e) LFiC).
    simpl.
    apply Kevaluation.
    apply stack_correctness_is_no_free.

    suff : (state_correctness (c, e, s)).
    intro sC3.
    destruct sC3; destruct H12.
    trivial.

    pose sC4 := krivine_trans_is_stategy ks (c, e, s) sC H5.
    destruct sC4.
    assumption.
Qed.

Lemma lemma02 : forall t_0 t_1: lambdaTermeN,
    t_0 s->* t_1 -> t_0 <> t_1 -> forall t_2 : lambdaTermeN, t_0 s-> t_2 -> t_0 = t_2 -> False.
Proof.
    intro t_0; intro t_1; intro trans.
    induction trans.
    auto.

    intro notEq; intro t_2.
    intro trans2.
    intro Eq.
    pose Eq2 := kv_red_is_functionnal t u t_2 (conj H trans2).
    congruence.

    intro notEq.
    case (decidable_lambda_terme_equality t u).
    intro Eq.
    rewrite Eq; rewrite Eq in notEq.
    exact (IHtrans2 notEq).
    assumption.
Qed.

Lemma lemma02bis : forall ks_0 ks_1 : krivineState,
    ks_0 km->* ks_1 -> state_correctness ks_0 -> tau ks_0 <> tau ks_1 ->
    (exists ks_2 : krivineState, ks_0 km->* ks_2 /\ (tau ks_0) s-> (tau ks_2)).
Proof.
    intro ks_0; intro ks_1; intro trans.
    induction trans.
    congruence.
    intro sC.
    intro notEq.
    exists ks_1.
    split.
    apply single_km; assumption.
    pose Ccl := trans_is_krivine_reduce ks_0 ks_1 H sC.
    case Ccl; trivial.
    congruence.

    intro sC.
    intro notEq1.
    case (decidable_lambda_terme_equality (tau ks_0) (tau ks_1)).
    intro Eq.
    rewrite <-Eq in IHtrans2.
    pose sC2 := krivine_trans_is_stategy ks_0 ks_1 sC trans1.
    destruct sC2.
    pose Exists := (IHtrans2 H0 notEq1).
    inversion Exists.
    exists x.
    destruct H1.
    split; trivial.
    apply (concat_km ks_0 ks_1 x); assumption.

    intro notEq2.
    apply IHtrans1; assumption.
Qed.

Lemma propagation_3 : forall ks : krivineState,
    state_correctness ks ->
    (exists t: lambdaTermeN, ((tau ks) s-> t))
    ->
    (exists ks_1 : krivineState, ks km->* ks_1 /\ ((tau ks) s-> (tau ks_1))).
Proof.
    intro ks.
    intro sC.
    intro H.
    inversion H.
    pose Cases := decidable_lambda_terme_equality (tau ks) x.
    case Cases.
    intro isEq.
    exists ks.
    split.
    apply refl_km.
    rewrite isEq; rewrite isEq in H0.
    assumption.

    intro notEq.
    suff : (exists t : lambdaTermeN, (tau ks) s->* t /\ (tau ks) <> t).
    2 : exists x.
    2 : split; trivial.
    2 : apply Ksingle; assumption.
    intro ExistwithNotEq.

    assert (tau ks = tau ks) as Eq. reflexivity.

    pose H2 := lemma00bis (tau ks) ExistwithNotEq.
    assert (not (forall ks_1 : krivineState, ks km->* ks_1 -> tau ks = tau ks_1)).
    intro Abs.
    exact (H2 (propagation_2 ks sC Abs)).


    pose H3 := grab_is_reachable ks sC.

    inversion H3.
    clear Cases.
    assert (tau ks = tau x0 \/ not (tau ks = tau x0)) as Cases.
    apply decidable_lambda_terme_equality.
    case Cases.
    1-2: clear Cases.

    intro tauKs_is_tau_x0.
    
    pose H5 := terminaison_state ks (tau ks) x sC Eq H0 notEq.

    pose next := transitionFunction x0.
    case_eq next.
    intro k.
    unfold next.
    intro Trans.
    exists k.
    apply transitionRelation_is_transitionFunction in Trans.
    destruct H4.
    split.
    apply (concat_km ks x0 k).
    assumption.
    exact (single_km _ _ Trans).

    assert (let (p_1, _) := x0 in
    let (c_1, _) := p_1 in
    (forall n : nat, c_1 <> Access n) ->
    match c_1 with
    | Grab ; _ => tau ks <> tau k
    | _ => True
    end) as t.
    exact (H5 x0 k H4 Trans tauKs_is_tau_x0).
    clear H5.

    induction x0.
    rename b into s_x0.
    induction a.
    rename a into c_x0; rename b into e_x0.
    case_eq c_x0.
    1-3 : intro c.
    3 : intro c2.
    1-3: intro Eq_c_x0.
    1-3 :rewrite Eq_c_x0 in H6.
    1, 3 : apply False_ind; done.

    rewrite Eq_c_x0 in t.
    rewrite tauKs_is_tau_x0.
    assert (state_correctness (c_x0, e_x0, s_x0)).
    pose stateIsCorrect := krivine_trans_is_stategy ks (c_x0, e_x0, s_x0) sC H4.
    destruct stateIsCorrect.
    assumption.

    pose isReduce := trans_is_krivine_reduce (c_x0, e_x0, s_x0) k Trans H5.
    case isReduce.
    trivial.

    assert (forall n : nat, Grab; c <> Access n).
    intro n.
    discriminate.

    intro AbsEq.
    pose AbsNEq := t H7.
    rewrite <- tauKs_is_tau_x0 in AbsEq.
    congruence.

    unfold next.

    all : swap 1 2.

    intro NotEq.

    inversion H4.
    pose ind :=  (transitionRelationExt_ind (fun ks x0 =>
        (tau ks <> tau x0) -> 
        state_correctness ks ->
        exists ks_1 : krivineState, ks km->* ks_1 /\ (tau ks) s-> (tau ks_1))).
    assert (forall ks : krivineState,
    (fun ks0 x0 : krivineState =>
     (tau ks <> tau x0) ->
     state_correctness ks ->
     exists ks_1 : krivineState,
       ks0 km->* ks_1 /\ (tau ks0) s-> (tau ks_1))
      ks ks) as Ind1.
    intro ks0.
    congruence.

    assert (forall ks_0 ks_1 : krivineState,
    (ks_0) km-> (ks_1) ->
    (fun ks x0 : krivineState =>
     tau ks <> tau x0 ->
     state_correctness ks ->
     exists ks_2 : krivineState,
       ks km->* ks_2 /\ (tau ks) s-> (tau ks_2))
      ks_0 ks_1) as Ind2.
    intro ks_0; intro ks_1.
    intro Trans.
    intro NotEq2.
    intro sC2.
    pose Cases := trans_is_krivine_reduce ks_0 ks_1 Trans sC2.
    case Cases; clear Cases.
    intro Trans2.
    exists ks_1.
    split; trivial.
    apply single_km; assumption.
    congruence.


    assert (forall ks_0 ks_1 ks_2 : krivineState,
    ks_0 km->* ks_1 ->
    (fun ks x0 : krivineState =>
     tau ks <> tau x0 ->
     state_correctness ks ->
     exists ks_3 : krivineState,
       ks km->* ks_3 /\ (tau ks) s-> (tau ks_3))
      ks_0 ks_1 ->
    ks_1 km->* ks_2 ->
    (fun ks x0 : krivineState =>
     tau ks <> tau x0 ->
     state_correctness ks ->
     exists ks_3 : krivineState,
       ks km->* ks_3 /\ (tau ks) s-> (tau ks_3))
      ks_1 ks_2 ->
    (fun ks x0 : krivineState =>
     tau ks <> tau x0 ->
     state_correctness ks ->
     exists ks_3 : krivineState,
       ks km->* ks_3 /\ (tau ks) s-> (tau ks_3))
      ks_0 ks_2) as Ind3.
    intro ks_0; intro ks_1; intro ks_2.
    intro T1; intro IH1; intro T2; intro IH2; intro NotEq2; intro sC2.


    pose Cases := decidable_lambda_terme_equality (tau ks_0) (tau ks_1).
    case Cases; clear Cases.
    intro Eq2.
    rewrite <-Eq2 in IH2.
    pose sC3 := krivine_trans_is_stategy ks_0 ks_1 sC2 T1.
    destruct sC3.
    pose IH := IH2 NotEq2 H8.
    inversion IH.
    destruct H9.
    exists x1.
    split; trivial.
    apply (concat_km ks_0 ks_1 x1); assumption.

    intro NotEq3.
    exact (IH1 NotEq3 sC2).

    pose ind2 := ind Ind1 Ind2 Ind3 ks x0 H5.
    simpl in ind2.
    exact (ind2 NotEq sC).

    intro transFx0.

    destruct H4.
    assert (forall ks_1 : krivineState, ks km->* ks_1 -> ks_1 km->* x0) as isTerm.
    intro ks_1; intro trans_ks1.
    pose single_path := single_path ks x0 H4 ks_1 trans_ks1.
    case single_path; trivial.
    intro trans2.
    pose isTerm := is_terminal x0 transFx0 ks_1 trans2.
    rewrite isTerm.
    apply refl_km.

    clear H3 H5 H2 H H6 H1.
    clear next Eq notEq H0 x.
    move : isTerm tauKs_is_tau_x0 transFx0 ExistwithNotEq sC.
    induction H4.
    all : intro Forall; intro tauEq; intro isTerm; intro notForall; intro sC.
    pose isTerm2 := is_terminal ks isTerm.
    suff : (forall ks_1 : krivineState, ks km->* ks_1 -> tau ks = tau ks_1).
    apply lemma00bis in notForall.
    assert (not (forall ks_1 : krivineState, ks km->* ks_1 -> tau ks = tau ks_1)).
    intro H.
    pose T := (propagation_2 ks sC H).
    auto.
    congruence.
    intro ks_1; intro trans.
    rewrite (isTerm2 ks_1 trans).
    reflexivity.

    suff :  (forall ks_2 : krivineState, ks_0 km->* ks_2 -> tau ks_0 = tau ks_2).
    suff :  (not (forall ks_2 : krivineState, ks_0 km->* ks_2 -> tau ks_0 = tau ks_2)).
    congruence.
    intro H0.
    pose T := (propagation_2 ks_0 sC H0).
    apply lemma00 in T.
    auto.

    intro ks_2; intro Trans2.
    suff : (ks_2 = ks_0 \/ ks_2 = ks_1).
    intro Cases; case Cases; clear Cases.
    1-2 : intro Eq3; rewrite Eq3; auto.

    clear notForall.
    induction Trans2.
    auto.
    apply transitionRelation_is_transitionFunction in H.
    apply transitionRelation_is_transitionFunction in H0.
    rewrite H0 in H.
    inversion H.
    auto.

    pose Cases := IHTrans2_1 H Forall tauEq.
    case Cases; clear Cases; auto.
    intro Eq.
    rewrite Eq in IHTrans2_2.
    exact (IHTrans2_2 H Forall tauEq sC).
    
    intro two_is_one.
    rewrite two_is_one in Trans2_2.
    pose isTerm2 := is_terminal ks_1 isTerm ks_3 Trans2_2.
    auto.

    case (decidable_lambda_terme_equality (tau ks_0) (tau ks_1)).
    intro Eq.
    rewrite <-Eq in IHtransitionRelationExt2.
    pose Forall2 := is_terminal ks_2 isTerm.
    pose Forall3 := single_path ks_1 ks_2 H4_0.
    assert (forall ks_3 : krivineState, ks_1 km->* ks_3 -> ks_3 km->* ks_2) as Forall4.
    intro ks_3; intro trans.
    case (Forall3 ks_3 trans).
    trivial.
    intro trans2.
    rewrite (Forall2 ks_3 trans2).
    apply refl_km.

    assert (not (forall ks_1 : krivineState, ks_0 km->* ks_1 -> tau ks_0 = tau ks_1)).
    intro H.

    pose H0 := krivine_trans_is_stategy ks_0 ks_1 sC H4_.
    destruct H0.
    
    pose IH := IHtransitionRelationExt2 Forall4 tauEq isTerm notForall H1.
    
    inversion IH.
    destruct H2.
    inversion notForall.
    destruct H4.

    apply (lemma02 (tau ks_0) x0 H4 H5 (tau x) H3).
    apply H.
    exact (concat_km ks_0 ks_1 x H4_ H2).

    suff : state_correctness ks_1.
    intro sC2.
    pose IH1 := IHtransitionRelationExt2 Forall4 tauEq isTerm notForall sC2.
    inversion IH1.
    exists x.
    destruct H0.
    split; trivial.
    apply (concat_km _ ks_1 _ H4_ H0).
    pose Suff := krivine_trans_is_stategy ks_0 ks_1 sC H4_.
    destruct Suff.
    assumption.

    intro notEq.
    exact (lemma02bis ks_0 ks_1 H4_ sC notEq).
Qed.

Lemma propagation_4 : forall t0 t1: lambdaTermeN, t0 s->* t1 ->
    forall ks : krivineState,  state_correctness ks -> (tau ks) = t0 -> (exists ks_1 : krivineState, ks km->* ks_1 /\ tau ks_1 = t1).
Proof.
    intro t0; intro t1.
    intro T.
    induction T.
    all : intro ks; intro sC; intro Eq.
    exists ks.
    split.
    apply refl_km.
    trivial.
    
    pose Cases := decidable_lambda_terme_equality t u.
    case Cases; clear Cases.
    intro isEq2.
    exists ks.
    rewrite Eq isEq2.
    split; trivial.
    apply refl_km.

    intro notEq.
    rewrite <-Eq in H.
    assert (exists t : lambdaTermeN, (tau ks) s-> (t)) as ExistT.
    exists u; assumption.
    pose ExistK :=  propagation_3 ks sC ExistT.
    inversion ExistK.
    destruct H0.
    exists x.
    split; trivial.
    apply (kv_red_is_functionnal (tau ks)).
    auto.

    pose Exist1 := IHT1 ks sC Eq.
    inversion Exist1.
    destruct H.

    pose Trans := krivine_trans_is_stategy ks x sC H.
    destruct Trans.
    
    pose Exist2 := IHT2 x H2 H0.
    inversion Exist2.
    destruct H3.
    exists x0.
    split; trivial.
    apply (concat_km ks x x0); assumption.
Qed.

