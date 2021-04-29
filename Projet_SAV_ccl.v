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
        pose Equiv := transitionRelation_is_transitionFunction ks_0 ks_1.
        case Equiv.
        intro Eq1. intro Eq2.
        pose Eq := Eq2 H.
        pose Formula := trans_is_krivine_reduce ks_0 ks_1 Eq StateC.
        case Formula.
        intro H0.
        apply (Ksingle (tau ks_0) (tau ks_1)). trivial.

        intro H0; rewrite H0; apply Krefl.

        apply (correctness_preserved ks_0 ks_1).
        trivial.

        apply transitionRelation_is_transitionFunction.
        trivial.

    + split.

        apply (Kconcat (tau ks_0) (tau ks_1) (tau ks_2)).
        all : pose H1 := IHtransitionRelationExt1 StateC.
        all : elim H1; intro H2; intro StateC2.
        trivial.
        all : pose H3 := IHtransitionRelationExt2 StateC2.
        all : elim H3; intro H4; intro H5.
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
