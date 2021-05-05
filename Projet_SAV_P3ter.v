Add LoadPath "C:\Users\Hp\Documents\Coq\projet_Semantique" as CoqDirectory.
Add LoadPath "/Users/samuel/Documents/Documents-L3/PolyCours/S2/Sem/projet_Semantique" as CoqDirectory.
Load Projet_SAV_Lemmas.



(* Définition du code de la machine de Krivine *)
Inductive codeBloc :=
    | Access : nat -> codeBloc
    | grab : codeBloc -> codeBloc
    | push : codeBloc -> codeBloc -> codeBloc.

(* Définition de la pile de la machine de Krivine *)
Inductive stack := 
    | empty_stack : stack
    | const_stack : codeBloc -> stack -> stack -> stack.


Notation "'Grab' ; tl " := (grab tl) (at level 20).
Notation "'Push' c ; tl " := (push c tl) (at level 20).
Notation " '$' ( c , e ) # s " := (const_stack c e s) (at level 19).
Notation " '$' '_' # s " := (const_stack _ _ s) (at level 19, only parsing).
Notation " '$' ( c , e ) # '_' " := (const_stack c e _) (at level 19, only parsing).

Fixpoint size (e: stack) : nat :=
  match e return nat with
    | empty_stack => 0
    | $ _ # tl => S (size tl)
end.

(* Définition de l'état de la machine de Krivine*)
Definition krivineState: Type := (codeBloc * stack * stack).

(* Définition de la fonction transition *)
Definition transitionFunction : krivineState -> option krivineState :=
  fun ks => match ks return option krivineState with 
    | (Access 0, $ (c_0, e_0) # _ , s) => Some (c_0, e_0, s)
    | (Access (S n), $ _ # tl, s)     => Some (Access n, tl, s)
    | (Push c_2; c, e, s)           => Some (c, e, $ (c_2, e) # s)
    | (Grab; c, e, $ (c2, e2) # s)           => Some (c, $ (c2, e2) # e, s)
    | _ => None
end.

Reserved Notation " A km-> B " (at level 0).

Inductive transitionRelation : krivineState -> krivineState -> Prop :=
  | TAccess_O : forall c : codeBloc, forall e s_0 s_1 : stack, (Access 0, $ (c, e) # s_0, s_1) km-> (c, e, s_1)
  | TAccess_S : forall n : nat, forall c : codeBloc, forall e s_0 s_1 : stack, (Access (S n), $ (c, e) # s_0, s_1) km-> (Access n, s_0, s_1)
  | TPush : forall c_0 c_1 : codeBloc, forall e s : stack, (Push c_0; c_1, e, s) km-> (c_1, e, $ (c_0, e) # s)
  | TGrab : forall c c2: codeBloc, forall e e2 s : stack, (Grab; c, e, $ (c2, e2) # s) km-> (c, $ (c2, e2) # e, s)
where
" ks_0 km-> ks_1 " := (transitionRelation ks_0 ks_1).

Reserved Notation " A km->* B " (at level 1).

Inductive transitionRelationExt : krivineState -> krivineState -> Prop :=
  | refl_km : forall ks : krivineState, ks km->* ks
  | single_km : forall ks_0 ks_1 : krivineState, (ks_0 km-> ks_1) -> (ks_0 km->* ks_1)
  | concat_km : forall ks_0 ks_1 ks_2 : krivineState, (ks_0 km->* ks_1) -> (ks_1 km->* ks_2) -> (ks_0 km->* ks_2)
where
" ks_0 km->* ks_1 " := (transitionRelationExt ks_0 ks_1).

Lemma transitionRelation_is_transitionFunction :
  forall ks_0 ks_1 : krivineState, transitionFunction ks_0 = Some ks_1 <-> ( ks_0 km-> ks_1 ).
Proof.
  case ks_0 as [p_0 s_0], ks_1 as [p_1 s_1], p_0 as [c_0 e_0], p_1 as [c_1 e_1]. split.
    * case c_0.
      + move => n. case n. case e_0.
        - simpl. discriminate.
        - simpl. move => c_2 e_2. move => s.
          move => Eq.
          assert (c_2 = c_1 /\ e_2 = e_1 /\ s_0 = s_1) as [Eq1 [Eq2 Eq3]].
          apply some_triple_to_eq. assumption.
          rewrite Eq1 Eq2 Eq3. apply TAccess_O.
        - move => n'. case e_0. simpl. discriminate.
          move => c_2 e_2 s. simpl. move => Eq.
          assert (Access n' = c_1 /\ s = e_1 /\ s_0 = s_1) as [Eq1 [Eq2 Eq3]].
          apply some_triple_to_eq. trivial.
          rewrite <-Eq1, <-Eq2, <-Eq3.
          apply TAccess_S.
      + move => c_2. case s_0.
        - move => Eq. simpl in Eq. discriminate.
        - move => c_3 e_3 s_2. simpl => Eq.
          assert (c_2 = c_1 /\ $ (c_3, e_3) # e_0 = e_1 /\ s_2 = s_1) as [Eq1 [Eq2 Eq3]].
          apply some_triple_to_eq. trivial.
          rewrite <-Eq1, <-Eq2, <-Eq3.
          apply TGrab.
      + move => c_2 c_3. simpl => Eq.
        assert (c_3 = c_1 /\ e_0 = e_1 /\ $ (c_2, e_0) # s_0 = s_1) as [Eq1 [Eq2 Eq3]].
        apply some_triple_to_eq. trivial.
        rewrite <-Eq1, <-Eq2, <-Eq3.
        apply TPush.

    * case c_0.
      + move => n. case n.
        - case e_0. simpl. move => KmTrans. inversion KmTrans.
          move => c_2 s_2 s_3. simpl. move => KmTrans.
          inversion KmTrans. reflexivity.
        - move => n' KmTrans. inversion KmTrans. simpl. reflexivity.
      + move => c_2. case s_0.
        - simpl. move => KmTrans. inversion KmTrans.
        - move => c_3 e_3 s. simpl.
          move => KmTrans. inversion KmTrans.
          reflexivity.
      + move => c_2 c_3. simpl.
        move => KmTrans. inversion KmTrans. reflexivity.
Qed.

Lemma is_functional_transitionRelation :
  forall ks_0 ks_1 ks_2 : krivineState, ks_0 km-> ks_1 -> ks_0 km-> ks_2 -> (ks_1 = ks_2).
Proof.
  move => ks_0 ks_1 ks_2 T01 T02.
  pose Eq0 := (transitionRelation_is_transitionFunction ks_0 ks_1).2 T01.
  pose Eq1 := (transitionRelation_is_transitionFunction ks_0 ks_2).2 T02.
  assert (Some ks_1 = Some ks_2). rewrite <-Eq0, <-Eq1 => //.
  congruence.
Qed.

Lemma functionality_1N :
  forall ks_0 ks_1 : krivineState, ks_0 km->* ks_1 ->
    forall ks_2 : krivineState, ks_0 km-> ks_2 -> ( ks_1 = ks_0 \/ ks_1 = ks_2 \/ ks_2 km->* ks_1 ).
Proof.
  apply: transitionRelationExt_ind.
    + move => ks_0 ks_1 _; left => //.
    + move => ks_0 ks_1 T01 ks_2 T02.
      rewrite (is_functional_transitionRelation _ _ _ T01 T02).
      right; left; trivial.
    + move => ks_0 ks_1 ks_2 T01S IH01 T12S IH12 ks_3 T03. 
      case: (IH01 ks_3 _) => //.
        - move => Eq10; rewrite <-Eq10 in T03. clear IH01.
          pose H := IH12 ks_3 T03.
          case H => //.
          move => Eq21; left; rewrite Eq21 => //.
          move => HR; right => //.
        - case.
          move => <-; right; right => //.
          move => T31S; right; right; apply (concat_km _ _ _ T31S T12S).
Qed.

Lemma single_path :
  forall ks_0 ks_1 : krivineState, ks_0 km->* ks_1 ->
    forall ks_2 : krivineState, ks_0 km->* ks_2 -> ( (ks_2 km->* ks_1) \/ (ks_1 km->* ks_2) ).
Proof.
  apply: transitionRelationExt_ind.
    + move => ks_0 ks_1 T01S; right => //.
    + move => ks_0 ks_1 T01 ks_2 T02S.
      case: (functionality_1N ks_0 ks_2 T02S ks_1 T01).
        move => ->; left; apply: single_km => //.
        move => H; case H.
        move => ->; left; apply: refl_km => //.
        auto.
    + move => ks_0 ks_1 ks_2 T01S IH01 T12S IH12 ks_3 T03S.
      case: (IH01 ks_3 T03S).
        move => T31S; left; apply: (concat_km ks_3 ks_1 ks_2 _ _) => //.
        move => T13S; exact: (IH12 ks_3 T13S).
Qed. 

Lemma is_terminal : forall ks_0 : krivineState,
  transitionFunction ks_0 = None -> forall ks_1 : krivineState, (ks_0 km->* ks_1) -> ks_0 = ks_1.
Proof.
  intro ks_0; intro trans; intro ks_1; intro trans2.
  move : trans.
  induction trans2.
  trivial.
  apply transitionRelation_is_transitionFunction in H.
  congruence.
  intro H.
  assert (ks_0 = ks_1) as Eq.
  exact (IHtrans2_1 H).
  rewrite <-Eq in IHtrans2_2.
  exact (IHtrans2_2 H).
Qed.
          
Fixpoint comp (t: lambdaTermeN) : codeBloc :=
  match t: lambdaTermeN return codeBloc with
    | var n => Access n
    | lambda t_0 => Grab; (comp t_0)
    | app t_0 t_1 => Push (comp t_1); (comp t_0)
end.

Definition comp_glob : lambdaTermeN -> krivineState := 
  fun t => (comp t, empty_stack, empty_stack).


Fixpoint tau_code (code: codeBloc) : lambdaTermeN :=
  match code return lambdaTermeN with
    | Access n => var n
    | Push c_2; c_1 => app (tau_code c_1) (tau_code c_2)
    | Grab; c => lambda (tau_code c)
end.

Fixpoint tau_stack (s: stack) : list lambdaTermeN :=
  match s with
    | empty_stack => nil
    | $ (c_0, e_0) # e_1 => (subst_list (tau_code c_0) 0 (tau_stack e_0)) :: (tau_stack e_1)
end.

Lemma tau_stack_formula: forall (c_0: codeBloc), forall (e_0 e_1 : stack),
    tau_stack ($ (c_0, e_0) # e_1) = List.cons (subst_list (tau_code c_0) 0 (tau_stack e_0)) (tau_stack e_1).
Proof.
  move => c_0 e_0 e_1.
  simpl.
  auto.
Qed.

Lemma tau_stack_length: forall s : stack, List.length (tau_stack s) = size s.
Proof.
  intro s.
  induction s.
  simpl.
  trivial.
  simpl.
  rewrite IHs2.
  trivial.
Qed.

Definition tau_tuple : codeBloc -> stack -> lambdaTermeN :=
  fun c e => subst_list (tau_code c) 0 (tau_stack e).

Fixpoint tau_inner (s: stack) (n: lambdaTermeN): lambdaTermeN :=
  match s return lambdaTermeN with
    | $ (c, e) # tl => tau_inner tl (app n (tau_tuple c e))
    | empty_stack => n
end.

Definition tau : krivineState -> lambdaTermeN := 
  fun ks =>  
    match ks return lambdaTermeN with 
      | (c, e, s) => tau_inner s (tau_tuple c e)
end.

Lemma comp_is_comp_glob: forall t: lambdaTermeN, tau (comp_glob t) = tau_code (comp t).
Proof.
  move => t.
  induction t.
  all : simpl.
  all : unfold tau_tuple.
  all : simpl.
  2-3 : repeat rewrite prop0.
  all : trivial.
Qed.

Lemma comp_and_tau: forall t: lambdaTermeN, tau (comp_glob t) = t.
Proof.
  induction t.
  all : simpl.
  all : unfold tau_tuple.
  all : simpl.
  trivial.
  all : repeat rewrite prop0.
  all : repeat rewrite <- comp_is_comp_glob.
  rewrite IHt.
  trivial.
  rewrite IHt1 IHt2.
  trivial.
Qed.

Lemma grab_krivine_sred : forall c c1 : codeBloc, forall s s1 : stack,
  List.Forall (fun t => C[0](t)) (tau_stack s) -> (app (tau_tuple (grab c) s) (tau_tuple c1 s1)) s-> (tau_tuple c ($ (c1, s1) # s)).
Proof.
  move => c c1 s s1 Hl.
  unfold tau_tuple.
  simpl.
  suff: List.map incr_free (tau_stack s) = tau_stack s.
  + intro H.
    rewrite H.
    suff : ((tau_code c) [0 <-- (tau_code c1) [0 <-- tau_stack s1] :: tau_stack s])
        = (tau_code c) [1 <-- tau_stack s] [0 <- (tau_code c1) [0 <-- tau_stack s1]].
      intro H0; rewrite H0.
    apply (Kevaluation (tau_code c) [1 <-- tau_stack s] (tau_code c1) [0 <-- tau_stack s1]).

    apply prop2.
    simpl.
    trivial.
  + apply lemma23; trivial.
Qed.
