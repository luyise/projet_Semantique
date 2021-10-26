Add LoadPath "C:\Users\Hp\Documents\Coq\projet_Semantique" as CoqDirectory.
Add LoadPath "/Users/samuel/Documents/Documents-L3/PolyCours/S2/Sem/projet_Semantique" as CoqDirectory.
Load Projet_SAV_P2.
Load Projet_SAV_utils.


Lemma lemma20 : forall x : nat, forall k : nat, hasAllFreeVarUnder k (var x) -> x < k.
Proof.
  unfold hasAllFreeVarUnder.
  unfold prop_aux_with_linkDepth.
  lia.
Qed.

Lemma lemma21 : forall t : lambdaTermeN, forall d : nat,
  prop_aux_with_linkDepth 0 d t -> incr_free_with_linkDepth d t = t.
Proof.
  induction t.
    + rename n into x.
      move => d. unfold prop_aux_with_linkDepth, incr_free_with_linkDepth.
      simpl. move => Ineq. assert (Nat.leb d x = false) as Rwrt. rewrite PeanoNat.Nat.leb_gt. 
      trivial. rewrite Rwrt. trivial.
    + move => d. simpl. move => Ht. assert ((incr_free_with_linkDepth (S d) t) = t).
      apply IHt. replace (S d) with (d + 1). 2 : lia. trivial. rewrite H. trivial.
    + move => d. simpl. case. move => Ht1 Ht2.
      assert (incr_free_with_linkDepth d t1 = t1) as Rwrt1. apply IHt1. trivial.
      assert (incr_free_with_linkDepth d t2 = t2) as Rwrt2. apply IHt2. trivial.
      rewrite Rwrt1 Rwrt2. trivial.
Qed.  

Lemma lemma22 : forall t : lambdaTermeN, isClosed t -> (incr_free t) = t.
Proof.
  unfold isClosed, incr_free. move => t. apply lemma21.
Qed.

Lemma lemma23 : forall l : list lambdaTermeN, List.Forall isClosed l -> List.map incr_free l = l.
Proof.
  apply List.Forall_ind.
    + simpl. trivial.
    + move => u_0 l Hu_0 Hl Il'.
      simpl. congr cons. apply lemma22. trivial.
      trivial.
Qed.

Lemma lemma24 : forall u : lambdaTermeN, forall d : nat, prop_aux_with_linkDepth 0 d u -> prop_aux_with_linkDepth 0 (d+1) u.
Proof.
  induction u.
    + move => d. rename n into x.
      unfold isClosed, hasAllFreeVarUnder, prop_aux_with_linkDepth.
      simpl. lia.
    + move => d. simpl.
      apply IHu.
    + simpl. move => d. case. move => Hu1 Hu2.
      split. apply IHu1. trivial. apply IHu2. trivial.
Qed.

Lemma lemma25 : forall u : lambdaTermeN, forall d h : nat, prop_aux_with_linkDepth 0 d u -> prop_aux_with_linkDepth 0 (d+h) u.
Proof.
  move => u d h. induction h.
    + simpl. replace (d + 0) with d. 2 : lia. trivial.
    + replace (d + S h) with ((d + h) + 1). 2 :lia.
      move => Hu. apply lemma24. apply IHh. trivial.
Qed.

Lemma lemma26 : forall A : Type, forall l : list A, List.map ssrfun.id l = l.
Proof.
  induction l.
    + simpl. trivial.
    + simpl. congr cons. apply IHl.
Qed.

Lemma lemma27 : forall u : lambdaTermeN, forall d : nat, forall l : list lambdaTermeN,
  (prop_aux_with_linkDepth (length l) d u) -> (List.Forall isClosed l) -> prop_aux_with_linkDepth 0 d (u [ d <-- l ]).
Proof.
  induction u.
    + rename n into x.
      move => d l.
      assert ((x >= d /\ x < d + length l) \/ (x < d \/ x >= d + length l)) as Disj. lia.
      case Disj.
        - move => Ineq_0 _ H.
          rewrite lemma11. lia. lia.
          assert (List.Forall (prop_aux_with_linkDepth 0 d) l) as H_weak.
          assert (forall u : lambdaTermeN, isClosed u -> (prop_aux_with_linkDepth 0 d) (ssrfun.id u)).
          assert (0<=d) as Ineq_1. lia. move => u. unfold isClosed, hasAllFreeVarUnder. apply (lemma25 u 0 d). trivial.
          pose H_1 := (Forall_map lambdaTermeN lambdaTermeN (fun x => x) isClosed (prop_aux_with_linkDepth 0 d) H0) l H.
          assert ((List.map ssrfun.id l) = l) as Rwrt. apply lemma26. replace (List.map ssrfun.id l) with l in H_1.
          trivial. apply List.Forall_nth. 2 : lia. trivial.
        - move => Ineq_0. move => Hl. simpl in Hl.
          assert (x < d) as Ineq_1. lia.
          move => _.
          rewrite lemma12. trivial. simpl. trivial. 
    + move => d l. simpl. move => Hu Hl.
      rewrite lemma23. trivial.
      apply IHu. trivial. trivial.
    + move => d l. simpl. case. auto.
Qed.

Lemma lemma28 : forall l : list lambdaTermeN, forall u : lambdaTermeN,
  (hasAllFreeVarUnder (length l) u) -> (List.Forall isClosed l) -> isClosed (u [ 0 <-- l ]).
Proof.
  move => l.
  induction u. 
    + rename n into x.
      move => H. pose Hx := lemma20 x (length l) H.
      unfold isClosed.
      move => Hl.
      apply lemma13. 2, 3 : lia. exact Hl.
    + simpl.
      move => Hu Hl.
      Check lemma23.
      rewrite lemma23. exact Hl.
      unfold hasAllFreeVarUnder in Hu. simpl in Hu.
      unfold isClosed. unfold hasAllFreeVarUnder. simpl. apply lemma27. trivial. trivial.
    + simpl. unfold hasAllFreeVarUnder. simpl. unfold hasAllFreeVarUnder in IHu1, IHu2. case.
      move => Hu1 Hu2 Hl. unfold isClosed. unfold hasAllFreeVarUnder. simpl. split.
      unfold isClosed, hasAllFreeVarUnder in IHu1. apply IHu1. trivial. trivial.
      unfold isClosed, hasAllFreeVarUnder in IHu2. apply IHu2. trivial. trivial.
Qed.
