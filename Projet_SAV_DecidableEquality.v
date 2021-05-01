Add LoadPath "C:\Users\Hp\Documents\Coq\projet_Semantique" as CoqDirectory.
Require Import Lia.
Require Import ssreflect.
Require Import ssrfun.
Require Import Coq.ssr.ssrbool.

Load Projet_SAV_P1.

Definition eqb :=
  fix eqb (t u : lambdaTermeN) {struct t} : bool :=
    match t with
      | var x =>
        match u with
          | var y => Nat.eqb x y
          | _ => false
        end
      | lambda t_0 =>
        match u with
          | lambda u_0 => (eqb t_0 u_0)
          | _ => false
        end
      | app t_0 t_1 =>
        match u with
          | app u_0 u_1 => (eqb t_0 u_0) && (eqb t_1 u_1)
          | _ => false
        end
    end.

Lemma eq_lambdaterme_P (t u : lambdaTermeN) : reflect (t = u) (eqb t u).
Proof.
  apply (iffP idP). move : u.
    + induction t, u => //.
        - rename n0 into m.
          simpl. move => Eqb.
          pose Eqp := (fst (PeanoNat.Nat.eqb_eq n m) Eqb); rewrite Eqp; reflexivity.
        - simpl. move => Eqb.
          pose Eqp := IHt u Eqb; rewrite Eqp; reflexivity.
        - simpl. move => H.
          pose H' := (andb_prop (eqb t1 u1) (eqb t2 u2) H). case H' as [Eq_1 Eq_2]. clear H.
          assert (t1 = u1) as Eqt1u1.
          apply IHt1 => //.
          assert (t2 = u2) as Eqt2u2.
          apply IHt2 => //.
          rewrite Eqt1u1 Eqt2u2; reflexivity.
    + move => H. rewrite H. clear H t. induction u => //. Print eq.
      simpl. pose Eqp := (snd (PeanoNat.Nat.eqb_eq n n) (eq_refl n)); rewrite Eqp; reflexivity.
      simpl. apply /andP. split => //.
Qed.

Proposition decidable_lambda_terme_equality :
  forall t u : lambdaTermeN, (t = u) \/ (t <> u).
Proof.
  move => t u.
  case (eq_lambdaterme_P t u); auto.
Qed.