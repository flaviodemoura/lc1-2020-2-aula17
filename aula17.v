Require Import Arith List.

Definition le_all x l := forall y, In y l -> x <= y.
Infix "<=*" := le_all (at level 70, no associativity).

Fixpoint insert (x:nat) (l: list nat) := match l with
                      | nil => x :: nil
                      | h :: tl => if x <=? h then (x :: l)
                                                  else (h :: (insert x tl)) 
                      end.

Lemma le_all_nil: forall a, a <=* nil.
Proof.
  intro a; unfold le_all.
  intros y H.
  inversion H.
Qed.

Lemma le_all_cons_part1: forall l a x, a <= x -> a <=* l -> a <=* x :: l.
Proof.
  induction l.
  - admit.
  - Admitted.

Lemma le_all_cons_part2: forall l a x, a <=* x :: l -> a <= x /\ a <=* l.
Proof.
  induction l.
  - admit.
  - Admitted.

Lemma le_all_insert: forall l a x, a <= x -> a <=* l -> a <=* insert x l.
Proof.
  induction l.
  - intros a x Hleq Hle_all.
    simpl.
    apply le_all_cons_part1; assumption.
  - intros a' x Hleq Hle_all.
    simpl.
    destruct (x <=? a) eqn: H.
    + apply le_all_cons_part1; assumption.
    + apply le_all_cons_part2  in Hle_all.
      destruct Hle_all as [H1 H2].
      apply le_all_cons_part1.
      * assumption.
      * apply IHl; assumption.
Qed.
  
