Require Import FOPL.Semantics.
Require Import FOPL.Arithmetic.
Require Import FOPL.Hierarchy.

Instance N : Model L := {
  Dom := nat;
  SDom := DSetoid nat;
  cnsM := 0;
  Fc0M := fun _ => 0;
  Fc1M := fun _ => S;
  Fc2M := fun c => 
    match c with
    | plA => plus
    | mlA => mult
    end;
  Pd0M := fun _ => False;
  Pd1M := fun _ => fun _ => False;
  Pd2M := fun _ => le
  }.

Lemma NQ : N |=th Q.
Proof.
  unfold modelsTh. unfold models.
  intros.
  inversion H.
  - simpl. lia.
  - simpl. lia.
  - simpl.
  intros.
  apply e_nfn.
  destruct t.
  lia.
  exists t.
  auto.
  - simpl. auto.
  - simpl. lia.
  - simpl. auto.
  - simpl. lia.
  - apply M_fal. intros.
  apply M_fal. intros.
  apply M_and_destruct.
  unfold models.
  split.
  + intros.
    simpl.
    intros.
    intro.
    specialize (H2 (s0 1 - s0 0)).
    lia.
  + intros.
    simpl.
    intros.
    apply NNPP.
    contradict H1.
    lia.
Qed.

Lemma NPA : N |=th PA.
Proof.
  unfold modelsTh. unfold models.
  intros.
  inversion H.
  apply NQ. auto.
  simpl.
  intros.
  induction t.
  apply lp_iff1 in H1.
  assert((0;s) ~ fun n => Valt N s (([0]; \0) n)). 
  { unfold function_equiv. destruct n. simpl. auto. simpl. auto. }
  setoid_rewrite -> H3.
  auto.
  specialize (H2 t).
  apply H2 in IHt.
  apply lp_iff1 in IHt.
  assert((S t;s) ~ fun n => Valt N (t; s) (([S] '0 .; \0) n)).
  { unfold function_equiv. destruct n. simpl. auto. simpl. auto. }
  rewrite -> H3.
  auto.
Qed.

Definition id {A : Type} (x : A) := x.

Lemma max_0 : forall n m, max n m = 0 -> (n = 0 /\ m = 0).
Proof.
  intros.
  split.
  assert(H0:=Nat.le_max_l n m).
  lia.
  assert(H0:=Nat.le_max_r n m).
  lia.
Qed.

Check Nat.le_max_l.

Lemma Delta0_term_complete : forall t, Art t = 0 -> (Q ||- t[=][Valt N id t]).
Proof.
  induction t.
  - intros.
    simpl in H.
    lia.
  - intros.
    simpl.
    AX.
  - destruct f.
  - destruct f.
    simpl.
    intros.
    apply IHt in H.
    REWRITE_r H.
    AX.
  - simpl.
    intros.
    apply max_0 in H. destruct H.
    apply IHt1 in H.
    apply IHt2 in H0.
    REWRITE H.
    REWRITE H0.
    destruct f.
    apply plus_compl.
    apply mult_compl.
Qed.

Lemma Delta0_complete : forall p, Delta0 p -> (N |= p) -> (Q ||- p).
Proof.
  unfold models, Delta0.
  intros.
  destruct H.
  destruct H1 as [q].
  destruct H1.
  DESTRUCT H2.
  induction p.
  - simpl in H0.
    simpl in H.
    specialize(H0 id).
    
