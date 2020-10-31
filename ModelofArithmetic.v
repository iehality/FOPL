Require Import FOPL.Semantics.
Require Import FOPL.Arithmetic.

Instance N : Model L := {
  Dom := nat;
  SDom := DSetoid nat;
  cnsM := 0;
  Fc0M := fun _ => 0;
  Fc1M := fun c => 
    match c with 
    | ScA => S 
    end;
  Fc2M := fun c => 
    match c with
    | plA => plus
    | mlA => mult
    end;
  Pd0M := fun _ => False;
  Pd1M := fun _ => fun _ => False;
  Pd2M := fun c =>
    match c with
    | lelA => le
    end  
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
