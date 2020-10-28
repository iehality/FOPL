Require Export Arith.
Require Export Lia.
Require Export FOPL.FOPL.
Require Export FOPL.Deduction.
Require Export FOPL.Semantics.

Set Implicit Arguments.

Inductive fc0A :=.
Inductive fc1A := ScA.
Inductive fc2A := plA | mlA.
Inductive pd0A :=.
Inductive pd1A :=.
Inductive pd2A := lelA.
Instance L : Lang := {fc0 := fc0A; fc1 := fc1A; fc2 := fc2A; pd0 := pd0A; pd1 := pd1A; pd2 := pd2A}.

Notation "a [+] b" := (Fc2 L plA a b) (at level 0, right associativity).
Notation "a [*] b" := (Fc2 L mlA a b) (at level 0, right associativity).
Notation "a [<=] b" := (Pd2 L lelA a b) (at level 60, right associativity).
Notation "[S]" := (Fc1 L ScA).
Notation "a [=/=] b" := ([~] a [=] b) (at level 60, no associativity).

Fixpoint innerNat (n0 : nat) : LC := 
  match n0 with
  | 0 => [0]
  | S n => [S] (innerNat n)
  end.

Notation "[ n ]" := (innerNat n) (at level 0).

Lemma IN_rewc : forall n s, [n] = rewc s [n].
Proof.
  intros.
  apply constant_rew.
  induction n.
  simpl. 
  auto.
  simpl.
  auto.
Qed.

Inductive Q : Th :=
  | NEQ0S : Q (fal ([0] [=/=] [S] '0))
  | SINJ  : Q (fal (fal ([S] '0 [=] [S] '1 [->] '0 [=] '1)))
  | PRED  : Q (fal ([0] [=/=] '0 [->] ext ('1 [=] [S] '0)))
  | PL0   : Q (fal ([0] [+] '0 [=] '0))
  | PLUS  : Q (fal (fal (([S] '0) [+] '1 [=] [S] ('0 [+] '1))))
  | ML0   : Q (fal ([0] [*] '0 [=] [0]))
  | MULT  : Q (fal (fal (([S] '0) [*] '1 [=] ('0 [*] '1) [+] '1)))
  | LE    : Q (fal (fal ('0 [<=] '1 [<->] ext ('0 [+] '1 [=] '2)))).
  
Inductive PA : Th :=
  | PA_Q  : forall p, Q p -> PA p
  | IND   : forall p, PA (p.([0]) [->] fal (p [->] p..([S] '0)) [->] fal p).

Lemma plus_L : forall n m, Q |- [n] [+] [m] [=] [n + m].
Proof.
  intros.
  induction n.
  + simpl.
    assert (([0] [+] '0 [=] '0).([m]) = ([0] [+] [m] [=] [m])).
    simpl.
    auto.
    rewrite <- H.
    apply fal_R.
    AX. apply PL0.
  + simpl.
    assert ((([S] [n]) [+] [m] [=] [S] [n + m]) = (([S] [n]) [+] [m] [=] [S] '0).([n + m])). {
      simpl.
      repeat rewrite <- IN_rewc.
      auto.
    }
    rewrite -> H.
    REWRITE ([n] [+] [m]).
    auto.
    simpl.
    repeat rewrite <- IN_rewc.
    assert ((([S] '0) [+] '1 [=] [S] ('0 [+] '1)).([n], [m]) = (([S] [n]) [+] [m] [=] [S] ([n] [+] [m]))). {
      simpl.
      auto.
    }
    rewrite <- H0.
    apply fal_R2.
    AX. apply PLUS.
Qed.

Instance N : Model L := {
    V := nat;
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
  apply Val_s_imp with (s0 := fun n => Valt N s (([0]; \0) n)). {
    apply functional_extensionality.
    intros.
    destruct x.
    simpl. auto.
    simpl. auto.
  }
  auto.
  specialize (H2 t).
  apply H2 in IHt.
  apply lp_iff1 in IHt.
  apply Val_s_imp with (s0 := fun n => Valt N (t; s) (([S] '0 .; \0) n)). {
  apply functional_extensionality.
  intros.
  destruct x.
  simpl. auto.
  simpl. auto.
  }
  auto.
Qed.
