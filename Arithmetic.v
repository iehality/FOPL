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

Compute (fal (fal ('0 [+] '1 [=] '1 [+] '0) [->] (fal ('0 [+] '1 [=] '1 [+] '0))..([S] '0))).

Lemma pl_symm : PA |- fal (fal ('0 [+] '1 [=] '1 [+] '0)).
Proof.
  GEN.
  MP (fal (fal ('0 [+] '1 [=] '1 [+] '0) [->] (fal ('0 [+] '1 [=] '1 [+] '0))..([S] '0))).
  GEN.
  INTRO.
  Compute.
  simpl. unfold sfc. simpl.
  GEN.
  apply sf_dsb.
  unfold sf. simpl. unfold sfc. simpl.
  SYMMETRY.
  apply eql_trans with (u := [S] ('0 [+] '1)).
  assert ([S] ('0 [+] '1) [=] )
  MP (fal (fal (([S] '0) [+] '1 [=] [S] ('0 [+] '1)))).
  


