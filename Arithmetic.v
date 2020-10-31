Require Export Arith.
Require Export Lia.
Require Export FOPL.FOPL.
Require Export FOPL.Deduction.
Require Export FOPL.SetoidL.

Set Implicit Arguments.

Inductive fc0A :=.
Inductive fc1A := ScA.
Inductive fc2A := plA | mlA.
Inductive pd0A :=.
Inductive pd1A :=.
Inductive pd2A := lelA.
Instance L : Lang := {fc0 := fc0A; fc1 := fc1A; fc2 := fc2A; pd0 := pd0A; pd1 := pd1A; pd2 := pd2A}.

Notation "a [+] b" := (@Fc2 L plA a b) (at level 9, right associativity).
Notation "a [*] b" := (@Fc2 L mlA a b) (at level 8, right associativity).
Notation "a [<=] b" := (@Pd2 L lelA a b) (at level 60, right associativity).
Notation "[S]" := (@Fc1 L ScA).
Notation "a [=/=] b" := ([~] a [=] b) (at level 60, no associativity).

Fixpoint innerNat (n0 : nat) : LC := 
  match n0 with
  | 0 => [O]
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
  | NEQ0S : Q ([fal][0][=/=][S]'0)
  | SINJ  : Q ([fal][fal][S]'0[=][S]'1[->]'0[=]'1)
  | PRED  : Q ([fal][0][=/=]'0[->][ext]'1[=][S]'0)
  | PL0   : Q ([fal][0][+]'0[=]'0)
  | PLUS  : Q ([fal][fal]([S]'0)[+]'1[=][S]('0[+]'1))
  | ML0   : Q ([fal][0][*]'0[=][0])
  | MULT  : Q ([fal][fal]([S]'0)[*]'1[=]('0[*]'1)[+]'1)
  | LE    : Q ([fal][fal]'0[<=]'1[<->][ext]'1[+]'0[=]'2).
  
Inductive PA : Th :=
  | PA_Q  : forall p, Q p -> PA p
  | IND   : forall p, PA (p.([0]) [->] ([fal] p [->] p..([S] '0)) [->] [fal] p).

Lemma PLUS0 : forall c d, Q |- ([S]c)[+]d[=][S](c[+]d).
Proof.
  intros.
  assert ((([S]'0)[+]'1[=][S]('0[+]'1)).(c, d) = (([S]c)[+]d[=][S](c[+]d))).
  simpl. reflexivity.
  rewrite <- H.
  apply fal_R2.
  AX. apply PLUS.
Qed.
  
Lemma MULT0 : forall c d, Q |- ([S]c)[*]d[=]c[*]d[+]d.
Proof.
  intros.
  assert ((([S]'0)[*]'1[=]('0[*]'1)[+]'1).(c, d) = (([S]c)[*]d[=]c[*]d[+]d)).
  simpl. reflexivity.
  rewrite <- H.
  apply fal_R2.
  AX. apply MULT.
Qed.

Lemma le_replace : forall T c d, 
  (T |- [fal][fal]'0[<=]'1[<->][ext]'1[+]'0[=]'2) -> 
  ([ext](sfc c)[+]'0[=](sfc d)) ==(T) (c[<=]d).
Proof.
  intros.
  assert(T |- c[<=]d[<->][ext](sfc c)[+]'0[=](sfc d)).
  - assert((('0[<=]'1)[<->]([ext]'1[+]'0[=]'2)).(c,d) = (c[<=]d[<->][ext](sfc c)[+]'0[=](sfc d))).
    simpl.
    reflexivity.
    rewrite <- H0.
    apply fal_R2.
    auto.
  - symmetry. auto.
Qed.

Lemma pred_replace : forall c, ([0][=/=]c) ==(Q) ([ext](sfc c)[=][S]'0).
Proof.
  intros.
  assert(Q |- [0][=/=]c[<->][ext](sfc c)[=][S]'0).
  - SPLIT.
    assert(([0][=/=]'0[->][ext]'1[=][S]'0).(c) = ([0][=/=]c[->][ext](sfc c)[=][S]'0)).
    simpl. reflexivity.
    rewrite <- H.
    apply fal_R.
    AX. apply PRED.
    apply ext_L.
    assert([0][=/=](sfc c) = sf([0][=/=]c)).
    unfold sf, sfc. simpl. reflexivity.
    rewrite <- H.
    apply contrad_elim.
    TRANS ([0][=](sfc c)).
    INTRO.
    apply pNNPP. AX.
    INTRO.
    MP ([0][=/=][S]'0).
    WL.
    assert(([0][=/=][S]'0).('0) = [0][=/=][S]'0).
    simpl. reflexivity.
    rewrite <- H0.
    apply fal_R.
    AX.
    apply prsfT.
    simpl. auto.
    apply NEQ0S.
    assert(forall t, ('0[=/=][S]'1).(t) = t[=/=][S]'0).
    intros.
    simpl. reflexivity.
    repeat rewrite <- H0.
    apply deduction_inv.
    AX.
  - auto.
Qed.

Lemma plus_compl : forall n m, Q |- [n][+][m][=][n + m].
Proof.
  intros.
  induction n.
  + simpl.
    assert (([0] [+] '0 [=] '0).([m]) = ([O] [+] [m] [=] [m])).
    simpl.
    auto.
    rewrite <- H.
    apply fal_R.
    AX. apply PL0.
  + simpl.
    apply eql_trans with (u:=([S][n][+][m])).
    apply PLUS0.
    REWRITEl IHn.
    AX.
Qed.

Lemma mult_compl : forall n m, Q |- [n][*][m][=][n * m].
Proof.
  intros.
  induction n.
  + simpl.
    assert (([0][*]'0[=][0]).([m]) = ([O][*][m][=][O])).
    simpl. auto.
    rewrite <- H.
    apply fal_R.
    AX. apply ML0.
  + simpl.
    apply eql_trans with (u:=([n][*][m][+][m])).
    apply MULT0.
    apply eql_trans with (u:=([n*m][+][m])).
    REWRITEl IHn. AX.
    assert(m + n*m = n*m + m). lia.
    rewrite -> H.
    apply plus_compl.
Qed.

Lemma le_compl : forall n m, n <= m -> (Q |- [n][<=][m]).
Proof.
  intros.
  rewrite <- le_replace.
  unfold sfc.
  repeat rewrite <- IN_rewc.
  EXISTS [m - n].
  simpl.
  repeat rewrite <- IN_rewc.
  assert (m = n + (m - n)).
  lia.
  rewrite -> H0 at 2.
  apply plus_compl.
  AX. apply LE.
Qed.
