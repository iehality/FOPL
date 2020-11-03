Require Export Arith.
Require Export Lia.
Require Export FOPL.Basic.

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

Lemma PL00 : forall c, [0][+]c ==[Q] c.
Proof.
  intros.
  unfoldeq.
  assert (([0][+]'0[=]'0).(c) = ([0][+]c[=]c)).
  simpl. reflexivity.
  rewrite <- H.
  apply fal_R.
  AX. apply PL0.
Qed.

Lemma PLUS0 : forall c d, ([S]c)[+]d ==[Q] [S](c[+]d).
Proof.
  intros.
  unfoldeq.
  assert ((([S]'0)[+]'1[=][S]('0[+]'1)).(c, d) = (([S]c)[+]d[=][S](c[+]d))).
  simpl. reflexivity.
  rewrite <- H.
  apply fal_R2.
  AX. apply PLUS.
Qed.
  
Lemma MULT0 : forall c d, ([S]c)[*]d ==[Q] c[*]d[+]d.
Proof.
  intros.
  unfoldeq.
  assert ((([S]'0)[*]'1[=]('0[*]'1)[+]'1).(c, d) = (([S]c)[*]d[=]c[*]d[+]d)).
  simpl. reflexivity.
  rewrite <- H.
  apply fal_R2.
  AX. apply MULT.
Qed.

Lemma SINJ0 : forall c d, Q ||- [S]c[=][S]d [->] c[=]d.
Proof.
  intros.
  assert(Q ||- [fal][fal][S]'0[=][S]'1[->]'0[=]'1).
  AX. apply SINJ.
  SPECIALIZE2 H c d.
  auto.
Qed.

Lemma le_replace : forall T c d, 
  (T ||- [fal][fal]'0[<=]'1[<->][ext]'1[+]'0[=]'2) -> 
  ([ext](sfc c)[+]'0[=](sfc d)) ==(T) (c[<=]d).
Proof.
  intros.
  assert(T ||- c[<=]d[<->][ext](sfc c)[+]'0[=](sfc d)).
  - assert((('0[<=]'1)[<->]([ext]'1[+]'0[=]'2)).(c,d) = (c[<=]d[<->][ext](sfc c)[+]'0[=](sfc d))).
    simpl.
    reflexivity.
    rewrite <- H0.
    apply fal_R2.
    auto.
  - symmetry. auto.
Qed.

Lemma pred_replace : forall T c,
  (T ||- [fal][0][=/=][S]'0) ->
  (T ||- [fal][0][=/=]'0[->][ext]'1[=][S]'0) ->
  (([ext](sfc c)[=][S]'0) ==(T) ([0][=/=]c)).
Proof.
  intros.
  assert(T ||- [0][=/=]c[<->][ext](sfc c)[=][S]'0).
  - SPLIT.
    assert(([0][=/=]'0[->][ext]'1[=][S]'0).(c) = ([0][=/=]c[->][ext](sfc c)[=][S]'0)).
    simpl. reflexivity.
    rewrite <- H1.
    apply fal_R.
    auto.
    MPI ([fal][0][=/=][S]'0). auto.
    apply ext_L.
    apply sf_dsb. unfold sf at 1. simpl.
    assert([0][=/=](sfc c) = sf([O][=/=]c)).
    unfold sf, sfc. simpl. reflexivity.
    rewrite <- H1.
    apply contrad_elim.
    TRANS ([0][=](sfc c)).
    INTRO.
    apply pNNPP. AX.
    INTRO.
    MP (([0][=/=][S]'0).('0)).
    apply fal_R. AX.
    simpl.
    apply contrad_add.
    INTRO.
    REW_at_1r.
    REW_at_2.
    AX.
  - symmetry.
    auto. 
Qed.

Notation 𝒙 := ('0).
Notation 𝒚 := ('1).
Notation 𝒛 := ('2).

Lemma le_asymm : forall x y, Q ||- x[<=]y [->] y[<=]x [->] x[=]y.
Proof.
  intros.
  rewrite <- le_replace.
  rewrite <- le_replace.
  apply ext_L.
  INTRO.
  assert(↑ (([∃] (sfc y) [+] 𝒙 [=] sfc x)) = TRUE).
  unfold ext, sf, sfc.
  simpl. fold ext.
  unfold ext, sf, sfc.
  simpl.
  rewrite <- nested_rewc. 
  rewrite <- nested_rewc.
  simpl. 
  fold ext.
  assert(sf (([ext] (sfc y)[+]'0[=]sfc x)[->]x[=]y) = ([ext](sfc (sfc y))[+]'0[=]sfc (sfc x))[->](sfc x)[=](sfc y)). {
    unfold ext, sf, sfc.
    simpl.
    unfold ext, sf, sfc.
    simpl.

    reflexivity.

  unfold sf. simpl.
  apply ext_L.
  INTRO.\

Lemma plus_compl : forall n m, [n][+][m] ==[Q] [n + m].
Proof.
  intros.
  unfoldeq.
  induction n.
  + simpl.
    assert (([0] [+] '0 [=] '0).([m]) = ([O] [+] [m] [=] [m])).
    simpl.
    auto.
    rewrite <- H.
    apply fal_R.
    AX. apply PL0.
  + simpl.
    foldeqh IHn.
    rewrite PLUS0.
    rewrite IHn.
    AX.
Qed.

Lemma mult_compl : forall n m, [n][*][m] ==[Q] [n * m].
Proof.
  intros.
  unfoldeq.
  induction n.
  + simpl.
    assert (([0][*]'0[=][0]).([m]) = ([O][*][m][=][O])).
    simpl. auto.
    rewrite <- H.
    apply fal_R.
    AX. apply ML0.
  + simpl.
    rewrite MULT0.
    foldeqh IHn.
    rewrite IHn.
    assert(m + n*m = n*m + m). lia.
    rewrite -> H.
    apply plus_compl.
Qed.

Lemma le_compl : forall n m, n <= m -> (Q ||- [n][<=][m]).
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

Lemma nat_neq : forall (p : nat -> nat -> Prop), 
  (forall n m, p n (S n + m)) -> 
  (forall n m, p (S n + m) n) -> 
  (forall n m, n <> m -> p n m).
Proof.
  intros.
  apply nat_total_order in H1.
  destruct H1.
  - specialize(H n (m - S n)).
    assert(m=S n + (m - S n)).
    lia.
    rewrite H2.
    auto.
  - specialize(H0 m (n - S m)).
    assert(n = S m + (n - S m)).
    lia.
    rewrite H2.
    auto.
Qed.

Lemma plus_inj : forall c d n, Q ||- [n][+]c[=][n][+]d[->]c[=]d.
Proof.
  induction n.
  - assert(forall x, [0][+]x ==[Q] x).
    apply PL00.
    rewrite H.
    rewrite H.
    AX.
  - TRANS ([n][+]c[=][n][+]d).
    simpl.
    rewrite PLUS0.
    rewrite PLUS0.
    assert(Q ||- [fal][fal][S]'0[=][S]'1[->]'0[=]'1).
    AX. apply SINJ.
    SPECIALIZE2 H ([n][+]c) ([n][+]d).
    auto.
    auto.
Qed.

Lemma O0 : [O] ==[Q] [0].
Proof.
  reflexivity.
Qed.

Lemma neq_compl : forall n m, n <> m -> (Q ||- [n][=/=][m]).
Proof.
  assert(forall n m : nat, Q ||- [n] [=/=] [S n + m]).
  - intros.
    assert([S n + m] ==[Q] [n][+][S m]). symmetry.
    assert(n + S m = S n + m). lia.
    rewrite <- H. apply plus_compl.
    rewrite H.
    assert([n] ==[Q] [n][+][0]). symmetry.
    assert(n = n + 0). lia.
    rewrite H0 at 2.
    apply plus_compl.
    rewrite H0 at 1.
    simpl.
    RAA ([O][=][S][m]).
    apply deduction_inv.
    apply plus_inj.
    WL.
    rewrite O0.
    assert(Q ||- [fal][0][=/=][S]'0). AX. apply NEQ0S.
    SPECIALIZE H1 [m].
    auto.
  - apply nat_neq.
    auto.
    intros.
    apply neq_symm. auto.
Qed.

Lemma nle_compl : forall n m, ~ n <= m -> (Q ||- [~][n][<=][m]).
Proof.
  intros.
  assert(m <= n /\ n <> m). lia. destruct H0.
  apply NNPP.
  apply le_not_lt.
  assert(forall n m : nat, Q ||- [n] [=/=] [S n + m]).
  - intros.
    assert([S n + m] ==[Q] [n][+][S m]). symmetry.
    assert(n + S m = S n + m). lia.
    rewrite <- H. apply plus_compl.
    rewrite H.
    assert([n] ==[Q] [n][+][0]). symmetry.
    assert(n = n + 0). lia.
    rewrite H0 at 2.
    apply plus_compl.
    rewrite H0 at 1.
    simpl.
    RAA ([O][=][S][m]).
    apply deduction_inv.
    apply plus_inj.
    WL.
    rewrite O0.
    assert(Q ||- [fal][0][=/=][S]'0). AX. apply NEQ0S.
    SPECIALIZE H1 [m].
    auto.
  - apply nat_neq.
    auto.
    intros.
    apply neq_symm. auto.
Qed.
