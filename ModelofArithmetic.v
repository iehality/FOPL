Require Import Bool.
Require Import FOPL.Semantics.
Require Import FOPL.Arithmetic.
Require Import FOPL.Hierarchy.

(**)
Lemma imp_nor : forall p q : Prop, (p -> q) -> (~ p \/ q).
Proof.
  intros.
  assert (em := classic p). destruct em.
  auto.
  auto.
Qed. 

Lemma nimp_andn : forall p q : Prop, ~ (p -> q) -> (p /\ ~ q).
Proof.
  intros.
  intros.
  split.
  apply NNPP. 
  contradict H.
  intros.
  contradiction.
  auto.
Qed. 

Lemma nat_leq : forall (p : nat -> nat -> Prop), 
  (forall n m, p n (S n + m)) -> 
  (forall n m, n < m -> p n m).
Proof.
  intros.
  specialize(H n (m - S n)).
  assert(m=S n + (m - S n)).
  lia.
  rewrite H1.
  auto.
Qed.
(**)

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

Lemma PA_Soundness : forall p, (PA ||- p) -> (N |= p).
Proof.
  assert (s:=Soundness).
  unfold SValid in s.
  intros.
  apply s with (T:=PA).
  auto.
  apply NPA.
Qed.

Lemma Q_PA : Q ⊆ PA.
Proof.
  unfold incT.
  intros.
  apply PA_Q.
  auto.
Qed.

Lemma Q_Soundness : forall p, (Q ||- p) -> (N |= p).
Proof.
  intros.
  apply PA_Soundness.
  apply TInclusion with (T := Q).
  apply Q_PA.
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

Lemma  sfTQQ : sfT Q ≡ Q.
Proof.
  unfold sfT, eqvT, incT.
  split.
  - intros.
    destruct H.
    unfold sf in H.
    destruct H0.
    simpl in H. rewrite <- H. QAX0.
    simpl in H. rewrite <- H. QAX0.
    simpl in H. rewrite <- H. QAX0.
    simpl in H. rewrite <- H. QAX0.
    simpl in H. rewrite <- H. QAX0.
    simpl in H. rewrite <- H. QAX0.
    simpl in H. rewrite <- H. QAX0.
    simpl in H. rewrite <- H. QAX0.
  - intros.
    unfold sf.
    destruct H.
    simpl. split. auto. QAX0.
    simpl. split. auto. QAX0.
    simpl. split. auto. QAX0. 
    simpl. split. auto. QAX0. 
    simpl. split. auto. QAX0. 
    simpl. split. auto. QAX0. 
    simpl. split. auto. QAX0.
    simpl. split. auto. QAX0.
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
  assert(m < n). lia.
  apply nat_leq with (p:=fun x y => Q ||- [~] [y] [<=] [x]).
  - intros.
    rewrite <- le_replace.
    unfold sf, sfc. simpl. repeat rewrite IN_rewc.
    unfold ext.
    apply pNN.
    induction n0.
    + simpl.
      GEN.
      apply TInclusion with (T:=Q).
      apply sfTQQ.
      rewrite PLUS0 at 1.
      assert(Q ||- [fal][0][=/=][S]'0). QAX.
      SPECIALIZE H1 ([m0][+]'0).
      apply neq_symm. auto.
    + simpl.
      GEN.
      apply TInclusion with (T:=Q).
      apply sfTQQ.
      rewrite PLUS0 at 1.
      SPECIALIZE IHn0 ('0).
      repeat rewrite IN_rewc in IHn0.
      RAA (([S] [n0 + m0]) [+] '0 [=] [n0]).
      apply deduction_inv.
      assert(si : Q ||- [fal][fal][S]'0[=][S]'1[->]'0[=]'1). QAX.
      SPECIALIZE2 si (([S][n0 + m0]) [+] '0) ([n0]). auto.
      WL. auto.
    + QAX.
  - auto.
Qed.

Lemma Delta0_term_complete : forall t s, Art t = 0 -> t ==[Q] [Valt N s t].
Proof.
  unfold equiv. simpl. unfold preq.
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
    apply (IHt s) in H.
    REWRITE_r H.
    AX.
  - simpl.
    intros.
    apply max_0 in H. destruct H.
    apply (IHt1 s) in H.
    apply (IHt2 s) in H0.
    REWRITE H.
    REWRITE H0.
    destruct f.
    apply plus_compl.
    apply mult_compl.
Qed.

Lemma Delta0_complete : forall p, Delta0 p -> (N |= p) -> (Q ||- p).
Proof.
  assert(forall p s, Ar p = 0 -> Is_true (delta0 p) -> (Valp N s p -> (Q ||- p)) /\ (~ Valp N s p -> (Q ||- [~]p))).
  - unfold models, Delta0.
    intros.
    induction p.
    + simpl in H.
      apply max_0 in H.
      destruct H.
      split.
      * simpl.
        intros.
        rewrite (Delta0_term_complete _ s).
        rewrite (Delta0_term_complete l0 s).
        rewrite H2.
        AX.
        auto. auto.
      * simpl.
        intros.
        rewrite (Delta0_term_complete _ s).
        rewrite (Delta0_term_complete l0 s).
        apply neq_compl. auto.
        auto. auto.
    + destruct p.
    + destruct p.
    + destruct p.
      simpl in H.
      apply max_0 in H.
      destruct H.
      simpl.
      split.
      * intros.
        rewrite (Delta0_term_complete _ s).
        rewrite (Delta0_term_complete l0 s).
        apply le_compl. auto.
        auto. auto.
      * intros.
        rewrite (Delta0_term_complete _ s).
        rewrite (Delta0_term_complete l0 s).
        apply nle_compl. auto.
        auto. auto.
    + simpl in H.
      apply max_0 in H.
      destruct H.
      simpl in H0.
      apply andb_prop_elim in H0.
      destruct H0.
      simpl.
      split.
      * intros.
        apply imp_nor in H3.
        destruct H3.
        MP ([~]p1).
        apply IHp1.
        auto. auto. auto.
        INTRO. INTRO.
        apply explosion0 with (p:=p1). AX. AX.
        MP p2.
        apply IHp2.
        auto. auto. auto.
        AX.
      * intros.
        apply nimp_andn in H3.
        destruct H3.
        assert(Q ||- p1[/\]([~]p2)).
        SPLIT.
        apply IHp1.
        auto. auto. auto.
        apply IHp2.
        auto. auto. auto.
        unfold andl in H5.
        rewrite (TNNPP _ _ p2).
        auto.
    + simpl in H.
      simpl in H0.
      simpl.
      split.
      * intros.
        apply IHp.
        auto. auto. auto.
      * intros.
        apply pNN.
        apply IHp.
        auto. auto. apply NNPP. auto.
    + simpl in H.
      simpl in H0.
      contradiction.
  - intros.
    destruct H0.
    destruct H2 as [q].
    destruct H2.
    destruct H3.
    DESTRUCT H4.
    MP q.
    apply H with (s:=id).
    auto.
    auto.
    assert(N |= p [->] q).
    apply Q_Soundness. auto.
    apply H6.
    apply H1.
    auto.
Qed.
    
