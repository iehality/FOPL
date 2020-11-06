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

Definition id {A : Type} (x : A) := x.

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

Lemma Valn_n : 
  forall n s, Valt N s [n] = n.
Proof.
  induction n.
  simpl. intros. auto.
  simpl.
  intros.
  rewrite(IHn).
  auto.
Qed.

Lemma PA_Soundness : forall p, 
  (PA ||- p) -> (N |= p).
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

Lemma Q_Soundness : forall p, 
  (Q ||- p) -> (N |= p).
Proof.
  intros.
  apply PA_Soundness.
  apply TInclusion with (T := Q).
  apply Q_PA.
  auto.
Qed.

Lemma ConPA : Consis PA.
Proof.
  unfold Consis.
  intro.
  destruct H as [p].
  destruct H.
  assert(N |= p).
  apply PA_Soundness. auto.
  assert(N |= [~] p).
  apply PA_Soundness. auto.
  unfold models in H1.
  unfold models in H2.
  specialize (H1 id).
  specialize (H2 id).
  simpl in H2.
  contradiction.
Qed.

Lemma ConQ : Consis Q.
Proof.
  unfold Consis.
  intro.
  destruct H as [p].
  destruct H.
  assert(ConPA:=ConPA).
  destruct ConPA.
  exists p.
  split.
  apply TInclusion with (T:=Q). apply Q_PA.
  auto.
  apply TInclusion with (T:=Q). apply Q_PA.
  auto.
Qed.

Lemma max_0 : forall n m, 
  max n m = 0 -> (n = 0 /\ m = 0).
Proof.
  intros.
  split.
  assert(H0:=Nat.le_max_l n m).
  lia.
  assert(H0:=Nat.le_max_r n m).
  lia.
Qed.

Lemma le_replace : forall T c d, 
  (T ||- [fal][fal]'0[<=]'1[<->][ext]'1[+]'0[=]'2) -> 
  ([ext](sfc c)[+]'0[=](sfc d)) ==(T) (c[<=]d).
Proof.
  intros.
  assert(T ||- c[<=]d[<->][ext](sfc c)[+]'0[=](sfc d)).
  - assert((('0[<=]'1)[<->]([ext]'1[+]'0[=]'2))/(c,d) = (c[<=]d[<->][ext](sfc c)[+]'0[=](sfc d))).
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
  - fsplit.
    assert(([0][=/=]'0[->][ext]'1[=][S]'0)/(c) = ([0][=/=]c[->][ext](sfc c)[=][S]'0)).
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
    ftrans ([0][=](sfc c)).
    fintro.
    apply pNNPP. auto.
    fintro.
    MP (([0][=/=][S]'0)/('0)).
    apply fal_R. auto.
    simpl.
    apply contrad_add.
    fintro.
    frewrite_by_1r.
    frewrite_by_2.
    auto.
  - symmetry.
    auto. 
Qed.

Lemma plus_compl : forall n m, [n][+][m] ==[Q] [n + m].
Proof.
  intros.
  unfoldeq.
  induction n.
  + simpl.
    assert (([0] [+] '0 [=] '0)/([m]) = ([O] [+] [m] [=] [m])).
    simpl.
    auto.
    rewrite <- H.
    apply fal_R.
    auto.
  + simpl.
    foldeqh IHn.
    rewrite PLUS0.
    rewrite IHn.
    auto.
Qed.

Lemma mult_compl : forall n m, [n][*][m] ==[Q] [n * m].
Proof.
  intros.
  unfoldeq.
  induction n.
  + simpl.
    assert (([0][*]'0[=][0])/([m]) = ([O][*][m][=][O])).
    simpl. auto.
    rewrite <- H.
    apply fal_R.
    auto.
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
  repeat rewrite IN_rewc.
  fexists [m - n].
  simpl.
  repeat rewrite IN_rewc.
  assert (m = n + (m - n)).
  lia.
  rewrite H0 at 2.
  apply plus_compl.
  auto.
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
    auto.
  - ftrans ([n][+]c[=][n][+]d).
    simpl.
    rewrite PLUS0.
    rewrite PLUS0.
    assert(Q ||- [fal][fal][S]'0[=][S]'1[->]'0[=]'1).
    auto.
    fspecialize2 H ([n][+]c) ([n][+]d).
    auto.
    auto.
Qed.

Lemma neq_compl : forall n m, 
  n <> m -> (Q ||- [n][=/=][m]).
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
    assert(Q ||- [fal][0][=/=][S]'0). auto.
    fspecialize H1 [m].
    auto.
  - apply nat_neq.
    auto.
    intros.
    apply neq_symm. auto.
Qed.

Lemma nle_compl : forall n m, 
  ~ n <= m -> (Q ||- [~][n][<=][m]).
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
      assert(Q ||- [fal][0][=/=][S]'0). auto.
      fspecialize H1 ([m0][+]'0).
      apply neq_symm. auto.
    + simpl.
      GEN.
      apply TInclusion with (T:=Q).
      apply sfTQQ.
      rewrite PLUS0 at 1.
      fspecialize IHn0 ('0).
      repeat rewrite IN_rewc in IHn0.
      RAA (([S] [n0 + m0]) [+] '0 [=] [n0]).
      apply deduction_inv.
      assert(si : Q ||- [fal][fal][S]'0[=][S]'1[->]'0[=]'1). auto.
      fspecialize2 si (([S][n0 + m0]) [+] '0) ([n0]). auto.
      WL. auto.
    + auto.
  - auto.
Qed.

Lemma Delta0_term_complete : forall t s, 
  Art t = 0 -> t ==[Q] [Valt N s t].
Proof.
  unfold equiv. simpl. unfold preq.
  induction t.
  - intros.
    simpl in H.
    lia.
  - intros.
    simpl.
    auto.
  - destruct f.
  - destruct f.
    simpl.
    intros.
    apply (IHt s) in H.
    frewrite_r H.
    auto.
  - simpl.
    intros.
    apply max_0 in H. destruct H.
    apply (IHt1 s) in H.
    apply (IHt2 s) in H0.
    frewrite H.
    frewrite H0.
    destruct f.
    apply plus_compl.
    apply mult_compl.
Qed.

Lemma delta0_complete : forall p, 
  Ar p = 0 -> Is_true(delta0 p) -> (N |= p) -> (Q ||- p).
Proof.
  assert(
    forall p s, Ar p = 0 -> 
    Is_true (delta0 p) -> 
    (Valp N s p -> (Q ||- p)) /\ (~ Valp N s p -> (Q ||- [~]p))
  ).
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
        rewrite (Delta0_term_complete t0 s).
        rewrite H2.
        auto.
        auto. auto.
      * simpl.
        intros.
        rewrite (Delta0_term_complete _ s).
        rewrite (Delta0_term_complete t0 s).
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
        rewrite (Delta0_term_complete t0 s).
        apply le_compl. auto.
        auto. auto.
      * intros.
        rewrite (Delta0_term_complete _ s).
        rewrite (Delta0_term_complete t0 s).
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
        fintros.
        apply explosion0 with (p:=p1). auto. auto.
        MP p2.
        apply IHp2.
        auto. auto. auto.
        auto.
      * intros.
        apply nimp_andn in H3.
        destruct H3.
        assert(Q ||- p1[/\]([~]p2)).
        fsplit.
        apply IHp1.
        auto. auto. auto.
        apply IHp2.
        auto. auto. auto.
        unfold andl in H5.
        rewrite (DNE _ _ p2).
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
    apply H with (s:=id).
    auto. auto. auto.
Qed.

Lemma Delta0_complete : forall p, 
  Delta0 p -> (N |= p) -> (Q ||- p).
Proof.
  intros.
  destruct H.
  destruct H1 as [q].
  destruct H1.
  destruct H2.
  fdestruct H3.
  MP q.
  apply delta0_complete.
  auto.
  auto.
  assert(N |= p [->] q).
  apply Q_Soundness. auto.
  unfold models. intros.
  apply H5.
  apply H0.
  auto.
Qed.

Lemma Sigma1_val : forall p, 
  Ar p <= 1 -> (N |= [ext]p) -> exists n, N |= p/([n]).
Proof.
  unfold models.
  intros.
  specialize(H0 id).
  rewrite M_ext in H0.
  destruct H0.
  exists x.
  intros.
  rewrite <- lp_iff1.
  apply Val_iff with (s0:=(x;id)).
  intros.
  destruct n.
  simpl.
  symmetry. apply Valn_n.
  lia.
  auto.
Qed.

Lemma sigma1_complete : forall p,
  Ar p = 0 -> stSigma 1 p -> (N |= p) -> (Q ||- p).
Proof.
  intros.
  inversion H0.
  - apply delta0_complete.
    auto. auto. auto.
  - rewrite <- H5 in H.
    rewrite <- H5 in H1.
    simpl in H.
    apply Sigma1_val in H1.
    destruct H1 as [m].
    fexists [m].
    apply delta0_complete.
    apply of_constant. lia.
    apply IN_constant.
    inversion H3.
    rewrite delta0_rew.
    auto. auto. lia.
Qed.

Lemma Sigma1_complete : forall p,
  Sigma 1 p -> (N |= p) -> (Q ||- p).
Proof.
  intros.
  destruct H.
  destruct H1 as [q].
  destruct H1.
  destruct H2.
  fdestruct H3.
  MP q.
  apply sigma1_complete.
  auto.
  auto.
  assert(N |= p [->] q).
  apply Q_Soundness. auto.
  unfold models. intros.
  apply H5.
  apply H0.
  auto.
Qed.