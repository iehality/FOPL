Require Import Arith.
Require Import Lia.
Require Export FOPL.FOPL.
Require Export FOPL.Deduction.
Require Export FOPL.SetoidL.
Require Export FOPL.Tactics.

Definition theory {L : Lang} (T : Th) := fun p => T ||- p.
Definition uniT {L : Lang} (T U : Th) := fun x => T x \/ U x.
Notation "T :\/ U" := (uniT T U) (at level 71, left associativity).

Definition Null {L : Lang} : Th := fun _ => False.
Definition null {L : Lang} (T : Th) := forall p, ~ T p.

Fixpoint Fal {L : Lang} n0 p :=
  match n0 with
  | 0 => p
  | S n => [fal](Fal n p)
  end.

Section deduction_facts2.
  Variable L : Lang.

  Lemma nullNull : null Null.
  Proof.
    unfold null, Null.
    auto.
  Qed.

  Lemma nullT_nullsfT : forall T, null (sfT T) <-> null T.
  Proof.
    unfold null, sfT.
    intros.
    split.
    intros.
    specialize(H (sf p)).
    contradict H.
    rewrite alt_sf.
    auto.
    intros. intro.
    destruct H0.
    destruct H0.
    specialize (H (alt p)).
    contradiction.
  Qed.

  Lemma null_sfT : forall T, null T -> T ≡ (sfT T).
  Proof.
    intros.
    unfold eqvT, incT.
    split.
    intros.
    specialize (H p).
    contradiction.
    intros.
    rewrite <- nullT_nullsfT in H.
    specialize(H p).
    contradiction.
  Qed.

  Lemma fal_Fal : forall p n, [fal] Fal n p = Fal n ([fal] p).
  Proof.
    induction n.
    simpl. auto.
    simpl.
    rewrite IHn.
    auto.
  Qed.

  Lemma Genp_ps : forall T p s, T ||- (Fal (Ar p) p) [->] p.[s].
  Proof.
    assert(forall T n p s, Ar p <= n -> T ||- (Fal n p) [->] p.[s]).
    - induction n.
      + simpl.
        intros.
        rewrite <- sentence_rew.
        AX.
        lia.
      + simpl.
        intros.
        rewrite fal_Fal.
        TRANS (([fal]p).[fun x :nat => s (S x)]).
        apply IHn.
        simpl. lia.
        simpl.
        INTRO.
        Tpp.
        SPECIALIZE H0 (s 0).
        rewrite <- nested_rew in H0.
        assert(p.[ fun x => rewc (s 0; \0) (('0; fun x0 => sfc (s (S x0))) x)] = p.[s]). {
          apply rew_rew. unfold sfc.
          intros. simpl.
          destruct n0.
          simpl. auto.
          simpl.
          rewrite <- nested_rewc.
          simpl.
          symmetry.
          apply rewc_id.
        }
        rewrite H1 in H0.
        auto.
    - intros.
      apply H.
      lia.
  Qed.

  Lemma Null_psfp : forall T p, null T -> (T ||- p) -> (T ||- sf p).
  Proof.
    intros.
    assert(forall n, T ||- Fal n p).
    - induction n.
      simpl. auto.
      simpl.
      GEN.
      apply TInclusion with (T:=T).
      apply null_sfT. auto.
      auto.
    - MP (Fal (Ar p) p). auto.
      unfold sf.
      apply Genp_ps.
  Qed.

  Inductive Array (f : nat -> LP) (n0 : nat) : Th := 
  | array : forall n, n < n0 -> Array f n0 (f n).

  Fixpoint Sum (f : nat -> LP) (n0 : nat) : Th := 
    match n0 with
    | 0 => Null
    | S n => (Sum f n) :+ (f n)
    end.

  Lemma Sump : forall f n p, (Sum f n p) -> exists m, m < n /\ p = f m.
  Proof.
    induction n.
    - simpl. intros.
      destruct H.
    - simpl.
      intros.
      destruct H.
      apply IHn in H.
      destruct H as [n0].
      destruct H.
      exists n0. auto.
      exists n. auto.
  Qed. 

  Lemma Sump_inv : forall f n m, m < n -> Sum f n (f m).
  Proof.
    induction n.
    - simpl. intros.
      lia.
    - simpl.
      intros.
      unfold addT.
      unfold lt in H.
      apply le_S_n in H.
      apply le_lt_or_eq in H.
      destruct H.
      left.
      auto.
      right.
      auto.
  Qed.

  Lemma sfSumsfp : forall f n p, (Sum f n ||- p) -> (sfT (Sum f n) ||- sf p).
  Proof.
    induction n.
    - simpl. intros.
      apply TInclusion with (T:=Null).
      unfold incT, Null, sfT.
      intros. 
      contradiction.
      apply Null_psfp.
      apply nullNull.
      auto.
    - simpl. intros.
      apply sf_dsb.
      apply deduction_inv.
      assert(sf(f n [->] p) = sf(f n)[->]sf p). unfold sf. simpl. auto.
      rewrite <- H0.
      apply IHn.
      INTRO.
      auto.
  Qed.

  Lemma sfTSum : forall f n p, (Sum (fun x => sf (f x)) n ||- p) -> (sfT (Sum f n) ||- p).
  Proof.
    induction n.
    - simpl.
      intros.
      apply TInclusion with (T:=Null).
      apply null_sfT.
      apply nullNull.
      auto.
    - simpl.
      intros.
      apply sf_dsb.
      apply deduction_inv.
      apply IHn.
      INTRO.
      auto.
  Qed.

  Lemma seq_comp : 
    forall f0 f1 n0 n1, 
    let f := (fun x : nat => if x <? n0 then f0 x else f1 (x - n0)) in 
    Sum f0 n0 ⊆ Sum f (n0 + n1) /\
    Sum f1 n1 ⊆ Sum f (n0 + n1).
  Proof.
    intros.
    unfold incT.
    split.
    - intros.
      apply Sump in H.
      destruct H as [m].
      destruct H.
      assert(f m = f0 m). {
        rewrite <- Nat.ltb_lt in H.
        unfold f.
        rewrite H.
        auto.
      }
      rewrite H0.
      rewrite <- H1.
      apply Sump_inv.
      lia.
    - intros.
      apply Sump in H.
      destruct H as [m].
      destruct H.
      assert(f (n0 + m) = f1 m). {
        assert(n0 + m <? n0 = false).
        rewrite <- Bool.not_true_iff_false.
        intro.
        rewrite Nat.ltb_lt in H1.
        lia.
        unfold f.
        rewrite H1.
        assert(n0 + m - n0 = m). lia.
        rewrite H2.
        auto.
      }
      rewrite H0.
      rewrite <- H1.
      apply Sump_inv.
      lia.
  Qed.

  Lemma proof_compact : forall T p, (T ||- p) -> exists f n, (Sum f n ⊆ T) /\ (Sum f n ||- p).
  Proof.
    assert(forall T p, (T ||- p) -> exists f n, (forall m, m < n -> T (f m)) /\ (Sum f n ||- p)).
    intros.
    induction H.
    - destruct IHprovable as [f]. 
      destruct H0 as [n].
      destruct H0.
      unfold sfT in H0.
      exists (fun n => alt (f n)).
      exists n.
      split.
      intros.
      specialize (H0 m).
      destruct H0.
      auto.
      auto.
      GEN.
      apply sfTSum.
      apply TInclusion with (T:=Sum f n). {
        unfold incT. intros.
        apply Sump in H2.
        destruct H2 as [m].
        destruct H2.
        pose (s := fun x => sf (alt (f x))).
        fold s.
        assert(s m = f m).
        apply H0. auto.
        rewrite H3.
        rewrite <- H4.
        apply Sump_inv. auto.
      }
      auto.
    - destruct IHprovable1 as [f0].
      destruct H1 as [n0].
      destruct H1.
      destruct IHprovable2 as [f1]. 
      destruct H3 as [n1].
      destruct H3.
      pose (f := (fun x : nat => if x <? n0 then f0 x else f1 (x - n0))).
      exists f. exists (n0 + n1).
      split.
      + intros.
        unfold f.
        assert(lem := classic (m <? n0 = true)). destruct lem.
        rewrite H6. apply H1.
        rewrite <- Nat.ltb_lt. auto.
        rewrite Bool.not_true_iff_false in H6.
        rewrite H6. apply H3.
        rewrite <- Bool.not_true_iff_false in H6.
        apply NNPP.
        contradict H6.
        rewrite Nat.ltb_lt. lia.
      + assert(Sum f0 n0 ⊆ Sum f (n0 + n1) /\ Sum f1 n1 ⊆ Sum f (n0 + n1)). {
          unfold f. apply seq_comp.
        }
        destruct H5.
        MP p.
        apply TInclusion with (T:=Sum f0 n0). auto. auto. 
        apply TInclusion with (T:=Sum f1 n1). auto. auto.
    - exists(fun _ => p).
      exists 1.
      split. auto.
      simpl. AX.
    - exists(fun _ => [O][=][O]).
      exists 0.
      split. lia.
      AX.
    - exists(fun _ => [O][=][O]).
      exists 0.
      split. lia.
      AX.
    - exists(fun _ => [O][=][O]).
      exists 0.
      split. lia.
      AX.
    - exists(fun _ => [O][=][O]).
      exists 0.
      split. lia.
      AX.
    - exists(fun _ => [O][=][O]).
      exists 0.
      split. lia.
      AX.
    - exists(fun _ => [O][=][O]).
      exists 0.
      split. lia.
      AX.
    - exists(fun _ => [O][=][O]).
      exists 0.
      split. lia.
      AX.
    - exists(fun _ => [O][=][O]).
      exists 0.
      split. lia.
      AX.
    - intros.
      specialize (H T p H0).
      destruct H as [f]. 
      destruct H as [n].
      exists f. 
      exists n.
      unfold incT.
      destruct H.
      split.
      intros.
      apply Sump in H2. destruct H2. 
      destruct H2.
      rewrite H3. auto.
      auto. 
  Qed.

  Lemma sfT_inc : forall T U, (T ⊆ U) -> (sfT T ⊆ sfT U).
  Proof.
    unfold sfT, incT.
    intros.
    destruct H0.
    auto.
  Qed.

  Lemma sf_add : forall T p, (T ||- p) -> (sfT T ||- sf p).
  Proof.
    intros.
    apply proof_compact in H.
    destruct H as [f].
    destruct H as [n].
    destruct H.
    apply sfSumsfp in H0.
    apply TInclusion with (T:=sfT (Sum f n)).
    apply sfT_inc. auto.
    auto.
  Qed.

  Lemma sfT_MP : forall T p q, (T ||- p) -> (sfT T :+ sf p ||- q) -> (sfT T ||- q).
  Proof.
    intros.
    MP (sf p).
    apply sf_add. auto.
    INTRO.
    auto.
  Qed. 
  
  Lemma fal_repl : forall T p, 
    ([fal][fal]p) ==(T) ([fal][fal]p.['1;('0;fun x => '(S (S x)))]).
  Proof.
    assert(forall T p, T ||- ([fal][fal]p)[->]([fal][fal]p.['1;('0;fun x => '(S (S x)))])).
    - intros.
      INTRO.
      GEN.
      GEN.
      assert(p.['0;('1;fun x => '(4 + x))].('1, '0) = p.['1;('0;fun x => '(S (S x)))]). {
        rewrite <- nested_rew.
        apply rew_rew.
        intros.
        destruct n.
        auto.
        destruct n.
        auto. auto.
      }
      rewrite <- H.
      apply fal_R2.
      assert(sf (sf ([fal][fal]p)) = ([fal][fal]p.['0; ('1; fun x => '(4 + x))])). {
        unfold sf. simpl.
        apply fal_eq.
        apply fal_eq.
        rewrite <- nested_rew.
        apply rew_rew.
        intros. unfold sfc. simpl.
        destruct n. auto.
        destruct n. auto.
        auto.
      }
      rewrite <- H0.
      AX.
    - intros.
      SPLIT.
      auto.
      assert(p = p.['1;('0;fun x => '(S (S x)))].['1;('0;fun x => '(S (S x)))]). {
        rewrite -> rew_id at 1.
        rewrite <- nested_rew.
        apply rew_rew.
        intros.
        destruct n. auto. simpl.
        destruct n. auto.
        auto.
      }
      rewrite -> H0 at 2.
      auto.
  Qed.

  Lemma neq_symm : forall T t u, (T ||- t[=/=]u) -> (T ||- u[=/=]t).
  Proof.
    intros.
    RAA (t[=]u).
    SYMMETRY. AX.
    WL. auto.
  Qed.
  
End deduction_facts2.

Ltac MPsf h := repeat WL; apply (@sfT_MP _ h _).