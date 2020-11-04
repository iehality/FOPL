Require Import Arith.
Require Import Lia.
Require Import FOPL.FOPL.
(* coqc -Q FOPL FOPL FOPL/Deduction.v *)

Set Implicit Arguments.
  
Definition Th {L : Lang} := @LP L -> Prop.
  
  (** * Hilbert Style Deduction System *)

Fixpoint alterablet {L : Lang} (n : nat) (t0 : LC) : bool :=
  match t0 with
  | 'v        => negb (n =? v)
  | Fc1 _ x   => alterablet n x
  | Fc2 _ x y => alterablet n x && alterablet n y
  | _         => true
  end.
  
Fixpoint alterable0 {L : Lang} (n : nat) (p0 : LP) : bool :=
  match p0 with
  | x[=]y     => alterablet n x && alterablet n y
  | Pd1 c x   => alterablet n x
  | Pd2 c x y => alterablet n x && alterablet n y
  | imp p q   => alterable0 n p && alterable0 n q
  | neg p     => alterable0 n p
  | fal p     => alterable0 (S n) p
  | _         => true
  end.

Definition alterable {L : Lang} p := alterable0 0 p.

Lemma alt_sf {L : Lang} : forall p, alt (sf p) = p.
Proof.
  intros.
  unfold alt, sf.
  rewrite <- nested_rew.
  simpl.
  rewrite rew_id.
  auto.
Qed.
  
Inductive sfT {L : Lang} (T : Th) : Th := 
| sfT_intro : forall p, T p -> sfT T (sf p).
Hint Constructors sfT : core.

Notation "⇑ T" := (sfT T) (at level 20).

Inductive provable {L : Lang} (T : Th) : LP -> Prop :=
  | GEN  : forall q, provable (sfT T) q -> provable T (fal q)
  | MP   : forall p q, provable T p -> provable T (p [->] q) -> provable T q
  | Pr0  : forall p, T p -> provable T p
  | Pr1  : forall p q, provable T (p [->] q [->] p)
  | Pr2  : forall p q r, provable T ((p [->] q [->] r) [->] ((p [->] q) [->] (p [->] r)))
  | Pr3  : forall p q, provable T (([~] p [->] [~] q) [->] (q [->] p))
  | Qt0  : forall p t, provable T (fal p [->] p/(t))
  | Qt1  : forall p q, provable T (fal (p [->] q) [->] ((fal p) [->] (fal q)))
  | Qt2  : forall p, provable T (p [->] fal (sf p))
  | Eq0  : forall t, provable T (t [=] t)
  | Eq1  : forall p t u, provable T (t [=] u [->] p/(t) [->] p/(u)).

Hint Resolve Pr1 Pr2 Pr3 Qt0 Qt1 Qt2 Eq0 Eq1 Pr0 : core.

Notation "T ||- p" := (provable T p) (at level 70).

Definition Consis {L : Lang} (T : Th) := ~ exists p, (T ||- p) /\ (T ||- [~]p).

Inductive addT {L : Lang} (T : Th) (p : LP) : Th :=
| appnew : addT T p p
| appdom : forall q, T q -> addT T p q.

Hint Constructors addT : core.

Definition elmT {L : Lang} (T : Th) p := fun x => T x /\ x <> p.
Definition incT {L : Lang} (T U : Th) := forall p, T p -> U p.
Definition eqvT {L : Lang} (T U : Th) := (incT T U) /\ (incT U T).
Notation "T ¦ p" := (addT T p) (at level 69, left associativity).
Notation "T ⊆ U" := (incT T U) (at level 72, left associativity).
Notation "T ≡ U" := (eqvT T U) (at level 72, left associativity).

Definition TRUE {L : Lang} := [O][=][O].  

Section deduction_facts.

  Ltac GEN := apply GEN.
  Ltac MP h := apply (@MP _ _ h _).

  Variable L : Lang.

  Lemma p__p : forall T p, T ||- p [->] p.
  Proof.
    intros.
    MP (p [->] (p [->] p)).
    apply Pr1.
    MP ((p [->] (p [->] p) [->] p)).
    apply Pr1.
    apply Pr2.
  Qed.

  Hint Resolve p__p : core.

  Ltac Prove_by_Pr0 :=
    apply Pr0;
    try repeat (apply appnew || apply appdom).
  
  Ltac AX := (simpl; apply p__p) 
    || apply Pr1 
    || apply Pr2 
    || apply Pr3 
    || apply Qt0 
    || apply Qt1 
    || apply Qt2 
    || apply Eq0 
    || apply Eq1 
    || Prove_by_Pr0; auto.
  
  (** ** Proof facts *)  
  
  Lemma imp_pr : forall T p q, (T ||- p) -> (T ||- q [->] p).
  Proof.
    intros.
    MP p.
    auto.
    auto.
  Qed.
  
  Lemma imp_trans : forall T p q r, (T ||- p [->] q) -> (T ||- q [->] r) -> (T ||- p [->] r).
  Proof.
    intros.
    MP (p [->] q). auto.
    MP (p [->] q [->] r).
    apply imp_pr. auto.
    auto.
  Qed.
  
  Ltac TRANS h := apply imp_trans with (q:=h).
  
  Lemma TInclusion : forall (T U : Th) p, T ⊆ U -> T ||- p -> U ||- p.
  Proof.
    assert (forall (T : Th) p, T ||- p -> forall (U : Th), T ⊆ U -> U ||- p).
    - intros T p H.
      unfold incT.
      induction H.
      + intros.
        apply GEN.
        apply IHprovable.
        intros.
        destruct H1.
        auto.
      + intros.
        MP p.
        auto. auto.
      + intros. auto.
      + intros. auto.
      + intros. auto.
      + intros. auto.
      + intros. auto.
      + intros. auto.
      + intros. auto.
      + intros. auto.
      + intros. auto.
    - intros.
      apply H with (T := T).
      auto.
      auto.
  Qed.
  
  Lemma weakening : forall T p q, (T ||- q) -> (T ¦ p ||- q).
  Proof.
    intros.
    apply TInclusion with (T := T).
    unfold incT. auto.
    auto.
  Qed.
  
  Theorem Deduction : forall T p q, (T ¦ p ||- q) -> (T ||- p [->] q).
  Proof.
    assert (forall T q, (T ||- q) -> (forall p, (elmT T p) ||- p [->] q)).
    - intros T q H.
      induction H.
      + intros.
        specialize (IHprovable (sf p)).
        apply imp_trans with (q := fal (sf p)).
        auto.
        MP (fal (sf p [->] q)).
        GEN.
        apply TInclusion with (T := elmT (sfT T) (sf p)).
        unfold elmT. unfold incT.
        intros.
        destruct H0.
        destruct H0.
        apply sfT_intro.
        split. auto.
        contradict H1.
        rewrite H1.
        auto.
        auto.
        auto.
      + intros.
        MP (p0 [->] p). auto.
        MP (p0 [->] p [->] q). auto.
        auto.
      + intros.
        assert (em := classic (p0 = p)).
        destruct em.
        * rewrite H0.
          auto.
        * apply imp_pr.
          apply Pr0.
          split.
          auto.
          contradict H0.
          symmetry.
          auto.
      + intros.
        apply imp_pr.
        auto.
      + intros.
        apply imp_pr.
        auto.
      + intros.
        apply imp_pr.
        auto.
      + intros.
        apply imp_pr.
        auto.
      + intros.
        apply imp_pr.
        auto.
      + intros.
        apply imp_pr.
        auto.
      + intros.
        apply imp_pr.
        auto.
      + intros.
        apply imp_pr.
        auto.
    - intros.
      assert (em := classic (T p)).
      destruct em.
      + apply imp_pr. 
        apply TInclusion with (T := T ¦ p).
        unfold incT.
        intros.
        destruct H2.
        auto.
        auto.
        auto.
      + apply TInclusion with (T := elmT (T ¦ p) p).
        unfold incT.
        intros. 
        destruct H2.
        destruct H2.
        contradiction.
        auto.
        auto.
  Qed.
  
  Ltac INTRO := apply Deduction.
  
  Lemma sf_dsb0 : forall T p, (sfT T¦ sf p) ⊆ (sfT (T ¦ p)).
  Proof.
    intros.
    unfold incT.
    intros.
    destruct H.
    auto.
    destruct H.
    auto.
  Qed.
  
  Lemma sf_dsb1 : forall T U p, T ⊆ U -> (T ¦ p) ⊆ (U¦ p).
  Proof.
    unfold incT.
    intros.
    destruct H0.
    auto.
    auto.
  Qed.
  
  Lemma sf_dsb : forall T p q, (sfT T ¦ sf p ||- q) -> (sfT (T ¦ p) ||- q).
  Proof.
    intros.
    apply TInclusion with (T := sfT T ¦ sf p).
    apply sf_dsb0.
    auto.
  Qed.

  Lemma MPintro : forall T p q, (T ||- p) -> (T ¦ p ||- q) -> (T ||- q).
  Proof.
    intros.
    MP p. auto.
    INTRO. auto.
  Qed.

  Ltac MPI h := apply MPintro with (p:=h).
  
  Lemma imp_pqrs : forall T p q r s, (T ||- p [->] q [->] r) -> (T ||- r [->] s) -> (T ||- p [->] q [->] s).
  Proof.
    intros.
    MP (p [->] q [->] r). auto.
    MP (p [->] (q [->] r) [->] (q [->] s)).
    apply imp_pr.
    MP (q [->] r [->] s).
    apply imp_pr. auto.
    auto.
    auto.
  Qed.
  
  Lemma explosion : forall T, (~ Consis T) -> forall p, T ||- p.
  Proof.
    intros.
    unfold Consis in H. apply NNPP in H.
    destruct H as [q].
    destruct H.
    MP q. auto.
    MP ([~] p [->] [~] q).
    MP ([~] q).
    auto.
    auto.
    auto.
  Qed.
  
  Lemma p_np_q : forall T p q, T ||- p [->] [~] p [->] q.
  Proof.
    intros.
    INTRO.
    INTRO.
    apply explosion.
    unfold Consis.
    intro.
    contradict H.
    exists p.
    split.
    auto.
    auto.
  Qed.

  Lemma explosion0 : forall T p q, (T ||- p) -> (T ||- [~] p) -> (T ||- q).
  Proof.
    intros.
    apply explosion.
    unfold Consis.
    intro. contradict H1.
    exists p.
    auto.
  Qed.
  
    
  Lemma deduction_inv : forall T p q, (T ||- p [->] q) -> (T ¦ p ||- q).
  Proof.
    intros.
    MP p. auto.
    apply weakening.
    auto.
  Qed.
  
  Lemma pr_NNPP : forall T p, T ||- [~] [~] p [->] p.
  Proof.
    intros.
    INTRO.
    MP ([~] [~] p).
    auto.
    MP ([~] p [->] [~] [~] [~] p).
    MP ([~] [~] [~] [~] p [->] [~] [~] p).
    MP ([~] [~] p).
    auto.
    auto.
    auto.
    auto.
  Qed.
  
  Lemma pr_NN : forall T p, T ||- p [->] [~] [~] p.
  Proof.
    intros.
    MP ([~] [~] [~] p [->] [~] p).
    apply pr_NNPP.
    auto.
  Qed.
  
  Lemma pNNPP : forall T p, (T ||- [~] [~] p) -> (T ||- p).
  Proof.
    intros.
    MP ([~] [~] p).
    auto.
    MP ([~] p [->] [~] [~] [~] p).
    MP ([~] [~] [~] [~] p [->] [~] [~] p).
    MP ([~] [~] p).
    auto.
    auto.
    auto.
    auto.
  Qed.
  
  Lemma pNN : forall T p, (T ||- p) -> (T ||- [~] [~] p).
  Proof.
    intros.
    MP p. auto.
    MP ([~] [~] [~] p [->] [~] p).
    apply pr_NNPP.
    auto.
  Qed.
  
  Lemma neg_intro : forall T p, T ||- (p [->] [~] p) -> (T ||- [~] p).
  Proof.
    intros.
    MP (p [->] [~] p). auto.
    INTRO.
    MP (p [->] [~] p).
    auto.
    MP ([~] [~] p [->] [~] (p [->] [~] p)).
    INTRO.
    apply explosion.
    unfold Consis.
    intro. contradict H0.
    exists p.
    split.
    apply pNNPP. auto.
    MP p.
    apply pNNPP. auto.
    auto.
    auto.
  Qed.

  Lemma RAA : forall T p q, 
    (T ¦ p ||- q) -> (T ¦ p ||- [~] q) -> (T ||- [~] p).
  Proof.
    intros.
    apply neg_intro.
    INTRO.
    apply explosion.
    unfold Consis. 
    intro. contradict H1.
    exists q.
    auto.
  Qed.
  
  Lemma contrad_elim : forall T p q, 
    (T ||- [~] p [->] [~] q) -> (T ||- q [->] p).
  Proof.
    intros.
    MP ([~] p [->] [~] q). auto.
    auto.
  Qed.
  
  Lemma contrad_add : forall T p q, 
    (T ||- p [->] q) -> (T ||- [~] q [->] [~] p).
  Proof.
    intros.
    MP ([~] [~] p [->] [~] [~] q).
    INTRO.
    MP q.
    MP p.
    MP ([~] [~] p). auto.
    apply pr_NNPP.
    apply weakening.
    auto.
    apply pr_NN.
    auto.
  Qed.
  
  Lemma destruct_and : forall T p q, 
    (T ||- p) -> (T ||- q) -> (T ||- p [/\] q).
  Proof.
    unfold andl.
    intros.
    apply neg_intro.
    - INTRO.
      MP q.
      apply weakening.
      auto.
      auto.
      MP ([~] [~] (p [->] [~] q) [->] [~] q).
      apply imp_pr.
      MP p.
      apply weakening.
      auto. auto.
      auto.
  Qed.
  
  Lemma and_destruct : forall T p q, 
    (T ||- p [/\] q) -> ((T ||- p) /\ (T ||- q)).
  Proof.
    unfold andl.
    intros.
    split.
    - MP ([~] (p [->] [~] q)). auto.
      MP ([~] p [->] [~] [~] (p [->] [~] q)).
      INTRO.
      MP (p [->] [~] q).
      INTRO.
      apply explosion0 with (p:=p).
      auto. auto.
      apply pr_NN.
      auto.
    - MP ([~] (p [->] [~] q)). auto.
      MP ([~] q [->] [~] [~] (p [->] [~] q)).
      INTRO.
      MP (p [->] [~] q).
      apply imp_pr. auto.
      apply pr_NN.
      auto.
  Qed.
  
  Lemma destruct_iff : forall T p q, 
    (T ||- p [->] q) -> (T ||- q [->] p) -> (T ||- p [<->] q).
  Proof.
    intros.
    unfold iffl.
    apply destruct_and.
    auto.
    auto.
  Qed.
  
  Ltac SPLIT := apply destruct_iff || apply destruct_and.
  Ltac DESTRUCT h := apply and_destruct in h; destruct h.
  
  Lemma pr_rewrite2 : forall {T} {p0 p1 r}, 
    (T ||- p0 [<->] p1) -> (T ||- p0 [->] r) -> (T ||- p1 [->] r).
  Proof.
    intros.
    DESTRUCT H.
    apply imp_trans with (q := p0). 
    auto.
    auto.
  Qed.

  Lemma fal_R : forall T p t, (T ||- fal p) -> (T ||- p/(t)).
  Proof.
    intros.
    MP (fal p). auto.
    auto.
  Qed.

  Lemma fal_R2 : forall T p t s, 
    (T ||- fal (fal p)) -> (T ||- p/(t, s)).
  Proof.
    intros.
    assert (p .['0; (sfc s .; \0)]/(t) = p/(t, s)).
    - unfold sfc.
      rewrite <- nested_rew.
      apply rew_rew.
      intros.
      destruct n.
      simpl.
      auto.
      simpl.
      destruct n.
      simpl.
      rewrite <- nested_rewc.
      simpl.
      symmetry.
      apply rewc_id.
      simpl.
      auto.
    - rewrite <- H0.
      apply fal_R.
      assert ((fal p)/(s) = fal (p .['0; (sfc s .; \0)])).
      simpl.
      assert (p .['0; fun x => sfc ((s; \0) x)] = p .['0; (sfc s .; \0)]).
      + unfold sfc.
        apply rew_rew.
        intros.
        destruct n.
        simpl.
        auto.
        simpl.
        destruct n.
        simpl. auto.
        simpl. auto.
      + rewrite -> H1.
        auto.
      + rewrite <- H1.
        apply fal_R.
        auto.
  Qed.

  Lemma ext_R : forall T p t, 
    (T ||- p/(t)) -> (T ||- ext p).
  Proof.
    intros.
    unfold ext.
    MP (p/(t)). auto.
    apply contrad_elim.
    INTRO.
    MP (fal ([~] p)).
    apply pNNPP. 
    auto.
    rewrite <- neg_sbs.
    auto.
  Qed.

  Lemma ext_L : forall T p q, 
    (sfT T ||- p [->] sf q) -> (T ||- ext p [->] q).
  Proof.
    unfold ext.
    intros.
    INTRO.
    apply pNNPP.
    apply deduction_inv.
    apply contrad_add.
    INTRO.
    GEN.
    apply sf_dsb.
    apply deduction_inv.
    assert (([~] (sf q)) = sf ([~] q)).
    unfold sf.
    simpl.
    auto.
    rewrite <- H0.
    apply contrad_add.
    auto.
  Qed.

  
  Ltac SPECIALIZE h u := apply fal_R with (t := u) in h.
  
  Lemma fal_and_destruct : forall T p q, 
    (T ||- fal (p [/\] q)) -> ((T ||- fal p) /\ (T ||- fal q)).
  Proof.
    intros.
    split.
    - MP (fal (p [/\] q)). auto.
      MP (fal ((p [/\] q) [->] p)).
      GEN.
      INTRO.
      assert (sfT T ¦ (p [/\] q) ||- p [/\] q). auto.
      DESTRUCT H0.
      auto.
      auto.
    - MP (fal (p [/\] q)). auto.
      MP (fal ((p [/\] q) [->] q)).
      GEN.
      INTRO.
      assert (sfT T ¦ (p [/\] q) ||- p [/\] q). auto.
      DESTRUCT H0.
      auto.
      auto.
  Qed.
  
  Lemma fal_trans : forall T p q r, 
    (T ||- fal (p [->] q)) -> (T ||- fal (q [->] r)) -> (T ||- fal (p [->] r)).
  Proof.
    intros.
    MP (fal (p [->] q)). auto.
    MP (fal ((p [->] q) [->] p [->] r)).
    MP (fal (p [->] q [->] r)).
    MP (fal (q [->] r)). auto.
    MP (fal ((q [->] r) [->] (p [->] q [->] r))).
    GEN.
    repeat INTRO.
    MP q.
    auto.
    auto.
    auto.
    MP (fal ((p [->] q [->] r) [->] (p [->] q) [->] (p [->] r))).
    GEN.
    auto.
    auto.
    auto.
  Qed.
  
  Lemma eql_refl : forall T t u, 
    (T ||- t [=] u) -> (T ||- u [=] t).
  Proof.
    intros.
    MP (t [=] u). auto.
    INTRO.
    MP (t [=] t). auto.
    MP (t [=] u). auto.
    assert (forall v, (v [=] t) = ('0 [=] sfc t)/(v)).
    unfold sfc.
    intros.
    simpl.
    rewrite <- nested_rewc.
    simpl.
    rewrite <- rewc_id.
    auto.
    rewrite -> H0.
    rewrite -> H0.
    auto.
  Qed.

  Lemma eql_rewrite : forall T p t s, 
    (T ||- t [=] s) -> (T ||- p/(t)) -> (T ||- p/(s)).
  Proof.
    intros.
    MP (p/(t)). auto.
    MP (t [=] s). auto.
    auto.
  Qed.

  Lemma eql_trans : forall T t u v, 
    (T ||- t [=] u) -> (T ||- u [=] v) -> (T ||- t [=] v).
  Proof.
    intros.
    MP (u [=] v). auto.
    MP (u [=] t).
    apply eql_refl. auto.
    assert (forall x, (x [=] v) = ('0 [=] sfc v)/(x)).
    unfold sfc.
    intros.
    simpl.
    rewrite <- nested_rewc.
    simpl.
    rewrite <- rewc_id.
    auto.
    rewrite -> H1.
    rewrite -> H1.
    auto.
  Qed.

End deduction_facts.

Ltac GEN0 := apply GEN.
Ltac GEN := apply GEN; try apply sf_dsb.
Ltac MP h := apply (@MP _ _ h _).
Hint Resolve p__p : core.
Ltac MPI h := apply MPintro with (p:=h).
Ltac TRANS h := apply imp_trans with (q:=h).
Ltac INTRO := apply Deduction.
Ltac SPLIT := apply destruct_iff || apply destruct_and.
Ltac DESTRUCT h := apply and_destruct in h; destruct h.
Ltac SPECIALIZE H u := apply fal_R with (t := u) in H; simpl in H.
Ltac EXISTS u := apply ext_R with (t := u).
Ltac SYMMETRY := apply eql_refl.
Ltac RAA h := apply RAA with (q:=h).
Ltac WL := apply weakening.