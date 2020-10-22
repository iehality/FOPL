Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import Lia.
Require Import FOPL.FOPL.
(* coqc -Q FOPL FOPL FOPL/Deduction.v *)

Set Implicit Arguments.

Section DeductionSystem.
  
  Variable L : Lang.
  
  Definition Th := LP -> Prop.
  
  (** * Hilbert Style Deduction System *)
  
  Definition sfT (T : Th) := fun p => exists q, p = sf q /\ T q.
  
  Inductive provable (T : Th) : LP -> Prop :=
  | GEN  : forall q, provable (sfT T) q -> provable T (fal q)
  | MP   : forall p q, provable T p -> provable T (p --> q) -> provable T q
  | Pr0  : forall p, T p -> provable T p
  | Pr1  : forall p q, provable T (p --> q --> p)
  | Pr2  : forall p q r, provable T ((p --> q --> r) --> ((p --> q) --> (p --> r)))
  | Pr3  : forall p q, provable T ((~~ p --> ~~ q) --> (q --> p))
  | Qt0  : forall p t, provable T (fal p --> p.(t))
  | Qt1  : forall p q, provable T (fal (p --> q) --> ((fal p) --> (fal q)))
  | Qt2  : forall p, provable T (p --> fal (sf p))
  | Eq0  : forall t, provable T (t == t)
  | Eq1  : forall p t u, provable T (t == u --> p.(t) --> p.(u)).
  
  Ltac MP h := apply MP with (p:=h).
  Ltac GEN := apply GEN.
  
  Notation "T |- p" := (provable T p) (at level 95).
  
  Definition Consis (T : Th) := ~ exists p, (T |- p) /\ (T |- ~~ p).
  
  Definition addT (T : Th) p := fun x => T x \/ x = p.
  Definition elmT (T : Th) p := fun x => T x /\ x <> p.
  Definition includeT (T U : Th) := forall p, T p -> U p.
  Notation "T :+ p" := (addT T p) (at level 71, left associativity).
  Notation "T :- p" := (elmT T p) (at level 71, left associativity). 
  Notation "T :< U" := (includeT T U) (at level 72, left associativity).
  
  Definition SentTh (T : Th) := T :< (sfT T) /\ (sfT T) :< T. 
  
  Lemma p__p : forall T p, T |- p --> p.
  Proof.
    intros.
    MP (p --> (p --> p)).
    apply Pr1.
    MP ((p --> (p --> p) --> p)).
    apply Pr1.
    apply Pr2.
  Qed.
  
  Ltac AX := (simpl; apply p__p) || apply Pr1 || apply Pr2 || apply Pr3 || apply Qt0 || apply Qt1 || apply Qt2 || apply Eq0 || apply Eq1 || unfold addT; apply Pr0; auto.
  
  (** ** Proof facts *)  
  
  Lemma imp_pr : forall T p q, (T |- p) -> (T |- q --> p).
  Proof.
    intros.
    MP p.
    auto.
    AX.
  Qed.
  
  Lemma imp_trans : forall T p q r, (T |- p --> q) -> (T |- q --> r) -> (T |- p --> r).
  Proof.
    intros.
    MP (p --> q). auto.
    MP (p --> q --> r).
    apply imp_pr. auto.
    AX.
  Qed.
  
  Ltac TRANS h := apply imp_trans with (q:=h).
  
  Lemma TInclusion : forall (T U : Th) p, T :< U -> T |- p -> U |- p.
  Proof.
    assert (forall (T : Th) p, T |- p -> forall (U : Th), T :< U -> U |- p).
    - intros T p H.
      unfold includeT.
      induction H.
      + intros.
        apply GEN.
        apply IHprovable.
        unfold sfT.
        intros.
        destruct H1 as [p0].
        destruct H1.
        exists p0.
        auto.
      + intros.
        MP p.
        auto. auto.
      + intros. AX.
      + intros. AX.
      + intros. AX.
      + intros. AX.
      + intros. AX.
      + intros. AX.
      + intros. AX.
      + intros. AX.
      + intros. AX.
    - intros.
      apply H with (T := T).
      auto.
      auto.
  Qed.
  
  Lemma weakening : forall T p q, (T |- q) -> (T :+ p |- q).
  Proof.
    intros.
    apply TInclusion with (T := T).
    unfold includeT. unfold addT. auto.
    auto.
  Qed.
  
  Theorem Deduction : forall T p q, (T :+ p |- q) -> (T |- p --> q).
  Proof.
    assert (forall T q, (T |- q) -> (forall p, T :- p |- p --> q)).
    - intros T q H.
      induction H.
      + intros.
        specialize (IHprovable (sf p)).
        apply imp_trans with (q := fal (sf p)).
        AX.
        MP (fal (sf p --> q)).
        GEN.
        apply TInclusion with (T := sfT T :- sf p).
        unfold sfT. unfold elmT. unfold includeT.
        intros.
        destruct H0.
        destruct H0 as [p1].
        destruct H0.
        exists p1.
        split. auto.
        split. auto.
        contradict H1.
        rewrite <- H1.
        auto.
        auto.
        AX.
      + intros.
        MP (p0 --> p). auto.
        MP (p0 --> p --> q). auto.
        AX.
      + intros.
        assert (em := classic (p0 = p)).
        destruct em.
        * rewrite <- H0.
          AX.
        * apply imp_pr.
          AX.
          split.
          auto.
          contradict H0.
          symmetry.
          auto.
      + intros.
        apply imp_pr.
        AX.
      + intros.
        apply imp_pr.
        AX.
      + intros.
        apply imp_pr.
        AX.
      + intros.
        apply imp_pr.
        AX.
      + intros.
        apply imp_pr.
        AX.
      + intros.
        apply imp_pr.
        AX.
      + intros.
        apply imp_pr.
        AX.
      + intros.
        apply imp_pr.
        AX.
    - intros.
      assert (em := classic (T p)).
      destruct em.
      + apply imp_pr. 
        apply TInclusion with (T := T :+ p).
        unfold includeT.
        intros.
        destruct H2.
        auto.
        rewrite -> H2.
        auto.
        auto.
      + apply TInclusion with (T := (T :+ p) :- p).
        unfold includeT.
        intros.
        destruct H2.
        destruct H2.
        auto.
        contradiction.
        auto.
  Qed.
  
  Ltac INTRO := apply Deduction.
  
  Lemma sf_dsb0 : forall T p, (sfT T :+ sf p) :< (sfT (T :+ p)).
  Proof.
    intros.
    unfold sfT. unfold addT. unfold includeT.
    intros.
    destruct H.
    destruct H as [p1].
    destruct H.
    exists p1.
    split. auto.
    auto.
    exists p.
    split.
    auto.
    auto.
  Qed.
  
  Lemma sf_dsb1 : forall T U p, T :< U -> (T :+ p) :< (U :+ p).
  Proof.
    unfold sfT. unfold addT. unfold includeT.
    intros.
    destruct H0.
    auto.
    auto.
  Qed.
  
  Lemma sf_dsb : forall T p q, (sfT T :+ sf p |- q) -> (sfT (T :+ p) |- q).
  Proof.
    intros.
    apply TInclusion with (T := sfT T :+ sf p).
    apply sf_dsb0.
    auto.
  Qed.
  
  Lemma imp_pqrs : forall T p q r s, (T |- p --> q --> r) -> (T |- r --> s) -> (T |- p --> q --> s).
  Proof.
    intros.
    MP (p --> q --> r). auto.
    MP (p --> (q --> r) --> (q --> s)).
    apply imp_pr.
    MP (q --> r --> s).
    apply imp_pr. auto.
    AX.
    AX.
  Qed.
  
  Lemma explosion : forall T, (~ Consis T) -> forall p, T |- p.
  Proof.
    intros.
    unfold Consis in H. apply NNPP in H.
    destruct H as [q].
    destruct H.
    MP q. auto.
    MP (~~ p --> ~~ q).
    MP (~~ q).
    auto.
    AX.
    AX.
  Qed.
  
  Lemma p_np_q : forall T p q, T |- p --> ~~ p --> q.
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
    AX.
    AX.
  Qed.
    
  Lemma deduction_inv : forall T p q, (T |- p --> q) -> (T :+ p |- q).
  Proof.
    intros.
    MP p. AX.
    apply weakening.
    auto.
  Qed.
  
  Lemma pr_NNPP : forall T p, T |- ~~ ~~ p --> p.
  Proof.
    intros.
    INTRO.
    MP (~~ ~~ p).
    AX.
    MP (~~ p --> ~~ ~~ ~~ p).
    MP (~~ ~~ ~~ ~~ p --> ~~ ~~ p).
    MP (~~ ~~ p).
    AX.
    AX.
    AX.
    AX.
  Qed.
  
  Lemma pr_NN : forall T p, T |- p --> ~~ ~~ p.
  Proof.
    intros.
    MP (~~ ~~ ~~ p --> ~~ p).
    apply pr_NNPP.
    AX.
  Qed.
  
  Lemma pNNPP : forall T p, (T |- ~~ ~~ p) -> (T |- p).
  Proof.
    intros.
    MP (~~ ~~ p).
    auto.
    MP (~~ p --> ~~ ~~ ~~ p).
    MP (~~ ~~ ~~ ~~ p --> ~~ ~~ p).
    MP (~~ ~~ p).
    auto.
    AX.
    AX.
    AX.
  Qed.
  
  Lemma pNN : forall T p, (T |- p) -> (T |- ~~ ~~ p).
  Proof.
    intros.
    MP p. auto.
    MP (~~ ~~ ~~ p --> ~~ p).
    apply pr_NNPP.
    AX.
  Qed.
  
  Lemma neg_intro : forall T p, T |- (p --> ~~ p) -> (T |- ~~ p).
  Proof.
    intros.
    MP (p --> ~~ p). auto.
    INTRO.
    MP (p --> ~~ p).
    AX.
    MP (~~ ~~ p --> ~~ (p --> ~~ p)).
    INTRO.
    apply explosion.
    unfold Consis.
    intro. contradict H0.
    exists p.
    split.
    apply pNNPP. AX.
    MP p.
    apply pNNPP. AX.
    AX.
    AX.
  Qed.
  
  Lemma contrad_elim : forall T p q, (T |- ~~ p --> ~~ q) -> (T |- q --> p).
  Proof.
    intros.
    MP (~~ p --> ~~ q). auto.
    AX.
  Qed.
  
  Lemma contrad_add : forall T p q, (T |- p --> q) -> (T |- ~~ q --> ~~ p).
  Proof.
    intros.
    MP (~~ ~~ p --> ~~ ~~ q).
    INTRO.
    MP q.
    MP p.
    MP (~~ ~~ p). AX.
    apply pr_NNPP.
    apply weakening.
    auto.
    apply pr_NN.
    AX.
  Qed.
  
  Lemma destruct_and : forall T p q, (T |- p) -> (T |- q) -> (T |- p //\ q).
  Proof.
    unfold andl.
    intros.
    apply neg_intro.
    - INTRO.
      MP q.
      apply weakening.
      auto.
      auto.
      MP (~~ ~~ (p --> ~~ q) --> ~~ q).
      apply imp_pr.
      MP p.
      apply weakening.
      auto. auto.
      AX.
      AX.
  Qed.
  
  Lemma and_destruct : forall T p q, (T |- p //\ q) -> ((T |- p) /\ (T |- q)).
  Proof.
    unfold andl.
    intros.
    split.
    - MP (~~ (p --> ~~ q)). auto.
      MP (~~ p --> ~~ ~~ (p --> ~~ q)).
      INTRO.
      MP (p --> ~~ q).
      INTRO.
      apply explosion.
      unfold Consis. intro. contradict H0. 
      exists p. split. AX. AX.
      apply pr_NN.
      AX.
    - MP (~~ (p --> ~~ q)). auto.
      MP (~~ q --> ~~ ~~ (p --> ~~ q)).
      INTRO.
      MP (p --> ~~ q).
      apply imp_pr. AX.
      apply pr_NN.
      AX.
  Qed.
  
  Lemma destruct_iff : forall T p q, (T |- p --> q) -> (T |- q --> p) -> (T |- p <--> q).
  Proof.
    intros.
    apply destruct_and.
    auto.
    auto.
  Qed.
  
  Ltac SPLIT := apply destruct_iff || apply destruct_and.
  Ltac DESTRUCT h := apply and_destruct in h; destruct h.
  
  Lemma pr_rewrite2 : forall {T} {p0 p1 r}, (T |- p0 <--> p1) -> (T |- p0 --> r) -> (T |- p1 --> r).
  Proof.
    intros.
    DESTRUCT H.
    apply imp_trans with (q := p0). 
    auto.
    auto.
  Qed.
  
  Lemma subst : forall T p t, (T |- fal p) -> (T |- p.(t)).
  Proof.
    intros.
    MP (fal p). auto.
    AX.
  Qed.

  Lemma ext_intro : forall T p t, (T |- p.(t)) -> (T |- ext p).
  Proof.
    intros.
    unfold ext.
    MP (p.(t)). auto.
    apply contrad_elim.
    INTRO.
    MP (fal (~~ p)).
    apply pNNPP. 
    AX.
    rewrite <- neg_sbs.
    AX.
  Qed.
  
  Ltac SPECIALIZE h u := apply subst with (t := u) in h.
  
  Lemma fal_and_destruct : forall T p q, (T |- fal (p //\ q)) -> ((T |- fal p) /\ (T |- fal q)).
  Proof.
    intros.
    split.
    - MP (fal (p //\ q)). auto.
      MP (fal ((p //\ q) --> p)).
      GEN.
      INTRO.
      assert (sfT T :+ (p //\ q) |- p //\ q). AX.
      DESTRUCT H0.
      auto.
      AX.
    - MP (fal (p //\ q)). auto.
      MP (fal ((p //\ q) --> q)).
      GEN.
      INTRO.
      assert (sfT T :+ (p //\ q) |- p //\ q). AX.
      DESTRUCT H0.
      auto.
      AX.
  Qed.
  
  Lemma fal_trans : forall T p q r, (T |- fal (p --> q)) -> (T |- fal (q --> r)) -> (T |- fal (p --> r)).
  Proof.
    intros.
    MP (fal (p --> q)). auto.
    MP (fal ((p --> q) --> p --> r)).
    MP (fal (p --> q --> r)).
    MP (fal (q --> r)). auto.
    MP (fal ((q --> r) --> (p --> q --> r))).
    GEN.
    repeat INTRO.
    MP q.
    AX.
    AX.
    AX.
    MP (fal ((p --> q --> r) --> (p --> q) --> (p --> r))).
    GEN.
    AX.
    AX.
    AX.
  Qed.
  
  Lemma eql_refl : forall T t u, (T |- t == u) -> (T |- u == t).
  Proof.
    intros.
    MP (t == u). auto.
    INTRO.
    MP (t == t). AX.
    MP (t == u). AX.
    assert (forall v, (v == t) = ('0 == sfc t).(v)).
    unfold sfc.
    intros.
    simpl.
    rewrite <- nested_rewc.
    simpl.
    rewrite <- rewc_id.
    auto.
    rewrite -> H0.
    rewrite -> H0.
    AX.
  Qed.

  Lemma eql_trans : forall T t u v, (T |- t == u) -> (T |- u == v) -> (T |- t == v).
  Proof.
    intros.
    MP (u == v). auto.
    MP (u == t).
    apply eql_refl. auto.
    assert (forall x, (x == v) = ('0 == sfc v).(x)).
    unfold sfc.
    intros.
    simpl.
    rewrite <- nested_rewc.
    simpl.
    rewrite <- rewc_id.
    auto.
    rewrite -> H1.
    rewrite -> H1.
    AX.
  Qed.
  
End DeductionSystem.

Arguments Th {_}.
Arguments provable {_}.
Arguments addT {_}.
Arguments elmT {_}.
Arguments includeT {_}.

Notation "T |- p" := (provable T p) (at level 95).
Notation "T :+ p" := (addT T p) (at level 71, left associativity).
Notation "T :- p" := (elmT T p) (at level 71, left associativity). 
Notation "T :< U" := (includeT T U) (at level 72, left associativity).

Ltac GEN := apply GEN.
Ltac MP h := apply MP with (p:=h).
Ltac AX := apply p__p || apply Pr1 || apply Pr2 || apply Pr3 || apply Qt0 || apply Qt1 || apply Qt2 || apply Eq0 || apply Eq1 || unfold addT; apply Pr0; auto.
Ltac TRANS h := apply imp_trans with (q:=h).
Ltac INTRO := apply Deduction.
Ltac SPLIT := apply destruct_iff || apply destruct_and.
Ltac DESTRUCT h := apply and_destruct in h; destruct h.
Ltac SPECIALIZE h u := apply subst with (t := u) in h.
Ltac EXISTS u := apply ext_intro with (t := u).
Ltac SYMMETRY := apply eql_refl.
Ltac WL := apply weakening.