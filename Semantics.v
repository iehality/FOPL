Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Lia.
Require Import FOPL.FOPL.
Require Import FOPL.Deduction.

Set Implicit Arguments.

Section TarskiSemantics.

  Variable L : Lang.
  
  Class Model :=
  {
    V : Type;
    cnsM : V;
    Fc0M : fc0 -> V;
    Fc1M : fc1 -> V -> V;
    Fc2M : fc2 -> V -> V -> V;
    Pd0M : pd0 -> Prop;
    Pd1M : pd1 -> V -> Prop;
    Pd2M : pd2 -> V -> V -> Prop;
  }.

  Fixpoint Valt
  (M : Model)
  (s : nat -> V)
  (t : LC) : V :=
    match t with
    | 'm          => s m 
    | !0          => cnsM
    | Fc0 _ c     => Fc0M c
    | Fc1 _ c x   => Fc1M c (Valt M s x)
    | Fc2 _ c x y => Fc2M c (Valt M s x) (Valt M s y)
    end.

  Fixpoint Valp
  (M : Model)
  (s : nat -> V)
  (p : LP) : Prop :=
    match p with
    | x == y      => (Valt M s x) = (Valt M s y)
    | Pd0 _ c     => Pd0M c
    | Pd1 _ c x   => Pd1M c (Valt M s x)
    | Pd2 _ c x y => Pd2M c (Valt M s x) (Valt M s y)
    | q --> r     => (Valp M s q) -> (Valp M s r)   
    | ~~ q        => ~ (Valp M s q)
    | fal q       => forall (t : V), Valp M (t;s) q
    end.

  Definition models M p := forall s, Valp M s p.
  Notation "M |= p" := (models M p) (at level 99).
  Notation "||= p" := (forall M, models M p) (at level 99).
  Definition modelsTh M (T :Th) := forall p, T p -> M |= p.

  
  Lemma mthMsfT: forall M T, SentTh T -> modelsTh M T -> modelsTh M (sfT T).
  Proof.
    unfold modelsTh.
    intros.
    apply H0.
    apply SentTheqvT.
    auto.
    auto.
  Qed.
  
  Section Soundness.
    Variable T : Th.
    Hypothesis StT : SentTh T.
    Variable M : Model.
    Hypothesis MthT : modelsTh M T.
    
    Lemma lc_eq : forall t s c, Valt M s (rewc c t) = Valt M (fun x => Valt M s (c x)) t.
    Proof.
      induction t.
      - simpl. auto.
      - simpl. auto.
      - simpl. auto.
      - simpl.
        intros.
        rewrite <- IHt.
        auto.
      - simpl.
        intros.
        rewrite <- IHt1.
        rewrite <- IHt2.
        auto.
    Qed.

    Lemma shiftc_eq : forall t s c, Valt M s c = Valt M (t; s) (sfc c).
    Proof.
      unfold sfc.
      induction c.
      - simpl. auto.
      - simpl. auto.
      - simpl. auto.
      - simpl.
        rewrite <- IHc.
        auto.
      - simpl.
        rewrite <- IHc1.
        rewrite <- IHc2.
        auto.
    Qed.

    Lemma lp_iff0 : forall p s0 s1 u, (forall n, s0 n = Valt M s1 (u n)) -> Valp M s0 p <-> Valp M s1 p [u].
    Proof.
      induction p.
      - simpl.
        intros.
        rewrite -> lc_eq. rewrite -> lc_eq.
        assert (seq : s0 = (fun x : nat => Valt M s1 (u x))).
        apply functional_extensionality. auto.                      
        rewrite <- seq.
        reflexivity.
      - simpl.
        intros.
        reflexivity.
      - simpl.
        intros.
        rewrite -> lc_eq.
        assert (seq : s0 = (fun x : nat => Valt M s1 (u x))).
        apply functional_extensionality. auto.      
        rewrite <- seq.
        reflexivity.
      - simpl.
        intros.
        rewrite -> lc_eq. rewrite -> lc_eq.
        assert (seq : s0 = (fun x : nat => Valt M s1 (u x))).
        apply functional_extensionality. auto.                      
        rewrite <- seq.
        reflexivity.
      - simpl.
        intros.
        rewrite <- (IHp1 s0 s1). rewrite <- (IHp2 s0 s1).
        reflexivity.
        auto. auto.
      - simpl.
        intros.
        rewrite <- (IHp s0 s1).
        reflexivity.
        auto.
      - simpl.
        intros.
        assert (miff : forall t, Valp M (t; s0) p <-> Valp M (t; s1) (p) ['0; fun x => sfc (u x)]).
        + intros.
          apply IHp.
          intros.
          destruct n.
          simpl. auto.
          simpl. rewrite <- shiftc_eq. auto.
        + split.
          intros.
          apply miff. auto.
          intros.
          apply miff. auto.
    Qed.

    Lemma lp_iff1 : forall p s u, Valp M (fun n => Valt M s (u n)) p <-> Valp M s p [u].
    Proof.
      intros.
      apply lp_iff0.
      auto.
    Qed.

    Theorem Soundness : forall p, (T |- p) -> (M |= p).
    Proof.
      intros.
      unfold models.
      induction H.
      - simpl.
        intros.
        apply IHprovable.
        apply sentsfT. auto.
        apply mthMsfT. auto. auto.
      - intros.
        simpl in IHprovable2.
        auto.
      - intros.
        apply MthT.
        auto.
      - simpl. auto.
      - simpl. auto.
      - simpl.
        intros.
        apply NNPP.
        intro.
        apply H.
        auto. auto.
      - simpl.
        intros.
        rewrite <- lp_iff1.
        assert ((Valt M s t; s) = fun n => Valt M s ((t; \0) n)).
        + apply functional_extensionality.
          intros.
          destruct x.
          simpl. auto.
          simpl. auto.
        + rewrite <- H0.
          auto.
      - simpl. auto.
      - simpl.
        intros.
        unfold sf.
        rewrite <- lp_iff1.
        assert (s = fun n => Valt M (t;s) '(S n)).
        + apply functional_extensionality.
          intros.
          simpl. auto.
        + rewrite <-  H0.
          auto.
      - simpl. auto.
      - simpl.
        intros.
        rewrite <- lp_iff1.
        rewrite <- lp_iff1 in H0.
        assert ((fun n => Valt M s ((t; \0) n)) = (fun n => Valt M s ((u; \0) n))).
        + apply functional_extensionality.
          intros.
          destruct x.
          simpl. auto.
          simpl. auto.
        + rewrite <- H1.
          auto.
    Qed.

  End Soundness.
  
  