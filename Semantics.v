Require Export SetoidClass.
Require Export RelationClasses.
Require Import Lia.
Require Export FOPL.Basic.

Set Implicit Arguments.

(**)
  Lemma nfn_e : forall (t : Type) p, (~ forall (x : t), ~ p x) -> exists x, p x.
  Proof.
    intros.
    apply NNPP.
    intro.
    contradict H.
    intros. intro.
    assert (exists x : t, p x).
    exists x. auto.
    auto.
  Qed.

  Lemma e_nfn : forall (t : Type) p, (exists x, p x) -> (~ forall (x : t), ~ p x).
  Proof.
    intros.
    intro.
    destruct H.
    specialize (H0 x).
    auto.
  Qed. 
(**) 

Section TarskiSemantics.

  Variable L : Lang.
  
  Class Model :=
  {
    Dom : Type;
    SDom :> Setoid Dom;
    cnsM : Dom;
    Fc0M : fc0 -> Dom;
    Fc1M : fc1 -> Dom -> Dom;
    Fc2M : fc2 -> Dom -> Dom -> Dom;
    Pd0M : pd0 -> Prop;
    Pd1M : pd1 -> Dom -> Prop;
    Pd2M : pd2 -> Dom -> Dom -> Prop;

    ProperFc1M :> forall (c : fc1), Proper (equiv ==> equiv) (Fc1M c);
    ProperFc2M :> forall (c : fc2), Proper (equiv ==> equiv ==> equiv) (Fc2M c);
    ProperPd1M :> forall (c : pd1), Proper (equiv ==> equiv) (Pd1M c);
    ProperPd2M :> forall (c : pd2), Proper (equiv ==> equiv ==> equiv) (Pd2M c)
  }.

  Fixpoint Valt
  (M : Model)
  (s : nat -> Dom)
  (t : Term) : Dom :=
    match t with
    | 'm          => s m 
    | [O]         => cnsM
    | Fc0 c     => Fc0M c
    | Fc1 c x   => Fc1M c (Valt M s x)
    | Fc2 c x y => Fc2M c (Valt M s x) (Valt M s y)
    end.

  Fixpoint Valp
  (M : Model)
  (s : nat -> Dom)
  (p : Formula) : Prop :=
    match p with
    | x [=] y     => (Valt M s x) == (Valt M s y)
    | Pd0 c     => Pd0M c
    | Pd1 c x   => Pd1M c (Valt M s x)
    | Pd2 c x y => Pd2M c (Valt M s x) (Valt M s y)
    | q [->] r    => (Valp M s q) -> (Valp M s r)   
    | [~] q       => ~ (Valp M s q)
    | fal q       => forall (t : Dom), Valp M (t;s) q
    end.

End TarskiSemantics.

  Definition models {L : Lang} M p := forall s, Valp M s p.
  Notation "M |= p" := (models M p) (at level 99).
  Definition modelsTh {L : Lang} M (T :Th) := forall p, T p -> M |= p.
  Notation "M |=th T" := (modelsTh M T) (at level 99).
  Definition SValid {L : Lang} (T : Th) p := forall M, modelsTh M T -> M |= p.
  Notation "T ||= p" := (SValid T p) (at level 99).
  Definition function_equiv {L : Lang} {M : Model L} (s0 s1 : nat -> @Dom _ _) := forall n, s0 n == s1 n.
  Notation " x ~ y " := (function_equiv x y) (at level 70, no associativity).  

Instance Valt_s_rew : forall (L : Lang) M, Proper (function_equiv ==> eq ==> equiv) (Valt M).
Proof.
  unfold Proper, respectful.
  intros L M s0 s1 H.
  assert(forall t, Valt M s0 t == Valt M s1 t).
  - induction t.
    + simpl. auto.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl.
      rewrite <- IHt.
      reflexivity.
    + simpl.
      rewrite <- IHt1.
      rewrite <- IHt2.
      reflexivity.
  - intros.
    rewrite <- H1.
    auto. 
Qed.

Instance Valp_s_rew : forall (L : Lang) M, Proper (function_equiv ==> eq ==> iff) (Valp M).
Proof.
  unfold Proper, respectful.
  intros L M s0 s1 H.
  assert (forall q s0 s1, (s0 ~ s1) -> Valp M s0 q <-> Valp M s1 q).
  - induction q.
    + simpl.
      intros.
      rewrite <- H0.
      reflexivity.
    + simpl.
      intros.
      reflexivity.
    + simpl.
      intros.
      rewrite <- H0.
      reflexivity.
    + simpl.
      intros.
      rewrite <- H0.
      reflexivity.
    + simpl.
      intros.
      rewrite <- (IHq1 s2 s3).
      rewrite <- (IHq2 s2 s3).
      reflexivity.
      auto. auto.
    + simpl.
      intros.
      rewrite <- (IHq s2 s3).
      reflexivity.
      auto.
    + simpl.
      intros.
      assert (forall t, Valp M (t;s2) q <-> Valp M (t;s3) q).
      intros. apply IHq.
      {unfold function_equiv. destruct n. simpl. reflexivity. simpl. auto. }
      split.
      intros.
      rewrite <- H1.
      auto.
      intros.
      rewrite -> H1.
      auto.
  - intros.
    rewrite <- H1.
    auto.
Qed.

Section Semantics.

  Variable L : Lang.
  
  Lemma M_and_destruct : forall M p q, (M |= p [/\] q) <-> (M |= p) /\ (M |= q).
  Proof.
    unfold models.
    simpl.
    intros.
    split.
    - intros.
      split.
      + intros.
        specialize (H s).
        apply NNPP.
        contradict H.
        auto.
      + intros.
        specialize (H s).
        apply NNPP.
        contradict H.
        auto.
    - intros.
      destruct H.
      intro.
      apply H1.
      auto. auto. 
  Qed.

  Lemma M_iff_destruct : forall M p q, (M |= p [<->] q) <-> (M |= p [->] q) /\ (M |= q [->] p).
  Proof.
    intros M p q.
    apply M_and_destruct.
  Qed.

  Lemma M_fal : forall M p s, (Valp M s (fal p)) <-> (forall x, Valp M (x;s) p).
  Proof.
    simpl.
    intros.
    reflexivity.
  Qed.

  Lemma M_ext : forall M p s, (Valp M s (ext p)) <-> (exists x, Valp M (x;s) p).
  Proof.
    simpl.
    intros.
    split.
    intros.
    apply nfn_e. auto.
    intros.
    apply e_nfn.
    auto.
  Qed.

  Lemma lc_eq : forall M t s c, Valt M s (rewc c t) == Valt M (fun x => Valt M s (c x)) t.
  Proof.
    induction t.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      intros.
      rewrite <- IHt.
      reflexivity.
    - simpl.
      intros.
      rewrite <- IHt1.
      rewrite <- IHt2.
      reflexivity.
  Qed.

  Lemma shiftc_eq : forall M t s c, Valt M s c == Valt M (t; s) (sfc c).
  Proof.
    unfold sfc.
    induction c.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl.
      rewrite <- IHc.
      reflexivity.
    - simpl.
      rewrite <- IHc1.
      rewrite <- IHc2.
      reflexivity.
  Qed.

  Lemma lp_iff0 : forall M p s0 s1 u, 
    (forall n, s0 n == Valt M s1 (u n)) -> 
    Valp M s0 p <-> Valp M s1 (p.[u]).
  Proof.
    intros M.
    induction p.
    - simpl.
      intros.
      rewrite -> lc_eq. rewrite -> lc_eq.
      assert (s0 ~ (fun x : nat => Valt M s1 (u x))).
      {unfold function_equiv. auto. }
      rewrite <- H0.
      reflexivity.
    - simpl.
      intros.
      reflexivity.
    - simpl.
      intros.
      rewrite -> lc_eq.
      assert (s0 ~ (fun x : nat => Valt M s1 (u x))).
      {unfold function_equiv. auto. }
      rewrite <- H0.
      reflexivity.
    - simpl.
      intros.
      rewrite -> lc_eq. rewrite -> lc_eq.
      assert (s0 ~ (fun x : nat => Valt M s1 (u x))).
      {unfold function_equiv. auto. }
      rewrite <- H0.
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
      assert (miff : forall t, Valp M (t; s0) p <-> Valp M (t; s1) (p.['0; fun x => sfc (u x)])).
      + intros.
        apply IHp.
        destruct n.
        simpl. reflexivity.
        simpl. rewrite <- shiftc_eq. auto.
      + split.
        intros.
        apply miff. auto.
        intros.
        apply miff. auto.
  Qed.

  Lemma lp_iff1 : forall M p s u, 
    Valp M (fun n => Valt M s (u n)) p <-> Valp M s (p.[u]).
  Proof.
    intros.
    apply lp_iff0.
    reflexivity.
  Qed.

  Lemma mthsfT: forall M T, modelsTh M T -> modelsTh M (sfT T).
  Proof.
    unfold modelsTh, sf, models.
    intros.
    destruct H0.
    unfold sf.
    rewrite <- lp_iff1.
    apply H.
    auto.
  Qed.
  
  Theorem Soundness : forall T p, (T ||- p) -> (T ||= p).
  Proof.
    unfold SValid.
    intros.
    unfold models.
    induction H.
    - simpl.
      intros.
      apply IHprovable.
      apply mthsfT.
      auto.
    - intros.
      simpl in IHprovable2.
      auto.
    - intros.
      apply H0.
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
      + rewrite <- H1.
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
      + rewrite <-  H1.
        auto.
    - simpl.
      intros.
      reflexivity.
    - simpl.
      intros.
      rewrite <- lp_iff1.
      rewrite <- lp_iff1 in H1.
      assert ((fun n => Valt M s ((t; \0) n)) ~ (fun n => Valt M s ((u; \0) n))).
      + unfold function_equiv.
        destruct n.
        simpl. auto.
        simpl. reflexivity.
      + rewrite <- H2.
        auto.
  Qed.

  Lemma Val_eq : forall M t s0 s1, 
    (forall n, n < Art t -> s0 n == s1 n) -> 
    Valt M s0 t == Valt M s1 t.
  Proof.
    intros M.
    induction t.
    - simpl.
      intros.
      auto.
    - simpl. intros. reflexivity.
    - simpl. intros. reflexivity.
    - simpl. intros.
      rewrite (IHt _ s1). 
      reflexivity.
      auto.
    - simpl. intros.
      rewrite (IHt1 _ s1).
      rewrite (IHt2 _ s1).
      reflexivity.
      intros.
      apply H.
      apply lt_lt_max_r. auto.
      intros.
      apply H.
      apply lt_lt_max_l. auto.
  Qed.
  
  Lemma Val_iff : forall M p s0 s1, 
    (forall n, n < Ar p -> s0 n == s1 n) -> 
    Valp M s0 p == Valp M s1 p.
  Proof.
    intros M.
    induction p.
    - simpl.
      intros.
      rewrite (Val_eq _ t _ s1).
      rewrite (Val_eq _ t0 _ s1).
      reflexivity.
      intros. apply H. apply lt_lt_max_r. auto.
      intros. apply H. apply lt_lt_max_l. auto.
    - simpl.
      intros.
      reflexivity.
    - simpl.
      intros.
      rewrite (Val_eq _ t _ s1).
      reflexivity.
      auto.
    - simpl.
      intros.
      rewrite (Val_eq _ t _ s1).
      rewrite (Val_eq _ t0 _ s1).
      reflexivity.
      intros. apply H. apply lt_lt_max_r. auto.
      intros. apply H. apply lt_lt_max_l. auto.
    - simpl.
      intros.
      rewrite (IHp1 s0 s1).
      rewrite (IHp2 s0 s1).
      reflexivity.
      intros. apply H. apply lt_lt_max_r. auto.
      intros. apply H. apply lt_lt_max_l. auto.
    - simpl.
      intros.
      rewrite (IHp s0 s1).
      reflexivity.
      auto.
    - simpl.
      intros.
      assert(forall t, Valp M (t; s0) p == Valp M (t; s1) p).
      + intros.
        apply IHp.
        intros.
        destruct n.
        simpl. reflexivity.
        simpl.
        apply H.
        lia.
      + split.
        intros. apply H0. auto.
        intros. apply H0. auto.
  Qed.

End Semantics.

Section DSetoid.

  Variable A : Type.
  
  Lemma equiveq : @Equivalence A eq.
  Proof.
    split.
    auto.
    auto.
    unfold Transitive.
    intros.
    rewrite -> H.
    auto.
  Qed.
  
  Instance DSetoid : Setoid A := {equiv:=eq; setoid_equiv:=equiveq}.

End DSetoid.