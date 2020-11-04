Require Export SetoidClass.
Require Import FOPL.FOPL.
Require Import FOPL.Deduction.

Definition preq {L :Lang} (T :Th) (c d :LC) := T ||- c[=]d.
Definition priff {L :Lang} (T :Th) (p q :LP) := T ||- p[<->]q.

Lemma priff_Equiv : forall (L :Lang) T, Equivalence (priff T).
Proof.
  unfold priff.
  intros.
  split.
  - unfold Reflexive.
    intros.
    SPLIT.
    auto. auto.
  - unfold Symmetric.
    intros.
    DESTRUCT H.
    SPLIT.
    auto. auto.
  - unfold Transitive.
    intros.
    DESTRUCT H.
    DESTRUCT H0.
    SPLIT.
    TRANS y. auto. auto.
    TRANS y. auto. auto.
Qed.

Program Instance Setoid_LC {L :Lang} (T : Th) : Setoid LC := {|equiv:=preq T|}.
Next Obligation.
Proof.
  unfold preq.
  intros.
  split.
  - unfold Reflexive.
    intros.
    auto.
  - unfold Symmetric.
    intros.
    SYMMETRY.
    auto.
  - unfold Transitive.
    apply eql_trans.
Qed.
Notation "p ==[ T ] q" := ((@equiv _ (Setoid_LC T)) p q) (at level 55).

Lemma preq0 : forall {L : Lang} T c d, (T ||- c[=]d) <-> (c ==[T] d).
Proof.
  intros.
  reflexivity.
Qed.

Program Instance Setoid_LP {L :Lang} (T : Th) : Setoid LP := {|equiv:=priff T|}.
Next Obligation.
Proof.
  unfold priff.
  intros.
  split.
  - unfold Reflexive.
    intros.
    SPLIT.
    auto. auto.
  - unfold Symmetric.
    intros.
    DESTRUCT H.
    SPLIT.
    auto. auto.
  - unfold Transitive.
    intros.
    DESTRUCT H.
    DESTRUCT H0.
    SPLIT.
    TRANS y. auto. auto.
    TRANS y. auto. auto.
Qed.
Notation "p ==( T ) q" := ((@equiv _ (Setoid_LP T)) p q) (at level 55).

Lemma priff0 : forall {L : Lang} T p q, (T ||- p[<->]q) <-> (p ==(T) q).
Proof.
  intros.
  reflexivity.
Qed.

Instance rew_LC_Fc1 : forall {L : Lang} (T : @Th L) c, 
  Proper ((@equiv _ (Setoid_LC T)) ==> (@equiv _ (Setoid_LC T))) (Fc1 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq.
  intros.
  MP (Fc1 c x [=] Fc1 c x). auto.
  assert(forall z, (Fc1 c (sfc x) [=] Fc1 c '0)/(z) = (Fc1 c x [=] Fc1 c z)).
  intros. simpl. rewrite <- rewc_sfc. auto.
  repeat rewrite <- H0.
  MP (x[=]y). auto.
  auto.
Qed.

Instance rew_LC_Fc2 : forall {L : Lang} T c, 
  Proper ((@equiv _ (Setoid_LC T)) ==> (@equiv _ (Setoid_LC T)) ==> (@equiv _ (Setoid_LC T))) (Fc2 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq.
  intros.
  apply eql_trans with (u:=Fc2 c y x0).
  - MP (Fc2 c x x0 [=] Fc2 c x x0). auto.
    assert(forall z, (Fc2 c (sfc x) (sfc x0) [=] Fc2 c '0 (sfc x0))/(z) = (Fc2 c x x0 [=] Fc2 c z x0)).
    intros. simpl. repeat rewrite <- rewc_sfc. auto.
    repeat rewrite <- H1.
    MP (x[=]y). auto.
    auto.
  - MP (Fc2 c y x0 [=] Fc2 c y x0). auto.
    assert(forall z, (Fc2 c (sfc y) (sfc x0) [=] Fc2 c (sfc y) '0)/(z) = (Fc2 c y x0 [=] Fc2 c y z)).
    intros. simpl. repeat rewrite <- rewc_sfc. auto.
    repeat rewrite <- H1.
    MP (x0[=]y0). auto.
    auto.
Qed.

Instance rew_LP_Eq : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_LC T)) ==> (@equiv _ (Setoid_LC T)) ==> (@equiv _ (Setoid_LP T))) eql.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  assert (forall z v, ('0[=](sfc v))/(z) = z[=]v).
  intros. simpl. repeat rewrite <- rewc_sfc. auto.
  assert (forall z v, ((sfc z)[=]'0)/(v) = z[=]v).
  intros. simpl. repeat rewrite <- rewc_sfc. auto.  
  SPLIT.
  - TRANS (y[=]x0).
    rewrite <- H1.
    rewrite <- (H1 y).
    MP (x[=]y). auto.
    auto.
    rewrite <- H2.
    rewrite <- (H2 y).
    MP (x0[=]y0). auto.
    auto.
  - TRANS (x[=]y0).
    rewrite <- H1.
    rewrite <- (H1 x).
    MP (y[=]x).
    SYMMETRY. auto.
    auto.
    rewrite <- H2.
    rewrite <- (H2 x).
    MP (y0[=]x0).
    SYMMETRY. auto.
    auto.
Qed.

Instance rew_LP_Pd0 : forall {L : Lang} T c, 
  Proper ((@equiv _ (Setoid_LP T))) (Pd0 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  SPLIT.
  auto. auto.
Qed.

Instance rew_LP_Pd1 : forall {L : Lang} T c, 
  Proper ((@equiv _ (Setoid_LC T)) ==> (@equiv _ (Setoid_LP T))) (Pd1 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  assert (forall z, (Pd1 c '0)/(z) = Pd1 c z).
  intros. simpl. auto.
  SPLIT.
  rewrite <- H0.
  rewrite <- (H0 y).
  MP (x[=]y). auto.
  auto.
  rewrite <- H0.
  rewrite <- (H0 x).
  MP (y[=]x).
  SYMMETRY. auto.
  auto.
Qed.

Instance rew_LP_Pd2 : forall {L : Lang} T c, 
  Proper ((@equiv _ (Setoid_LC T)) ==> (@equiv _ (Setoid_LC T)) ==> (@equiv _ (Setoid_LP T))) (Pd2 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  assert (forall z v, (Pd2 c '0 (sfc v))/(z) = Pd2 c z v).
  intros. simpl. repeat rewrite <- rewc_sfc. auto.
  assert (forall z v, (Pd2 c (sfc z) '0)/(v) = Pd2 c z v).
  intros. simpl. repeat rewrite <- rewc_sfc. auto.  
  SPLIT.
  - TRANS (Pd2 c y x0).
    rewrite <- H1.
    rewrite <- (H1 y).
    MP (x[=]y). auto.
    auto.
    rewrite <- H2.
    rewrite <- (H2 y).
    MP (x0[=]y0). auto.
    auto.
  - TRANS (Pd2 c x y0).
    rewrite <- H1.
    rewrite <- (H1 x).
    MP (y[=]x).
    SYMMETRY. auto.
    auto.
    rewrite <- H2.
    rewrite <- (H2 x).
    MP (y0[=]x0).
    SYMMETRY. auto.
    auto.
Qed.

Instance rew_LP_imp : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_LP T)) ==> (@equiv _ (Setoid_LP T)) ==> (@equiv _ (Setoid_LP T))) imp.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  DESTRUCT H.
  DESTRUCT H0.
  SPLIT.
  - repeat INTRO.
    MP x0.
    MP x.
    MP y.
    auto.
    repeat WL. auto.
    auto.
    repeat WL.
    auto.
  - repeat INTRO.
    MP y0.
    MP y.
    MP x.
    auto.
    repeat WL. auto.
    auto.
    repeat WL. auto.
Qed.

Instance rew_LP_neg : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_LP T)) ==> (@equiv _ (Setoid_LP T))) neg.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  DESTRUCT H.
  SPLIT.
  - apply contrad_add. auto.
  - apply contrad_add. auto.
Qed.

Instance rew_LP_andl : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_LP T)) ==> (@equiv _ (Setoid_LP T)) ==> (@equiv _ (Setoid_LP T))) andl.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  DESTRUCT H.
  DESTRUCT H0.
  SPLIT.
  - repeat INTRO.
    assert(T ¦ x[/\]x0 ||- x[/\]x0). auto.
    DESTRUCT H3.
    SPLIT.
    MP x. auto.
    WL. auto.
    MP x0. auto.
    WL. auto.
  - repeat INTRO.
    assert(T ¦ y[/\]y0 ||- y[/\]y0). auto.
    DESTRUCT H3.
    SPLIT.
    MP y. auto.
    WL. auto.
    MP y0. auto.
    WL. auto.
Qed.

Instance rew_LP_orl : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_LP T)) ==> (@equiv _ (Setoid_LP T)) ==> (@equiv _ (Setoid_LP T))) orl.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  DESTRUCT H.
  DESTRUCT H0.
  unfold orl.
  SPLIT.
  - repeat INTRO.
    MP x0.
    MP ([~]x).
    apply deduction_inv.
    apply contrad_add.
    WL. auto.
    auto.
    repeat WL. auto.
  - repeat INTRO.
    MP y0.
    MP ([~]y).
    apply deduction_inv.
    apply contrad_add.
    WL. auto.
    auto.
    repeat WL. auto.
Qed.

Instance rew_LP_iffl : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_LP T)) ==> (@equiv _ (Setoid_LP T)) ==> (@equiv _ (Setoid_LP T))) iffl.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  DESTRUCT H.
  DESTRUCT H0.
  SPLIT.
  - repeat INTRO.
    assert(T ¦ (x [<->] x0) ||- x[<->]x0). auto.
    DESTRUCT H3.
    SPLIT.
    INTRO.
    MP x0.
    MP x.
    MP y. auto.
    WL. WL. auto.
    WL. auto.
    WL. WL. auto.
    INTRO.
    MP x.
    MP x0.
    MP y0. auto.
    WL. WL. auto.
    WL. auto.
    WL. WL. auto.
  - repeat INTRO.
    assert(T ¦ (y [<->] y0) ||- y[<->]y0). auto.
    DESTRUCT H3.
    SPLIT.
    INTRO.
    MP y0.
    MP y.
    MP x. auto.
    WL. WL. auto.
    WL. auto.
    WL. WL. auto.
    INTRO.
    MP y.
    MP y0.
    MP x0. auto.
    WL. WL. auto.
    WL. auto.
    WL. WL. auto.
Qed.

Instance rew_LP_pr : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_LP T)) ==> equiv) (provable T).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  DESTRUCT H.
  split.
  - intros.
    MP x. auto.
    auto.
  - intros.
    MP y. auto.
    auto.
Qed.