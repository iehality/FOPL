Require Export SetoidClass.
Require Import FOPL.FOPL.
Require Import FOPL.Deduction.

Definition preq {L :Lang} (T :Th) (c d :Term) := T ||- c[=]d.
Definition priff {L :Lang} (T :Th) (p q :Formula) := T ||- p[<->]q.

Lemma priff_Equiv : forall (L :Lang) T, Equivalence (priff T).
Proof.
  unfold priff.
  intros.
  split.
  - unfold Reflexive.
    intros.
    fsplit.
    auto. auto.
  - unfold Symmetric.
    intros.
    fdestruct H.
    fsplit.
    auto. auto.
  - unfold Transitive.
    intros.
    fdestruct H.
    fdestruct H0.
    fsplit.
    ftrans y. auto. auto.
    ftrans y. auto. auto.
Qed.

Program Instance Setoid_Term {L :Lang} (T : Th) : Setoid Term := {|equiv:=preq T|}.
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
    fsymmetry.
    auto.
  - unfold Transitive.
    apply eql_trans.
Qed.
Notation "p ==[ T ] q" := ((@equiv _ (Setoid_Term T)) p q) (at level 55).

Lemma preq0 : forall {L : Lang} T c d, (T ||- c[=]d) <-> (c ==[T] d).
Proof.
  intros.
  reflexivity.
Qed.

Program Instance Setoid_Formula {L :Lang} (T : Th) : Setoid Formula := {|equiv:=priff T|}.
Next Obligation.
Proof.
  unfold priff.
  intros.
  split.
  - unfold Reflexive.
    intros.
    fsplit.
    auto. auto.
  - unfold Symmetric.
    intros.
    fdestruct H.
    fsplit.
    auto. auto.
  - unfold Transitive.
    intros.
    fdestruct H.
    fdestruct H0.
    fsplit.
    ftrans y. auto. auto.
    ftrans y. auto. auto.
Qed.
Notation "p ==( T ) q" := ((@equiv _ (Setoid_Formula T)) p q) (at level 55).

Lemma priff0 : forall {L : Lang} T p q, (T ||- p[<->]q) <-> (p ==(T) q).
Proof.
  intros.
  reflexivity.
Qed.

Instance rew_Term_Fc1 : forall {L : Lang} (T : @Th L) c, 
  Proper ((@equiv _ (Setoid_Term T)) ==> (@equiv _ (Setoid_Term T))) (Fc1 c).
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

Instance rew_Term_Fc2 : forall {L : Lang} T c, 
  Proper ((@equiv _ (Setoid_Term T)) ==> (@equiv _ (Setoid_Term T)) ==> (@equiv _ (Setoid_Term T))) (Fc2 c).
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

Instance rew_Formula_Eq : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_Term T)) ==> (@equiv _ (Setoid_Term T)) ==> (@equiv _ (Setoid_Formula T))) eql.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  assert (forall z v, ('0[=](sfc v))/(z) = z[=]v).
  intros. simpl. repeat rewrite <- rewc_sfc. auto.
  assert (forall z v, ((sfc z)[=]'0)/(v) = z[=]v).
  intros. simpl. repeat rewrite <- rewc_sfc. auto.  
  fsplit.
  - ftrans (y[=]x0).
    rewrite <- H1.
    rewrite <- (H1 y).
    MP (x[=]y). auto.
    auto.
    rewrite <- H2.
    rewrite <- (H2 y).
    MP (x0[=]y0). auto.
    auto.
  - ftrans (x[=]y0).
    rewrite <- H1.
    rewrite <- (H1 x).
    MP (y[=]x).
    fsymmetry. auto.
    auto.
    rewrite <- H2.
    rewrite <- (H2 x).
    MP (y0[=]x0).
    fsymmetry. auto.
    auto.
Qed.

Instance rew_Formula_Pd0 : forall {L : Lang} T c, 
  Proper ((@equiv _ (Setoid_Formula T))) (Pd0 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  fsplit.
  auto. auto.
Qed.

Instance rew_Formula_Pd1 : forall {L : Lang} T c, 
  Proper ((@equiv _ (Setoid_Term T)) ==> (@equiv _ (Setoid_Formula T))) (Pd1 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  assert (forall z, (Pd1 c '0)/(z) = Pd1 c z).
  intros. simpl. auto.
  fsplit.
  rewrite <- H0.
  rewrite <- (H0 y).
  MP (x[=]y). auto.
  auto.
  rewrite <- H0.
  rewrite <- (H0 x).
  MP (y[=]x).
  fsymmetry. auto.
  auto.
Qed.

Instance rew_Formula_Pd2 : forall {L : Lang} T c, 
  Proper ((@equiv _ (Setoid_Term T)) ==> (@equiv _ (Setoid_Term T)) ==> (@equiv _ (Setoid_Formula T))) (Pd2 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  assert (forall z v, (Pd2 c '0 (sfc v))/(z) = Pd2 c z v).
  intros. simpl. repeat rewrite <- rewc_sfc. auto.
  assert (forall z v, (Pd2 c (sfc z) '0)/(v) = Pd2 c z v).
  intros. simpl. repeat rewrite <- rewc_sfc. auto.  
  fsplit.
  - ftrans (Pd2 c y x0).
    rewrite <- H1.
    rewrite <- (H1 y).
    MP (x[=]y). auto.
    auto.
    rewrite <- H2.
    rewrite <- (H2 y).
    MP (x0[=]y0). auto.
    auto.
  - ftrans (Pd2 c x y0).
    rewrite <- H1.
    rewrite <- (H1 x).
    MP (y[=]x).
    fsymmetry. auto.
    auto.
    rewrite <- H2.
    rewrite <- (H2 x).
    MP (y0[=]x0).
    fsymmetry. auto.
    auto.
Qed.

Instance rew_Formula_imp : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_Formula T)) ==> (@equiv _ (Setoid_Formula T)) ==> (@equiv _ (Setoid_Formula T))) imp.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  fdestruct H.
  fdestruct H0.
  fsplit.
  - fintros.
    MP x0.
    MP x.
    MP y.
    auto.
    WLs. auto.
    auto.
    WLs.
    auto.
  - fintros.
    MP y0.
    MP y.
    MP x.
    auto.
    WLs. auto.
    auto.
    WLs. auto.
Qed.

Instance rew_Formula_neg : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_Formula T)) ==> (@equiv _ (Setoid_Formula T))) neg.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  fdestruct H.
  fsplit.
  - apply contrad_add. auto.
  - apply contrad_add. auto.
Qed.

Instance rew_Formula_andl : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_Formula T)) ==> (@equiv _ (Setoid_Formula T)) ==> (@equiv _ (Setoid_Formula T))) andl.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  fdestruct H.
  fdestruct H0.
  fsplit.
  - fintros.
    assert(T ¦ x[/\]x0 ||- x[/\]x0). auto.
    fdestruct H3.
    fsplit.
    MP x. auto.
    WL. auto.
    MP x0. auto.
    WL. auto.
  - fintros.
    assert(T ¦ y[/\]y0 ||- y[/\]y0). auto.
    fdestruct H3.
    fsplit.
    MP y. auto.
    WL. auto.
    MP y0. auto.
    WL. auto.
Qed.

Instance rew_Formula_orl : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_Formula T)) ==> (@equiv _ (Setoid_Formula T)) ==> (@equiv _ (Setoid_Formula T))) orl.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  fdestruct H.
  fdestruct H0.
  unfold orl.
  fsplit.
  - fintros.
    MP x0.
    MP ([~]x).
    apply deduction_inv.
    apply contrad_add.
    WL. auto.
    auto.
    WLs. auto.
  - fintros.
    MP y0.
    MP ([~]y).
    apply deduction_inv.
    apply contrad_add.
    WL. auto.
    auto.
    WLs. auto.
Qed.

Instance rew_Formula_iffl : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_Formula T)) ==> (@equiv _ (Setoid_Formula T)) ==> (@equiv _ (Setoid_Formula T))) iffl.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  fdestruct H.
  fdestruct H0.
  fsplit.
  - fintros.
    assert(T ¦ (x [<->] x0) ||- x[<->]x0). auto.
    fdestruct H3.
    fsplit.
    fintro.
    MP x0.
    MP x.
    MP y. auto.
    WL. WL. auto.
    WL. auto.
    WL. WL. auto.
    fintro.
    MP x.
    MP x0.
    MP y0. auto.
    WL. WL. auto.
    WL. auto.
    WL. WL. auto.
  - fintros.
    assert(T ¦ (y [<->] y0) ||- y[<->]y0). auto.
    fdestruct H3.
    fsplit.
    fintro.
    MP y0.
    MP y.
    MP x. auto.
    WL. WL. auto.
    WL. auto.
    WL. WL. auto.
    fintro.
    MP y.
    MP y0.
    MP x0. auto.
    WL. WL. auto.
    WL. auto.
    WL. WL. auto.
Qed.

Instance rew_Formula_pr : forall {L : Lang} T, 
  Proper ((@equiv _ (Setoid_Formula T)) ==> equiv) (provable T).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  fdestruct H.
  split.
  - intros.
    MP x. auto.
    auto.
  - intros.
    MP y. auto.
    auto.
Qed.