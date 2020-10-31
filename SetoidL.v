Require Export SetoidClass.
Require Export RelationClasses.
Require Export FOPL.FOPL.
Require Export FOPL.Deduction.

Definition preq {L :Lang} (T :Th) (c d :LC) := T |- c[=]d.
Definition priff {L :Lang} (T :Th) (p q :LP) := T |- p[<->]q.

Lemma preq_Equiv : forall (L :Lang) T, Equivalence (preq T).
Proof.
  unfold preq.
  intros.
  split.
  - unfold Reflexive.
    intros.
    AX.
  - unfold Symmetric.
    intros.
    SYMMETRY.
    auto.
  - unfold Transitive.
    apply eql_trans.
Qed.

Lemma priff_Equiv : forall (L :Lang) T, Equivalence (priff T).
Proof.
  unfold priff.
  intros.
  split.
  - unfold Reflexive.
    intros.
    SPLIT.
    AX. AX.
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

Instance Setoid_LC {L :Lang} (T : Th) : Setoid LC := {equiv:=preq T; setoid_equiv:=preq_Equiv L T}.
Instance Setoid_LP {L :Lang} (T : Th) : Setoid LP := {equiv:=priff T; setoid_equiv:=priff_Equiv L T}.

Instance rew_LC_Fc1 : forall {L : Lang} T c, Proper (@equiv _ (Setoid_LC T) ==> @equiv _ (Setoid_LC T)) (Fc1 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq.
  intros.
  MP (Fc1 c x [=] Fc1 c x). AX.
  assert(forall z, (Fc1 c (sfc x) [=] Fc1 c '0).(z) = (Fc1 c x [=] Fc1 c z)).
  intros. simpl. rewrite <- rewc_sfc. auto.
  repeat rewrite <- H0.
  MP (x[=]y). auto.
  AX.
Qed.

Instance rew_LC_Fc2 : forall {L : Lang} T c, 
  Proper (@equiv _ (Setoid_LC T) ==> @equiv _ (Setoid_LC T) ==> @equiv _ (Setoid_LC T)) (Fc2 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq.
  intros.
  apply eql_trans with (u:=Fc2 c y x0).
  - MP (Fc2 c x x0 [=] Fc2 c x x0). AX.
    assert(forall z, (Fc2 c (sfc x) (sfc x0) [=] Fc2 c '0 (sfc x0)).(z) = (Fc2 c x x0 [=] Fc2 c z x0)).
    intros. simpl. repeat rewrite <- rewc_sfc. auto.
    repeat rewrite <- H1.
    MP (x[=]y). auto.
    AX.
  - MP (Fc2 c y x0 [=] Fc2 c y x0). AX.
    assert(forall z, (Fc2 c (sfc y) (sfc x0) [=] Fc2 c (sfc y) '0).(z) = (Fc2 c y x0 [=] Fc2 c y z)).
    intros. simpl. repeat rewrite <- rewc_sfc. auto.
    repeat rewrite <- H1.
    MP (x0[=]y0). auto.
    AX.
Qed.

Instance rew_LP_Pd1 : forall {L : Lang} T c, 
  Proper (@equiv _ (Setoid_LC T) ==> @equiv _ (Setoid_LP T)) (Pd1 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  assert (forall z, (Pd1 c '0).(z) = Pd1 c z).
  intros. simpl. auto.
  SPLIT.
  rewrite <- H0.
  rewrite <- (H0 y).
  MP (x[=]y). auto.
  AX.
  rewrite <- H0.
  rewrite <- (H0 x).
  MP (y[=]x).
  SYMMETRY. auto.
  AX.
Qed.

Instance rew_LP_Pd2 : forall {L : Lang} T c, 
  Proper (@equiv _ (Setoid_LC T) ==> @equiv _ (Setoid_LC T) ==> @equiv _ (Setoid_LP T)) (Pd2 c).
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  unfold preq, priff.
  intros.
  assert (forall z v, (Pd2 c '0 (sfc v)).(z) = Pd2 c z v).
  intros. simpl. repeat rewrite <- rewc_sfc. auto.
  assert (forall z v, (Pd2 c (sfc z) '0).(v) = Pd2 c z v).
  intros. simpl. repeat rewrite <- rewc_sfc. auto.  
  SPLIT.
  - TRANS (Pd2 c y x0).
    rewrite <- H1.
    rewrite <- (H1 y).
    MP (x[=]y). auto.
    AX.
    rewrite <- H2.
    rewrite <- (H2 y).
    MP (x0[=]y0). auto.
    AX.
  - TRANS (Pd2 c x y0).
    rewrite <- H1.
    rewrite <- (H1 x).
    MP (y[=]x).
    SYMMETRY. auto.
    AX.
    rewrite <- H2.
    rewrite <- (H2 x).
    MP (y0[=]x0).
    SYMMETRY. auto.
    AX.
Qed.

Instance rew_LP_pr : forall {L : Lang} T, Proper (@equiv _ (Setoid_LP T) ==> iff) (provable T).
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
