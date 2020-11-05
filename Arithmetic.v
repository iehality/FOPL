Require Export Arith.
Require Export Lia.
Require Export FOPL.Basic.

Set Implicit Arguments.

Inductive fc0A :=.
Inductive fc1A := ScA.
Inductive fc2A := plA | mlA.
Inductive pd0A :=.
Inductive pd1A :=.
Inductive pd2A := lelA.
Instance L : Lang := {fc0 := fc0A; fc1 := fc1A; fc2 := fc2A; pd0 := pd0A; pd1 := pd1A; pd2 := pd2A}.

Notation "a [+] b" := (@Fc2 L plA a b) (at level 45, right associativity).
Notation "a [*] b" := (@Fc2 L mlA a b) (at level 44, right associativity).
Notation "a [<=] b" := (@Pd2 L lelA a b) (at level 60, right associativity).
Notation "[S] a" := (@Fc1 L ScA a) (at level 43, right associativity).

Fixpoint innerNat (n0 : nat) : Term := 
  match n0 with
  | 0 => [O]
  | S n => [S] (innerNat n)
  end.

Notation "[ n ]" := (innerNat n) (at level 0).

Lemma IN_constant : forall n, Art [n] = 0.
Proof.
  induction n.
  simpl. auto.
  simpl.
  auto.
Qed.

Lemma IN_rewc : forall n s, rewc s [n] = [n].
Proof.
  intros.
  symmetry.
  apply constant_rew.
  induction n.
  simpl. 
  auto.
  simpl.
  auto.
Qed.

Lemma O0 : [O] = [0].
Proof.
  reflexivity.
Qed.

Inductive Q : Th :=
  | NEQ0S : Q ([fal][0][=/=][S]'0)
  | SINJ  : Q ([fal][fal][S]'0[=][S]'1[->]'0[=]'1)
  | PRED  : Q ([fal][0][=/=]'0[->][ext]'1[=][S]'0)
  | PL0   : Q ([fal][0][+]'0[=]'0)
  | PLUS  : Q ([fal][fal]([S]'0)[+]'1[=][S]('0[+]'1))
  | ML0   : Q ([fal][0][*]'0[=][0])
  | MULT  : Q ([fal][fal]([S]'0)[*]'1[=]('0[*]'1)[+]'1)
  | LE    : Q ([fal][fal]'0[<=]'1[<->][ext]'1[+]'0[=]'2).
Hint Constructors Q : core.

Inductive PA : Th :=
  | PA_Q  : forall p, Q p -> PA p
  | IND   : forall p, PA (p/([0]) [->] ([fal] p [->] p//([S] '0)) [->] [fal] p).
Hint Constructors PA : core.

Lemma PL00 : forall c, [0][+]c ==[Q] c.
Proof.
  intros.
  unfoldeq.
  assert (([0][+]'0[=]'0)/(c) = ([0][+]c[=]c)).
  simpl. reflexivity.
  rewrite <- H.
  apply fal_R.
  auto.
Qed.

Lemma PLUS0 : forall c d, ([S]c)[+]d ==[Q] [S](c[+]d).
Proof.
  intros.
  unfoldeq.
  assert ((([S]'0)[+]'1[=][S]('0[+]'1))/(c, d) = (([S]c)[+]d[=][S](c[+]d))).
  simpl. reflexivity.
  rewrite <- H.
  apply fal_R2.
  auto.
Qed.
  
Lemma MULT0 : forall c d, ([S]c)[*]d ==[Q] c[*]d[+]d.
Proof.
  intros.
  unfoldeq.
  assert ((([S]'0)[*]'1[=]('0[*]'1)[+]'1)/(c, d) = (([S]c)[*]d[=]c[*]d[+]d)).
  simpl. reflexivity.
  rewrite <- H.
  apply fal_R2.
  auto.
Qed.

Lemma  sfTQQ : sfT Q ≡ Q.
Proof.
  unfold eqvT, incT.
  split.
  - intros.
    destruct H.
    unfold sf.
    destruct H.
    simpl. auto.
    simpl. auto.
    simpl. auto.
    simpl. auto.
    simpl. auto.
    simpl. auto.
    simpl. auto.
    simpl. auto.
  - intros.
    assert(p = sf p). unfold sf.
    destruct H.
    simpl. auto.
    simpl. unfold sfc. simpl. auto.
    simpl. unfold sfc. simpl. auto.
    simpl. unfold sfc. simpl. auto.
    simpl. unfold sfc. simpl. auto.
    simpl. unfold sfc. simpl. auto.
    simpl. unfold sfc. simpl. auto.
    simpl. unfold sfc. simpl. auto.
    rewrite H0.
    auto.
Qed.

Ltac rewrite_formula x y :=
  let H := fresh "H" in
  let n0 := fresh "n" in
  assert(x = y);
  [unfold sf, sfc;
  try rewrite nested_rew;
  try rewrite nested_rewc;
  apply rew_rew;
  intros;
  repeat (lia || (destruct n0; simpl; [auto || apply IN_rewc| ])) |
  rewrite H; clear H].

Ltac rewrite_formula_in H0 x y :=
  let H := fresh "H" in
  let n0 := fresh "n" in
  assert(x = y);
  [unfold sf, sfc;
  try rewrite nested_rew;
  try rewrite nested_rewc;
  apply rew_rew;
  intros;
  repeat (lia || (destruct n0; simpl; [auto || apply IN_rewc| ])) |
  rewrite H in H0; clear H].