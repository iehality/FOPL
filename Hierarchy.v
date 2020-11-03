
Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import FOPL.Arithmetic.

Set Implicit Arguments.

Check ([fal]'0[<=]'1[->][0][=][1]).

Fixpoint delta0 (p0 : LP) : bool :=
  match p0 with
  | [~]p   => delta0 p
  | p[->]q => (delta0 p) && (delta0 q)
  | x[=]y  => true
  | Pd2 _ _ _ => true
  | _ => false
  end.

Fixpoint arithhie (b : bool) (n0 : nat) (p0 : LP) : bool :=
  if (delta0 p0) then true else
  match n0 with
  | S n =>
    match p0 with
    | [~]p   => arithhie (negb b) n0 p
    | [fal]p => 
      match b with
      | true  => arithhie false n p
      | false => false
      end
    | _ => false
    end
  | _ => false
  end.

Definition pieform n p := arithhie true (2*n) p.
Definition sigmaform n p := arithhie false (2*n) p.
Definition Delta0 p := Ar p = 0 /\ exists q, Ar q = 0 /\ Is_true (delta0 q) /\ (Q ||- p[<->]q).
Definition Pie n p := Ar p = 0 /\ exists q, Is_true (pieform n q) /\ (Q ||- p[<->]q).
Definition Sigma n p := Ar p = 0 /\ exists q, Is_true (sigmaform n q) /\ (Q ||- p[<->]q).

Lemma delta0_rew : forall p s, delta0 p = delta0 p.[s].
Proof.
  induction p.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl.
    intros.
    rewrite <- IHp1.
    rewrite <- IHp2.
    reflexivity.
  - simpl. auto.
  - simpl. auto.
Qed.

Fixpoint And (f : nat -> LP) (n0 : nat) :=
  match n0 with
  | 0 => f 0
  | S n => (And f n)[/\](f n0)
  end.

Lemma bounded_quantifiar : forall n p, Q ||- ([fal]'0[<=][n][->]p)[<->](And (fun x => p.([x])) n).
Proof.
  induction n.
  - intros.
    simpl.
    SPLIT.
    + INTRO.
      MP (('0[<=][0][->]p).([0])).
      apply fal_R. 
      AX.
      simpl.
      INTRO.
      MP ([O][<=][O]).
      WL. WL.
      assert([O] = [0]). simpl. reflexivity.
      rewrite -> H.
      apply le_compl. lia.
      AX.
    + INTRO.
      GEN.
      rewrite <- le_replace.
      unfold sfc.
      simpl.
      apply ext_L.
      apply sf_dsb.
Abort.
