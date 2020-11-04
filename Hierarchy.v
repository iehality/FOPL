
Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import FOPL.Arithmetic.

Set Implicit Arguments.

Fixpoint delta0 (p0 : LP) : bool :=
  match p0 with
  | [~]p   => delta0 p
  | p[->]q => (delta0 p) && (delta0 q)
  | x[=]y  => true
  | Pd2 _ _ _ => true
  | _ => false
  end.

Definition sigma1 (p0 : LP) : bool := delta0 p0 ||
  match p0 with
  | [~][fal][~]p => delta0 p
  | _ => false
  end.

Inductive arHie : bool -> nat -> LP -> Prop :=
| delta0_arh : forall b n p, Is_true(delta0 p) -> arHie b n p
| sigma_hie  : forall n p, arHie false n p -> arHie true (S n) ([ext]p)
| pie_hie    : forall n p, arHie true n p -> arHie false (S n) ([fal]p).

Definition stSigma n p := arHie true n p.
Definition stPie n p := arHie false n p.
Definition Delta0 p := Ar p = 0 /\ exists q, Ar q = 0 /\ Is_true (delta0 q) /\ (Q ||- p[<->]q).
Definition Sigma n p := Ar p = 0 /\ exists q, Ar q = 0 /\ stSigma n q /\ (Q ||- p[<->]q).
Definition Pie n p := Ar p = 0 /\ exists q, Ar q = 0 /\ stPie n q /\ (Q ||- p[<->]q).

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
