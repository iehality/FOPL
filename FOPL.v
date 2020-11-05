Require Export Classical.
Require Export FunctionalExtensionality.
Require Import Arith.
Require Import Lia.
(* coqc -Q FOPL FOPL FOPL/FOPL.v *)


(**)

  Lemma lt_lt_max_l : forall n m r, n < m -> n < max m r.
  Proof.
    unfold lt.
    intros.
    assert (lml := (Nat.le_max_l m r)).
    apply Nat.le_trans with (m := m).
    auto.
    auto.
  Qed.

  Lemma lt_lt_max_r : forall n m r, n < m -> n < max r m.
  Proof.
    unfold lt.
    intros.
    assert (lml := (Nat.le_max_r r m)).
    apply Nat.le_trans with (m := m).
    auto.
    auto.
  Qed.

  Lemma le_le_max_l : forall n m r, n <= m -> n <= max m r.
  Proof.
    intros.
    assert (lml := (Nat.le_max_l m r)).
    apply Nat.le_trans with (m := m).
    auto.
    auto.
  Qed.

  Lemma le_le_max_r : forall n m r, n <= m -> n <= max r m.
  Proof.
    intros.
    assert (lml := (Nat.le_max_r r m)).
    apply Nat.le_trans with (m := m).
    auto.
    auto.
  Qed.

(**)

Class Lang := {fc0 : Type; fc1 : Type; fc2 : Type; pd0 : Type; pd1 : Type; pd2 : Type}.

Inductive Term {L : Lang} :=
| var : nat -> Term
| cns : Term
| Fc0 : fc0 -> Term
| Fc1 : fc1 -> Term -> Term
| Fc2 : fc2 -> Term -> Term -> Term.

Inductive Formula {L : Lang} :=
| eql : Term -> Term -> Formula
| Pd0 : pd0 -> Formula
| Pd1 : pd1 -> Term -> Formula
| Pd2 : pd2 -> Term -> Term -> Formula
| imp : Formula -> Formula -> Formula
| neg : Formula -> Formula
| fal : Formula -> Formula.

Notation "' v " := (var v) (at level 5).
Notation "𝟬" := ('0).
Notation "𝟭" := ('1).
Notation "𝟮" := ('2).
Notation "𝟯" := ('3).
Notation "[O]" := (cns) (at level 0).
Notation "a [=] b" := (eql a b) (at level 60, right associativity).
Notation "p [->] q" := (imp p q) (at level 62, right associativity, q at level 200).
Notation "[~] p" := (neg p) (at level 61, right associativity).
Notation "[fal] p" := (fal p) (at level 66, right associativity).
Notation "[∀] p" := (fal p) (at level 66, right associativity).

Definition andl {L : Lang} p q := neg (imp p (neg q)).
Notation "p [/\] q" := (andl p q) (at level 63, right associativity).
Definition orl {L : Lang}  p q := imp (neg p) q.
Notation "p [\/] q" := (orl p q) (at level 64, right associativity).
Definition iffl {L : Lang} p q := (p[->]q)[/\](q[->]p).
Notation "p [<->] q" := (iffl p q) (at level 65, right associativity, q at level 200).
Definition ext {L : Lang}  p := neg (fal (neg p)).
Notation "[ext] p" := (ext p) (at level 66, right associativity).
Notation "[∃] p" := (ext p) (at level 66, right associativity).
Notation "a [=/=] b" := ([~] a [=] b) (at level 60, no associativity).

Definition slide {A : Type} (s : nat -> A) (n : A) : nat -> A := fun x0 => 
  match x0 with
  | 0 => n
  | S m => s m
  end.
  
Definition embed {A : Type} (s : nat -> A) (a : A) : nat -> A := fun n => 
  match n with 
  | 0 => a 
  | _ => s n 
  end.

Notation "( n ; s )" := (slide s n) (at level 0).
Notation "( n .; s )" := (embed s n) (at level 0).

Fixpoint rewc {L : Lang} (s : nat -> Term) (c : Term) : Term :=
  match c with
  | var v     => s v
  | cns       => cns
  | Fc0 c     => Fc0 c
  | Fc1 c x   => Fc1 c (rewc s x)
  | Fc2 c x y => Fc2 c (rewc s x) (rewc s y)
  end.

Definition sfc {L : Lang} (c : Term) := rewc (fun x => (var (S x))) c.

Fixpoint rew {L : Lang} (s : nat -> Term) (p0 : Formula) : Formula :=
  match p0 with
  | eql x y   => eql (rewc s x) (rewc s y)
  | Pd0 c     => Pd0 c
  | Pd1 c x   => Pd1 c (rewc s x)
  | Pd2 c x y => Pd2 c (rewc s x) (rewc s y)
  | imp p q   => imp (rew s p) (rew s q)
  | neg p     => neg (rew s p)
  | fal p     => fal (rew ((var 0); fun x => (sfc (s x))) p)
  end.

Notation "p .[ s ]" := (rew s p) (at level 20).
Notation "p .[ n ; s ]" := (p .[(n;s)]) (at level 20).
Notation "\0" := (fun x => (var x)) (at level 0).
Definition sf {L : Lang} (p : Formula) : Formula := p .[fun x => (var (S x))].
Definition alt {L : Lang} (p : Formula) : Formula := p.[fun x => '(pred x)].
Notation "🠙 t" := (sfc t) (at level 5, right associativity).
Notation "🡑 p" := (sf p) (at level 5, right associativity).
Notation "🡓 p" := (alt p) (at level 5, right associativity).
Definition norm {L : Lang} c p := p .[fun x => c].
Notation "p /( x )" := (p .[x;\0]) (at level 50).
Notation "p /( x , y )" := (p .[x; (y; \0)]) (at level 50).
Notation "p /( x , y , z )" := (p .[x; (y; (z; \0))]) (at level 50).
Notation "p //( x )" := (p .[(x.;\0)]) (at level 50).

(** ** Syntax Facts *)
Section basic_facts.
  Variable L : Lang.

  Lemma nested_rewc : forall s0 s1 t, (rewc s1 (rewc s0 t)) = rewc (fun x => rewc s1 (s0 x)) t.
  Proof.
    intros.
    induction t.
    - simpl.
      auto.
    - simpl.
      auto.
    - simpl.
      auto.
    - simpl.
      rewrite IHt.
      auto.
    - simpl.
      rewrite IHt1.
      rewrite IHt2.
      auto.
  Qed.

  Lemma rewcsf_rwec : forall t0 s t, rewc (t0;s) (sfc t) = rewc s t.
  Proof.
    intros. unfold sfc.
    induction t.
    - simpl.
      auto.
    - simpl.
      auto.
    - simpl.
      auto.
    - simpl.
      rewrite IHt.
      auto.
    - simpl.
      rewrite IHt1.
      rewrite IHt2.
      auto.
  Qed.

  Lemma nested_rew : forall p s0 s1, p.[s0].[s1] = p.[fun x => rewc s1 (s0 x)].
  Proof.
    induction p.
    - simpl.
      intros.
      rewrite nested_rewc.
      rewrite nested_rewc.
      auto.
    - simpl.
      auto.
    - simpl.
      intros.
      rewrite nested_rewc.
      auto.
    - simpl.
      intros.
      rewrite nested_rewc.
      rewrite nested_rewc.
      auto.
    - simpl.
      intros.
      rewrite <- IHp1.
      rewrite <- IHp2.
      auto.
    - simpl.
      intros.
      rewrite <- IHp.
      auto.
    - simpl.
      intros.
      rewrite IHp.
      assert (
        (fun x => rewc ((var 0); fun x0 => sfc (s1 x0)) (((var 0); fun x0 => sfc (s0 x0)) x)) =
        ((var 0); fun x => sfc (rewc s1 (s0 x)))
      ).
      + apply functional_extensionality.
        intros.
        destruct x.
        simpl.
        auto.
        simpl.
        rewrite rewcsf_rwec.
        unfold sfc.
        rewrite nested_rewc.
        auto.
      + rewrite H.
        auto.
  Qed.

  Lemma neg_sbs : forall p t, (neg p)/(t) = neg (p/(t)).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Lemma fal_eq : forall p q, p = q -> [fal]p = [fal]q.
  Proof.
    intros.
    rewrite <- H.
    reflexivity.
  Qed.

  Lemma rewc_id : forall t, t = rewc \0 t.
  Proof.
    induction t.
    - simpl. auto.
    - simpl. auto.
    - simpl. auto.
    - simpl. 
      rewrite <- IHt.
      auto.
    - simpl.
      rewrite <- IHt1.
      rewrite <- IHt2.
      auto.
  Qed.

  Lemma rew_id : forall p, p = p.[\0].
  Proof.
    induction p.
    - simpl. 
      rewrite <- rewc_id.
      rewrite <- rewc_id.
      auto.
    - simpl. auto.
    - simpl. 
      rewrite <- rewc_id.
      auto.
    - simpl.
      rewrite <- rewc_id.
      rewrite <- rewc_id.
      auto.
    - simpl.
      rewrite <- IHp1.
      rewrite <- IHp2.
      auto.
    - simpl.
      rewrite <- IHp.
      auto.
    - simpl.
      assert (\0 = ((var 0); fun x => sfc (var x))).
      + unfold sfc.
        apply functional_extensionality.
        intros.
        destruct x.
        simpl.
        auto.
        simpl.
        auto.
      + rewrite <- H.
        rewrite <- IHp.
        auto.
  Qed.

  Lemma rewc_sfc : forall t u, t = rewc (u; \0) (sfc t).
  Proof.
    unfold sfc.
    intros.
    rewrite nested_rewc.
    simpl.
    apply rewc_id.
  Qed.

  Lemma alt_sf : forall p, alt (sf p) = p.
  Proof.
    intros.
    unfold alt, sf.
    rewrite nested_rew.
    simpl.
    rewrite rew_id.
    auto.
  Qed.
  
End basic_facts.
  
Fixpoint Art {L : Lang} (t0 : Term) : nat :=
  match t0 with
  | var n     => S n
  | cns       => 0
  | Fc0 _     => 0
  | Fc1 _ x   => Art x
  | Fc2 _ x y => max (Art x) (Art y)
  end.

Fixpoint Ar {L : Lang} (p0 : Formula) : nat :=
  match p0 with
  | eql t u   => max (Art t) (Art u)
  | Pd0 _     => 0
  | Pd1 _ x   => Art x
  | Pd2 _ x y => max (Art x) (Art y)
  | imp p q   => max (Ar p) (Ar q)
  | neg p     => Ar p
  | fal p     => pred (Ar p)
  end.

Section rew_facts.
  Variable L : Lang.

  Lemma rewc_rewc : forall t s0 s1, (forall n, n < Art t -> s0 n = s1 n) -> rewc s0 t = rewc s1 t.
  Proof.
    intros.
    induction t.
    - simpl.
      apply H.
      simpl.
      lia.
    - simpl.
      auto.
    - simpl.
      auto.
    - simpl.
      assert (rewc s0 t = rewc s1 t).
      apply IHt.
      intros.
      apply H.
      simpl.
      auto.
      rewrite <- H0.
      auto.
    - simpl.
      assert (rewc s0 t1 = rewc s1 t1).
      apply IHt1.
      intros.
      apply H.
      simpl.
      apply lt_lt_max_l. auto.
      assert (rewc s0 t2 = rewc s1 t2).
      apply IHt2.
      intros.
      apply H.
      simpl.
      apply lt_lt_max_r. auto.
      rewrite <- H0. 
      rewrite <- H1.
      auto.
  Qed.

  Lemma rew_rew : forall p s0 s1, (forall n, n < Ar p -> s0 n = s1 n) -> p .[s0] = p .[s1].
  Proof.
    induction p.
    - simpl.
      intros.
      assert (rewc s0 t = rewc s1 t).
      apply rewc_rewc.
      intros.
      apply H.
      apply lt_lt_max_l. auto.
      assert (rewc s0 t0 = rewc s1 t0).
      apply rewc_rewc.
      intros.
      apply H.
      apply lt_lt_max_r. auto.
      rewrite <- H0.
      rewrite <- H1.
      auto.
    - simpl.
      auto.
    - simpl.
      intros.
      assert (rewc s0 t = rewc s1 t).
      apply rewc_rewc.
      intros.
      auto.
      rewrite <- H0.
      auto.
    - simpl.
      intros.
      assert (rewc s0 t = rewc s1 t).
      apply rewc_rewc.
      intros.
      apply H.
      apply lt_lt_max_l. auto.
      assert (rewc s0 t0 = rewc s1 t0).
      apply rewc_rewc.
      intros.
      apply H.
      apply lt_lt_max_r. auto.
      rewrite <- H0.
      rewrite <- H1.
      auto.
    - simpl.
      intros.
      assert (p1 .[s0] = p1 .[s1]).
      + apply IHp1.
        intros.
        apply H.
        apply lt_lt_max_l.
        auto.
      + assert (p2 .[s0] = p2 .[s1]).
        apply IHp2.
        intros.
        apply H.
        apply lt_lt_max_r.
        auto.
      rewrite <- H0.
      rewrite <- H1.
      auto.
    - simpl.
      intros.
      rewrite <- (IHp s0 s1 H).
      auto.
    - simpl.
      intros.
      assert (p .[(var 0); fun x => sfc (s0 x)] = p .[(var 0); fun x => sfc (s1 x)]).
      + apply IHp.
        unfold sfc. intros.
        destruct n.
        simpl. auto.
        simpl.
        assert (s0 n = s1 n).
        * apply H.
          lia.
        * rewrite <- H1.
          auto.
      + rewrite <- H0.
        auto.
  Qed.

  Lemma constant_rew : forall t s, Art t = 0 -> t = rewc s t.
  Proof.
    intros.
    assert ( rewc \0 t = rewc s t).
    - apply rewc_rewc.
      rewrite H.
      lia.
    - rewrite <- H0.
      apply rewc_id.
  Qed. 

  Lemma sentence_rew : forall p s, Ar p = 0 -> p = p .[s].
  Proof.
    intros.
    assert (p .[\0] = p .[s]).
    - apply rew_rew.
      rewrite H.
      intros.
      destruct n.
      lia.
      lia.
    - rewrite <- H0.
      apply rew_id.
  Qed. 

  Lemma form1_p_ps : forall p s, Ar p = 1 -> (var 0 = s 0) -> p = p .[s].
  Proof.
    intros.
    assert (p .[\0] = p .[s]).
    - apply rew_rew.
      rewrite H.
      intros.
      destruct n.
      auto.
      lia.
    - rewrite <- H1.
      apply rew_id.
  Qed. 

  Lemma form2_ps_ps : forall p s0 s1, Ar p = 2 -> (s0 0 = s1 0) -> (s0 1 = s1 1) -> p .[s0] = p .[s1].
  Proof.
    intros.
    apply rew_rew.
    rewrite H.
    intros.
    destruct n.
    auto.
    destruct n.
    auto.
    lia.
  Qed. 

  Lemma form3_ps_ps : forall p s0 s1, Ar p = 3 -> (s0 0 = s1 0) -> (s0 1 = s1 1) -> (s0 2 = s1 2) -> p .[s0] = p .[s1].
  Proof.
    intros.
    apply rew_rew.
    intros.
    destruct n. auto.
    destruct n. auto.
    destruct n. auto.
    lia.
  Qed.

  Lemma form3_rw0 : forall p s, Ar p = 3 -> p/(s 0, s 1, s 2) = p .[s].
  Proof.
    intros.
    apply rew_rew.
    rewrite H.
    intros.
    destruct n.
    simpl. auto.
    destruct n.
    simpl. auto.
    destruct n.
    simpl. auto.
    lia.
  Qed.

  Lemma Art_rew_le: forall t s n, 
    (forall m, m < Art t -> Art (s m) <= n) ->
    Art (rewc s t) <= n.
  Proof.
    intros.
    induction t.
    - simpl. auto.
    - simpl. lia.
    - simpl. lia.
    - simpl. auto.
    - simpl.
      simpl in H.
      apply Nat.max_lub.
      apply IHt1. intros. apply H. lia.
      apply IHt2. intros. apply H. lia.
  Qed.

  Lemma Ar_rew_le : forall p s n,
    (forall m, m < Ar p -> Art (s m) <= n) -> Ar (p.[s]) <= n.
  Proof.
    assert(le_pred : forall n m, n <= S m -> pred n <= m).
    {intros. lia. }
    induction p.
    - simpl.
      intros.
      apply Nat.max_lub.
      rewrite (Art_rew_le _ _ n). lia. intros. apply H. lia.
      rewrite (Art_rew_le _ _ n). lia. intros. apply H. lia.
    - simpl. lia.
    - simpl.
      intros.
      rewrite (Art_rew_le _ _ n). lia. intros. apply H. lia.
    - simpl.
      intros.
      apply Nat.max_lub.
      rewrite (Art_rew_le _ _ n). lia. intros. apply H. lia.
      rewrite (Art_rew_le _ _ n). lia. intros. apply H. lia.
    - simpl.
      intros.
      apply Nat.max_lub.
      apply IHp1. intros. apply H. lia.
      apply IHp2. intros. apply H. lia.
    - simpl.
      intros.
      apply IHp. intros. apply H. lia.
    - simpl.
      intros.
      unfold sfc.
      apply le_pred.
      apply IHp.
      intros.
      destruct m.
      simpl. lia.
      simpl.
      apply Art_rew_le. simpl.
      intros.
      assert(Art (s m) <= n).
      apply H. lia.
      lia.
  Qed.

  Lemma of_constant : forall p t, 
    Ar p <= 1 -> Art t = 0 -> Ar (p/(t)) = 0.
  Proof.
    intros.
    assert(Ar (p/(t)) <= 0).
    apply Ar_rew_le.
    intros.
    destruct m.
    simpl. lia.
    lia.
    lia.
  Qed.

End rew_facts.
