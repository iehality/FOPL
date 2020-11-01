Require Import Arith.
Require Import Lia.
Require Export FOPL.FOPL.
Require Export FOPL.Deduction.
Require Export FOPL.SetoidL.

Section deduction_facts2.
  Variable L : Lang.
  
  Lemma fal_repl : forall T p, 
    ([fal][fal]p) ==(T) ([fal][fal]p.['1;('0;fun x => '(S (S x)))]).
  Proof.
    assert(forall T p, T |- ([fal][fal]p)[->]([fal][fal]p.['1;('0;fun x => '(S (S x)))])).
    - intros.
      INTRO.
      GEN. apply sf_dsb.
      GEN. apply sf_dsb.
      assert(p.['0;('1;fun x => '(4 + x))].('1, '0) = p.['1;('0;fun x => '(S (S x)))]). {
        rewrite <- nested_rew.
        apply rew_rew.
        intros.
        destruct n.
        auto.
        destruct n.
        auto. auto.
      }
      rewrite <- H.
      apply fal_R2.
      assert(sf (sf ([fal][fal]p)) = ([fal][fal]p.['0; ('1; fun x => '(4 + x))])). {
        unfold sf. simpl.
        apply fal_eq.
        apply fal_eq.
        rewrite <- nested_rew.
        apply rew_rew.
        intros. unfold sfc. simpl.
        destruct n. auto.
        destruct n. auto.
        auto.
      }
      rewrite <- H0.
      AX.
    - intros.
      SPLIT.
      auto.
      assert(p = p.['1;('0;fun x => '(S (S x)))].['1;('0;fun x => '(S (S x)))]). {
        rewrite -> rew_id at 1.
        rewrite <- nested_rew.
        apply rew_rew.
        intros.
        destruct n. auto. simpl.
        destruct n. auto.
        auto.
      }
      rewrite -> H0 at 2.
      auto.
  Qed.
  
  Lemma sfT_add : forall T p, (T |- p) -> (sfT T |- sf p).
  Proof.
    unfold sf.
    intros.
    induction H.
    - simpl.
      apply GEN in IHprovable.
      assert((([fal]q.['0;fun x => '(3 + x)]).('0)) = ([fal] q.['0; fun x => sfc '(S x)])). {
        unfold sfc.
        simpl.
        rewrite <- nested_rew.
        apply fal_eq.
        apply rew_rew.
        intros.
        destruct n. simpl. auto.
        auto.
      }
      rewrite <- H0.
      apply fal_R.
      rewrite -> fal_repl.
      rewrite <- nested_rew.
      simpl.
      GEN.
  Abort.
  
End deduction_facts2.