Require Import FOPL.FOA.

Set Implicit Arguments.


Parameter T : Th.
Parameter code : Formula -> nat.
Axiom code_inj : forall p q, code p = code q -> p = q.
Notation "⌜ p ⌝" := (code p) (at level 0).

(** * Diagonal Lemma *)

Parameter Γ : Formula.
Axiom artG : Ar Γ = 3.
Axiom Gdefg : forall p n, T ||- [fal]Γ/([⌜p⌝], n, '0) [<->] '0[=][⌜p/(n)⌝].

Section FixPoint.
  
  Variable θ : Formula.
  Hypothesis opf : Ar θ = 1.
  Definition σ : Formula := [fal](Γ/('1, '1, '0)[->]θ/('0)).
    
  Lemma sigiff : forall p, T ||- σ/([⌜p⌝])[<->]θ/([⌜p/([⌜p⌝])⌝]).
  Proof.
    intros.
    assert(artG := artG).
    assert(Gdefg := Gdefg).
    unfold σ.
    fsimpl.
    specialize(Gdefg p [⌜p⌝]).
    apply fal_and_destruct in Gdefg.
    destruct Gdefg.
    fsplit.
    + fintro.
      MP(Γ/([⌜p⌝], [⌜p⌝], [⌜p/([⌜p⌝])⌝])).
      WL.
      fspecialize H0 [⌜p/([⌜p⌝])⌝].
      fsimpl_in H0.
      fapply H0.
      auto.
      Tpp.
      fspecialize H1 [⌜p/([⌜p⌝])⌝].
      fsimpl_in H1.
      auto.
    + fintro.
      apply fal_trans with (q := '0 [=] [⌜p/([⌜p⌝])⌝]).
      WL.
      auto.
      GEN.
      fintro.
      fsimpl.
      MP (θ/([⌜p/([⌜p⌝])⌝])). auto.
      MP ([⌜p/([⌜p⌝])⌝] [=] '0).
      fsymmetry.
      auto.
      auto.
  Qed.

    (** $\gamma := (\dot{\forall} (\Gamma/('1, '1, '0) \dot{\to} \theta/('0)))/(\delta \ulcorner \dot{\forall} (\Gamma/('1, '1, '0) \dot{\to} \theta/('0)) \urcorner )$ *)

  Definition fixpoint := σ/([⌜σ⌝]).

  Lemma Diagonal : T ||- fixpoint [<->] θ/([⌜fixpoint⌝]).
  Proof. 
    apply sigiff.
  Qed.

End FixPoint.

Theorem Undefinability : Consis T -> ~ (exists Tr, Ar Tr = 1 /\ forall p, T ||- p [<->] Tr/([⌜p⌝])).
Proof.
  intros conT. intro.
  destruct H as [Tr].
  destruct H.
  assert (Ar ([~] Tr) = 1).
  simpl. auto.
  pose (d := fixpoint ([~] Tr)).
  assert (D := Diagonal ([~] Tr) H1). fold d in D.
  specialize (H0 d).
  rewrite neg_sbs in D.
  fdestruct H0.
  fdestruct D.
  apply conT.
  exists d.
  split.
  - apply pNNPP.
    apply neg_intro.
    fintro.
    MP ([~] [~] Tr/([⌜d⌝])).
    apply deduction_inv.
    apply contrad_add. auto.
    apply contrad_add.
    apply contrad_add.
    WL. auto.
  - apply neg_intro.
    fintro.
    MP ([~] Tr/([⌜d⌝])).
    apply deduction_inv. auto.
    apply contrad_add.
    WL.
    auto.
Qed.
  

  (** ** Incompleteness *)
  
  Section Incompleteness1.
    
    Variable prov : nat -> nat -> Prop.
    Hypothesis proofH : forall p, (T ||- p) <-> (exists n, prov n ⌜p⌝).  
  
    Variable Prov : Formula.
    Hypothesis arProv : Ar Prov = 2.
    Hypothesis ProvH : forall n m, prov n m <-> (T ||- Prov/([n], [m])). 
    Hypothesis nProvH : forall n m, ~ prov n m <-> (T ||- [~] Prov/([n], [m])).
  
    Local Definition Pr : Formula := [ext] Prov/('0, '1).
    Hint Unfold Pr : core.

    Let Omega_ConT := forall p, (forall n, T ||- [~] p/([n])) -> ~ (T ||- ext p).

    Lemma Prov_ext : Omega_ConT -> forall p, (T ||- Pr/([⌜p⌝])) -> exists n, (T ||- Prov/([n], [⌜p⌝])).
    Proof.
      unfold Pr.
      intros.
      fsimpl_in H0.
      apply NNPP.
      contradict H0.
      apply H.
      intros.
      fsimpl.
      rewrite <- nProvH.
      intro.
      rewrite ProvH in H1.
      apply H0.
      exists n.
      auto.
    Qed.
  
    Lemma E1 : forall p, Omega_ConT -> (T ||- p) <-> (T ||- Pr/([⌜p⌝])).
    Proof.
      intros.
      split.
      - intros.
        rewrite proofH in H0.
        destruct H0 as [n].
        unfold Pr.
        fsimpl.
        fexists [n].
        fsimpl.
        rewrite <-ProvH.
        auto.
      - intros.
        assert (exists n, (T ||- Prov/([n], [⌜p⌝]))).
        + apply Prov_ext.
          auto. auto.
        + destruct H1 as [n].
          rewrite proofH.
          exists n.
          rewrite ProvH.
          auto.
    Qed.
  
    Lemma OmCon_Con : Omega_ConT -> Consis T.
    Proof.
      intros.
      apply NNPP.
      intro.
      specialize (H ([~] [O] [=] [O])).
      assert (~ (T ||- ext ([~] [O] [=] [O]))).
      apply H.
      intros.
      simpl.
      apply pNN.
      auto.
      apply explosion with (p := ext ([~] [O] [=] [O])) in H0.
      auto.
    Qed.
  
    Local Definition ConGT : Formula := [~] Pr/([⌜[~][0][=][0]⌝]).
    Local Definition G : Formula := fixpoint ([~] Pr).
  
    Local Lemma Gfixpoint : T ||- G [<->] [~]Pr/([⌜G⌝]).
    Proof.
      assert (Ar ([~] Pr) = 1).
      simpl.
      rewrite_formula (Prov /('0, '1)) (Prov.[\0]). rewrite <- rew_id.
      lia.
      assert (D := Diagonal ([~] Pr) H).
      fold G in D. 
      rewrite neg_sbs in D.
      auto.
    Qed.
  
    Theorem Incompleteness1 : Omega_ConT -> ~ (T ||- G) /\ ~ (T ||- [~] G).
    Proof.
      intros.
      assert (gf := Gfixpoint).
      fdestruct gf.
      assert (con := OmCon_Con H).    
      split.
      - intro.
        destruct con.
        exists (Pr/([⌜G⌝])).
        split.
        + rewrite <- E1.
          auto. auto.
        + MP G. auto.
          auto.
      - intro.
        destruct con.
        exists G.
        split.
        + rewrite -> E1.
          apply pNNPP.
          MP ([~] G). auto.
          apply contrad_add.
          auto.
          auto.
        + auto.
    Qed.
  
  End Incompleteness1.

  Section Incompleteness2.
  
    Variable Pr : Formula.
    Hypothesis arPr : Ar Pr = 1.
    
    Hypothesis D1 : forall p, T ||- p -> T ||- Pr/([⌜p⌝]).
    Hypothesis D2 : forall p q, T ||- Pr/([⌜p[->]q⌝]) [->] Pr/([⌜p⌝]) [->] Pr/([⌜q⌝]).
    Hypothesis D3 : forall p, T ||- Pr/([⌜p⌝]) [->] Pr/([⌜Pr/([⌜p⌝])⌝]).
    
    Definition γ : Formula := fixpoint ([~] Pr).
    Definition ConT : Formula := [~] Pr/([⌜[~][0][=][0]⌝]).
    
    Lemma nPrfix : T ||- γ[<->][~]Pr/([⌜γ⌝]).
    Proof.
      assert (Ar ([~] Pr) = 1).
      simpl.
      auto.
      assert (D := Diagonal ([~] Pr) H).
      fold γ in D. 
      rewrite -> neg_sbs in D.
      auto.
    Qed.
    
    Lemma Consis_g : T ||- ConT [->] γ.
    Proof.
      assert (D := nPrfix). 
      fdestruct D.
      unfold ConT.
      apply contrad_elim.
      fintro.
      apply pNN.
      assert (forall p, T ¦ ([~] γ) ||- Pr/([⌜p⌝])).
      - intros.
        MP (Pr/([⌜[~]Pr/([⌜γ⌝])⌝])).
        + MP (Pr/([⌜γ⌝])).
          apply pNNPP.
          apply deduction_inv.
          apply contrad_add. auto.
          MP (Pr/([⌜γ[->][~]Pr/([⌜γ⌝])⌝])).
          WL.
          apply D1. auto.
          WL.        
          apply D2.
        + MP (Pr/([⌜[~]Pr/([⌜γ⌝])[->]p⌝])).
          MP (Pr/([⌜Pr/([⌜γ⌝])⌝])).
          MP (Pr/([⌜γ⌝])).
          apply pNNPP.
          apply deduction_inv.
          apply contrad_add. auto.
          WL.
          apply D3.
          MP (Pr/([⌜Pr/([⌜γ⌝])[->][~]Pr/([⌜γ⌝])[->]p⌝])).
          WL.
          apply D1.
          fintro. fintro.
          apply explosion.
          intro. destruct H1.
          exists (Pr/([⌜γ⌝])). split.
          auto. auto.
          WL.
          apply D2.
          WL.
          apply D2.
      - auto.
    Qed.
    
    Theorem Incompleteness2 : T ||- ConT -> ~ Consis T.
    Proof.
      assert (D := nPrfix).
      fdestruct D.
      intros.
      assert (T ||- γ).
      MP ConT. auto.
      apply Consis_g.    
      intro. 
      destruct H3.
      exists (Pr/([⌜γ⌝])).
      split.
      apply D1.
      auto.
      MP γ. auto.
      auto.
    Qed.
  
    Lemma pr_distr : forall p q r, (T ¦ r ||- Pr/([⌜p[->]q⌝])) -> (T ¦ r ||- Pr/([⌜p⌝]) [->] Pr/([⌜q⌝])).
    Proof.
      intros.
      MP (Pr/([⌜p[->]q⌝])). auto.
      WL.
      apply D2.
    Qed. 
  
    Theorem Loeb : forall p, Ar p = 0 -> (T ||- Pr/([⌜p⌝]) [->] p) -> (T ||- p).
    Proof.
      intros.
      assert (Ar (Pr/('0) [->] p) = 1).
      {simpl. rewrite_formula (Pr/('0)) (Pr.[\0]). rewrite <- rew_id. lia. }
      pose (q := fixpoint (Pr/('0) [->] p)).
      assert (D := Diagonal _ H1). fold q in D.
      fsimpl_in D.
  
      fdestruct D.
      assert (T ||- Pr/([⌜q⌝]) [->] p).
      - fintro.
        MP (Pr/([⌜p⌝])).
        MP (Pr/([⌜Pr/([⌜q⌝])⌝])).
        apply deduction_inv.
        apply D3.
        MP (Pr/([⌜Pr/([⌜q⌝])[->]p⌝])).
        apply deduction_inv.
        MP (Pr/([⌜q[->]Pr/([⌜q⌝])[->]p⌝])).
        apply D1.
        auto.
        apply D2.
        WL.
        apply D2.
        WL.
        auto.
      - MP (Pr/([⌜q⌝])).
        apply D1.
        MP (Pr/([⌜q⌝]) [->] p).
        auto.
        auto.
        auto.
    Qed.
  
  End Incompleteness2.
  
End Incompleteness.
