Require Import FOPL.FOA.

Set Implicit Arguments.

Parameter code : Formula -> nat.
Axiom code_inj : forall p q, code p = code q -> p = q.
Notation "⌜ p ⌝" := (code p) (at level 0).

(** * Diagonal Lemma *)

Parameter Γ : Formula.
Axiom artG : Ar Γ = 3.
Axiom Gdefg : forall p n, PA ||- [fal]Γ/([⌜p⌝], n, '0) [<->] '0[=][⌜p/(n)⌝].

Section FixPoint.
  
  Variable θ : Formula.
  Hypothesis opf : Ar θ = 1.
  Definition σ : Formula := [fal](Γ/('1, '1, '0)[->]θ/('0)).
    
  Lemma sigiff : forall p, PA ||- σ/([⌜p⌝])[<->]θ/([⌜p/([⌜p⌝])⌝]).
  Proof.
    intros.
    assert(artG := artG).
    assert(Gdefg := Gdefg).
    assert (θrew : forall s, θ = θ .[('0);s]).
    intros.
    apply form1_p_ps.
    auto.
    simpl. auto.
    unfold σ.
    simpl.
    rewrite_formula ((Γ /('1, '1, '0)).['0; fun x => sfc (([⌜p⌝]; \0) x)]) (Γ /( [⌜p⌝], [⌜p⌝], '0)).
    rewrite_formula ((θ /('0)).['0; fun x => sfc (([⌜p⌝]; \0) x)]) (θ /('0)).
    specialize(Gdefg p [⌜p⌝]).
    apply fal_and_destruct in Gdefg.
    destruct Gdefg.
    fsplit.
    + fintro.
      Tpp.
      fspecialize H1 [⌜p/([⌜p⌝])⌝].
      rewrite_formula_in H1 (Γ /([⌜p⌝], [⌜p⌝], '0)/([⌜p/([⌜p⌝])⌝])) (Γ /([⌜p⌝], [⌜p⌝], [⌜p/([⌜p⌝])⌝])).
      rewrite_formula_in H1 (θ/('0)/([⌜p/([⌜p⌝])⌝])) (θ /([⌜p/([⌜p⌝])⌝])).
      MP(Γ/([⌜p⌝], [⌜p⌝], [⌜p/([⌜p⌝])⌝])).
      WL.
      fspecialize H0 [⌜p/([⌜p⌝])⌝].
      repeat rewrite IN_rewc in H0.
      rewrite_formula_in H0 (Γ /([⌜p⌝], [⌜p⌝], '0)/([⌜p/([⌜p⌝])⌝])) (Γ /([⌜p⌝], [⌜p⌝], [⌜p/([⌜p⌝])⌝])).
      papply H0.
      auto.
      auto.
    + fintro.
      apply fal_trans with (q := '0 [=] [⌜p/([⌜p⌝])⌝]).
      WL.
      auto.
      GEN.
      fintro.
      rewrite_formula (sf (θ/([⌜p/([⌜p⌝])⌝]))) (θ/([⌜p/([⌜p⌝])⌝])).
      MP (θ/([⌜p/([⌜p⌝])⌝])). auto.
      MP ([⌜p/([⌜p⌝])⌝] [=] '0).
      fsymmetry.
      auto.
      auto.
  Qed.

    (** $\gamma := (\dot{\forall} (\Gamma/('1, '1, '0) \dot{\to} \theta/('0)))/(\delta \ulcorner \dot{\forall} (\Gamma/('1, '1, '0) \dot{\to} \theta/('0)) \urcorner )$ *)

  Definition fixpoint := σ/([⌜σ⌝]).

  Lemma Diagonal : PA ||- fixpoint [<->] θ/([⌜fixpoint⌝]).
  Proof. 
    apply sigiff.
  Qed.

End FixPoint.

Theorem Undefinability : Consis PA -> ~ (exists Tr, Ar Tr = 1 /\ forall p, PA ||- p [<->] Tr/([⌜p⌝])).
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
    Hypothesis proofH : forall p, (PA ||- p) <-> (exists n, prov n ⌜p⌝).  
  
    Variable Prov : Formula.
    Hypothesis arProv : Ar Prov = 2.
    Hypothesis ProvH : forall n m, prov n m <-> (PA ||- Prov/([n], [m])). 
    Hypothesis nProvH : forall n m, ~ prov n m <-> (PA ||- [~] Prov/([n], [m])).
  
    Let PrG : Formula := ext Prov.
  
    Lemma Pr_sbs : forall n, PrG/([n]) = ext (Prov/('0, [n])).
    Proof.
      unfold ext.
      intros.
      simpl.
      assert (Prov.['0; fun x => sfc (([n]; \0) x)] = Prov/('0, [n])).
      apply rew_rew.
      rewrite arProv.
      intros.
      destruct n0.
      simpl.
      auto.
      destruct n0.
      simpl.
      apply IN_rewc.
      lia.
      rewrite H.
      auto.
    Qed.
  
    Lemma Prov_sbs : forall n m, Prov/('0, [n])/([m]) = Prov/([m], [n]).
    Proof.
      intros.
      simpl.
      rewrite <- nested_rew.
      apply rew_rew.
      rewrite -> arProv.
      intros.
      destruct n0.
      simpl.
      auto.
      destruct n0.
      simpl.
      apply IN_rewc.
      lia.
    Qed.

    Let Omega_ConT := forall p, (forall n, PA ||- [~] p/([n])) -> ~ (PA ||- ext p).

    Lemma Prov_ext : Omega_ConT -> forall p, (PA ||- PrG/([⌜p⌝])) -> exists n, (PA ||- Prov/([n], [⌜p⌝])).
    Proof.
      intros.
      rewrite -> Pr_sbs in H0.
      apply NNPP.
      contradict H0.
      apply H.
      intros.
      rewrite -> Prov_sbs.
      rewrite <- nProvH.
      intro.
      rewrite -> ProvH in H1.
      apply H0.
      exists n.
      auto.
    Qed.
  
    Lemma E1 : forall p, Omega_ConT -> (PA ||- p) <-> (PA ||- PrG/([⌜p⌝])).
    Proof.
      intros.
      split.
      - intros.
        rewrite -> proofH in H0.
        destruct H0 as [n].
        rewrite -> Pr_sbs.
        EXISTS ([n]).
        rewrite -> Prov_sbs.
        rewrite <-ProvH.
        auto.
      - intros.
        assert (exists n, (PA ||- Prov/([n], [⌜p⌝]))).
        + apply Prov_ext.
          auto. auto.
        + destruct H1 as [n].
          rewrite -> proofH.
          exists n.
          rewrite -> ProvH.
          auto.
    Qed.
  
    Lemma OmCon_Con : Omega_ConT -> Consis PA.
    Proof.
      intros.
      apply NNPP.
      intro.
      specialize (H ([~] [O] [=] [O])).
      assert (~ (PA ||- ext ([~] [O] [=] [O]))).
      apply H.
      intros.
      simpl.
      apply pNN.
      auto.
      apply explosion with (p := ext ([~] [O] [=] [O])) in H0.
      auto.
    Qed.
  
    Definition ConGT : Formula := [~] PrG/([⌜[~][0][=][0]⌝]).
    Definition G : Formula := fixpoint ([~] PrG).
  
    Lemma Gfixpoint : PA ||- G[<->][~]PrG/([⌜G⌝]).
    Proof.
      assert (Ar ([~] PrG) = 1).
      simpl.
      auto.
      rewrite -> arProv.
      lia.
      assert (D := Diagonal ([~] PrG) H).
      fold G in D. 
      rewrite -> neg_sbs in D.
      auto.
    Qed.
  
    Theorem Incompleteness1 : Omega_ConT -> ~ (PA ||- G) /\ ~ (PA ||- [~] G).
    Proof.
      intros.
      assert (gf := Gfixpoint).
      fdestruct gf.
      assert (con := OmCon_Con H).    
      split.
      - intro.
        destruct con.
        exists (PrG/([⌜G⌝])).
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
    
    Hypothesis D1 : forall p, PA ||- p -> PA ||- Pr/([⌜p⌝]).
    Hypothesis D2 : forall p q, PA ||- Pr/([⌜p[->]q⌝]) [->] Pr/([⌜p⌝]) [->] Pr/([⌜q⌝]).
    Hypothesis D3 : forall p, PA ||- Pr/([⌜p⌝]) [->] Pr/([⌜Pr/([⌜p⌝])⌝]).
    
    Definition γ : Formula := fixpoint ([~] Pr).
    Definition ConT : Formula := [~] Pr/([⌜[~][0][=][0]⌝]).
    
    Lemma nPrfix : PA ||- γ[<->][~]Pr/([⌜γ⌝]).
    Proof.
      assert (Ar ([~] Pr) = 1).
      simpl.
      auto.
      assert (D := Diagonal ([~] Pr) H).
      fold γ in D. 
      rewrite -> neg_sbs in D.
      auto.
    Qed.
    
    Lemma Consis_g : PA ||- ConT [->] γ.
    Proof.
      assert (D := nPrfix). 
      fdestruct D.
      unfold ConT.
      apply contrad_elim.
      fintro.
      apply pNN.
      assert (forall p, PA ¦ ([~] γ) ||- Pr/([⌜p⌝])).
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
    
    Theorem Incompleteness : PA ||- ConT -> ~ Consis PA.
    Proof.
      assert (D := nPrfix).
      fdestruct D.
      intros.
      assert (PA ||- γ).
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
  
    Lemma pr_distr : forall p q r, (PA ¦ r ||- Pr/([⌜p[->]q⌝])) -> (PA ¦ r ||- Pr/([⌜p⌝]) [->] Pr/([⌜q⌝])).
    Proof.
      intros.
      MP (Pr/([⌜p[->]q⌝])). auto.
      WL.
      apply D2.
    Qed. 
  
    Theorem Loeb : forall p, Ar p = 0 -> (PA ||- Pr/([⌜p⌝])[->]p) -> (PA ||- p).
    Proof.
      intros.
      assert (Ar (Pr/('0) [->] p) = 1).
      simpl.
      rewrite <- form1_p_ps.
      rewrite -> arPr.
      rewrite -> H.
      simpl. auto.
      auto. auto.
      pose (q := fixpoint (Pr/('0) [->] p)).
      assert (D := Diagonal _ H1). fold q in D.
      assert ((Pr/([⌜q⌝]) [->] p) = (Pr/('0) [->] p)/([⌜q⌝])).
      simpl.
      rewrite <- nested_rew.
      assert (Pr/([⌜q⌝]) = Pr .[fun x => rewc ([⌜q⌝]; \0) (('0; \0) x)]).
      apply rew_rew.
      rewrite -> arPr.
      intros.
      destruct n.
      simpl. auto.
      lia.
      rewrite <- H2.
      rewrite <- sentence_rew with (p:=p).
      auto. auto.
      rewrite <- H2 in D.
  
      fdestruct D.
      assert (PA ||- Pr/([⌜q⌝]) [->] p).
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
