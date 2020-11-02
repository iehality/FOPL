Require Import Classical.
Require Import Lia.
Require Import FOPL.FOPL.
Require Import FOPL.Deduction.

Set Implicit Arguments.

Section Incompleteness.

  Variable L : Lang.
  Variable o : LC.
  Variable Sc : LC -> LC.
  Hypothesis o_constant : Art o = 0.
  Hypothesis S_constant : forall x, Art x = 0 -> Art (Sc x) = 0.

  Variable quin : LP -> nat.
  Hypothesis quin_inj : forall p q, quin p = quin q -> p = q.
  Notation "⌜ p ⌝" := (quin p) (at level 0).

(** * Diagonal Lemma *)

  Fixpoint lnat (n0 : nat) : LC := 
    match n0 with
    | 0 => o
    | S n => Sc (lnat n)
    end.

  Notation "[ n ]" := (lnat n) (at level 0).

  Lemma d_rewc : forall n s, [n] = rewc s [n].
  Proof.
    intros.
    apply constant_rew.
    induction n.
    simpl. 
    apply o_constant.
    simpl.
    apply S_constant.
    auto.
  Qed.

  Variable T : Th.
  Variable Γ : LP.
  Hypothesis artG : Ar Γ = 3.
  Hypothesis Gdefg : forall p n, T ||- [fal]Γ.([⌜p⌝], n, '0)[<->]'0[=][⌜p.(n)⌝].

  Section FixPoint.
  
    Variable θ : LP.
    Hypothesis opf : Ar θ = 1.
    Definition σ : LP := [fal](Γ.('1, '1, '0)[->]θ.('0)).
    
    Lemma sigiff : forall p, T ||- σ.([⌜p⌝])[<->]θ.([⌜p.([⌜p⌝])⌝]).
    Proof.
      intros.
      assert (θrew : forall s, θ = θ .[('0);s]).
      intros.
      apply form1_p_ps.
      auto.
      simpl. auto.
      assert (forall n, σ.([n]) = (fal (Γ.([n], [n], '0) [->] θ.('0)))).
      - unfold σ. simpl. simpl.
        simpl.
        intros.
        rewrite <- θrew.
        rewrite <- θrew.
        rewrite <- nested_rew.
        assert (Γ.([n], [n], '0) = Γ .[fun x => rewc (('0); fun x0 => sfc (([n]; \0) x0)) ((('1); (('1); (('0); \0))) x)]).
        + unfold sfc.
          apply rew_rew.
          rewrite -> artG.
          intros.
          destruct n0.
          simpl.
          apply d_rewc.
          destruct n0.
          simpl.
          apply d_rewc.
          destruct n0.
          simpl.
          auto.
          lia.
        + rewrite <- H.
          auto.
      - rewrite -> H.
        simpl.
        SPLIT.
        + assert (Gr : forall a b t, Γ.([a], [b], t) = Γ.([a], [b], '0).(t)). { 
          intros.
          rewrite <- nested_rew.
          apply rew_rew.
          rewrite -> artG.
          intros.
          destruct n.
          simpl.
          apply d_rewc.
          destruct n.
          simpl.
          apply d_rewc.
          destruct n.
          simpl.
          auto.
          lia. 
          }
          assert (Ur : forall t, θ.(t) = θ.('0).(t)). {
          intros.
          rewrite <- nested_rew.
          apply rew_rew.
          intros.
          destruct n.
          simpl. auto.
          lia.
          }
          INTRO.
          MP ((Γ.([⌜p⌝], [⌜p⌝], '0) [->] θ.('0)).([⌜p.([⌜p⌝])⌝])).
          MP (fal (Γ.([⌜p⌝], [⌜p⌝], '0) [->] θ.('0))).
          AX.
          AX.
          simpl.
          rewrite <- Gr.
          rewrite <- Ur.
          INTRO.
          MP ([⌜p.([⌜p⌝])⌝] [=] [⌜p.([⌜p⌝])⌝] [->] θ.([⌜p.([⌜p⌝])⌝])).
          TRANS (Γ.([⌜p⌝], [⌜p⌝], [⌜p.([⌜p⌝])⌝])).
          
          assert (T ||- Γ.([⌜p⌝], [⌜p⌝], [⌜p.([⌜p⌝])⌝]) [<->] [⌜p.([⌜p⌝])⌝] [=] [⌜p.([⌜p⌝])⌝]).
          specialize (Gdefg p ([⌜p⌝])).
          SPECIALIZE Gdefg ([⌜p.([⌜p⌝])⌝]).
          simpl in Gdefg.
          rewrite <- Gr in Gdefg.
          rewrite <- d_rewc in Gdefg.
          auto.

          DESTRUCT H0.
          WL. 
          WL.
          auto.
          AX.
          INTRO.
          MP ([⌜p.([⌜p⌝])⌝] [=] [⌜p.([⌜p⌝])⌝]).
          AX.
          AX.
        + INTRO.
          specialize (Gdefg p ([⌜p⌝])).
          apply fal_and_destruct in Gdefg.
          destruct Gdefg.
          apply fal_trans with (q := '0 [=] [⌜p.([⌜p⌝])⌝]).
          WL.
          auto.
          GEN.
          apply sf_dsb.
          INTRO.
          assert (θ.([⌜p.([⌜p⌝])⌝]) = sf θ.([⌜p.([⌜p⌝])⌝])). {
            unfold sf.
            rewrite <- nested_rew.
            apply rew_rew. rewrite -> opf.
            intros. 
            destruct n.
            simpl.
            apply d_rewc.
            lia.
          }
          rewrite <- H2.
          MP (θ.([⌜p.([⌜p⌝])⌝])). AX.
          MP ([⌜p.([⌜p⌝])⌝] [=] '0).
          SYMMETRY.
          AX.
          AX.
    Qed.

    (** $\gamma := (\dot{\forall} (\Gamma.('1, '1, '0) \dot{\to} \theta.('0))).(\delta \ulcorner \dot{\forall} (\Gamma.('1, '1, '0) \dot{\to} \theta.('0)) \urcorner )$ *)

    Definition fixpoint := σ.([⌜σ⌝]).

    Lemma Diagonal : T ||- fixpoint [<->] θ.([⌜fixpoint⌝]).
    Proof. 
      apply sigiff.
    Qed.

  End FixPoint.
  
  Theorem Undefinability : (exists Tr, Ar Tr = 1 /\ forall p, T ||- p [<->] Tr.([⌜p⌝])) -> ~ Consis T.
  Proof.
    intros. intro conT.
    destruct H as [Tr].
    destruct H.
    assert (Ar ([~] Tr) = 1).
    simpl. auto.
    pose (d := fixpoint ([~] Tr)).
    assert (D := Diagonal ([~] Tr) H1). fold d in D.
    specialize (H0 d).
    rewrite -> neg_sbs in D.
    DESTRUCT H0.
    DESTRUCT D.
    apply conT.
    exists d.
    split.
    - MP ([~] [~] d).
      apply neg_intro.
      INTRO.
      MP ([~] [~] Tr.([⌜d⌝])).
      apply deduction_inv.
      apply contrad_add. auto.
      apply contrad_add.
      apply contrad_add.
      WL. auto.
      apply pr_NNPP.
    - apply neg_intro.
      INTRO.
      MP ([~] Tr.([⌜d⌝])).
      apply deduction_inv. auto.
      apply contrad_add.
      WL.
      auto.
  Qed.
  
  (** ** Incompleteness *)
  
  Section Goedel_Incompleteness1.
    
    Variable prov : nat -> nat -> Prop.
    Hypothesis proofH : forall p, (T ||- p) <-> (exists n, prov n ⌜p⌝).  
  
    Variable Prov : LP.
    Hypothesis arProv : Ar Prov = 2.
    Hypothesis ProvH : forall n m, prov n m <-> (T ||- Prov.([n], [m])). 
    Hypothesis nProvH : forall n m, ~ prov n m <-> (T ||- [~] Prov.([n], [m])).
  
    Let PrG : LP := ext Prov.
  
    Lemma Pr_sbs : forall n, PrG.([n]) = ext (Prov.('0, [n])).
    Proof.
      unfold ext.
      intros.
      simpl.
      assert (Prov.('0, [n]) = Prov.['0; fun x => sfc (([n]; \0) x)]).
      apply rew_rew.
      rewrite -> arProv.
      intros.
      destruct n0.
      simpl.
      auto.
      destruct n0.
      simpl.
      apply d_rewc.
      lia.
      rewrite <- H.
      auto.
    Qed.
  
    Lemma Prov_sbs : forall n m, Prov.('0, [n]).([m]) = Prov.([m], [n]).
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
      symmetry.
      apply d_rewc.
      lia.
    Qed.

    Let Omega_ConT := forall p, (forall n, T ||- [~] p.([n])) -> ~ (T ||- ext p).

    Lemma Prov_ext : Omega_ConT -> forall p, (T ||- PrG.([⌜p⌝])) -> exists n, (T ||- Prov.([n], [⌜p⌝])).
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
  
    Lemma E1 : forall p, Omega_ConT -> (T ||- p) <-> (T ||- PrG.([⌜p⌝])).
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
        assert (exists n, (T ||- Prov.([n], [⌜p⌝]))).
        + apply Prov_ext.
          auto. auto.
        + destruct H1 as [n].
          rewrite -> proofH.
          exists n.
          rewrite -> ProvH.
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
      AX.
      apply explosion with (p := ext ([~] [O] [=] [O])) in H0.
      auto.
    Qed.
  
    Definition ConGT : LP := [~] PrG.([⌜[~][O][=][O]⌝]).
    Definition G : LP := fixpoint ([~] PrG).
  
    Lemma Gfixpoint : T ||- G[<->][~]PrG.([⌜G⌝]).
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
  
    Theorem Incompleteness1 : Omega_ConT -> ~ (T ||- G) /\ ~ (T ||- [~] G).
    Proof.
      intros.
      assert (gf := Gfixpoint).
      DESTRUCT gf.
      assert (con := OmCon_Con H).    
      split.
      - intro.
        destruct con.
        exists (PrG.([⌜G⌝])).
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
  
  End Goedel_Incompleteness1.

  Section Rosser_Incompleteness1.
    
    Variable prov : nat -> LP -> Prop.
    Hypothesis proofH : forall p, (T ||- p) <-> (exists n, prov n p).
    Let provR n p := (prov n p) /\ (~ exists m, m <= n /\ prov m ([~] p)).  
    
    Variable ProvR : LP.
    Hypothesis arProv : Ar ProvR = 2.
    Hypothesis ProvRH : forall n p, provR n p <-> (T ||- ProvR.([n], [⌜p⌝])).
    Hypothesis nProvRH : forall n p, ~ provR n p <-> (T ||- [~] ProvR.([n], [⌜p⌝])).
  
    Let PrR : LP := ext ProvR.

    Lemma PrR_sbs : forall n, PrR.([n]) = ext (ProvR.('0, [n])).
    Proof.
      unfold ext.
      intros.
      simpl.
      assert (ProvR.('0, [n]) = ProvR.['0; fun x => sfc (([n]; \0) x)]).
      apply rew_rew.
      rewrite -> arProv.
      intros.
      destruct n0.
      simpl.
      auto.
      destruct n0.
      simpl.
      apply d_rewc.
      lia.
      rewrite <- H.
      auto.
    Qed.
  
    Lemma ProvR_sbs : forall n m, ProvR.('0, [n]).([m]) = ProvR.([m], [n]).
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
      symmetry.
      apply d_rewc.
      lia.
    Qed.

    Let ConRT : LP := [~] PrR.([⌜[~][O][=][O]⌝]).

    Lemma E1R : Consis T -> forall p, (T ||- p) <-> (T ||- PrR.([⌜p⌝])).
    Proof.
      intros.
      split.
      - intros.
        rewrite -> proofH in H0.
        destruct H0 as [n].
        rewrite -> PrR_sbs.
        EXISTS ([n]).
        rewrite -> ProvR_sbs.
        rewrite <-ProvRH.
        split.
        + auto.
        + intro.
          destruct H1 as [m].
          destruct H1.
          apply H.
          exists p.
          split.
          rewrite -> proofH.
          exists n. auto.
          rewrite -> proofH.
          exists m. auto.
      - intros.
        rewrite -> PrR_sbs in H0.
        rewrite proofH.
        Abort.
  
  End Rosser_Incompleteness1.

  Section Incompleteness2.
  
    Variable Pr : LP.
    Hypothesis arPr : Ar Pr = 1.
    
    Hypothesis D1 : forall p, T ||- p -> T ||- Pr.([⌜p⌝]).
    Hypothesis D2 : forall p q, T ||- Pr.([⌜p[->]q⌝]) [->] Pr.([⌜p⌝]) [->] Pr.([⌜q⌝]).
    Hypothesis D3 : forall p, T ||- Pr.([⌜p⌝]) [->] Pr.([⌜Pr.([⌜p⌝])⌝]).
    
    Definition γ : LP := fixpoint ([~] Pr).
    Definition ConT : LP := [~] Pr.([⌜[~][O][=][O]⌝]).
    
    Lemma nPrfix : T ||- γ[<->][~]Pr.([⌜γ⌝]).
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
      DESTRUCT D.
      unfold ConT.
      apply contrad_elim.
      INTRO.
      apply pNN.
      assert (forall p, T :+ ([~] γ) ||- Pr.([⌜p⌝])).
      - intros.
        MP (Pr.([⌜[~]Pr.([⌜γ⌝])⌝])).
        + MP (Pr.([⌜γ⌝])).
          apply pNNPP.
          apply deduction_inv.
          apply contrad_add. auto.
          MP (Pr.([⌜γ[->][~]Pr.([⌜γ⌝])⌝])).
          WL.
          apply D1. auto.
          WL.        
          apply D2.
        + MP (Pr.([⌜[~]Pr.([⌜γ⌝])[->]p⌝])).
          MP (Pr.([⌜Pr.([⌜γ⌝])⌝])).
          MP (Pr.([⌜γ⌝])).
          apply pNNPP.
          apply deduction_inv.
          apply contrad_add. auto.
          WL.
          apply D3.
          MP (Pr.([⌜Pr.([⌜γ⌝])[->][~]Pr.([⌜γ⌝])[->]p⌝])).
          WL.
          apply D1.
          INTRO. INTRO.
          apply explosion.
          intro. destruct H1.
          exists (Pr.([⌜γ⌝])). split.
          AX. AX.
          WL.
          apply D2.
          WL.
          apply D2.
      - auto.
    Qed.
    
    Theorem Incompleteness : T ||- ConT -> ~ Consis T.
    Proof.
      assert (D := nPrfix).
      DESTRUCT D.
      intros.
      assert (T ||- γ).
      MP ConT. auto.
      apply Consis_g.    
      intro. 
      destruct H3.
      exists (Pr.([⌜γ⌝])).
      split.
      apply D1.
      auto.
      MP γ. auto.
      auto.
    Qed.
  
    Lemma pr_distr : forall p q r, (T :+ r ||- Pr.([⌜p[->]q⌝])) -> (T :+ r ||- Pr.([⌜p⌝]) [->] Pr.([⌜q⌝])).
    Proof.
      intros.
      MP (Pr.([⌜p[->]q⌝])). auto.
      WL.
      apply D2.
    Qed. 
  
    Theorem Loeb : forall p, Ar p = 0 -> (T ||- Pr.([⌜p⌝])[->]p) -> (T ||- p).
    Proof.
      intros.
      assert (Ar (Pr.('0) [->] p) = 1).
      simpl.
      rewrite <- form1_p_ps.
      rewrite -> arPr.
      rewrite -> H.
      simpl. auto.
      auto. auto.
      pose (q := fixpoint (Pr.('0) [->] p)).
      assert (D := Diagonal _ H1). fold q in D.
      assert ((Pr.([⌜q⌝]) [->] p) = (Pr.('0) [->] p).([⌜q⌝])).
      simpl.
      rewrite <- nested_rew.
      assert (Pr.([⌜q⌝]) = Pr .[fun x => rewc ([⌜q⌝]; \0) (('0; \0) x)]).
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
  
      DESTRUCT D.
      assert (T ||- Pr.([⌜q⌝]) [->] p).
      - INTRO.
        MP (Pr.([⌜p⌝])).
        MP (Pr.([⌜Pr.([⌜q⌝])⌝])).
        apply deduction_inv.
        apply D3.
        MP (Pr.([⌜Pr.([⌜q⌝])[->]p⌝])).
        apply deduction_inv.
        MP (Pr.([⌜q[->]Pr.([⌜q⌝])[->]p⌝])).
        apply D1.
        auto.
        apply D2.
        WL.
        apply D2.
        WL.
        auto.
      - MP (Pr.([⌜q⌝])).
        apply D1.
        MP (Pr.([⌜q⌝]) [->] p).
        auto.
        auto.
        auto.
    Qed.
  
  End Incompleteness2.
  
End Incompleteness.
