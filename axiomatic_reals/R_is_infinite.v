(* 实数集是无限集 *)

Require Import mk.infinite_sets.
Require Import axiomatic_reals.R_axioms.

Proposition ω_equivalent_N : ω ≈ N.
Proof.
  set (U := \{\ λ u v, u ∈ R /\ v ∈ R /\ u < v \}\).
  assert (WellOrdered E ω).
  { apply MKT107. New MKT138. apply AxiomII in H; tauto. }
  assert (WellOrdered U N).
  { split; intros. unfold Connect; intros.
    apply N_Subset_R in H0,H1. New H0.
    apply (Leq_P4 u v) in H2 as []; auto; TF (u = v); auto;
    [left|right;left]; apply AxiomII'; repeat split; auto;
    apply MKT49a; eauto.
    New H0. apply Nat_P7 in H2 as [x[H2[]]]; auto.
    exists x. split; auto. intros. intro.
    apply AxiomII' in H6 as [H6[H7[H8[]]]].
    apply H4 in H5. apply H10,Leq_P2; auto. }
  New H0. apply (@ MKT99 E U ω N) in H1
  as [f[H1[[_[_[H2[]]]]]]]; auto. New H2.
  apply MKT96 in H6 as [[_]].
  destruct H3 as [H3[_]], H4 as [H4[_]].
  assert (dom(f) = ω /\ ran(f) = N) as [].
  { destruct H5; split; auto; apply AxiomI; split; intros; auto.
    - assert (ran(f) ⊂ Z /\ ran(f) ⊂ R) as [].
      { unfold Included; split; intros; eauto with real. }
      apply NNPP; intro. assert (∃ x, Upper ran(f) x).
      { exists z. repeat split; auto with real.
        intros. apply NNPP; intro.
        assert (Rrelation z U x).
        { apply AxiomII'; repeat split; auto with real.
          apply MKT49a; eauto. apply N_Subset_R,(Leq_P4 x)
          in H10 as []; auto with real. contradiction.
          intro. rewrite H16 in H15.
          apply H15,Leq_P1; auto with real. }
        apply H9 in H16; auto. }
      apply Arch_P3a in H14 as [x[H14[]]]; auto.
      assert (∀ x0, x0 ∈ dom(f) -> x0 ∈ f⁻¹[x] \/ x0 = f⁻¹[x]).
      { intros. New H17. apply Property_Value,Property_ran
        in H18; auto. New H18. apply H16 in H19.
        TF (f[x0] = x). right. rewrite <-H20,f11iv; auto.
        destruct H7 as [_[_[_]]].
        assert (Rrelation f[x0] U x).
        { apply AxiomII'; repeat split; auto. apply MKT49a; eauto. }
        apply H7 in H21; try rewrite <-reqdi; auto.
        apply AxiomII' in H21 as []. rewrite f11iv in H22; auto. }
      rewrite reqdi in H15. apply Property_Value,Property_ran
      in H15; auto. rewrite <-deqri,H5 in H15. rewrite H5 in H17.
      assert ((f⁻¹)[x] ∈ PlusOne ((f⁻¹)[x])).
      { apply MKT4; right. apply MKT41; eauto. }
      New H15. apply MKT134,H17 in H19 as [].
      apply (MKT102 ((f⁻¹)[x]) (PlusOne (f⁻¹)[x])); auto.
      rewrite H19 in H18. apply (MKT101 ((f⁻¹)[x])); auto.
      apply NEexE. exists f[Φ].
      apply (@ Property_ran Φ),Property_Value; [ |rewrite H5]; auto.
    - assert (Ordinal dom(f)).
      { apply MKT114. split; [ |split]. unfold Included; intros.
        apply H3,AxiomII in H11 as [H11[]]. apply AxiomII; auto.
        apply MKT107,MKT113a. intros. apply (H8 u v); auto.
        New H12. apply H3 in H12. apply H3,AxiomII in H14 as [_[[]]].
        apply AxiomII' in H13 as []. New MKT138.
        apply AxiomII in H18 as [_[]]. apply H19 in H12; auto. }
      apply NNPP; intro. assert (dom(f) ∈ ω).
      { New H11. apply (@ MKT110 ω) in H13 as [H13|[]]; auto.
        destruct H11. apply H14 in H13. elim H12; auto.
        rewrite H13 in H10. contradiction. }
      assert (∃ m, LastMember m E dom(f)) as [m[]].
      { apply AxiomII in H13 as [H13[_[]]]. apply H15; auto.
        apply NEexE. New one_in_N. rewrite <-H5 in H16.
        apply Einr in H16 as [x[]]; eauto. }
      New H14. apply Property_Value,Property_ran in H16; auto.
      rewrite H5 in H16. New H16. apply (Nat_P1a _ 1) in H17;
      [ |auto with real].
      assert (f[m] < (f[m] + 1)).
      { New OrderPM_Co9. apply (OrderPM_Co4 f[m] f[m])
        in H18; auto with real; [rewrite Plus_P1 in H18|
        apply Leq_P1]; auto with real. }
      assert (Rrelation f[m] U (f[m] + 1)).
      { destruct H18. apply AxiomII'; repeat split;
        auto with real. apply MKT49a; eauto. }
      destruct H7 as [_[_[_]]]. apply H7,AxiomII' in H19 as [];
      try rewrite <-reqdi,H5; auto. rewrite f11iv in H19,H20; auto.
      New H17. rewrite <-H5,reqdi in H21.
      apply Property_Value,Property_ran in H21; auto.
      rewrite <-deqri in H21. apply H15 in H21.
      apply H21. apply AxiomII'; split; [ |apply AxiomII'; auto].
      apply MKT49b in H19 as []. apply MKT49a; auto. }
  exists f; split; [split| ]; auto.
Qed.

Proposition N_is_Infinite : ~ Finite N.
Proof.
  assert (~ Finite ω).
  { apply Inf_P3. rewrite Inf_P1; auto. }
  apply (Inf_P5 N ω); auto. apply MKT146,ω_equivalent_N.
Qed.

Proposition R_is_Infinite : ~ Finite R.
Proof.
  apply Inf_P3. New ω_equivalent_N. apply MKT154 in H.
  rewrite <-Inf_P1,H. apply MKT158; auto with real.
  New MKT138; eauto. apply (MKT33 R); auto with real.
  apply Ensemble_R.
Qed.
































