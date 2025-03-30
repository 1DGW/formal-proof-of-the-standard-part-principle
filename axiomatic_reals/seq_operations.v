(** seq_operation *) (* Ｒᴺ *)

Require Import mk.mk_theorems.
Require Export axiomatic_reals.R_axioms.

(* N->R的函数空间, 也是所有数列的集合 *)
Definition Rᴺ := \{ λ f, Function f /\ dom(f) = N /\ ran(f) ⊂ R \}.

Fact Rᴺ_is_Set : Ensemble Rᴺ.
Proof.
  apply (MKT33 pow(N × R)). apply MKT38a,MKT74.
  apply (MKT33 R). apply Ensemble_R. apply N_Subset_R. apply Ensemble_R.
  unfold Included; intros. apply AxiomII in H as [H[H0[]]].
  apply AxiomII; split; unfold Included; intros; auto.
  New H3. rewrite MKT70 in H4; auto.
  apply AxiomII in H4 as [H4[x[y[]]]]. rewrite H5 in *.
  apply AxiomII'; repeat split; auto.
  rewrite <-H1. apply Property_dom in H3; auto.
  apply Property_ran in H3; auto.
Qed.

(* N->N的函数空间 *)
Definition Nᴺ := \{ λ f, Function f /\ dom(f) = N /\ ran(f) ⊂ N \}.

Fact Nᴺ_Subset_Rᴺ : Nᴺ ⊂ Rᴺ.
Proof.
  red; intros. apply AxiomII in H as [H[H0[]]].
  apply AxiomII; split; auto. split; auto. split; auto.
  red; intros; auto with real.
Qed.

Fact Nᴺ_is_Set : Ensemble Nᴺ.
Proof. apply (MKT33 Rᴺ). apply Rᴺ_is_Set. apply Nᴺ_Subset_Rᴺ. Qed.

Property Nᴺ_Comp_Rᴺ : ∀ f g, f ∈ Nᴺ -> g ∈ Rᴺ -> (g ∘ f) ∈ Rᴺ.
Proof.
  intros. apply AxiomII in H as [_[H[]]], H0 as [_[H0[]]].
  assert (Function (g ∘ f)). { apply MKT64; auto. }
  assert (dom(g ∘ f) = N).
  { apply AxiomI; split; intros. apply AxiomII in H6 as [_[]].
    apply AxiomII' in H6 as [_[x0[]]]. apply Property_dom in H6.
    rewrite <-H1; auto. apply AxiomII; split. eauto. exists g[f[z]].
    rewrite <-H1 in H6. pose proof H6. apply Property_Value in H7; auto.
    pose proof H7. apply Property_ran in H8. pose proof H8. apply H2 in H9.
    rewrite <-H3 in H9. pose proof H9. apply Property_Value in H10; auto.
    apply AxiomII'; split; eauto. apply Property_ran in H10.
    apply MKT49a; eauto. }
  assert (ran(g ∘ f) ⊂ R).
  { red; intros. apply AxiomII in H7 as [H7[]].
    apply AxiomII' in H8 as [_[x0[]]]. apply Property_ran in H9; auto. }
  apply AxiomII; split; auto. apply MKT75; auto. rewrite H6. apply (MKT33 R).
  apply Ensemble_R. apply N_Subset_R.
Qed.

Declare Scope Seq_scope.
Delimit Scope Seq_scope with seq.
Open Scope Seq_scope.

(*定义 数列的加法运算 *)
Definition Seq_Plus f g := \{\ λ u v, u ∈ N /\ v = (f[u]) + (g[u]) \}\.
Notation "f + g" := (Seq_Plus f g) : Seq_scope.

(*验证 加法在数列空间中封闭 *)
Corollary Seq_Plus_Close : ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ
  -> (f + g) ∈ Rᴺ.
Proof.
  intros. apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  assert (Function (f + g)).
  { split; unfold Relation; intros.
    apply AxiomII in H7 as [H7[x[y[H8[]]]]]; eauto.
    apply AxiomII' in H7 as [_[_]], H8 as [_[_]].
    rewrite H7,H8; auto. }
  assert (dom(f + g) = N).
  { apply AxiomI; split; intros. apply AxiomII in H8 as [H8[]].
    apply AxiomII' in H9 as []; tauto. apply AxiomII; split; eauto.
    exists ((f[z]) + (g[z]))%r. apply AxiomII'; split; auto.
    assert (f[z] ∈ R /\ g[z] ∈ R) as [].
    { split; [rewrite <-H2 in H8|rewrite <-H5 in H8];
      apply Property_Value,Property_ran in H8; auto. }
    assert (((f[z]) + (g[z]))%r ∈ R). auto with real.
    apply MKT49a; eauto. }
  assert (ran(f + g) ⊂ R).
  { unfold Included; intros. apply AxiomII in H9 as [H9[]].
    apply AxiomII' in H10 as [H10[]]. rewrite H12.
    apply Plus_close; [apply H3|apply H6];
    apply (@ Property_ran x); apply Property_Value; auto;
    [rewrite H2|rewrite H5]; auto. }
  apply AxiomII; split; auto. apply MKT75; auto.
  rewrite H8. apply (MKT33 R). apply Ensemble_R. apply N_Subset_R.
Qed.

(*验证 函数f,g满足：(f+g)[x] = f[x] + g[x] *)
Corollary Seq_Plus_Property : ∀ f g x, f ∈ Rᴺ -> g ∈ Rᴺ
  -> (f + g)[x] = ((f[x]) + (g[x]))%r.
Proof.
  intros. apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  destruct (classic (x ∈ N)).
  - assert ((f[x] + g[x])%r ∈ R); eauto.
    { apply Plus_close; [apply H3|apply H6];
      apply (@ Property_ran x),Property_Value; auto;
      [rewrite H2|rewrite H5]; auto. }
    apply AxiomI; split; intros.
    + apply AxiomII in H9 as []. apply H10. apply AxiomII; split.
      eauto. apply AxiomII'; split; auto. apply MKT49a; eauto.
    + apply AxiomII; split; eauto. intros.
      apply AxiomII in H10 as []. apply AxiomII' in H11 as [H11[]].
      rewrite H13; auto.
  - assert ((f + g) ∈ Rᴺ).
    { apply Seq_Plus_Close; apply AxiomII; auto. }
    apply AxiomII in H8 as [_[_[]]]. New H7. rewrite <-H8 in H10.
    apply MKT69a in H10. rewrite <-H2 in H7. apply MKT69a in H7.
    destruct PlusR as [_[]]. rewrite H10. symmetry.
    apply MKT69a. intro. rewrite H11 in H13.
    apply AxiomII' in H13 as [_[]]. rewrite H7 in H13.
    apply MKT39; eauto.
Qed.

(* (*定义 数列的减法运算 *)
Definition Seq_Minus f g := \{\ λ u v, u ∈ N /\ v = (f[u]) - (g[u]) \}\.
Notation "f - g" := (Seq_Minus f g) : Seq_scope.

(*验证 减法在数列空间中封闭 *)
Corollary Seq_Minus_Close : ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ -> (f - g) ∈ Rᴺ.
Proof.
  intros. apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  assert (Function (f - g)).
  { split; unfold Relation; intros.
    apply AxiomII in H7 as [H7[x[y[H8[]]]]]; eauto.
    apply AxiomII' in H7 as [_[_]], H8 as [_[_]].
    rewrite H7,H8; auto. }
  assert (dom(f - g) = N).
  { apply AxiomI; split; intros. apply AxiomII in H8 as [H8[]].
    apply AxiomII' in H9 as []; tauto. apply AxiomII; split; eauto.
    exists ((f[z]) - (g[z]))%r. apply AxiomII'; split; auto.
    assert (f[z] ∈ R /\ g[z] ∈ R) as [].
    { split; [rewrite <-H2 in H8|rewrite <-H5 in H8];
      apply Property_Value,Property_ran in H8; auto. }
    assert (((f[z]) - (g[z]))%r ∈ R). auto with real.
    apply MKT49a; eauto. }
  assert (ran(f - g) ⊂ R).
  { unfold Included; intros. apply AxiomII in H9 as [H9[]].
    apply AxiomII' in H10 as [H10[]]. rewrite H12.
    apply Plus_close; [apply H3|apply Plus_neg1a,H6];
    apply (@ Property_ran x); apply Property_Value; auto;
    [rewrite H2|rewrite H5]; auto. }
  apply AxiomII; split; auto. apply MKT75; auto.
  rewrite H8. apply (MKT33 R). apply Ensemble_R. apply N_Subset_R.
Qed.

(*验证 函数f,g满足：(f-g)[x] = f[x] - g[x] *)
Corollary Seq_Minus_Property : ∀ f g x, f ∈ Rᴺ -> g ∈ Rᴺ
  -> (f - g)[x] = ((f[x]) - (g[x]))%r.
Proof.
  intros. apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  destruct (classic (x ∈ N)).
  - assert ((f[x] - g[x])%r ∈ R); eauto.
    { apply Plus_close; [apply H3|apply Plus_neg1a,H6];
      apply (@ Property_ran x),Property_Value; auto;
      [rewrite H2|rewrite H5]; auto. }
    apply AxiomI; split; intros.
    + apply AxiomII in H9 as []. apply H10. apply AxiomII; split.
      eauto. apply AxiomII'; split; auto. apply MKT49a; eauto.
    + apply AxiomII; split; eauto. intros.
      apply AxiomII in H10 as []. apply AxiomII' in H11 as [H11[]].
      rewrite H13; auto.
  - assert ((f - g) ∈ Rᴺ).
    { apply Seq_Minus_Close; apply AxiomII; auto. }
    apply AxiomII in H8 as [_[_[]]]. New H7. rewrite <-H8 in H10.
    apply MKT69a in H10. rewrite <-H2 in H7. apply MKT69a in H7.
    destruct PlusR as [_[]]. rewrite H10. symmetry.
    apply MKT69a. intro. rewrite H11 in H13.
    apply AxiomII' in H13 as [_[]]. rewrite H7 in H13.
    apply MKT39; eauto.
Qed. *)

(*定义 数列的乘法运算 *)
Definition Seq_Mult f g := \{\ λ u v, u ∈ N /\ v = (f[u]) · (g[u]) \}\.
Notation "f · g" := (Seq_Mult f g) : Seq_scope.

(*验证 乘法在函数空间中封闭 *)
Corollary Seq_Mult_Close : ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ -> (f · g) ∈ Rᴺ.
Proof.
  intros. apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  assert (Function (f · g)).
  { split; unfold Relation; intros.
    apply AxiomII in H7 as [H7[x[y[H8[]]]]]; eauto.
    apply AxiomII' in H7 as [_[_]], H8 as [_[_]].
    rewrite H7,H8; auto. }
  assert (dom(f · g) = N).
  { apply AxiomI; split; intros. apply AxiomII in H8 as [H8[]].
    apply AxiomII' in H9 as []; tauto. apply AxiomII; split; eauto.
    exists ((f[z]) · (g[z]))%r. apply AxiomII'; split; auto.
    assert (f[z] ∈ R /\ g[z] ∈ R) as [].
    { split; [rewrite <-H2 in H8|rewrite <-H5 in H8];
      apply Property_Value,Property_ran in H8; auto. }
    assert (((f[z]) · (g[z]))%r ∈ R). auto with real.
    apply MKT49a; eauto. }
  assert (ran(f · g) ⊂ R).
  { unfold Included; intros. apply AxiomII in H9 as [H9[]].
    apply AxiomII' in H10 as [H10[]]. rewrite H12.
    apply Mult_close; [apply H3|apply H6];
    apply (@ Property_ran x); apply Property_Value; auto;
    [rewrite H2|rewrite H5]; auto. }
  apply AxiomII; split; auto. apply MKT75; auto. rewrite H8.
  apply (MKT33 R). apply Ensemble_R. apply N_Subset_R; auto.
Qed.

(*验证 函数f,g满足：(f·g)[x] = f[x] · g[x] *)
Corollary Seq_Mult_Property : ∀ f g x, f ∈ Rᴺ -> g ∈ Rᴺ
  -> (f · g)[x] = ((f[x]) · (g[x]))%r.
Proof.
  intros. apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  destruct (classic (x ∈ N)).
  - assert ((f[x] · g[x])%r ∈ R); eauto.
    { apply Mult_close; [apply H3|apply H6];
      apply (@ Property_ran x),Property_Value; auto;
      [rewrite H2|rewrite H5]; auto. }
    apply AxiomI; split; intros.
    + apply AxiomII in H9 as []. apply H10. apply AxiomII; split.
      eauto. apply AxiomII'; split; auto. apply MKT49a; eauto.
    + apply AxiomII; split; eauto. intros.
      apply AxiomII in H10 as []. apply AxiomII' in H11 as [H11[]].
      rewrite H13; auto.
  - assert ((f · g) ∈ Rᴺ).
    { apply Seq_Mult_Close; apply AxiomII; auto. }
    apply AxiomII in H8 as [_[_[]]]. New H7. rewrite <-H8 in H10.
    apply MKT69a in H10. rewrite <-H2 in H7. apply MKT69a in H7.
    destruct MultR as [_[]]. rewrite H10. symmetry. apply MKT69a.
    intro. rewrite H11 in H13. apply AxiomII' in H13 as [_[]].
    rewrite H7 in H13. apply MKT39; eauto.
Qed.

(* (*定义 数列的除法运算 *)
Definition Seq_Div f g := \{\ λ u v, u ∈ N /\ v = (f[u]) / (g[u]) \}\.
Notation "f / g" := (Seq_Div f g) : Seq_scope.

Lemma Inverse_0_is_universe : 0⁻ = μ.
Proof.
  apply AxiomI; split; intros. apply MKT19. eauto. apply AxiomII; split.
  eauto. intros. apply AxiomII in H0 as [H0[]]. rewrite PlusMult_Co1 in H2.
  New OrderPM_Co9. rewrite H2 in H3. destruct H3. elim H4; auto.
  apply MKT4' in H1; tauto.
Qed.

Lemma Div_0_is_universe : ∀ r, (r / 0)%r = μ.
Proof.
  intros. rewrite Inverse_0_is_universe,MKT69a; auto. intro.
  assert (Ensemble ([r,μ])). eauto. apply MKT49b in H0 as [].
  apply MKT39; auto.
Qed.

(*验证 除法在数列空间中封闭 *)
Corollary Seq_Div_Close : ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ
  -> (∀ n, n ∈ N -> g[n] <> 0) <-> (f / g) ∈ Rᴺ.
Proof.
  intros. apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  assert (Function (f / g)).
  { split; unfold Relation; intros.
    apply AxiomII in H7 as [H7[x[y[H8[]]]]]; eauto.
    apply AxiomII' in H7 as [_[_]], H8 as [_[_]]. rewrite H7,H8; auto. }
  split; intros.
  - assert (∀ z, z ∈ N -> g[z] ∈ (R ~ [0])).
    { intros. apply MKT4'. New H9. rewrite <-H5 in H10.
      apply Property_Value,Property_ran in H10; auto. split; auto.
      apply AxiomII; split. eauto. intro. apply MKT41 in H11; eauto with real.
      eapply H8; eauto. }
    assert (∀ z, z ∈ N -> (g[z])⁻ ∈ (R ~ [0])).
    { intros. apply ->PlusMult_Co6; auto. }
    assert (dom(f / g) = N).
    { apply AxiomI; split; intros. apply AxiomII in H11 as [H11[]].
      apply AxiomII' in H12 as []; tauto. apply AxiomII; split; eauto.
      exists ((f[z]) / (g[z]))%r. apply AxiomII'; split; auto.
      assert (f[z] ∈ R /\ g[z] ∈ R) as [].
      { split; [rewrite <-H2 in H11|rewrite <-H5 in H11];
        apply Property_Value,Property_ran in H11; auto. }
      assert (((f[z]) / (g[z]))%r ∈ R). apply Mult_close; auto.
      assert (g[z] ∈ (R ~ [0])).
      { apply MKT4'; split; auto. apply AxiomII; split. eauto. intro.
        apply MKT41 in H14; eauto with real. eapply H8; eauto. }
      apply PlusMult_Co6,MKT4' in H14; tauto. apply MKT49a; eauto. }
    assert (ran(f / g) ⊂ R).
    { unfold Included; intros. apply AxiomII in H12 as [H12[]].
      apply AxiomII' in H13 as [H13[]]. rewrite H15.
      apply Mult_close. apply H3,(@ Property_ran x),Property_Value; auto.
      rewrite H2; auto. apply H10,MKT4' in H14; tauto. }
    apply AxiomII; split; auto. apply MKT75; auto. rewrite H11.
    apply (MKT33 R). apply Ensemble_R. apply N_Subset_R; auto.
  - intro. apply AxiomII in H8 as [H8[H11[]]]. rewrite <-H12 in H9.
    apply Property_Value,AxiomII' in H9 as [H9[]]; auto.
    apply MKT49b in H9 as []. rewrite H10,Div_0_is_universe in H15.
    rewrite H15 in H16. apply MKT39; auto.
Qed.

(*验证 数列f,g满足：(f/g)[x] = f[x] / g[x] *)
Corollary Seq_Div_Property : ∀ f g x, f ∈ Rᴺ -> g ∈ Rᴺ
  -> (f / g)[x] = ((f[x]) / (g[x]))%r.
Proof.
  intros. apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  assert (Function (f / g)).
  { split; unfold Relation; intros.
    apply AxiomII in H7 as [H7[a[b[H8[]]]]]; eauto.
    apply AxiomII' in H7 as [_[_]], H8 as [_[_]]. rewrite H7,H8; auto. }
  assert (dom(f / g) ⊂ N).
  { red; intros. apply AxiomII in H8 as [H8[]].
    apply AxiomII' in H9 as []; tauto. }
  destruct (classic (x ∈ N)).
  - destruct (classic (g[x] = 0)).
    + rewrite H10,Div_0_is_universe. apply MKT69a. intro.
      apply Property_Value,AxiomII' in H11 as [H11[]]; auto.
      rewrite H10,Div_0_is_universe in H13. rewrite H13 in H11.
      apply MKT49b in H11 as []. apply MKT39; auto.
    + assert (x ∈ dom(f / g)).
      { apply (@ Property_dom _ (f[x] / g[x])%r _),AxiomII'; split; auto.
        apply MKT49a. eauto. assert (f[x] ∈ R /\ g[x] ∈ R) as [].
        { split; [apply H3|apply H6]; apply (@ Property_ran x),Property_Value;
          auto; [rewrite H2|rewrite H5]; auto. }
        assert (g[x] ∈ (R ~ [0])).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto.
          intro. apply MKT41 in H13; eauto with real. }
        apply PlusMult_Co6,MKT4' in H13 as []. eauto with real. }
      apply Property_Value,AxiomII' in H11; tauto.
  - assert (~ x ∈ dom(f / g)). { intro. apply H9; auto. }
    rewrite <-H2 in H9. apply MKT69a in H9,H10. rewrite H9,H10,MKT69a; auto.
    intro. assert (Ensemble ([μ,(g[x])⁻])). eauto. apply MKT49b in H12 as [].
    apply MKT39; auto.
Qed. *)

(*定义 数列的相反数列 *)
Definition Seq_Neg f := \{\ λ u v, u ∈ N /\ v = -f[u] \}\.
Notation "- f" := (Seq_Neg f) : Seq_scope.

(*验证 相反运算在数列空间中封闭 *)
Corollary Seq_Neg_Close : ∀ f, f ∈ Rᴺ -> (-f) ∈ Rᴺ.
Proof.
  intros. apply AxiomII in H as [H[H1[]]].
  assert (Function (-f)).
  { split; unfold Relation; intros.
    apply AxiomII in H3 as [H3[x[y[H4[]]]]]; eauto.
    apply AxiomII' in H3 as [_[_]], H4 as [_[_]].
    rewrite H3,H4; auto. }
  assert (dom(-f) = N).
  { apply AxiomI; split; intros. apply AxiomII in H4 as [H4[]].
    apply AxiomII' in H5 as []; tauto. apply AxiomII; split; eauto.
    exists (-f[z])%r. apply AxiomII'; split; auto.
    assert (f[z] ∈ R).
    { apply H2,(@ Property_ran z),Property_Value; auto.
      rewrite H0; auto. } apply MKT49a; eauto with real. }
  assert (ran(-f) ⊂ R).
  { unfold Included; intros. apply AxiomII in H5 as [H5[]].
    apply AxiomII' in H6 as [H6[]]. rewrite H8.
    apply Plus_neg1a,H2,(@ Property_ran x),Property_Value; auto.
    rewrite H0; auto. }
  apply AxiomII; split; auto. apply MKT75; auto.
  rewrite H4. apply (MKT33 R). apply Ensemble_R. apply N_Subset_R.
Qed.

(*验证 函数f满足：(-f)[x] = -f[x] *)
Corollary Seq_Neg_Property : ∀ f x, f ∈ Rᴺ -> (-f)[x] = (-f[x])%r.
Proof.
  intros. New H. apply Seq_Neg_Close in H0.
  apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  destruct (classic (x ∈ N)).
  - rewrite <-H5 in H7. apply Property_Value,AxiomII' in H7; tauto.
  - New H7. rewrite <-H5 in H7. rewrite <-H2 in H8.
    apply MKT69a in H7,H8. rewrite H7,H8.
    assert (\{ λ u, u ∈ R /\ (u + μ)%r = 0 \} = Φ).
    { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
      apply AxiomII in H9 as [H9[]].
      assert ([z,μ] ∉ dom(fp)).
      { intro. apply AxiomII in H12 as []. apply MKT49b in H12 as [].
        apply MKT39; auto. }
      apply MKT69a in H12. rewrite H11 in H12.
      assert (0 ∈ μ). { apply MKT19; eauto with real. }
      rewrite H12 in H13. elim MKT39; eauto. }
    rewrite H9,MKT24; auto.
Qed.

Lemma Inv_0_is_universe : 0⁻ = μ.
Proof.
  apply AxiomI; split; intros. apply MKT19. eauto. apply AxiomII; split.
  eauto. intros. apply AxiomII in H0 as [H0[]]. rewrite PlusMult_Co1 in H2.
  New OrderPM_Co9. rewrite H2 in H3. destruct H3. elim H4; auto.
  apply MKT4' in H1; tauto.
Qed.

Lemma Inv_universe_is_universe : μ⁻ = μ.
Proof.
  apply AxiomI; split; intros. apply MKT19. eauto. apply AxiomII; split.
  eauto. intros. apply AxiomII in H0 as [H0[]].
  assert ([y,μ] ∉ dom(fm)).
  { intro. apply AxiomII in H3 as []. apply MKT49b in H3 as [].
    apply MKT39; auto. }
  apply MKT69a in H3. rewrite H2 in H3. elim MKT39.
  rewrite <-H3; eauto with real.
Qed.

(*定义 数列的逆数列(值为0的项保持为0) *)
Definition Seq_Inv f := \{\ λ u v, u ∈ N
  /\ ((f[u] = 0 /\ v = 0) \/ (f[u] <> 0 /\ v = (f[u])⁻)) \}\.
Notation "/ f" := (Seq_Inv f) : Seq_scope.

(*验证 逆运算在数列空间中封闭 *)
Corollary Seq_Inv_Close : ∀ f, f ∈ Rᴺ -> (/f) ∈ Rᴺ.
Proof.
  intros. apply AxiomII in H as [H[H1[]]].
  assert (Function (/f)).
  { split; unfold Relation; intros.
    apply AxiomII in H3 as [H3[x[y[]]]]; eauto.
    apply AxiomII' in H3 as [_[_[[]|[]]]], H4 as [_[_[[]|[]]]]; subst; auto.
    rewrite H3 in H4. contradiction. rewrite H4 in H3. contradiction. }
  assert (dom(/f) = N).
  { apply AxiomI; split; intros. apply AxiomII in H4 as [H4[]].
    apply AxiomII' in H5 as []; tauto. apply AxiomII; split; eauto.
    destruct (classic (f[z] = 0)).
    - exists 0. apply AxiomII'; split; auto. apply MKT49a; eauto with real.
    - exists ((f[z])⁻). apply AxiomII'; split; auto. apply MKT49a; eauto.
      exists (R ~ [0]). apply Mult_inv1. rewrite <-H0 in H4.
      apply Property_Value,Property_ran,H2 in H4; auto.
      apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H6; eauto with real. }
  assert (ran(/f) ⊂ R).
  { unfold Included; intros. apply AxiomII in H5 as [H5[]].
    apply AxiomII' in H6 as [H6[H7[[]|[]]]]; rewrite H9. eauto with real.
    assert (f[x] ∈ R).
    { apply H2,(@ Property_ran x),Property_Value; auto. rewrite H0; auto. }
    assert (f[x] ∈ (R ~ [0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
      apply MKT41 in H11; eauto with real. }
    apply Mult_inv1,MKT4' in H11; tauto. }
  apply AxiomII; split; auto. apply MKT75; auto.
  rewrite H4. apply (MKT33 R). apply Ensemble_R. apply N_Subset_R.
Qed.

(*验证 函数f满足：(/f)[x] = (f[x])⁻ *)
Corollary Seq_Inv_Property_a : ∀ f x, f ∈ Rᴺ -> f[x] = 0 <-> (/f)[x] = 0.
Proof.
  intros. New H. apply Seq_Inv_Close in H0.
  apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  destruct (classic (x ∈ N)).
  - New H7. rewrite <-H2 in H7. rewrite <-H5 in H8.
    apply Property_Value,AxiomII' in H8 as [H8[H9[[]|[]]]]; auto.
    rewrite H10,H11. split; auto. split; intros. contradiction.
    assert (f[x] ∈ (R ~ [0])).
    { assert (f[x] ∈ R).
      { apply Property_Value,Property_ran,H3 in H7; auto. }
      apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H14; eauto with real. }
    apply Mult_inv1,MKT4' in H13 as []. apply AxiomII in H14 as [].
    elim H15. rewrite H11 in H12. apply MKT41; eauto with real.
  - New H7. rewrite <-H2 in H7. rewrite <-H5 in H8.
    apply MKT69a in H7,H8. rewrite H7,H8. split; auto.
Qed.

Corollary Seq_Inv_Property_b : ∀ f x, f ∈ Rᴺ -> f[x] <> 0 <-> (/f)[x] = (f[x])⁻.
Proof.
  intros. New H. apply Seq_Inv_Close in H0.
  apply AxiomII in H as [H[H1[]]], H0 as [H0[H4[]]].
  destruct (classic (x ∈ N)).
  - New H7. rewrite <-H2 in H7. rewrite <-H5 in H8.
    apply Property_Value,AxiomII' in H8 as [H8[H9[[]|[]]]]; auto.
    rewrite H10,H11,Inv_0_is_universe. split; intros. contradiction.
    elim MKT39. rewrite <-H12. eauto with real. split; auto.
  - New H7. rewrite <-H2 in H7. rewrite <-H5 in H8.
    apply MKT69a in H7,H8. rewrite H7,H8,Inv_universe_is_universe.
    split; auto. intros. intro. apply MKT39. rewrite H10. eauto with real.
Qed.


(*********  一些具体数列  *********)

(* 常值数列 *)
Definition ConstSeq r := \{\ λ u v, u ∈ N /\ v = r \}\.

Property ConstSeq_is_Seq : ∀ r, r ∈ R -> (ConstSeq r) ∈ Rᴺ.
Proof.
  intros. assert (Function (ConstSeq r)).
  { split; unfold Relation; intros.
    apply AxiomII in H0 as [H0[x[y[]]]]; eauto.
    apply AxiomII' in H0 as [H0[]], H1 as [H1[]]. rewrite H3,H5; auto. }
  assert (dom(ConstSeq r) = N).
  { apply AxiomI; split; intros. apply Property_Value,AxiomII' in H1; tauto.
    apply AxiomII; split; eauto. exists r. apply AxiomII'; split; auto.
    apply MKT49a; eauto. }
  assert (ran(ConstSeq r) ⊂ R).
  { unfold Included; intros. apply AxiomII in H2 as [H2[]].
    apply AxiomII' in H3 as [_[]]. rewrite H4; auto. }
  apply AxiomII; split; auto. apply MKT75; auto.
  rewrite H1. apply (MKT33 R). apply Ensemble_R. apply N_Subset_R.
Qed.

Property ConstSeq_Value : ∀ r n, r ∈ R -> n ∈ N -> (ConstSeq r)[n] = r.
Proof.
  intros. New H. apply ConstSeq_is_Seq,AxiomII in H1 as [H1[H2[]]].
  rewrite <-H3 in H0. apply Property_Value,AxiomII' in H0; tauto.
Qed.

Property ConstSeq_Neg : ∀ r, r ∈ R -> (-(ConstSeq r))%seq = ConstSeq (-r)%r.
Proof.
  intros. New H. apply ConstSeq_is_Seq,Seq_Neg_Close,AxiomII in H0 as [_[H0[]]].
  New H. apply Plus_neg1a,ConstSeq_is_Seq,AxiomII in H3 as [_[H3[]]].
  apply MKT71; auto. intros. destruct (classic (x ∈ N)).
  - rewrite Seq_Neg_Property,ConstSeq_Value,ConstSeq_Value; auto.
    apply Plus_neg1a; auto. apply ConstSeq_is_Seq; auto.
  - New H6. rewrite <-H1 in H6. rewrite <-H4 in H7.
    apply MKT69a in H6,H7. rewrite H6,H7; auto.
Qed.

Property ConstSeq_Inv : ∀ r, r ∈ R -> r <> 0%r
  -> (/(ConstSeq r))%seq = ConstSeq (r⁻)%r.
Proof.
  intros. assert (r ∈ R ~ [0%r]).
  { apply MKT4'; split; auto. apply AxiomII; split. eauto. intro.
    apply MKT41 in H1; eauto with real. }
  apply Mult_inv1,MKT4' in H1 as []. apply AxiomII in H2 as [].
  New H. apply ConstSeq_is_Seq,Seq_Inv_Close,AxiomII in H4 as [_[H4[]]].
  New H1. apply ConstSeq_is_Seq,AxiomII in H7 as [_[H7[]]].
  apply MKT71; auto. intros. destruct (classic (x ∈ N)).
  - New H. apply ConstSeq_is_Seq,AxiomII in H11 as [_[H11[]]].
    assert ((ConstSeq r)[x] <> 0). { rewrite ConstSeq_Value; auto. }
    apply Seq_Inv_Property_b in H14; try apply ConstSeq_is_Seq; auto.
    rewrite H14,ConstSeq_Value,ConstSeq_Value; auto.
  - New H10. rewrite <-H5 in H10. rewrite <-H8 in H11.
    apply MKT69a in H10,H11. rewrite H10,H11; auto.
Qed.

Property ConstSeq_Plus : ∀ u v, u ∈ R -> v ∈ R
  -> ((ConstSeq u) + (ConstSeq v))%seq = ConstSeq (u + v)%r.
Proof.
  intros. New H. New H0. apply ConstSeq_is_Seq in H1,H2; auto.
  assert (((ConstSeq u) + (ConstSeq v))%seq ∈ Rᴺ) by (apply Seq_Plus_Close; auto).
  assert ((u + v)%r ∈ R) by auto with real. apply ConstSeq_is_Seq in H4.
  apply AxiomII in H3 as [_[H3[]]], H4 as [_[H4[]]]. apply MKT71; auto; intros.
  destruct (classic (x ∈ N)).
  - rewrite Seq_Plus_Property,ConstSeq_Value,ConstSeq_Value,ConstSeq_Value;
    auto with real.
  - New H9. rewrite <-H5 in H9. rewrite <-H7 in H10.
    apply MKT69a in H9,H10. rewrite H9,H10; auto.
Qed.

Property ConstSeq_Mult : ∀ u v, u ∈ R -> v ∈ R
  -> ((ConstSeq u) · (ConstSeq v))%seq = ConstSeq (u · v)%r.
Proof.
  intros. New H. New H0. apply ConstSeq_is_Seq in H1,H2; auto.
  assert (((ConstSeq u) · (ConstSeq v))%seq ∈ Rᴺ) by (apply Seq_Mult_Close; auto).
  assert ((u · v)%r ∈ R) by auto with real. apply ConstSeq_is_Seq in H4.
  apply AxiomII in H3 as [_[H3[]]], H4 as [_[H4[]]]. apply MKT71; auto; intros.
  destruct (classic (x ∈ N)).
  - rewrite Seq_Mult_Property,ConstSeq_Value,ConstSeq_Value,ConstSeq_Value;
    auto with real.
  - New H9. rewrite <-H5 in H9. rewrite <-H7 in H10.
    apply MKT69a in H9,H10. rewrite H9,H10; auto.
Qed.










