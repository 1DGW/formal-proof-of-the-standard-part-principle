Require Import axiomatic_reals.seq_operations.
Require Import mk.equivalence_relation.
Require Export hr_NPUF.standard_numbers_in_hr.

(* 超自然数集 *)
Definition HN := \{ λ u, ∃ f, f ∈ Nᴺ /\ u = \[ f \] \}.

(* 超自然数集是超实数的子集 *)
Property HN_subset_HR : HN ⊂ HR.
Proof.
  red; intros. apply AxiomII in H as [H[f[]]].
  apply HR_Elements. exists f. split; auto. apply Nᴺ_Subset_Rᴺ; auto.
Qed.

(* 超自然数集不等于超实数集 *)
Property HN_isnot_HR : HN <> HR.
Proof.
  intro. New HR_Zero_in_HR. rewrite <-H in H0. apply AxiomII in H0 as [H0[f[]]].
  apply equClassT1,AxiomII' in H2 as [H2[H3[]]]. apply AxiomII in H1 as [_[H1[]]].
  assert (\{ λ u, u ∈ N /\ (ConstSeq 0%r)[u] = f[u] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H8 as [H8[]].
    rewrite ConstSeq_Value in H10; auto with real. rewrite <-H6 in H9.
    apply Property_Value,Property_ran,H7 in H9; auto. rewrite <-H10 in H9.
    elim zero_not_in_N; auto. elim (@ MKT16 z); auto. }
  rewrite H8 in H5. destruct F0_is_NPUF_over_N as [[[_[]]]]; auto.
  apply Equ_NPUF_is_equRelation_over_Rᴺ. apply ConstSeq_is_Seq; auto with real.
  apply Nᴺ_Subset_Rᴺ; auto.
Qed.

(* 自然数集是超自然数的子集 *)
Property HR_N_subset_HN : HR_N ⊂ HN.
Proof.
  red; intros. apply AxiomII in H as [H[n[]]]. apply AxiomII; split. auto.
  exists (ConstSeq n). split; auto. New H0. apply N_Subset_R in H2.
  apply ConstSeq_is_Seq,AxiomII in H2 as [H2[H3[]]]. apply AxiomII; split; auto.
  split; auto. split; auto. red; intros. apply Einr in H6 as [x[]]; auto.
  rewrite H4 in H6. rewrite ConstSeq_Value in H7; auto. rewrite H7; auto.
  apply N_Subset_R; auto.
Qed.

(* 一个具体的无穷大自然数 τ (恒等函数的等价类)
   可以简单理解τ为数列 1,2,3, ... ,n, ... 延伸至无穷项以后达到的无穷大 *)
Definition τ := \[ (\{\ λ u v, u ∈ N /\ v = u \}\) \].

Property τ_is_infinity_N : τ ∈ (HN ~ HR_N).
Proof.
  assert (\{\ λ u v, u ∈ N /\ v = u \}\ ∈ Nᴺ).
  { assert (Function (\{\ λ u v, u ∈ N /\ v = u \}\)).
    { split; unfold Relation; intros. apply AxiomII in H as [H[x[y[]]]]; eauto.
      apply AxiomII' in H as [H[]], H0 as [H0[]]. subst; auto. }
    assert (dom(\{\ λ u v, u ∈ N /\ v = u \}\) = N).
    { apply AxiomI; split; intros. apply AxiomII in H0 as [_[]].
      apply AxiomII' in H0; tauto. apply AxiomII. split. eauto. exists z.
      apply AxiomII'; split; auto. apply MKT49a; eauto. }
    assert (ran(\{\ λ u v, u ∈ N /\ v = u \}\) ⊂ N).
    { red; intros. apply AxiomII in H1 as [_[]].
      apply AxiomII' in H1 as [_[]]. rewrite H2; auto. }
    apply AxiomII; split; auto. apply MKT75; auto. rewrite H0. apply N_is_Set. }
  apply MKT4'; split. apply AxiomII; split. apply Hyperreal_is_set.
  exists (\{\ λ u v, u ∈ N /\ v = u \}\). auto. apply AxiomII; split.
  apply Hyperreal_is_set. intro. apply AxiomII in H0 as [H0[n[]]].
  New H1. apply N_Subset_R in H3. apply equClassT1,AxiomII' in H2 as [H2[H4[]]].
  assert (\{ λ u, u ∈ N /\ (\{\ λ u v, u ∈ N /\ v = u \}\)[u]
    = (ConstSeq n)[u] \} = [n]).
  { apply AxiomI; split; intros.
    - apply AxiomII in H7 as [H7[]]. rewrite ConstSeq_Value in H9; auto.
      apply AxiomII in H as [_[H[]]]. rewrite <-H10 in H8.
      apply Property_Value,AxiomII' in H8 as [_[]]; auto. rewrite H12 in H9.
      apply MKT41; eauto.
    - apply MKT41 in H7; eauto. rewrite H7. apply AxiomII; repeat split; eauto.
      rewrite ConstSeq_Value; auto. apply AxiomII in H as [_[H[]]].
      rewrite <-H8 in H1. apply Property_Value,AxiomII' in H1 as [_[]]; auto. }
  rewrite H7 in H6. destruct F0_is_NPUF_over_N.
  elim (H9 ([n])); auto. red; intros. apply MKT41 in H10; eauto.
  rewrite H10; auto. apply finsin; eauto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply Nᴺ_Subset_Rᴺ; auto. apply ConstSeq_is_Seq; auto.
Qed.

Property τ_in_HR : τ ∈ HR.
Proof.
  New τ_is_infinity_N. apply MKT4' in H as []. apply HN_subset_HR; auto.
Qed.

Property HNinf_larger_than_N : ∀ n t, n ∈ HR_N -> t ∈ (HN ~ HR_N)
  -> n < t.
Proof.
  intros. assert (n <> t).
  { intro. apply MKT4' in H0 as []. apply AxiomII in H2 as [].
    apply H3. rewrite <-H1; auto. }
  split; auto. apply AxiomII in H as [H[x[]]]. apply MKT4' in H0 as [].
  apply AxiomII in H0 as [H0[f[]]]. rewrite H3,H6. apply HR_Leq_Instantiate.
  apply ConstSeq_is_Seq,N_Subset_R; auto. apply Nᴺ_Subset_Rᴺ; auto.
  New H2. apply N_Subset_R in H7. New H7. apply ConstSeq_is_Seq,AxiomII in H8
  as [_[H8[]]]. New H5. apply AxiomII in H11 as [_[H11[]]].
  assert (\{ λ w, w ∈ N /\ ((ConstSeq x)[w] ≤ f[w])%r \}
    ∪ \{ λ w, w ∈ N /\ (f[w] ≤ (ConstSeq x)[w])%r \} = N).
  { apply AxiomI; split; intros.
    apply MKT4 in H14 as []; apply AxiomII in H14; tauto. apply MKT4.
    New H14. rewrite <-H12 in H15. apply Property_Value,Property_ran,H13
    in H15; auto. New (ConstSeq_Value x z H7 H14).
    destruct (Leq_P4 f[z] x); auto with real; [right|left]; apply AxiomII;
    rewrite H16; split; eauto. }
  destruct F0_is_NPUF_over_N as [H15 _]. New H15.
  destruct H16 as [[H16[H17[H18[]]]]_]. rewrite <-H14 in H18.
  apply (FT1 F0 N) in H18 as []; auto.
  assert (\{ λ w, w ∈ N /\ (f[w] ≤ (ConstSeq x)[w])%r \}
    ⊂ ∪\{ λ u, ∃ n, n ∈ N /\ (n ≤ x)%r /\ u = \{ λ w, w ∈ N /\ f[w] = n \} \}).
  { red; intros. apply AxiomII in H21 as [_[]]. apply AxiomII; split. eauto.
    exists (\{ λ w, w ∈ N /\ f[w] = f[z] \}). split. apply AxiomII; split; eauto.
    apply AxiomII; split; [ |exists f[z]]. apply (MKT33 N). apply N_is_Set.
    red; intros. apply AxiomII in H23; tauto. rewrite ConstSeq_Value in H22; auto.
    split; auto. apply AxiomII in H5 as [_[H5[]]]. rewrite <-H23 in H21.
    apply Property_Value,Property_ran in H21; auto. }
  set (h := \{\ λ u v, u ∈ N /\ (u ≤ x)%r
    /\ v = \{ λ w, w ∈ N /\ f[w] = u \} \}\).
  assert (Function h /\ dom(h) = \{ λ u, u ∈ N /\ (u ≤ x)%r \}
    /\ ran(h) = \{ λ u, ∃ n, n ∈ N /\ (n ≤ x)%r
    /\ u = \{ λ w, w ∈ N /\ f[w] = n \} \}) as [H22[]].
  { repeat split; unfold Relation; intros.
    - apply AxiomII in H22 as [_[a[b[]]]]; eauto.
    - apply AxiomII' in H22 as [_[_[]]], H23 as [_[_[]]]. subst; auto.
    - apply AxiomI; split; intros. apply AxiomII in H22 as [_[]].
      apply AxiomII' in H22 as [H22[H23[]]]. apply AxiomII; split; eauto.
      apply AxiomII in H22 as [H22[]]. apply AxiomII; split; auto.
      exists (\{ λ w, w ∈ N /\ f[w] = z \}). apply AxiomII'; split; auto.
      apply MKT49a; auto. apply (MKT33 N). apply N_is_Set. red; intros.
      apply AxiomII in H25; tauto.
    - apply AxiomI; split; intros. apply AxiomII in H22 as [H22[]].
      apply AxiomII' in H23 as [H23[H24[]]]. apply AxiomII; split; eauto.
      apply AxiomII in H22 as [H22[x0[H23[]]]]. apply AxiomII; split; auto.
      exists x0. apply AxiomII'; split; auto. apply MKT49a; eauto. }
  assert (∀ m, m ∈ N -> Finite (\{ λ u, u ∈ N /\ (u ≤ m)%r \})).
  { intros. set (E := \{ λ u, u ∈ N /\ Finite (\{ λ w, w ∈ N /\ (w ≤ u)%r \}) \}).
    assert (E = N).
    { apply MathInd. red; intros. apply AxiomII in H26; tauto.
      apply AxiomII; repeat split; eauto with real.
      assert (\{ λ w, w ∈ N /\ (w ≤ 1)%r \} = [1%r]).
      { apply AxiomI; split; intros. apply AxiomII in H26 as [H26[]].
        apply MKT41; eauto with real. destruct one_is_min_in_N as [_[_]].
        New H27. apply H29 in H30. apply Leq_P2; auto with real.
        apply MKT41 in H26; eauto with real. apply AxiomII. rewrite H26.
        repeat split; eauto with real. apply Leq_P1; auto with real. }
      rewrite H26. apply finsin. eauto with real. intros. apply AxiomII in H26
      as [H26[]]. apply AxiomII; repeat split; eauto with real.
      assert (\{ λ w, w ∈ N /\ (w ≤ x0 + 1)%r \}
        = \{ λ w, w ∈ N /\ (w ≤ x0)%r \} ∪ [(x0 + 1)%r]).
      { apply AxiomI; split; intros. apply AxiomII in H29 as [H29[]].
        apply MKT4. destruct (Leq_P4 z x0); auto with real. left.
        apply AxiomII; auto. destruct (classic (z = x0)).
        left. apply AxiomII; repeat split; auto. rewrite H33.
        apply Leq_P1; auto with real. assert (z = (x0 + 1)%r).
        { apply Leq_P2; auto with real. apply Nat_P4; auto. split; auto. }
        right. apply MKT41; eauto with real. apply AxiomII; split. eauto.
        apply MKT4 in H29 as []. apply AxiomII in H29 as [H29[]]. split; auto.
        apply (Leq_P3 z x0); auto with real. destruct OrderPM_Co9.
        apply (OrderPM_Co3 x0 x0) in H32; auto with real.
        rewrite Plus_P1 in H32; auto with real. apply Leq_P1; auto with real.
        apply MKT41 in H29; eauto with real. rewrite H29. split. auto with real.
        apply Leq_P1; auto with real. }
      rewrite H29. apply MKT168; auto. apply finsin. eauto with real. }
    rewrite <-H26 in H25. apply AxiomII in H25; tauto. }
  apply H20,(FT1_Corollary _ N) in H21 as [X[]]; auto.
  apply AxiomII in H21 as [H21[x0[H27[]]]]. apply AxiomII in H4 as [].
  elim H30. apply AxiomII. split. rewrite H6. apply Hyperreal_is_set.
  exists x0. split; auto. New H5. apply Nᴺ_Subset_Rᴺ in H31. New H27.
  apply N_Subset_R,ConstSeq_is_Seq in H32. rewrite H6. apply equClassT1; auto.
  apply Equ_NPUF_is_equRelation_over_Rᴺ. apply AxiomII'; repeat split; auto.
  apply MKT49a; eauto. assert (X ⊂ \{ λ u,u ∈ N /\ f[u] = (ConstSeq x0)[u] \}).
  { red; intros. rewrite H29 in H33. apply AxiomII in H33 as [H33[]].
    apply AxiomII; repeat split; auto. rewrite ConstSeq_Value; auto with real. }
  apply H20 in H33; auto. red; intros. apply AxiomII in H34; tauto.
  assert (Ensemble h).
  { apply MKT75; auto. rewrite H23. apply (MKT33 N). apply N_is_Set.
    red; intros. apply AxiomII in H26; tauto. }
  apply MKT160 in H26; auto. assert (Finite dom(h)). { rewrite H23; auto. }
  destruct H26. red in H27. New MKT138. apply AxiomII in H28 as [_[_]].
  apply H28 in H27. apply H27 in H26. rewrite <-H24; auto. red in H27.
  rewrite <-H26,H24 in H27; auto. red; intros. apply AxiomII in H26 as [_[x0[]]].
  apply AxiomII in H27 as [_[x1[_[]]]]. rewrite H28 in H26.
  apply AxiomII in H26; tauto.
Qed.

Property τ_larger_than_N : ∀ n, n ∈ HR_N -> n < τ.
Proof. intros. apply HNinf_larger_than_N; auto. apply τ_is_infinity_N. Qed.

Property τ_is_Pos : 0 < τ.
Proof.
  New HR_One_in_HR_N. apply τ_larger_than_N in H. New τ_in_HR. New HR_One_in_HR.
  New HR_Zero_in_HR. apply (HR_Less_Transitivity 0 1); auto. apply HR_0_less_1.
Qed.


(* 三个重要非标准数集, 其中有限大数集在超实数集中的补集称为无穷大集(HR ~ HR_Finity) *)

(* 有限大数集合 *)
Definition HR_Finity := \{ λ u, u ∈ HR /\ (∃ r, r ∈ HR_R /\ ∣u∣ ≤ r) \}.

(* 无穷大集合 *)
Definition HR_Infinity := \{ λ u, u ∈ HR /\ (∀ r, r ∈ HR_R -> r < ∣u∣) \}.

(* 无穷小集合 *)
Definition HR_Infsimal := \{ λ u, u ∈ HR
  /\ (∀ r, r ∈ HR_R -> r <> 0 -> ∣u∣ < ∣r∣) \}.



(************************ 非标准数与标准数之间的关系 **********************)

(* 有限大集为超实数集的子集 *)
Property HR_Finity_subset_HR : HR_Finity ⊂ HR.
Proof. red; intros. apply AxiomII in H; tauto. Qed.

(* 无穷大集为超实数集的子集 *)
Property HR_Infinity_subset_HR : HR_Infinity ⊂ HR.
Proof. red; intros. apply AxiomII in H; tauto. Qed.

(* 无穷小集为超实数集的子集 *)
Property HR_Infsimal_subset_HR : HR_Infsimal ⊂ HR.
Proof. red; intros. apply AxiomII in H; tauto. Qed.

(* 无穷小集为有限大数集的子集 *)
Property HR_Infsimal_subset_Finity : HR_Infsimal ⊂ HR_Finity.
Proof.
  red; intros. apply AxiomII in H as [H[]]. apply AxiomII; repeat split; auto.
  New HR_One_in_HR_R. New H2. apply HR_R_Abs_Close in H3. exists (∣1∣).
  split; auto. apply H1; auto. intro. apply HR_Zero_isnot_One; auto.
Qed.


(* 标准数集为有限大集合的子集 *)
Property HR_R_subset_Finity : HR_R ⊂ HR_Finity.
Proof.
  red; intros. New H. apply HR_R_subset_HR in H0. apply AxiomII;
  repeat split; eauto. exists ∣z∣. split. apply ->HR_R_Abs_Close; auto.
  apply HR_Leq_Reflexivity. apply ->HR_Abs_Close; auto.
Qed.

Property HR_Q_subset_Finity : HR_Q ⊂ HR_Finity.
Proof.
  red; intros. New H. apply HR_Q_subset_HR in H0. apply AxiomII;
  repeat split; eauto. exists ∣z∣. split. apply HR_Q_subset_HR_R.
  apply ->HR_Q_Abs_Close; auto. apply HR_Leq_Reflexivity.
  apply ->HR_Abs_Close; auto.
Qed.

Property HR_Z_subset_Finity : HR_Z ⊂ HR_Finity.
Proof.
  red; intros. New H. apply HR_Z_subset_HR in H0. apply AxiomII;
  repeat split; eauto. exists ∣z∣. split. apply HR_Z_subset_HR_R.
  apply ->HR_Z_Abs_Close; auto. apply HR_Leq_Reflexivity.
  apply ->HR_Abs_Close; auto.
Qed.

Property HR_N_subset_Finity : HR_N ⊂ HR_Finity.
Proof.
  red; intros. New H. apply HR_N_subset_HR in H0. apply AxiomII;
  repeat split; eauto. exists ∣z∣. split. apply HR_N_subset_HR_R.
  rewrite HR_N_Abs_Close; auto. apply HR_Leq_Reflexivity.
  rewrite HR_N_Abs_Close; auto.
Qed.


(* 无穷大自然数集是无穷大集的子集 *)
Property HNinf_subset_Infinity : (HN ~ HR_N) ⊂ HR_Infinity.
Proof.
  red; intros. New H. apply MKT4' in H0 as [H0 _]. New H0.
  apply HN_subset_HR in H1. apply AxiomII; split. eauto. split; auto.
  intros. New H2. apply HR_R_Arch_b in H3 as [n[H3[]]].
  assert ((n + 1) ∈ HR_N).
  { destruct H3. rewrite H3,HR_0_Plus. apply HR_One_in_HR_N.
    apply HR_One_in_HR. apply HR_N_Plus_Close; auto. apply HR_One_in_HR_N. }
  apply (HNinf_larger_than_N (n + 1) z) in H; auto.
  assert (∣z∣ = z).
  { apply HR_Abs_Pos; auto. New H6. apply HR_N_subset_HR in H7.
    apply (HR_Less_Transitivity 0 (n + 1)); auto. apply HR_Zero_in_HR.
    destruct H3. rewrite H3,HR_0_Plus. apply HR_0_less_1. apply HR_One_in_HR.
    apply HR_0_less_n; auto. }
  rewrite H7 in *. New H2. apply HR_R_subset_HR in H8. New H8.
  apply HR_Abs_Close in H9. apply (HR_Less_Transitivity_Co r (∣r∣)); auto.
  right. split. apply HR_r_leq_abs_r; auto.
  apply (HR_Less_Transitivity _ (n + 1)); auto. apply HR_N_subset_HR; auto.
Qed.


Property HR_Zero_in_Finity : 0 ∈ HR_Finity.
Proof. apply HR_R_subset_Finity. apply HR_Zero_in_HR_R. Qed.

Property HR_One_in_Finity : 1 ∈ HR_Finity.
Proof. apply HR_R_subset_Finity. apply HR_One_in_HR_R. Qed.

(* 无穷小集与标准数集只有一个公共元0 *)
Property HR_Zero_in_Infsimal : 0 ∈ HR_Infsimal.
Proof.
  New HR_Zero_in_HR. apply AxiomII; split; eauto. split; auto. intros.
  rewrite HR_Abs_0. apply HR_0_less_abs; auto. apply HR_R_subset_HR; auto.
Qed.

Property HR_Infsimal_inter_R : HR_Infsimal ∩ HR_R = [0].
Proof.
  New HR_Zero_in_HR. apply AxiomI; split; intros.
  - apply MKT4' in H0 as []. apply MKT41; eauto. apply AxiomII in H0 as [H0[]].
    apply NNPP; intro. assert (∣z∣ < ∣z∣) as []. { apply H3; auto. } auto.
  - apply MKT41 in H0; eauto. rewrite H0. apply MKT4'; split.
    apply HR_Zero_in_Infsimal. apply HR_Zero_in_HR_R.
Qed.

Property HR_Infsimal_inter_Q : HR_Infsimal ∩ HR_Q = [0].
Proof.
  New HR_Zero_in_HR. apply AxiomI; split; intros.
  - apply MKT4' in H0 as []. apply MKT41; eauto. apply AxiomII in H0 as [H0[]].
    apply NNPP; intro. assert (∣z∣ < ∣z∣) as [].
    { apply H3; auto. apply HR_Q_subset_HR_R; auto. } auto.
  - apply MKT41 in H0; eauto. rewrite H0. apply MKT4'; split.
    apply HR_Zero_in_Infsimal. apply HR_Zero_in_HR_Q.
Qed.

Property HR_Infsimal_inter_Z : HR_Infsimal ∩ HR_Z = [0].
Proof.
  New HR_Zero_in_HR. apply AxiomI; split; intros.
  - apply MKT4' in H0 as []. apply MKT41; eauto. apply AxiomII in H0 as [H0[]].
    apply NNPP; intro. assert (∣z∣ < ∣z∣) as [].
    { apply H3; auto. apply HR_Z_subset_HR_R; auto. } auto.
  - apply MKT41 in H0; eauto. rewrite H0. apply MKT4'; split.
    apply HR_Zero_in_Infsimal. apply HR_Zero_in_HR_Z.
Qed.


(* 有限大数集与无穷大集互补 *)
Property HR_Finity_and_Infinity_Complement_a : HR_Finity ∪ HR_Infinity = HR.
Proof.
  apply AxiomI; split; intros.
  - apply MKT4 in H as []; apply AxiomII in H; tauto.
  - apply MKT4. destruct (classic ((∃ r, r ∈ HR_R /\ ∣z∣ ≤ r))). left.
    apply AxiomII; split; eauto. right. apply AxiomII; split; eauto.
    split; auto. intros. New H. apply HR_Abs_Close in H2. New H1.
    apply HR_R_subset_HR in H3. New H2.
    apply (HR_Less_Trichotomy r) in H4 as [H4|[]]; auto; elim H0.
    destruct H4; eauto. exists r. rewrite <-H4. split; auto.
    apply HR_Leq_Reflexivity; auto.
Qed.

Property HR_Finity_and_Infinity_Complement_b : HR_Finity ∩ HR_Infinity = Φ.
Proof.
  apply AxiomI; split; intros; elim (@ MKT16 z); auto.
  apply MKT4' in H as []. apply AxiomII in H as [H[H1[r[]]]].
  apply AxiomII in H0 as [_[_]]. New H1. apply HR_Abs_Close in H4.
  New H2. apply H0 in H5 as []. elim H6. apply HR_Leq_Asymmetry; auto.
  apply HR_R_subset_HR; auto.
Qed.


(* τ是一个无穷大数 *)
Property τ_in_Infinity : τ ∈ HR_Infinity.
Proof. New τ_is_infinity_N. apply HNinf_subset_Infinity; auto. Qed.

Property τ_larger_than_r : ∀ r, r ∈ HR_R -> r < τ.
Proof.
  New τ_in_Infinity. intros. apply AxiomII in H as [_[]]. apply H1 in H0.
  New τ_is_Pos. apply HR_Abs_Pos in H2; auto. rewrite H2 in H0; auto.
Qed.

(* τ⁻是一个正无穷小 *)
Property invτ_in_Infsimal : τ⁻ ∈ HR_Infsimal.
Proof.
  New τ_in_HR. New τ_in_Infinity. New τ_is_Pos.
  assert (τ⁻ ∈ HR). { apply ->HR_Inv_Close. destruct H1; auto. }
  apply AxiomII; split. eauto. split; auto. intros.
  assert (r⁻ ∈ HR_R). { apply ->HR_R_Inv_Close; auto. }
  New H5. apply HR_R_Arch_c in H6 as [n[]]. New H6. apply τ_larger_than_N in H8.
  apply HR_N_subset_HR in H6. apply HR_R_subset_HR in H3,H5. New H5.
  apply HR_Abs_Close in H9. assert (∣r⁻∣ < τ).
  { apply (HR_Less_Transitivity _ n); auto. }
  apply HR_inv_less_inv in H10; auto. rewrite HR_Abs_Pr_Inv in H10.
  rewrite HR_Abs_Pr_Inv. apply HR_Abs_Pos in H1; auto. rewrite H1.
  assert (∣r∣ <> 0). { intro. apply ->HR_abs_eq_0 in H11; auto. }
  apply HR_Double_Inv in H11. rewrite <-H11; auto. apply ->HR_Abs_Close; auto.
  right. split; auto. rewrite HR_Abs_Pr_Inv. apply ->HR_0_less_inv.
  apply HR_0_less_abs; auto. apply ->HR_Abs_Close; auto.
Qed.

Property invτ_is_Pos : 0 < τ⁻.
Proof.
  New τ_in_HR. New τ_in_Infinity. apply ->HR_0_less_inv; auto.
  apply (HR_Less_Transitivity 0 1); auto. apply HR_Zero_in_HR.
  apply HR_One_in_HR. apply HR_0_less_1. apply τ_larger_than_N.
  apply HR_One_in_HR_N.
Qed.

Property invτ_less_than_r : ∀ r, r ∈ HR_R -> r <> 0 -> τ⁻ < ∣r∣.
Proof.
  New invτ_in_Infsimal. intros. apply AxiomII in H as [_[]].
  apply H2 in H0; auto. New invτ_is_Pos. apply HR_Abs_Pos in H3; auto.
  rewrite H3 in H0; auto.
Qed.


(* 标准数集与非标准数集不相等 *)
Property HR_R_isnot_HR : HR_R <> HR.
Proof.
  New τ_in_HR. New τ_in_Infinity. New HR_Finity_and_Infinity_Complement_b.
  intro. rewrite <-H2 in H. apply (@ MKT16 τ). rewrite <-H1.
  apply MKT4'; split; auto. apply HR_R_subset_Finity; auto.
Qed.

Property HR_Q_isnot_HR : HR_Q <> HR.
Proof.
  New τ_in_HR. New τ_in_Infinity. New HR_Finity_and_Infinity_Complement_b.
  intro. rewrite <-H2 in H. apply (@ MKT16 τ). rewrite <-H1.
  apply MKT4'; split; auto. apply HR_Q_subset_Finity; auto.
Qed.

Property HR_Z_isnot_HR : HR_Z <> HR.
Proof.
  New τ_in_HR. New τ_in_Infinity. New HR_Finity_and_Infinity_Complement_b.
  intro. rewrite <-H2 in H. apply (@ MKT16 τ). rewrite <-H1.
  apply MKT4'; split; auto. apply HR_Z_subset_Finity; auto.
Qed.

Property HR_N_isnot_HR : HR_N <> HR.
Proof.
  New τ_in_HR. New τ_in_Infinity. New HR_Finity_and_Infinity_Complement_b.
  intro. rewrite <-H2 in H. apply (@ MKT16 τ). rewrite <-H1.
  apply MKT4'; split; auto. apply HR_N_subset_Finity; auto.
Qed.

Property HR_R_isnot_Finity : HR_R <> HR_Finity.
Proof.
  New invτ_in_Infsimal. New H. apply HR_Infsimal_subset_Finity in H0.
  intro. rewrite <-H1 in H0. apply AxiomII in H as [_[]].
  apply H2 in H0 as []; auto. apply HR_Inv_isnot_0.
Qed.

Property HR_Q_isnot_Finity : HR_Q <> HR_Finity.
Proof.
  New invτ_in_Infsimal. New H. apply HR_Infsimal_subset_Finity in H0.
  intro. rewrite <-H1 in H0. apply AxiomII in H as [_[]].
  apply HR_Q_subset_HR_R,H2 in H0 as []; auto. apply HR_Inv_isnot_0.
Qed.

Property HR_Z_isnot_Finity : HR_Z <> HR_Finity.
Proof.
  New invτ_in_Infsimal. New H. apply HR_Infsimal_subset_Finity in H0.
  intro. rewrite <-H1 in H0. apply AxiomII in H as [_[]].
  apply HR_Z_subset_HR_R,H2 in H0 as []; auto. apply HR_Inv_isnot_0.
Qed.

Property HR_N_isnot_Finity : HR_N <> HR_Finity.
Proof.
  New invτ_in_Infsimal. New H. apply HR_Infsimal_subset_Finity in H0.
  intro. rewrite <-H1 in H0. apply AxiomII in H as [_[]].
  apply HR_N_subset_HR_R,H2 in H0 as []; auto. apply HR_Inv_isnot_0.
Qed.

Property HR_R_isnot_Infsimal : HR_R <> HR_Infsimal.
Proof.
  New HR_One_in_HR_R. intro. rewrite H0 in H. apply AxiomII in H as [_[]].
  New HR_0_less_1. New HR_One_in_HR_R. apply H1 in H3 as []; auto.
  destruct H2; auto.
Qed.

Property HR_Q_isnot_Infsimal : HR_Q <> HR_Infsimal.
Proof.
  New HR_One_in_HR_Q. intro. rewrite H0 in H. apply AxiomII in H as [_[]].
  New HR_0_less_1. New HR_One_in_HR_R. apply H1 in H3 as []; auto.
  destruct H2; auto.
Qed.

Property HR_Z_isnot_Infsimal : HR_Z <> HR_Infsimal.
Proof.
  New HR_One_in_HR_Z. intro. rewrite H0 in H. apply AxiomII in H as [_[]].
  New HR_0_less_1. New HR_One_in_HR_R. apply H1 in H3 as []; auto.
  destruct H2; auto.
Qed.

Property HR_N_isnot_Infsimal : HR_N <> HR_Infsimal.
Proof.
  New HR_One_in_HR_N. intro. rewrite H0 in H. apply AxiomII in H as [_[]].
  New HR_0_less_1. New HR_One_in_HR_R. apply H1 in H3 as []; auto.
  destruct H2; auto.
Qed.

Property HR_R_isnot_Infinity : HR_R <> HR_Infinity.
Proof.
  New HR_One_in_HR_R. intro. New H. rewrite H0 in H1. apply AxiomII in H1
  as [_[]]. apply H2 in H as []. New HR_0_less_1. apply HR_Abs_Pos in H4; auto.
Qed.

Property HR_Q_isnot_Infinity : HR_Q <> HR_Infinity.
Proof.
  New HR_One_in_HR_Q. intro. New H. rewrite H0 in H1. apply AxiomII in H1
  as [_[]]. apply HR_Q_subset_HR_R,H2 in H as []. New HR_0_less_1.
  apply HR_Abs_Pos in H4; auto.
Qed.

Property HR_Z_isnot_Infinity : HR_Z <> HR_Infinity.
Proof.
  New HR_One_in_HR_Z. intro. New H. rewrite H0 in H1. apply AxiomII in H1
  as [_[]]. apply HR_Z_subset_HR_R,H2 in H as []. New HR_0_less_1.
  apply HR_Abs_Pos in H4; auto.
Qed.

Property HR_N_isnot_Infinity : HR_N <> HR_Infinity.
Proof.
  New HR_One_in_HR_N. intro. New H. rewrite H0 in H1. apply AxiomII in H1
  as [_[]]. apply HR_N_subset_HR_R,H2 in H as []. New HR_0_less_1.
  apply HR_Abs_Pos in H4; auto.
Qed.


(* 非标准数集之间也不尽相等 *)
Property HR_Finity_isnot_HR : HR_Finity <> HR.
Proof.
  New τ_in_HR. New τ_in_Infinity. New HR_Finity_and_Infinity_Complement_b.
  intro. rewrite <-H2 in H. apply (@ MKT16 τ). rewrite <-H1. apply MKT4'; auto.
Qed.

Property HR_Infinity_isnot_HR : HR_Infinity <> HR.
Proof.
  New HR_One_in_HR. intro. New H. rewrite <-H0 in H1. apply AxiomII in H1
  as [_[]]. New HR_One_in_HR_R. apply H2 in H3 as []. New HR_0_less_1.
  apply HR_Abs_Pos in H5; auto.
Qed.

Property HR_Infsimal_isnot_HR : HR_Infsimal <> HR.
Proof.
  New HR_One_in_HR. intro. New H. rewrite <-H0 in H1. apply AxiomII in H1
  as [_[]]. New HR_One_in_HR_R. New HR_0_less_1. apply H2 in H3 as []; auto.
  destruct H4; auto.
Qed.

Property HR_Infsimal_isnot_Finity : HR_Infsimal <> HR_Finity.
Proof.
  New HR_One_in_Finity. intro. rewrite <-H0 in H. apply AxiomII in H as [_[]].
  New HR_One_in_HR_R. New HR_0_less_1. apply H1 in H2 as []; auto.
  destruct H3; auto.
Qed.

Property HR_Infsimal_isnot_Infinity : HR_Infsimal <> HR_Infinity.
Proof.
  intro. New HR_Finity_and_Infinity_Complement_b. rewrite <-H in H0.
  apply (@ MKT16 0). rewrite <-H0. apply MKT4'. split.
  apply HR_Zero_in_Finity. apply HR_Zero_in_Infsimal.
Qed.

Property HR_Finity_isnot_Infinity : HR_Finity <> HR_Infinity.
Proof.
  intro. New HR_Finity_and_Infinity_Complement_b. rewrite <-H,MKT5' in H0.
  apply (@ MKT16 0). rewrite <-H0. apply HR_Zero_in_Finity.
Qed.

(* 无穷大自然数集不等于无穷大集 *)
Property HNinf_isnot_HR_Infinity : (HN ~ HR_N) <> HR_Infinity.
Proof.
  intro. New τ_in_HR. New τ_in_Infinity.
  assert (-τ ∈ HR_Infinity).
  { apply AxiomII in H1 as [_[]]. apply HR_Neg_Close in H1.
    apply AxiomII; split. eauto. split; auto. intros.
    rewrite HR_Abs_neg_eq_pos; auto. } rewrite <-H in H2.
  New HR_One_in_HR_N. apply (HNinf_larger_than_N 1) in H2; auto.
  New HR_Zero_in_HR. New HR_One_in_HR. New H0. apply HR_Neg_Close in H6.
  assert (0 < -τ).
  { apply (HR_Less_Transitivity 0 1); auto. apply HR_0_less_1. }
  New τ_is_Pos. apply HR_neg_less_0 in H8; auto. destruct H7,H8.
  apply H10,HR_Leq_Asymmetry; auto.
Qed.


(************************** 非标准数集中运算的封闭性 ***************************)

(* 全体有限数构成超实数的子环: 有限数的和、差、积均为有限数 *)
Property HR_Finity_Plus_Close : ∀ u v, u ∈ HR_Finity -> v ∈ HR_Finity
  -> (u + v) ∈ HR_Finity.
Proof.
  intros. apply AxiomII in H as [_[H[a[]]]],H0 as [_[H0[b[]]]].
  assert (u + v ∈ HR). { apply HR_Plus_Close; auto. }
  apply AxiomII; split. eauto. split; auto. New H. New H0. New H5.
  apply HR_Abs_Close in H6,H7,H8. New H1. New H3. apply HR_R_subset_HR in H9,H10.
  assert (∣u∣ + ∣v∣ ≤ a + b).
  { apply (HR_Leq_Pr_Plus _ _ ∣v∣) in H2; auto.
    apply (HR_Leq_Pr_Plus _ _ a) in H4; auto.
    rewrite HR_Plus_Com,(HR_Plus_Com b) in H4.
    apply (HR_Leq_Transitivity _ (a + ∣v∣)); auto; apply HR_Plus_Close; auto. }
  exists (a + b). split. apply HR_R_Plus_Close; auto.
  apply (HR_Leq_Transitivity _ ( ∣u∣ + ∣v∣)); try apply HR_Plus_Close; auto.
  apply HR_Abs_Triangle_inEqu; auto.
Qed.

Property HR_Finity_Neg_Close : ∀ u, u ∈ HR_Finity <-> -u ∈ HR_Finity.
Proof.
  assert (∀ u, u ∈ HR_Finity -> -u ∈ HR_Finity).
  { intros. apply AxiomII in H as [_[H[x[]]]]. New H. apply HR_Neg_Close in H2.
    apply AxiomII. rewrite HR_Abs_neg_eq_pos. split; eauto. }
  split; intros; auto. New H0. apply AxiomII in H1 as [_[H1 _]].
  apply H in H0. apply HR_Neg_Close in H1. rewrite HR_Double_Neg in H0; auto.
Qed.

Property HR_Finity_Minus_Close : ∀ u v, u ∈ HR_Finity -> v ∈ HR_Finity
  -> (u - v) ∈ HR_Finity.
Proof.
  intros. apply HR_Finity_Plus_Close; auto. apply ->HR_Finity_Neg_Close; auto.
Qed.

Property HR_Finity_Mult_Close : ∀ u v, u ∈ HR_Finity -> v ∈ HR_Finity
  -> (u · v) ∈ HR_Finity.
Proof.
  intros. apply AxiomII in H as [_[H[a[]]]], H0 as [_[H0[b[]]]].
  New H. apply HR_0_leq_abs in H5. New H0. apply HR_0_leq_abs in H6.
  assert (u·v ∈ HR). { apply HR_Mult_Close; auto. }
  assert (a·b ∈ HR_R). { apply HR_R_Mult_Close; auto. }
  apply AxiomII; split. eauto. split; auto. exists (a·b). split; auto.
  New H. apply HR_Abs_Close in H9. New H0. apply HR_Abs_Close in H10.
  apply HR_R_subset_HR in H1,H3.
  assert (∣u∣·∣v∣ ≤ a·∣v∣). { apply HR_Leq_and_Less_Pr_Mult_a; auto. }
  assert (a·∣v∣ ≤ a·b).
  { rewrite HR_Mult_Com,(HR_Mult_Com a). apply HR_Leq_and_Less_Pr_Mult_a; auto.
    apply (HR_Leq_Transitivity _ ∣u∣); auto. apply HR_Zero_in_HR. }
  rewrite HR_Abs_Pr_Mult. apply (HR_Leq_Transitivity _ (a·∣v∣)); auto;
  apply HR_Mult_Close; auto.
Qed.


(* 无穷小集构成超实数的子环: 无穷小的和、差、积均为无穷小 *)
Property HR_Infsimal_Plus_Close : ∀ u v, u ∈ HR_Infsimal -> v ∈ HR_Infsimal
  -> (u + v) ∈ HR_Infsimal.
Proof.
  intros. apply AxiomII in H as [_[]], H0 as [_[]].
  assert (u + v ∈ HR). { apply HR_Plus_Close; auto. }
  apply AxiomII; split. eauto. split; auto. intros.
  New H4. apply HR_R_Abs_Close in H6. New H4. New H6.
  apply HR_R_subset_HR in H7,H8. New HR_Zero_in_HR. New HR_One_in_HR.
  assert (1+1 ∈ HR). { apply HR_Plus_Close; auto. }
  assert (0 < 1+1).
  { New HR_0_less_1. New H12. apply (HR_Less_Pr_Plus 0 1 1) in H12; auto.
    rewrite HR_0_Plus in H12; auto. apply (HR_Less_Transitivity 0 1); auto. }
  assert (1+1 <> 0). { destruct H12; auto. }
  assert (∣r∣/(1+1) ∈ HR_R).
  { apply HR_R_Div_Close; auto. apply HR_R_Plus_Close; apply HR_One_in_HR_R. }
  assert (∣r∣/(1+1) <> 0).
  { intro. assert (∣r∣/(1+1) · (1+1) = 0·(1+1)). { rewrite H15; auto. }
    rewrite HR_Mult_Ass,(HR_Mult_Com (1+1)⁻),HR_r_Div_r,HR_Mult_1,HR_0_Mult
    in H16; auto. apply ->HR_abs_eq_0 in H16; auto. }
  New H14. New H14. apply H1 in H16; auto. apply H2 in H17; auto.
  apply HR_R_subset_HR in H14. New H. New H0. New H14.
  apply HR_Abs_Close in H18,H19,H20.
  apply (HR_Less_Pr_Plus _ _ ∣v∣) in H16; auto.
  apply (HR_Less_Pr_Plus _ _ ∣(∣r∣/(1+1))∣) in H17; auto.
  assert (∣(∣r∣/(1+1))∣ + ∣(∣r∣/(1+1))∣ = ∣r∣).
  { rewrite HR_Abs_Pr_Mult,HR_Double_Abs,<-HR_Mult_Dis_l.
    assert ((1+1)⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
    New H21. apply HR_Abs_Close in H22.
    replace (∣((1+1)⁻)∣) with (1·∣((1+1)⁻)∣).
    rewrite <-HR_Mult_Dis_r,<-(HR_Abs_Pos (1+1)),<-HR_Abs_Pr_Mult,
    (HR_Abs_Pos (1+1)),HR_r_Div_r,(HR_Abs_Pos 1),HR_Mult_1; auto.
    apply HR_0_less_1. rewrite HR_1_Mult; auto. }
  rewrite H21 in H17. assert (∣u∣ + ∣v∣ < ∣r∣).
  { apply (HR_Less_Transitivity _ (∣v∣ + ∣(∣r∣/(1+1))∣)); auto;
    try apply HR_Plus_Close; auto. rewrite (HR_Plus_Com ∣v∣); auto. }
  apply (HR_Less_Transitivity_Co _ (∣u∣ + ∣v∣)); auto.
  apply ->HR_Abs_Close; auto. apply HR_Plus_Close; auto. right. split; auto.
  apply HR_Abs_Triangle_inEqu; auto.
Qed.

Property HR_Infsimal_Neg_Close : ∀ u, u ∈ HR_Infsimal <-> -u ∈ HR_Infsimal.
Proof.
  assert (∀ u, u ∈ HR_Infsimal -> -u ∈ HR_Infsimal).
  { intros. apply AxiomII in H as [_[]]. New H. apply HR_Neg_Close in H1.
    apply AxiomII; split. eauto. split; auto. intros. rewrite HR_Abs_neg_eq_pos.
    apply H0; auto. }
  split; intros; auto. New H0. apply AxiomII in H1 as [_[H1 _]].
  apply <-HR_Neg_Close in H1. apply H in H0. rewrite HR_Double_Neg in H0; auto.
Qed.

Property HR_Infsimal_Minus_Close : ∀ u v, u ∈ HR_Infsimal -> v ∈ HR_Infsimal
  -> (u - v) ∈ HR_Infsimal.
Proof.
  intros. apply HR_Infsimal_Plus_Close; auto.
  apply ->HR_Infsimal_Neg_Close; auto.
Qed.

Property HR_Infsimal_Mult_Close : ∀ u v, u ∈ HR_Infsimal -> v ∈ HR_Infsimal
  -> (u · v) ∈ HR_Infsimal.
Proof.
  intros. apply AxiomII in H as [_[]], H0 as [_[]].
  assert (u·v ∈ HR). { apply HR_Mult_Close; auto. }
  apply AxiomII; split. eauto. split; auto. intros. destruct HR_0_less_1 as [_].
  New HR_Zero_in_HR. New HR_One_in_HR. New HR_One_in_HR_R. New H4.
  apply H1 in H9; auto. apply H2 in H10; auto. apply HR_R_subset_HR in H4.
  New H. New H0. New H4. rewrite (HR_Abs_Pos 1) in H9; auto.
  apply HR_Abs_Close in H11,H12,H13. destruct (classic (v = 0)).
  rewrite H14,HR_Mult_0,HR_Abs_0; auto. apply HR_0_less_abs; auto.
  assert (0 < ∣v∣). { apply HR_0_less_abs; auto. }
  apply (HR_Less_Pr_Mult_a _ _ ∣v∣) in H9; auto.
  rewrite <-HR_Abs_Pr_Mult,HR_1_Mult in H9; auto.
  apply (HR_Less_Transitivity _ ∣v∣); auto. apply ->HR_Abs_Close; auto.
  apply HR_0_less_1.
Qed.

(* 无穷小集构成有限集的理想: 无穷小与有限数的积为无穷小. *)
Property HR_Infsimal_Mult_Finity : ∀ u v, u ∈ HR_Infsimal -> v ∈ HR_Finity
  -> (u · v) ∈ HR_Infsimal.
Proof.
  intros. apply AxiomII in H as [_[]], H0 as [_[H0[x[]]]].
  assert (u·v ∈ HR). { apply HR_Mult_Close; auto. }
  apply AxiomII; split. eauto. split; auto. intros. New H2. New H5.
  apply HR_R_subset_HR in H7,H8. New HR_Zero_in_HR. New HR_One_in_HR.
  destruct (classic (v = 0)). rewrite H11,HR_Mult_0,HR_Abs_0; auto.
  apply HR_0_less_abs; auto. New H5. apply HR_R_Abs_Close in H12.
  New H. New H0. New H12. apply HR_R_subset_HR in H15.
  apply HR_Abs_Close in H13,H14. assert (0 < x).
  { apply (HR_Less_Transitivity_Co 0 ∣v∣); auto. left. split; auto.
    apply HR_0_less_abs; auto. } New H16. destruct H17 as [_].
  assert (∣r∣/x ∈ HR_R). { apply HR_R_Div_Close; auto. }
  assert (∣r∣/x <> 0).
  { intro. assert (x · (∣r∣/x) = x·0). rewrite H19; auto.
    rewrite HR_Mult_Com,HR_Mult_Ass,(HR_Mult_Com _ x),HR_r_Div_r,
    HR_Mult_1,HR_Mult_0 in H20; auto. apply ->HR_abs_eq_0 in H20; auto. }
  apply H1 in H19; auto. apply HR_R_subset_HR in H18.
  assert (0 < ∣(∣r∣/x)∣).
  { apply (HR_Less_Transitivity_Co 0 (∣u∣)); auto. apply ->HR_Abs_Close; auto.
    right. split; auto. apply HR_0_leq_abs; auto. }
  New H18. apply HR_Abs_Close in H21.
  apply (HR_Less_Pr_Mult_a _ _ ∣v∣) in H19; auto.
  rewrite <-(HR_Abs_Pos x) in H3; auto. New H7. apply HR_Abs_Close in H22.
  apply (HR_Leq_Pr_Mult_a _ _ (∣(∣r∣/x)∣)) in H3; auto.
  rewrite <-(HR_Abs_Pr_Mult x),(HR_Mult_Com x),HR_Mult_Ass,(HR_Mult_Com _ x),
  HR_r_Div_r,HR_Mult_1,HR_Double_Abs,HR_Mult_Com in H3; auto.
  rewrite <-HR_Abs_Pr_Mult in H19.
  apply (HR_Less_Transitivity_Co _ (∣(∣r∣/x)∣ · ∣v∣)); auto.
  apply ->HR_Abs_Close; auto. apply HR_Mult_Close; auto.
  apply HR_0_less_abs; auto.
Qed.


(* 无穷大集仅对乘法封闭 *)
Property HR_Infinity_Neg_Close : ∀ u, u ∈ HR_Infinity <-> -u ∈ HR_Infinity.
Proof.
  assert (∀ u, u ∈ HR_Infinity -> -u ∈ HR_Infinity).
  { intros. apply AxiomII in H as [_[]]. New H. apply HR_Neg_Close in H1.
    apply AxiomII. rewrite HR_Abs_neg_eq_pos. split; eauto. }
  split; intros; auto. New H0. apply AxiomII in H1 as [_[H1 _]].
  apply <-HR_Neg_Close in H1. apply H in H0. rewrite HR_Double_Neg in H0; auto.
Qed.

Property HR_Infinity_Mult_Close : ∀ u v, u ∈ HR_Infinity -> v ∈ HR_Infinity
  -> (u · v) ∈ HR_Infinity.
Proof.
  intros. apply AxiomII in H as [_[]], H0 as [_[]].
  assert (u·v ∈ HR). { apply HR_Mult_Close; auto. }
  apply AxiomII; split. eauto. split; auto. intros. New HR_0_less_1.
  New HR_Zero_in_HR. New HR_One_in_HR. New HR_One_in_HR_R. New H4.
  apply H1 in H8; auto. apply H2 in H9; auto. apply HR_R_subset_HR in H4.
  destruct (classic (v = 0)). rewrite H10,HR_Mult_0,HR_Abs_0; auto.
  rewrite H10,HR_Abs_0 in H9; auto.
  assert (0 < ∣v∣). { apply HR_0_less_abs; auto. }
  New H. New H0. apply HR_Abs_Close in H12,H13.
  apply (HR_Less_Pr_Mult_a _ _ ∣v∣) in H8; auto.
  rewrite HR_1_Mult,<-HR_Abs_Pr_Mult in H8; auto.  
  apply (HR_Less_Transitivity _ ∣v∣); auto. apply ->HR_Abs_Close; auto.
Qed.


(* 无穷小的逆为无穷大, 反之亦然 *)
Property HR_inv_of_Infsimal_is_Infinity :
  ∀ u, (u ∈ HR_Infsimal /\ u <> 0) <-> u⁻ ∈ HR_Infinity.
Proof.
  split; intros.
  - destruct H. apply AxiomII in H as [_[]].
    assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
    apply AxiomII; split. eauto. split; auto. intros.
    assert (u⁻ <> 0). { apply HR_Inv_isnot_0. }
    destruct (classic (r = 0)). rewrite H5. apply HR_0_less_abs; auto.
    assert (r⁻ ∈ HR_R). { apply ->HR_R_Inv_Close; auto. }
    New H3. New H6. apply HR_R_subset_HR in H7,H8. apply H1 in H6.
    New H. New H2. New H7. New H8. New H9. apply HR_Abs_Close in H10,H11,H12,H13.
    rewrite HR_Abs_Pr_Inv in H6. apply HR_inv_less_inv in H6; auto.
    assert (∣r∣ <> 0). { intro. apply ->HR_abs_eq_0 in H14; auto. }
    apply HR_Double_Inv in H14; auto. rewrite H14,<-HR_Abs_Pr_Inv in H6; auto.
    apply (HR_Less_Transitivity_Co r (∣r∣)); auto. right. split; auto.
    apply HR_r_leq_abs_r; auto. apply ->HR_Inv_Close; split; auto. intro.
    apply ->HR_abs_eq_0 in H15; auto. right. split. apply HR_0_less_abs; auto.
    apply ->HR_0_less_inv; auto. apply HR_0_less_abs; auto. apply HR_Inv_isnot_0.
  - apply AxiomII in H as [_[]]. New H. apply HR_Inv_Close in H1 as [].
    split; auto. apply AxiomII; split. eauto. split; auto. intros.
    assert (r⁻ ∈ HR_R). { apply ->HR_R_Inv_Close; auto. }
    New H5. apply HR_R_Abs_Close in H6. apply HR_R_subset_HR in H3,H5.
    New H1. New H3. New H5. apply HR_Abs_Close in H7,H8,H9.
    apply H0 in H6; auto. rewrite HR_Abs_Pr_Inv,HR_Abs_Pr_Inv in H6.
    apply HR_inv_less_inv in H6; auto. right. split; apply HR_0_less_abs; auto.
Qed.

Property HR_inv_of_Infinity_is_Infsimal :
  ∀ u, u ∈ HR_Infinity <-> u⁻ ∈ HR_Infsimal.
Proof.
  split; intros. apply HR_inv_of_Infsimal_is_Infinity.
  New H. apply AxiomII in H0 as [_[]]. assert (u <> 0).
  { intro. New HR_Zero_in_HR_R. apply H1 in H3. rewrite H2,HR_Abs_0 in H3.
    destruct H3; auto. } apply HR_Double_Inv in H2; auto. rewrite H2; auto.
  New H. apply AxiomII in H0 as [_[]]. apply HR_Inv_Close in H0 as [].
  New H2. apply HR_Double_Inv in H3; auto. rewrite <-H3.
  apply HR_inv_of_Infsimal_is_Infinity. split; auto. apply HR_Inv_isnot_0.
Qed.



(* 有限超实数基本定理: 每个有限大数都可由唯一的标准实数和唯一的无穷小数唯一确定. *)
Theorem HR_Fundamental_Theorem_a : ∀ r, r ∈ HR_Finity
  -> ∃ u v, u ∈ HR_R /\ v ∈ HR_Infsimal /\ r = u + v.
Proof.
  intros. apply AxiomII in H as [_[H[x[]]]].
  set (A := \{ λ u, u ∈ HR_R /\ u ≤ r \}).
  New HR_Zero_in_HR. New H. apply HR_Abs_Close in H3.
  New H0. apply HR_R_subset_HR in H4.
  assert (-x ∈ A).
  { apply HR_neg_leq_neg in H1; auto. destruct (HR_Leq_Trichotomy 0 r); auto.
    New H5. apply HR_Abs_nonNeg in H6; auto. rewrite H6 in H1. New H5.
    apply HR_neg_leq_0 in H7; auto. apply AxiomII. apply HR_R_Neg_Close in H0.
    repeat split; eauto. apply (HR_Leq_Transitivity _ 0); auto.
    apply HR_R_subset_HR; auto. apply (HR_Leq_Transitivity _ (-r)); auto.
    apply HR_R_subset_HR; auto. apply ->HR_Neg_Close; auto.
    apply HR_Abs_nonPos in H5; auto. rewrite H5,HR_Double_Neg in H1; auto.
    apply AxiomII. apply HR_R_Neg_Close in H0. split; eauto. }
  assert (HR_R_Up x A).
  { repeat split; auto. red; intros. apply AxiomII in H6; tauto.
    intros. apply AxiomII in H6 as [_[]]. apply (HR_Leq_Transitivity _ r); auto.
    apply HR_R_subset_HR; auto. apply (HR_Leq_Transitivity _ (∣r∣)); auto.
    apply HR_r_leq_abs_r; auto. }
  apply HR_R_Sup_Exists in H6 as [s[[H6[]]]]; [ |apply NEexE; eauto].
  New H6. apply HR_R_subset_HR in H10.
  New H10. apply (HR_Minus_Close r) in H11; auto.
  New H10. apply (HR_Minus_Close _ r) in H12; auto.
  assert ((s - r) ∈ HR_Infsimal).
  { New H6. apply AxiomII; split; eauto. split; auto. intros.
    New H14. apply HR_R_subset_HR in H16. New H11. New H12. New H16.
    apply HR_Abs_Close in H17,H18,H19; auto.
    New H14. apply HR_R_Abs_Close in H20. apply NNPP; intro.
    assert (∣r0∣ ≤ ∣(s - r)∣).
    { destruct (HR_Less_Trichotomy ∣(s - r)∣ ∣r0∣) as [H22|[]]; auto.
      contradiction. destruct H22; auto. rewrite H22.
      apply HR_Leq_Reflexivity; auto. } clear H21.
    assert (0 < ∣r0∣). { apply HR_0_less_abs; auto. }
    destruct (HR_Less_Trichotomy s r) as [H23|[]]; auto.
    - apply HR_Less_Pr_Plus_Co in H23; auto. rewrite <-HR_Neg_u_minus_v,
      HR_Abs_neg_eq_pos,(HR_Abs_Pos (r-s)) in H22; auto.
      apply (HR_Leq_Pr_Plus _ _ s) in H22; auto.
      rewrite HR_Plus_Ass,(HR_Plus_Com (-s)),HR_r_Minus_r,HR_Plus_0 in H22; auto.
      assert (∣r0∣ + s ∈ HR_R). { apply HR_R_Plus_Close; auto. }
      assert (∣r0∣ + s ∈ A). { apply AxiomII. split; eauto. }
      apply H8 in H25. apply (HR_Less_Pr_Plus _ _ s) in H21; auto.
      rewrite HR_0_Plus in H21; auto. destruct H21.
      apply H26,HR_Leq_Asymmetry; auto. apply HR_Plus_Close; auto.
    - apply HR_Less_Pr_Plus_Co in H23; auto.
      rewrite (HR_Abs_Pos (s-r)) in H22; auto.
      apply (HR_Leq_Pr_Plus _ _ r) in H22; auto.
      rewrite HR_Plus_Ass,(HR_Plus_Com (-r)),HR_r_Minus_r,HR_Plus_0 in H22; auto.
      New H19. apply HR_Neg_Close in H24.
      apply (HR_Leq_Pr_Plus _ _ (-∣r0∣)) in H22; auto.
      rewrite (HR_Plus_Com ∣r0∣),HR_Plus_Ass,HR_r_Minus_r,HR_Plus_0 in H22; auto.
      apply HR_neg_less_0,(HR_Less_Pr_Plus _ _ s) in H21; auto.
      rewrite HR_Plus_Com,HR_0_Plus in H21; auto.
      apply H9 in H21 as [x0[]]; [ |apply HR_R_Minus_Close; auto].
      apply AxiomII in H21 as [_[]]. apply HR_R_subset_HR in H21.
      apply (HR_Leq_Transitivity x0) in H22; auto; [ |apply HR_Minus_Close; auto].
      destruct H25. apply H27,HR_Leq_Asymmetry; auto. apply HR_Minus_Close; auto.
      apply HR_Plus_Close; auto.
    - rewrite H23,HR_r_Minus_r,HR_Abs_0 in H22; auto. destruct H21.
      apply H24,HR_Leq_Asymmetry; auto. }
  apply HR_Infsimal_Neg_Close in H13. rewrite HR_Neg_u_minus_v in H13; auto.
  exists s,(r - s). repeat split; auto. rewrite <-HR_Plus_Ass,(HR_Plus_Com s),
  HR_Plus_Ass,HR_r_Minus_r,HR_Plus_0; auto.
Qed.

(* 唯一性 *)
Theorem HR_Fundamental_Theorem_b : ∀ u1 u2 v1 v2,
  u1 ∈ HR_R -> u2 ∈ HR_R -> v1 ∈ HR_Infsimal -> v2 ∈ HR_Infsimal
  -> u1 + v1 = u2 + v2 -> u1 = u2 /\ v1 = v2.
Proof.
  intros. New H. New H0. apply HR_R_subset_HR in H4,H5.
  New H1. New H2. apply HR_Infsimal_subset_HR in H6,H7.
  assert (u1 - u2 = v2 - v1).
  { assert (u1 + v1 - u2 = u2 + v2 - u2). { rewrite H3; auto. }
    rewrite (HR_Plus_Com u2),(HR_Plus_Ass v2),HR_r_Minus_r,HR_Plus_0 in H8; auto.
    rewrite <-H8,HR_Plus_Ass,(HR_Plus_Com (-u2)),HR_Plus_Ass,<-(HR_Plus_Ass v1),
    HR_r_Minus_r,<-HR_Plus_Ass,HR_Plus_0; auto. }
  assert ((u1 - u2) ∈ HR_Infsimal ∩ HR_R).
  { apply MKT4'; split. rewrite H8. apply HR_Infsimal_Minus_Close; auto.
    apply HR_R_Minus_Close; auto. }
  rewrite HR_Infsimal_inter_R in H9. New HR_Zero_in_HR. apply MKT41 in H9; eauto.
  New H9. rewrite H8 in H11. assert (u1 - u2 + u2 = u2 /\ v2 - v1 + v1 = v1) as [].
  { rewrite H9,H11,HR_0_Plus,HR_0_Plus; auto. }
  rewrite HR_Plus_Ass in H12,H13. rewrite (HR_Plus_Com (-u2)) in H12.
  rewrite (HR_Plus_Com (-v1)) in H13.
  rewrite HR_r_Minus_r,HR_Plus_0 in H12,H13; auto.
Qed.



