(** properties_of_standard_reals *)

(* 验证超实数的序域性质 *)

Require Import axiomatic_reals.seq_operations.
Require Export hr_NPUF.construction_of_hr. Export instantiate_hr_with_NPUF.
Require Import mk.equivalence_relation.

(* 加法性质 *)

(* 交换律 *)
Property HR_Plus_Com : ∀ u v, (u + v = v + u)%hr.
Proof.
  intros. destruct (classic ([u,v] ∈ dom(HR_Plus_Func))).
  - rewrite HR_Plus_Func_dom in H. apply AxiomII' in H as [H[]].
    apply HR_Elements in H0 as [f[]], H1 as [g[]]. rewrite H2,H3.
    rewrite HR_Plus_Instantiate,HR_Plus_Instantiate; auto.
    replace (f + g)%seq with (g + f)%seq; auto. New H0. New H1.
    apply (Seq_Plus_Close f g) in H4; apply (Seq_Plus_Close g f) in H5; auto.
    apply AxiomII in H4 as [_[H4[]]], H5 as [_[H5[]]]. apply MKT71; auto.
    intros. destruct (classic (x ∈ N)).
    rewrite Seq_Plus_Property,Seq_Plus_Property; auto.
    apply AxiomII in H0 as [_[H0[]]], H1 as [_[H1[]]]. apply Plus_P4;
    [apply H14|apply H12]; apply (@ Property_ran x),Property_Value; auto;
    [rewrite H13|rewrite H11]; auto. New H10. rewrite <-H6 in H10.
    rewrite <-H8 in H11. apply MKT69a in H10,H11. rewrite H10,H11; auto.
  - New H. rewrite HR_Plus_Func_dom in H0.
    assert ([v,u] ∉ dom(HR_Plus_Func)).
    { intro. rewrite HR_Plus_Func_dom in H1. apply AxiomII' in H1 as [H1[]].
      apply H0,AxiomII'; split; auto. apply MKT49b in H1 as [].
      apply MKT49a; auto. }
    apply MKT69a in H,H1. rewrite H,H1; auto.
Qed.

(* 结合律 *)
Property HR_Plus_Ass : ∀ u v w, ((u + v) + w = u + (v + w))%hr.
Proof.
  intros. destruct (classic ([(u + v),w] ∈ dom(HR_Plus_Func))).
  - rewrite HR_Plus_Func_dom in H. apply AxiomII' in H as [H[]].
    assert ([u,v] ∈ dom(HR_Plus_Func)).
    { apply NNPP; intro. apply MKT69a in H2. rewrite H2 in H0.
      apply MKT39; eauto. } rewrite HR_Plus_Func_dom in H2.
    apply AxiomII' in H2 as [H2[]]. apply HR_Elements in H1 as [f[]],
    H3 as [g[]], H4 as [h[]]. rewrite H5,H6,H7.
    repeat rewrite HR_Plus_Instantiate; try apply Seq_Plus_Close; auto.
    replace (g + h + f)%seq with (g + (h + f))%seq; auto. New H3. New H4.
    apply (Seq_Plus_Close g h) in H8; apply (Seq_Plus_Close h f) in H9; auto.
    apply (Seq_Plus_Close _ f) in H8; apply (Seq_Plus_Close g) in H9; auto.
    apply AxiomII in H8 as [_[H8[]]], H9 as [_[H9[]]]. apply MKT71; auto.
    intros. destruct (classic (x ∈ N)). repeat rewrite Seq_Plus_Property;
    try apply Seq_Plus_Close; auto. apply AxiomII in H1 as [_[H1[]]],
    H3 as [_[H3[]]], H4 as [_[H4[]]].
    apply Plus_P3; [apply H18|apply H20|apply H16]; apply (@ Property_ran x);
    apply Property_Value; auto; [rewrite H17|rewrite H19|rewrite H15]; auto.
    New H14. rewrite <-H10 in H14. rewrite <-H12 in H15.
    apply MKT69a in H14,H15; auto. rewrite H14,H15; auto.
  - assert ([u,(v + w)] ∉ dom(HR_Plus_Func)).
    { intro. rewrite HR_Plus_Func_dom in *. apply AxiomII' in H0 as [_[]].
      assert ([v,w] ∈ dom(HR_Plus_Func)).
      { apply NNPP; intro. apply MKT69a in H2. rewrite H2 in H1.
        apply MKT39; eauto. } rewrite HR_Plus_Func_dom in H2.
      apply AxiomII' in H2 as [_[]]. New H0.
      apply (HR_Plus_Close u v) in H4; auto. elim H.
      apply AxiomII'; split; auto. apply MKT49a; eauto. }
    apply MKT69a in H,H0. rewrite H,H0; auto.
Qed.

(* 右加零 *)
Property HR_Plus_0 : ∀ u, u ∈ HR -> (u + 0 = u)%hr.
Proof.
  intros. apply HR_Elements in H as [f[]]. unfold "0".
  rewrite H0,HR_Plus_Instantiate; try apply ConstSeq_is_Seq; auto with real.
  replace (f + ConstSeq 0%r)%seq with f; auto. New zero_in_R.
  apply ConstSeq_is_Seq in H1. New H1. apply (Seq_Plus_Close f) in H2; auto.
  New H. apply AxiomII in H2 as [_[H2[]]],H3 as [_[H3[]]]. apply MKT71; auto.
  intros. destruct (classic (x ∈ N)). rewrite Seq_Plus_Property; auto.
  rewrite ConstSeq_Value; auto with real. rewrite Plus_P1; auto.
  apply H7,(@ Property_ran x),Property_Value; auto. rewrite H6; auto.
  New H8. rewrite <-H4 in H8. rewrite <-H6 in H9. apply MKT69a in H8,H9.
  rewrite H8,H9; auto.
Qed.

(* 左加零 *)
Property HR_0_Plus : ∀ u, u ∈ HR -> (0 + u = u)%hr.
Proof. intros. rewrite HR_Plus_Com,HR_Plus_0; auto. Qed.


(* 负元及减法性质 *)
Property HR_Double_Neg : ∀ r, r ∈ HR -> -(-r) = r.
Proof.
  intros. New H. apply HR_Elements in H0 as [f[]].
  New H0. apply Seq_Neg_Close in H2.
  rewrite H1,HR_Neg_Instantiate,HR_Neg_Instantiate; auto.
  assert ((-(-f))%seq = f).
  { New H2. apply Seq_Neg_Close in H3. New H0.
    apply AxiomII in H3 as [H3[H5[]]], H4 as [H4[H8[]]].
    apply MKT71; auto. intros. destruct (classic (x ∈ N)).
    rewrite Seq_Neg_Property,Seq_Neg_Property; auto.
    rewrite <-H9 in H11. apply Property_Value,Property_ran in H11; auto.
    rewrite PlusMult_Co3,(PlusMult_Co3 f[x]),Mult_P3,PlusMult_Co5,
    Mult_P1,Mult_P4,Mult_P1; auto with real. New H11. rewrite <-H6 in H11.
    rewrite <-H9 in H12. apply MKT69a in H11,H12. rewrite H11,H12; auto. }
  rewrite H3; auto.
Qed.

Property HR_Neg_0 : -0 = 0.
Proof.
  unfold "0". rewrite HR_Neg_Instantiate,ConstSeq_Neg;
  try apply ConstSeq_is_Seq; auto with real. replace (-0)%r with 0%r; auto.
  New zero_in_R. apply Plus_Co2 in H as [x[[]]].
  assert (0 + 0 = 0 /\ 0 - 0 = 0)%r as [].
  { split; try apply Plus_P1; auto with real. }
  assert (x = 0 /\ x = -0)%r as [].
  { split; apply H1; split; auto with real. }
  rewrite <-H5,<-H4; auto.
Qed.

(* 减零 *)
Property HR_Minus_0 : ∀ r, r ∈ HR -> (r - 0 = r)%hr.
Proof. intros. rewrite HR_Neg_0,HR_Plus_0; auto. Qed.

(* 零减 *)
Property HR_0_Minus : ∀ r, r ∈ HR -> (0 - r = -r)%hr.
Proof. intros. rewrite HR_0_Plus; try apply ->HR_Neg_Close; auto. Qed.

(* 减自己 *)
Property HR_r_Minus_r : ∀ r, r ∈ HR -> (r - r = 0)%hr.
Proof.
  intros. apply HR_Elements in H as [f[]]. rewrite H0,HR_Neg_Instantiate,
  HR_Plus_Instantiate; try apply Seq_Neg_Close; auto.
  replace (f + (-f))%seq with (ConstSeq 0%r); auto.
  New H. apply Seq_Neg_Close in H1.
  New H1. apply (Seq_Plus_Close f) in H2; auto.
  New zero_in_R. apply ConstSeq_is_Seq in H3.
  apply AxiomII in H2 as [_[H2[]]], H3 as [_[H3[]]].
  apply MKT71; auto. intros. destruct (classic (x ∈ N)).
  rewrite ConstSeq_Value,Seq_Plus_Property,Seq_Neg_Property; auto with real.
  apply AxiomII in H as [_[H[]]]. rewrite Minus_P1; auto.
  apply H10,(@ Property_ran x),Property_Value; auto. rewrite H9; auto.
  New H8. rewrite <-H4 in H8; rewrite <-H6 in H9. apply MKT69a in H8,H9.
  rewrite H8,H9; auto.
Qed.

Corollary HR_Plus_Cancel : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> u + w = v + w -> u = v.
Proof.
  intros. assert (u + w - w = v + w - w). { rewrite H2; auto. }
  rewrite HR_Plus_Ass,HR_Plus_Ass,HR_r_Minus_r,HR_Plus_0,HR_Plus_0 in H3; auto.
Qed.

Corollary HR_Neg_u_minus_v : ∀ u v, u ∈ HR -> v ∈ HR -> -(u - v) = v - u.
Proof.
  intros. assert (-(u - v) + (u - v) = 0).
  { rewrite HR_Plus_Com,HR_r_Minus_r; auto. apply HR_Minus_Close; auto. }
  assert ((v - u) + (u - v) = 0).
  { rewrite HR_Plus_Ass,<-(HR_Plus_Ass (-u)),(HR_Plus_Com (-u)),HR_r_Minus_r,
    <-HR_Plus_Com,HR_0_Plus,HR_Plus_Com,HR_r_Minus_r; auto.
    apply ->HR_Neg_Close; auto. }
  apply (HR_Plus_Cancel _ _ (u - v)); try apply ->HR_Neg_Close;
  try apply HR_Minus_Close; auto. rewrite H1,H2; auto.
Qed.

(* 乘法性质 *)

(* 交换律 *)
Property HR_Mult_Com : ∀ u v, (u · v = v · u)%hr.
Proof.
  intros. destruct (classic ([u,v] ∈ dom(HR_Mult_Func))).
  - rewrite HR_Mult_Func_dom in H. apply AxiomII' in H as [H[]].
    apply HR_Elements in H0 as [f[]], H1 as [g[]]. rewrite H2,H3.
    rewrite HR_Mult_Instantiate,HR_Mult_Instantiate; auto.
    replace (f · g)%seq with (g · f)%seq; auto. New H0. New H1.
    apply (Seq_Mult_Close f g) in H4; apply (Seq_Mult_Close g f) in H5; auto.
    apply AxiomII in H4 as [_[H4[]]], H5 as [_[H5[]]]. apply MKT71; auto.
    intros. destruct (classic (x ∈ N)).
    rewrite Seq_Mult_Property,Seq_Mult_Property; auto.
    apply AxiomII in H0 as [_[H0[]]], H1 as [_[H1[]]]. apply Mult_P4;
    [apply H14|apply H12]; apply (@ Property_ran x),Property_Value; auto;
    [rewrite H13|rewrite H11]; auto. New H10. rewrite <-H6 in H10.
    rewrite <-H8 in H11. apply MKT69a in H10,H11. rewrite H10,H11; auto.
  - New H. rewrite HR_Mult_Func_dom in H0.
    assert ([v,u] ∉ dom(HR_Mult_Func)).
    { intro. rewrite HR_Mult_Func_dom in H1. apply AxiomII' in H1 as [H1[]].
      apply H0,AxiomII'; split; auto. apply MKT49b in H1 as [].
      apply MKT49a; auto. }
    apply MKT69a in H,H1. rewrite H,H1; auto.
Qed.

(* 结合律 *)
Property HR_Mult_Ass : ∀ u v w, ((u · v) · w = u · (v · w))%hr.
Proof.
  intros. destruct (classic ([(u · v),w] ∈ dom(HR_Mult_Func))).
  - rewrite HR_Mult_Func_dom in H. apply AxiomII' in H as [H[]].
    assert ([u,v] ∈ dom(HR_Mult_Func)).
    { apply NNPP; intro. apply MKT69a in H2. rewrite H2 in H0.
      apply MKT39; eauto. } rewrite HR_Mult_Func_dom in H2.
    apply AxiomII' in H2 as [H2[]]. apply HR_Elements in H1 as [f[]],
    H3 as [g[]], H4 as [h[]]. rewrite H5,H6,H7.
    repeat rewrite HR_Mult_Instantiate; try apply Seq_Mult_Close; auto.
    replace (g · h · f)%seq with (g · (h · f))%seq; auto. New H3. New H4.
    apply (Seq_Mult_Close g h) in H8; apply (Seq_Mult_Close h f) in H9; auto.
    apply (Seq_Mult_Close _ f) in H8; apply (Seq_Mult_Close g) in H9; auto.
    apply AxiomII in H8 as [_[H8[]]], H9 as [_[H9[]]]. apply MKT71; auto.
    intros. destruct (classic (x ∈ N)). repeat rewrite Seq_Mult_Property;
    try apply Seq_Mult_Close; auto. apply AxiomII in H1 as [_[H1[]]],
    H3 as [_[H3[]]], H4 as [_[H4[]]].
    apply Mult_P3; [apply H18|apply H20|apply H16]; apply (@ Property_ran x);
    apply Property_Value; auto; [rewrite H17|rewrite H19|rewrite H15]; auto.
    New H14. rewrite <-H10 in H14. rewrite <-H12 in H15.
    apply MKT69a in H14,H15; auto. rewrite H14,H15; auto.
  - assert ([u,(v · w)] ∉ dom(HR_Mult_Func)).
    { intro. rewrite HR_Mult_Func_dom in *. apply AxiomII' in H0 as [_[]].
      assert ([v,w] ∈ dom(HR_Mult_Func)).
      { apply NNPP; intro. apply MKT69a in H2. rewrite H2 in H1.
        apply MKT39; eauto. } rewrite HR_Mult_Func_dom in H2.
      apply AxiomII' in H2 as [_[]]. New H0.
      apply (HR_Mult_Close u v) in H4; auto. elim H.
      apply AxiomII'; split; auto. apply MKT49a; eauto. }
    apply MKT69a in H,H0. rewrite H,H0; auto.
Qed.

(* 右分配律 *)
Property HR_Mult_Dis_r : ∀ u v w, ((u + v) · w = u·w + v·w)%hr.
Proof.
  intros. destruct (classic ([(u + v),w] ∈ dom(HR_Mult_Func))).
  - rewrite HR_Mult_Func_dom in H. apply AxiomII' in H as [_[]].
    assert ([u,v] ∈ dom(HR_Plus_Func)).
    { apply NNPP; intro. apply MKT69a in H1. rewrite H1 in H.
      apply MKT39; eauto. }
    rewrite HR_Plus_Func_dom in H1. apply AxiomII' in H1 as [_[]].
    apply HR_Elements in H0 as [f[]], H1 as [g[]], H2 as [h[]].
    rewrite H3,H4,H5. rewrite HR_Plus_Instantiate; auto.
    repeat rewrite HR_Mult_Instantiate; try apply Seq_Plus_Close; auto.
    rewrite HR_Plus_Instantiate; try apply Seq_Mult_Close; auto.
    assert (((g + h) · f)%seq ∈ Rᴺ /\ (g·f + h·f)%seq ∈ Rᴺ) as [].
    { split. apply Seq_Mult_Close; auto. apply Seq_Plus_Close; auto.
      apply Seq_Plus_Close; apply Seq_Mult_Close; auto. }
    apply equClassT1; auto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    assert (\{ λ u0, u0 ∈ N
      /\ ((g + h) · f)%seq[u0] = (g·f + h·f)%seq[u0] \} = N).
    { apply AxiomI; split; intros. apply AxiomII in H8; tauto.
      apply AxiomII; repeat split; eauto. rewrite Seq_Mult_Property,
      Seq_Plus_Property,Seq_Plus_Property,Seq_Mult_Property,Seq_Mult_Property;
      try apply Seq_Plus_Close; try apply Seq_Mult_Close; auto.
      apply AxiomII in H0 as [_[H0[]]], H1 as [_[H1[]]], H2 as [_[H2[]]].
      apply Mult_P5; [apply H12|apply H14|apply H10]; apply (@ Property_ran z),
      Property_Value; auto; [rewrite H11|rewrite H13|rewrite H9]; auto. }
    rewrite H8. destruct F0_is_NPUF_over_N as [[[_[_[]]]]]; auto.
  - assert ([u·w,v·w] ∉ dom(HR_Plus_Func)).
    { intro. rewrite HR_Plus_Func_dom in H0. apply AxiomII' in H0 as [_[]].
      assert ([u,w] ∈ dom(HR_Mult_Func) /\ [v,w] ∈ dom(HR_Mult_Func)) as [].
      { split; apply NNPP; intro; apply MKT69a in H2;
        [rewrite H2 in H0|rewrite H2 in H1]; apply MKT39; eauto. }
      rewrite HR_Mult_Func_dom in *.
      apply AxiomII' in H2 as [_[]], H3 as [_[]].
      assert ((u + v) ∈ HR) by (apply HR_Plus_Close; auto).
      elim H. apply AxiomII'; split; auto. apply MKT49a; eauto. }
    apply MKT69a in H,H0. rewrite H,H0; auto.
Qed.

(* 左分配律 *)
Property HR_Mult_Dis_l : ∀ u v w, (w · (u + v) = w·u + w·v)%hr.
Proof. intros. repeat rewrite (HR_Mult_Com w). apply HR_Mult_Dis_r. Qed.

(* 右乘零 *)
Property HR_Mult_0 : ∀ u, u ∈ HR -> (u · 0 = 0)%hr.
Proof.
  intros. apply HR_Elements in H as [f[]]. unfold "0".
  rewrite H0,HR_Mult_Instantiate; try apply ConstSeq_is_Seq; auto with real.
  replace (f · ConstSeq 0%r)%seq with (ConstSeq 0%r); auto. New zero_in_R.
  apply ConstSeq_is_Seq in H1. New H1. apply (Seq_Mult_Close f) in H2; auto.
  New H1. apply AxiomII in H2 as [_[H2[]]],H3 as [_[H3[]]]. apply MKT71; auto.
  intros. destruct (classic (x ∈ N)). rewrite Seq_Mult_Property; auto.
  rewrite ConstSeq_Value; auto with real. rewrite PlusMult_Co1; auto.
  apply AxiomII in H as [_[H[]]]. apply H10,(@ Property_ran x),Property_Value;
  auto. rewrite H9; auto. New H8. rewrite <-H4 in H8. rewrite <-H6 in H9.
  apply MKT69a in H8,H9. rewrite H8,H9; auto.
Qed.

(* 左乘零 *)
Property HR_0_Mult : ∀ u, u ∈ HR -> (0 · u = 0)%hr.
Proof. intros. rewrite HR_Mult_Com,HR_Mult_0; auto. Qed.

(* 右乘一 *)
Property HR_Mult_1 : ∀ u, u ∈ HR -> (u · 1 = u)%hr.
Proof.
  intros. apply HR_Elements in H as [f[]]. unfold "1".
  rewrite H0,HR_Mult_Instantiate; try apply ConstSeq_is_Seq; auto with real.
  replace (f · ConstSeq 1%r)%seq with f; auto. New one_in_R.
  apply MKT4' in H1 as [H1 _]. apply ConstSeq_is_Seq in H1. New H1.
  apply (Seq_Mult_Close f) in H2; auto. New H.
  apply AxiomII in H2 as [_[H2[]]],H3 as [_[H3[]]]. apply MKT71; auto.
  intros. destruct (classic (x ∈ N)). rewrite Seq_Mult_Property; auto.
  rewrite ConstSeq_Value; auto with real. rewrite Mult_P1; auto.
  apply H7,(@ Property_ran x),Property_Value; auto. rewrite H6; auto.
  New H8. rewrite <-H4 in H8. rewrite <-H6 in H9.
  apply MKT69a in H8,H9. rewrite H8,H9; auto.
Qed.

(* 左乘一 *)
Property HR_1_Mult : ∀ u, u ∈ HR -> (1 · u = u)%hr.
Proof. intros. rewrite HR_Mult_Com,HR_Mult_1; auto. Qed.

(* 负一乘负一 *)
Property HR_neg1_Mult_neg1 : (-(1) · -(1) = 1)%hr.
Proof.
  unfold "1". rewrite HR_Neg_Instantiate; try apply ConstSeq_is_Seq;
  auto with real. New one_in_R_Co. New H. apply ConstSeq_is_Seq in H0.
  New H0. apply Seq_Neg_Close in H1. New H. apply Plus_neg1a in H2. New H2.
  apply ConstSeq_is_Seq in H3. rewrite HR_Mult_Instantiate,ConstSeq_Neg; auto.
  New H3. apply (Seq_Mult_Close (ConstSeq (-(1))%r)) in H4; auto.
  apply equClassT1; auto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
  assert (\{ λ u, u ∈ N
    /\ (ConstSeq (-(1))%r · ConstSeq (-(1))%r)%seq[u] = (ConstSeq 1%r)[u] \} = N).
  { apply AxiomI; split; intros. apply AxiomII in H5; tauto.
    apply AxiomII; repeat split; eauto. rewrite ConstSeq_Value; auto.
    rewrite Seq_Mult_Property,ConstSeq_Value; auto.
    rewrite PlusMult_Co5,Mult_P1; auto. }
  rewrite H5. destruct F0_is_NPUF_over_N as [[[_[_[]]]]]; auto.
Qed.

Property HR_Neg_and_Mult : ∀ r, r ∈ HR -> -r = (-(1))·r.
Proof.
  intros. apply HR_Elements in H as [f[]]. rewrite H0. unfold "1".
  rewrite HR_Neg_Instantiate,HR_Neg_Instantiate,HR_Mult_Instantiate;
  try apply Seq_Neg_Close; try apply ConstSeq_is_Seq; auto with real.
  rewrite ConstSeq_Neg; auto with real. New H. apply Seq_Neg_Close in H1.
  assert (((ConstSeq (-(1))%r) · f)%seq ∈ Rᴺ).
  { apply Seq_Mult_Close; try apply ConstSeq_is_Seq; auto with real. }
  apply equClassT1; auto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
  assert (\{ λ u, u ∈ N /\ (-f)%seq[u] = ((ConstSeq (-(1))%r) · f)%seq[u] \} = N).
  { apply AxiomI; split; intros. apply AxiomII in H3; tauto.
    apply AxiomII; repeat split; eauto.
    rewrite Seq_Neg_Property,Seq_Mult_Property,ConstSeq_Value,PlusMult_Co3;
    try apply ConstSeq_is_Seq; auto with real. apply AxiomII in H as [_[H[]]].
    apply H5,(@ Property_ran z),Property_Value; auto. rewrite H4; auto. }
  rewrite H3. destruct F0_is_NPUF_over_N as [[[_[_[]]]]]; auto.
Qed.

Property HR_neg_Mult_neg : ∀ u v, ((-u)·(-v) = u·v)%hr.
Proof.
  intros. destruct (classic (u ∈ HR /\ v ∈ HR)).
  - destruct H. rewrite HR_Neg_and_Mult,(HR_Neg_and_Mult v),HR_Mult_Ass,
    <-(HR_Mult_Ass u),(HR_Mult_Com u),<-(HR_Mult_Ass (-(1))),
    <-(HR_Mult_Ass (-(1))),HR_neg1_Mult_neg1,HR_1_Mult; auto.
  - apply notandor in H.
    assert (u · v = μ).
    { apply MKT69a. intro. rewrite HR_Mult_Func_dom in H0.
      apply AxiomII' in H0 as [_[]]. destruct H; auto. }
    rewrite H0. apply MKT69a. intro. rewrite HR_Mult_Func_dom in H1.
    apply AxiomII' in H1 as [_[]]. apply HR_Neg_Close in H1,H2. destruct H; auto.
Qed.

(* 逆元及除法性质 *)
Property HR_Inv_isnot_0 : ∀ r, r⁻ <> 0.
Proof.
  intros. destruct (classic (r ∈ HR)).
  - intro. New H. apply HR_Elements in H1 as [f[]].
    assert (r <> 0).
    { intro. rewrite H3,HR_Inv_0_is_universe in H0.
      elim MKT39. rewrite H0. apply Hyperreal_is_set. }
    New H3. rewrite H2 in H4. apply HR_Inv_Instantiate in H4; auto.
    rewrite H2,H4 in H0. New H1. apply Seq_Inv_Close in H5.
    apply equClassT1,AxiomII' in H0 as [H0[H6[]]]. elim H3. rewrite H2.
    apply equClassT1; auto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    assert (\{ λ u, u ∈ N /\ (/f)[u] = (ConstSeq 0%r)[u] \}
      ⊂ \{ λ u, u ∈ N /\ f[u] = (ConstSeq 0%r)[u] \}).
    { red; intros. apply AxiomII in H9 as [H9[]].
      apply AxiomII; repeat split; auto. apply AxiomII in H1 as [H1[H12[]]].
      New H10. rewrite <-H13 in H15. apply Property_Value,Property_ran in H15;
      auto. rewrite ConstSeq_Value in *; auto with real. apply NNPP; intro.
      assert (f[z] ∈ (R ~ [0%r])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
        apply MKT41 in H17; eauto with real. }
      apply Mult_inv1,MKT4' in H17 as []. apply Seq_Inv_Property_b in H16.
      rewrite H16 in H11. apply AxiomII in H18 as []. elim H19.
      apply MKT41; eauto with real. apply AxiomII; auto. }
    destruct F0_is_NPUF_over_N as [[[_[_[_[]]]]]].
    apply H11 in H9; auto. red; intros. apply AxiomII in H14; tauto.
    apply Equ_NPUF_is_equRelation_over_Rᴺ. apply Seq_Inv_Close; auto.
    apply ConstSeq_is_Seq; auto with real.
  - intro. unfold HR_Inv in H0.
    assert (\{ λ a, a ∈ HR /\ a <> 0 /\ r·a = 1 \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H1 as [H1[H2[]]].
      rewrite MKT69a in H4. elim MKT39. rewrite H4. apply Hyperreal_is_set.
      intro. rewrite HR_Mult_Func_dom in H5. apply AxiomII' in H5; tauto.
      elim (@ MKT16 z); auto. }
    rewrite H1,MKT24 in H0. elim MKT39. rewrite H0. apply Hyperreal_is_set.
Qed.

Property HR_Double_Inv : ∀ r, r ∈ HR -> r <> 0 <-> (r⁻)⁻ = r.
Proof.
  split; intros.
  - New H. apply HR_Elements in H1 as [f[]].
    New H1. apply Seq_Inv_Close in H3. rewrite H2 in H0.
    New H0. apply HR_Inv_Instantiate in H4; auto.
    rewrite H2,H4. New (HR_Inv_isnot_0 r). rewrite H2,H4 in H5.
    apply HR_Inv_Instantiate in H5; auto. rewrite H5.
    assert ((/(/f))%seq = f).
    { New H3. apply Seq_Inv_Close in H6. New H1.
      apply AxiomII in H6 as [H6[H8[]]], H7 as [H7[H11[]]].
      apply MKT71; auto. intros. destruct (classic (x ∈ N)).
      destruct (classic (f[x] = 0%r)). rewrite H15.
      apply Seq_Inv_Property_a in H15; auto.
      apply ->Seq_Inv_Property_a in H15; auto.
      New H15. apply Seq_Inv_Property_b in H16; auto.
      New H14. New H1. apply AxiomII in H18 as [H18[H19[]]].
      rewrite <-H20 in H17. apply Property_Value,Property_ran in H17; auto.
      assert (f[x] ∈ (R ~ [0%r])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. apply MKT41 in H22; eauto with real. }
      New H22. apply Mult_inv1 in H23. New H23. apply MKT4' in H24 as [].
      assert ((/f)[x] <> 0%r).
      { intro. rewrite H16 in H26. apply AxiomII in H25 as [].
        apply H27,MKT41; eauto with real. }
      New H26. apply Seq_Inv_Property_b in H27; auto. rewrite H27,H16.
      assert (((f[x])⁻)·(f[x]) = 1)%r. { rewrite Mult_P4,Mult_inv2; auto. }
      apply Mult_Co3 in H28; auto with real.
      New H23. apply Mult_inv1,MKT4' in H29 as [].
      rewrite Mult_P4,Mult_P1 in H28; auto with real.
      New H14. rewrite <-H9 in H14. rewrite <-H12 in H15.
      apply MKT69a in H14,H15. rewrite H14,H15; auto. }
    rewrite H6; auto.
  - intro. rewrite H1,HR_Inv_0_is_universe in H0. unfold HR_Inv in H0.
    assert (\{ λ a, a ∈ HR /\ a <> 0 /\ μ·a = 1 \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H2 as [H2[H3[]]].
      rewrite MKT69a in H5. elim MKT39. rewrite H5. apply Hyperreal_is_set.
      intro. rewrite HR_Mult_Func_dom in H6. apply AxiomII' in H6 as [_[]].
      elim MKT39; eauto. elim (@ MKT16 z); auto. }
    rewrite H2,MKT24 in H0. elim MKT39. rewrite H0. apply Hyperreal_is_set.
Qed.

Property HR_Inv_1_is_1 : 1⁻ = 1.
Proof.
  unfold HR_Inv. New HR_One_in_HR.
  assert (\{ λ a, a ∈ HR /\ a <> 0 /\ 1·a = 1 \} = [1]).
  { apply AxiomI; split; intros. apply AxiomII in H0 as [H0[H1[]]].
    rewrite HR_1_Mult in H3; auto. apply MKT41; eauto. apply MKT41 in H0; eauto.
    apply AxiomII; repeat split; try rewrite H0; eauto. intro.
    apply HR_Zero_isnot_One; auto. rewrite HR_Mult_1; auto. }
  rewrite H0. assert (Ensemble 1). eauto. apply MKT44 in H1 as []; auto.
Qed.

Property HR_Inv_of_neg1 : (-(1))⁻ = -(1).
Proof.
  unfold HR_Inv. New HR_One_in_HR. New H. apply HR_Neg_Close in H0.
  assert (\{ λ a, a ∈ HR /\ a <> 0 /\ (-(1))·a = 1 \} = [-(1)]).
  { apply AxiomI; split; intros. apply AxiomII in H1 as [H1[H2[]]].
    assert ((-(1)) · ((-(1))·z) = (-(1))·1). { rewrite H4; auto. }
    rewrite <-HR_Mult_Ass,HR_neg1_Mult_neg1,HR_1_Mult,HR_Mult_1 in H5; auto.
    apply MKT41; eauto. apply MKT41 in H1; eauto. rewrite H1.
    apply AxiomII; repeat split; eauto. intro.
    assert ((-(1))·(-(1)) = 0·(-(1))). { rewrite H2; auto. }
    rewrite HR_neg1_Mult_neg1,HR_0_Mult in H3; auto.
    apply HR_Zero_isnot_One; auto. rewrite HR_neg1_Mult_neg1; auto. }
  rewrite H1. assert (Ensemble (-(1))). eauto. apply MKT44 in H2 as []; auto.
Qed.

Property HR_r_Div_r : ∀ r, r ∈ HR -> r <> 0 -> r/r = 1.
Proof.
  intros. New H. apply HR_Inv_Reasonable in H1 as [r1[[H1[]]]]; auto.
  assert (\{ λ a, a ∈ HR /\ a <> 0%hr /\ (r·a = 1)%hr \} = [r1]).
  { apply AxiomI; split; intros. apply AxiomII in H5 as [H5[H6[]]].
    apply MKT41; eauto. symmetry. apply H4; auto. apply MKT41 in H5; eauto.
    rewrite H5. apply AxiomII; split; eauto. }
  unfold HR_Inv. rewrite H5. assert (Ensemble r1); eauto.
  apply MKT44 in H6 as []. rewrite H6; auto.
Qed.

Property HR_Inv_of_Mult : ∀ u v, (u·v)⁻ = (u⁻)·(v⁻).
Proof.
  intros. destruct (classic (u ∈ HR /\ v ∈ HR)).
  - destruct H. destruct (classic (u <> 0 /\ v <> 0)).
    + destruct H1. assert (u·v <> 0).
      { intro. assert (u·v·(v⁻) = 0·(v⁻)). { rewrite H3; auto. }
        rewrite HR_Mult_Ass,HR_0_Mult,HR_r_Div_r,HR_Mult_1 in H4; auto.
        apply ->HR_Inv_Close; auto. }
      assert (u·v · ((u·v)⁻) = 1).
      { apply HR_r_Div_r; auto. apply HR_Mult_Close; auto. }
      assert (u·v · ((u⁻)·(v⁻)) = 1).
      { rewrite HR_Mult_Ass,(HR_Mult_Com (u⁻)),<-(HR_Mult_Ass v),HR_r_Div_r,
        HR_1_Mult,HR_r_Div_r; auto. apply ->HR_Inv_Close; auto. }
      New H. apply (HR_Mult_Close u v) in H6; auto.
      assert (u⁻ ∈ HR /\ v⁻ ∈ HR) as []. { split; apply ->HR_Inv_Close; auto. }
      assert (u⁻ <> 0 /\ v⁻ <> 0) as []. { split; apply HR_Inv_isnot_0. }
      New H3. apply HR_Inv_Reasonable in H11 as [x[_]]; auto.
      assert (x = (u·v)⁻ /\ x = (u⁻)·(v⁻)) as [].
      { split; apply H11; repeat split; auto. apply ->HR_Inv_Close; auto.
        apply HR_Inv_isnot_0. apply HR_Mult_Close; auto. intro.
        assert (u · ((u⁻)·(v⁻)) = u·0). { rewrite H12; auto. }
        rewrite <-HR_Mult_Ass,HR_r_Div_r,HR_1_Mult,HR_Mult_0 in H13; auto. }
      rewrite <-H12,<-H13; auto.
    + assert ([μ,v⁻] ∉ dom(HR_Mult_Func) /\ [u⁻,μ] ∉ dom(HR_Mult_Func)) as [].
      { split; intro; rewrite HR_Mult_Func_dom in H2;
        apply AxiomII' in H2 as [_[]]; apply MKT39; eauto. }
      apply MKT69a in H2,H3. apply notandor in H1 as []; apply ->NNPP in H1;
      auto; rewrite H1; [rewrite HR_0_Mult|rewrite HR_Mult_0]; auto;
      rewrite HR_Inv_0_is_universe; [rewrite H2|rewrite H3]; auto.
  - assert (u⁻ ∉ HR \/ v⁻ ∉ HR).
    { apply notandor in H as []; [left|right]; intro; elim H;
      apply HR_Inv_Close in H0; tauto. }
    assert (u·v = μ).
    { apply MKT69a. rewrite HR_Mult_Func_dom. intro.
      apply AxiomII' in H1 as [_[]]. elim H; auto. }
    assert ((u⁻)·(v⁻) = μ).
    { apply MKT69a. rewrite HR_Mult_Func_dom. intro.
      apply AxiomII' in H2 as [_[]]. destruct H0; auto. }
    assert (\{ λ a, a ∈ HR /\ a <> 0 /\ μ·a = 1 \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H3 as [H3[H4[]]].
      assert (μ·z = μ).
      { apply MKT69a. rewrite HR_Mult_Func_dom. intro.
        apply AxiomII' in H7 as [_[]]. apply MKT39; eauto. }
      rewrite H7 in H6. elim MKT39. rewrite H6. New HR_One_in_HR. eauto.
      elim (@ MKT16 z); auto. }
    rewrite H1,H2. unfold HR_Inv. rewrite H3,MKT24; auto.
Qed.

Property HR_Inv_of_neg_r_is_neg_r : ∀ r, r ∈ HR -> (-r)⁻ = -(r⁻).
Proof.
  intros. destruct (classic (r = 0)).
  - rewrite H0,HR_Neg_0,HR_Inv_0_is_universe. unfold HR_Neg.
    assert (\{ λ a, a ∈ HR /\ μ + a = 0 \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H1 as [H1[]].
      assert (μ + z = μ).
      { apply MKT69a. rewrite HR_Plus_Func_dom. intro.
        apply AxiomII' in H4 as [_[]]. apply MKT39; eauto. }
      elim MKT39. rewrite <-H4,H3. New HR_Zero_in_HR. eauto.
      elim (@ MKT16 z); auto. }
    rewrite H1,MKT24; auto.
  - rewrite HR_Neg_and_Mult,HR_Inv_of_Mult,HR_Inv_of_neg1,<-HR_Neg_and_Mult; auto.
    apply ->HR_Inv_Close; auto.
Qed.


(* 序性质 *)

Property HR_0_less_1 : (0 < 1)%hr.
Proof.
  split.
  - apply HR_Leq_Instantiate; try apply ConstSeq_is_Seq; auto with real.
    assert (\{ λ w, w ∈ N /\ ((ConstSeq 0)[w] ≤ (ConstSeq 1)[w])%r \} = N).
    { apply AxiomI; split; intros. apply AxiomII in H; tauto.
      apply AxiomII; repeat split; eauto. rewrite ConstSeq_Value,ConstSeq_Value;
      auto with real. apply OrderPM_Co9. }
    rewrite H. destruct F0_is_NPUF_over_N as [[[_[_[]]]_]_]; auto.
  - apply HR_Zero_isnot_One.
Qed.

Property HR_neg1_less_0 : (-(1) < 0)%hr.
Proof.
  split.
  - unfold "1". rewrite HR_Neg_Instantiate,ConstSeq_Neg;
    try apply ConstSeq_is_Seq; auto with real.
    apply HR_Leq_Instantiate; try apply ConstSeq_is_Seq; auto with real.
    assert (\{ λ w, w ∈ N /\ ((ConstSeq (-(1))%r)[w] ≤ (ConstSeq 0)[w])%r \} = N).
    { apply AxiomI; split; intros. apply AxiomII in H; tauto.
      apply AxiomII; repeat split; eauto. rewrite ConstSeq_Value,ConstSeq_Value;
      auto with real. apply OrderPM_Co2b; auto with real. apply OrderPM_Co9. }
    rewrite H. destruct F0_is_NPUF_over_N as [[[_[_[]]]_]_]; auto.
  - intro. assert (-(-(1)) = -0). { rewrite H; auto. }
    rewrite HR_Double_Neg,HR_Neg_0 in H0. apply HR_Zero_isnot_One; auto.
    apply HR_One_in_HR.
Qed.

(* 自反性(小于等于) *)
Property HR_Leq_Reflexivity : ∀ u, u ∈ HR -> u ≤ u.
Proof.
  intros. apply HR_Elements in H as [f[]].
  rewrite H0. apply HR_Leq_Instantiate; auto.
  assert (\{ λ w, w ∈ N /\ (f[w] ≤ f[w])%r \} = N).
  { apply AxiomI; split; intros. apply AxiomII in H1; tauto.
    apply AxiomII; repeat split; eauto. apply Leq_P1.
    apply AxiomII in H as [H[H2[]]].
    apply H4,(@ Property_ran z),Property_Value; auto. rewrite H3; auto. }
  rewrite H1. destruct F0_is_NPUF_over_N as [[[_[_[]]]]]; auto.
Qed.

(* 非对称性(小于等于) *)
Property HR_Leq_Asymmetry : ∀ u v, u ∈ HR -> v ∈ HR -> u ≤ v -> v ≤ u -> u = v.
Proof.
  intros. apply HR_Elements in H as [f[]], H0 as [g[]]. subst.
  apply equClassT1; auto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
  apply HR_Leq_Instantiate in H1,H2; auto.
  assert (\{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \}
    ∩ \{ λ w, w ∈ N /\ (g[w] ≤ f[w])%r \}
    ⊂ \{ λ w, w ∈ N /\ (f[w] = g[w])%r \}).
  { red; intros. apply MKT4' in H3 as [].
    apply AxiomII in H3 as [H3[]], H4 as [H4[]].
    apply AxiomII; repeat split; auto.
    apply AxiomII in H as [_[H[]]], H0 as [_[H0[]]].
    apply (Leq_P2 _ g[z]); auto; [apply H10|apply H12];
    apply (@ Property_ran z),Property_Value; auto;
    [rewrite H9|rewrite H11]; auto. }
  destruct F0_is_NPUF_over_N as [[[_[_[_[]]]]]].
  apply H5 in H3; auto. red; intros. apply AxiomII in H8; tauto.
Qed.

(* 传递性(小于等于) *)
Property HR_Leq_Transitivity : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> u ≤ v -> v ≤ w -> u ≤ w.
Proof.
  intros. apply HR_Elements in H as [f[]], H0 as [g[]], H1 as [h[]].
  subst. apply HR_Leq_Instantiate in H3,H2; auto.
  apply HR_Leq_Instantiate; auto.
  assert (\{ λ w, w ∈ N /\ (g[w] ≤ h[w])%r \}
    ∩ \{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \}
    ⊂ \{ λ w, w ∈ N /\ (f[w] ≤ h[w])%r \}).
  { red; intros. apply MKT4' in H4 as [].
    apply AxiomII in H4 as [H4[]], H5 as [H5[]].
    apply AxiomII; repeat split; auto.
    apply AxiomII in H as [_[H[]]], H0 as [_[H0[]]], H1 as [_[H1[]]].
    apply (Leq_P3 _ g[z]); auto; [apply H11|apply H13|apply H15];
    apply (@ Property_ran z),Property_Value; auto;
    [rewrite H10|rewrite H12|rewrite H14]; auto. }
  destruct F0_is_NPUF_over_N as [[[_[_[_[]]]]]].
  apply H6 in H4; auto. red; intros. apply AxiomII in H9; tauto.
Qed.

(* 三分性(小于等于) *)
Property HR_Leq_Trichotomy : ∀ u v, u ∈ HR -> v ∈ HR -> u ≤ v \/ v ≤ u.
Proof.
  intros. apply HR_Elements in H as [f[]], H0 as [g[]]. subst.
  assert (\{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \}
    ∪ \{ λ w, w ∈ N /\ (g[w] ≤ f[w])%r \} = N).
  { apply AxiomI; split; intros. apply MKT4 in H1 as [];
    apply AxiomII in H1; tauto. apply MKT4.
    apply AxiomII in H as [_[H[]]], H0 as [_[H0[]]].
    New H1. New H1. rewrite <-H2 in H6. rewrite <-H4 in H7.
    apply Property_Value,Property_ran in H6,H7; auto.
    destruct (Leq_P4 f[z] g[z]); auto; [left|right]; apply AxiomII; eauto. }
  destruct F0_is_NPUF_over_N as []. New H2.
  destruct H4 as [[_[_[H4 _]]]_]. rewrite <-H1 in H4.
  apply (FT1 F0 N) in H4 as []; auto; apply HR_Leq_Instantiate in H4; auto.
Qed.

(* 反自反性(严格小于) *)
Property HR_Less_Irreflexivity : ∀ u, ~ u < u.
Proof. intros. intro. destruct H; auto. Qed.

(* 传递性(严格小于) *)
Property HR_Less_Transitivity : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> u < v -> v < w -> u < w.
Proof.
  intros. destruct H2,H3. split. apply (HR_Leq_Transitivity u v); auto.
  intro. rewrite H6 in H2. elim H5. apply HR_Leq_Asymmetry; auto.
Qed.

(* 传递性推论(混合传递性) *)
Corollary HR_Less_Transitivity_Co : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> ((u < v /\ v ≤ w) \/ (u ≤ v /\ v < w)) -> u < w.
Proof.
  intros. destruct H2 as [[[]]|[H3[]]]; split;
  try apply (HR_Leq_Transitivity _ v); auto; intro;
  [rewrite <-H5 in H4; apply H3|rewrite H5 in H3; apply H4];
  apply HR_Leq_Asymmetry; auto.
Qed.

(* 三分性(严格小于) *)
Property HR_Less_Trichotomy : ∀ u v, u ∈ HR -> v ∈ HR
  -> u < v \/ v < u \/ u = v.
Proof.
  intros. destruct (classic (u = v)); auto.
  destruct (HR_Leq_Trichotomy u v); auto.
Qed.



(* 序与运算的联合性质 *)

(* 加法保持(小于等于) *)
Property HR_Leq_Pr_Plus : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> (u ≤ v <-> u + w ≤ v + w)%hr.
Proof.
  assert (∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR -> u ≤ v -> u + w ≤ v + w).
  { intros. apply HR_Elements in H as [f[]], H0 as [g[]], H1 as [h[]].
    rewrite H3,H4,H5,HR_Plus_Instantiate,HR_Plus_Instantiate; auto.
    apply HR_Leq_Instantiate; try apply Seq_Plus_Close; auto.
    rewrite H3,H4 in H2. apply HR_Leq_Instantiate in H2; auto.
    assert (\{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \}
      ⊂ \{ λ w0, w0 ∈ N /\ ((f + h)%seq[w0] ≤ (g + h)%seq[w0])%r \}).
    { red; intros. apply AxiomII in H6 as [H6[]].
      apply AxiomII; repeat split; auto. repeat rewrite Seq_Plus_Property; auto.
      apply AxiomII in H as [_[H[]]], H0 as [_[H0[]]], H1 as [_[H1[]]].
      apply Plus_Leq; auto; [apply H10|apply H12|apply H14];
      apply (@ Property_ran z),Property_Value; auto;
      [rewrite H9|rewrite H11|rewrite H13]; auto. }
    destruct F0_is_NPUF_over_N as [[[_[_[_[]]]]_]_].
    apply H8 in H6; auto. red; intros. apply AxiomII in H9; tauto. }
  split; intros; auto. New H2. apply HR_Neg_Close in H4.
  apply (H _ _ (-w)) in H3; try apply HR_Plus_Close; auto.
  rewrite HR_Plus_Ass,HR_Plus_Ass,HR_r_Minus_r,HR_Plus_0,HR_Plus_0 in H3; auto.
Qed.

(* 加法保持推论(小于等于) *)
Corollary HR_Leq_Pr_Plus_Co : ∀ u v, u ∈ HR -> v ∈ HR
  -> (u ≤ v <-> 0 ≤ v - u)%hr.
Proof.
  intros. New H. apply HR_Neg_Close in H1. split; intros;
  [apply (HR_Leq_Pr_Plus u v (-u)) in H2|apply (HR_Leq_Pr_Plus u v (-u))]; auto;
  [rewrite HR_r_Minus_r in H2|rewrite HR_r_Minus_r]; auto.
Qed.

(* 加法保持(小于) *)
Property HR_Less_Pr_Plus : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> (u < v <-> u + w < v + w)%hr.
Proof.
  assert (∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR -> u < v -> u + w < v + w).
  { intros. destruct H2. split. apply HR_Leq_Pr_Plus; auto.
    intro. apply HR_Plus_Cancel in H4; auto. }
  split; intros; auto. destruct H3. split. apply HR_Leq_Pr_Plus in H3; auto.
  intro. elim H4. rewrite H5; auto.
Qed.

(* 加法保持推论(小于) *)
Corollary HR_Less_Pr_Plus_Co : ∀ u v, u ∈ HR -> v ∈ HR
  -> (u < v <-> 0 < v - u)%hr.
Proof.
  split; intros; destruct H1; split. apply ->HR_Leq_Pr_Plus_Co; auto.
  intro. elim H2. assert (0 + u = v - u + u). { rewrite H3; auto. }
  rewrite HR_0_Plus,HR_Plus_Ass,(HR_Plus_Com (-u)),HR_r_Minus_r,HR_Plus_0 in H4;
  auto. apply HR_Leq_Pr_Plus_Co in H1; auto.
  intro. rewrite H3,HR_r_Minus_r in H2; auto.
Qed.

(* 加法保持的其他推论 *)
Corollary HR_neg_leq_0 : ∀ u, u ∈ HR -> (0 ≤ u <-> (-u) ≤ 0)%hr.
Proof.
  intros. New HR_Zero_in_HR. New H. apply HR_Neg_Close in H1.
  split; intros. apply (HR_Leq_Pr_Plus 0 u (-u)) in H2; auto.
  rewrite HR_r_Minus_r,HR_0_Plus in H2; auto.
  apply (HR_Leq_Pr_Plus _ _ u) in H2; auto.
  rewrite HR_Plus_Com,HR_r_Minus_r,HR_0_Plus in H2; auto.
Qed.

Corollary HR_0_leq_neg : ∀ u, u ∈ HR -> (u ≤ 0 <-> 0 ≤ (-u))%hr.
Proof.
  split; intros. rewrite <-(HR_Double_Neg u) in H0; auto.
  apply HR_neg_leq_0 in H0; auto. apply ->HR_Neg_Close; auto.
  apply HR_neg_leq_0 in H0. rewrite HR_Double_Neg in H0; auto.
  apply ->HR_Neg_Close; auto.
Qed.

Corollary HR_neg_less_0 : ∀ u, u ∈ HR -> (0 < u <-> (-u) < 0)%hr.
Proof.
  intros. split; intros; destruct H0; split. apply HR_neg_leq_0; auto.
  intro. elim H1. rewrite <-(HR_Double_Neg u); auto. rewrite H2,HR_Neg_0; auto.
  apply HR_neg_leq_0; auto. intro. rewrite <-H2 in *. elim H1.
  rewrite HR_Neg_0; auto.
Qed.

Corollary HR_0_less_neg : ∀ u, u ∈ HR -> (u < 0 <-> 0 < (-u))%hr.
Proof.
  intros. split; intros; destruct H0; split. apply HR_0_leq_neg; auto.
  intro. New H2. rewrite <-HR_Neg_0 in H2. New H2.
  rewrite H3,HR_Double_Neg in H4; auto. rewrite H4,HR_Double_Neg in H3; auto.
  apply HR_0_leq_neg; auto. intro. rewrite H2,HR_Neg_0 in H1; auto.
Qed.

Corollary HR_neg_leq_neg : ∀ u v, u ∈ HR -> v ∈ HR -> (u ≤ v <-> -v ≤ -u)%hr.
Proof.
  intros. New H. New H0. apply HR_Neg_Close in H1,H2. split; intros.
  - apply (HR_Leq_Pr_Plus u v (-u)) in H3; auto.
    rewrite HR_r_Minus_r in H3; auto.
    apply (HR_Leq_Pr_Plus _ _ (-v)) in H3; auto.
    rewrite HR_0_Plus,HR_Plus_Ass,(HR_Plus_Com (-u)),<-HR_Plus_Ass,
    HR_r_Minus_r,HR_0_Plus in H3; auto. apply HR_Zero_in_HR.
    apply HR_Minus_Close; auto.
  - apply (HR_Leq_Pr_Plus _ _ u) in H3; auto.
    rewrite (HR_Plus_Com (-u)),HR_r_Minus_r in H3; auto.
    apply (HR_Leq_Pr_Plus _ _ v) in H3; auto.
    rewrite HR_0_Plus,HR_Plus_Ass,(HR_Plus_Com u),<-HR_Plus_Ass,
    (HR_Plus_Com (-v)),HR_r_Minus_r,HR_0_Plus in H3; auto.
    apply HR_Plus_Close; auto. apply HR_Zero_in_HR.
Qed.

Corollary HR_neg_less_neg : ∀ u v, u ∈ HR -> v ∈ HR -> (u < v <-> -v < -u)%hr.
Proof.
  intros. New H. New H0. apply HR_Neg_Close in H1,H2. split; intros.
  - apply (HR_Less_Pr_Plus u v (-u)) in H3; auto.
    rewrite HR_r_Minus_r in H3; auto.
    apply (HR_Less_Pr_Plus _ _ (-v)) in H3; auto.
    rewrite HR_0_Plus,HR_Plus_Ass,(HR_Plus_Com (-u)),<-HR_Plus_Ass,
    HR_r_Minus_r,HR_0_Plus in H3; auto. apply HR_Zero_in_HR.
    apply HR_Minus_Close; auto.
  - apply (HR_Less_Pr_Plus _ _ u) in H3; auto.
    rewrite (HR_Plus_Com (-u)),HR_r_Minus_r in H3; auto.
    apply (HR_Less_Pr_Plus _ _ v) in H3; auto.
    rewrite HR_0_Plus,HR_Plus_Ass,(HR_Plus_Com u),<-HR_Plus_Ass,
    (HR_Plus_Com (-v)),HR_r_Minus_r,HR_0_Plus in H3; auto.
    apply HR_Plus_Close; auto. apply HR_Zero_in_HR.
Qed.



(* 乘法保持(小于等于) *)
Property HR_Leq_Pr_Mult_a : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> (0 < w)%hr -> (u ≤ v <-> u·w ≤ v·w)%hr.
Proof.
  intros. apply HR_Elements in H as [f[]], H0 as [g[]], H1 as [h[]].
  New zero_in_R. apply ConstSeq_is_Seq in H6.
  rewrite H3,H4,H5,HR_Mult_Instantiate,HR_Mult_Instantiate; auto.
  rewrite H5 in H2. apply HR_Less_Instantiate in H2; auto.
  destruct F0_is_NPUF_over_N as [[[_[_[_[]]]]_]_].
  assert (∀ f x, f ∈ Rᴺ -> x ∈ N -> f[x] ∈ R).
  { intros. apply AxiomII in H9 as [_[H9[]]].
    apply H12,(@ Property_ran x),Property_Value; auto. rewrite H11; auto. }
  split; intros; apply HR_Leq_Instantiate in H10; try apply Seq_Mult_Close;
  auto; apply HR_Leq_Instantiate; try apply Seq_Mult_Close; auto.
  - assert (\{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \}
      ∩ \{ λ w, w ∈ N /\ ((ConstSeq 0)[w] < h[w])%r \}
      ⊂ \{ λ w, w ∈ N /\ ((f·h)%seq[w] ≤ (g·h)%seq[w])%r \}).
    { red; intros. apply MKT4' in H11 as [].
      apply AxiomII in H11 as [_[]], H12 as [_[H12[]]].
      apply AxiomII; repeat split; eauto. repeat rewrite Seq_Mult_Property; auto.
      rewrite ConstSeq_Value in H14; auto with real. apply OrderPM_Co7b; auto. }
    apply H8 in H11; auto. red; intros. apply AxiomII in H12; tauto.
  - assert (\{ λ w, w ∈ N /\ ((f·h)%seq[w] ≤ (g·h)%seq[w])%r \}
      ∩ \{ λ w, w ∈ N /\ ((ConstSeq 0)[w] < h[w])%r \}
      ⊂ \{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \}).
    { red; intros. apply MKT4' in H11 as [].
      apply AxiomII in H11 as [_[]], H12 as [_[]].
      apply AxiomII; repeat split; eauto.
      rewrite ConstSeq_Value in H14; auto with real.
      rewrite Seq_Mult_Property,Seq_Mult_Property in H13; auto.
      assert (h[z] ∈ R ~ [0%r]).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
        apply MKT41 in H15; eauto with real. destruct H14; auto. }
      New H15. apply Mult_inv1 in H16. New H16. apply MKT4' in H17 as [H17 _].
      New H14. apply OrderPM_Co10 in H18; auto. New H18. destruct H19.
      apply (OrderPM_Co7b _ _ ((h[z])⁻)%r) in H13; auto with real.
      rewrite <-Mult_P3,<-Mult_P3,Divide_P1,Mult_P1,Mult_P1 in H13; auto. }
    apply H8 in H11; auto. red; intros. apply AxiomII in H12; tauto.
Qed.

Property HR_Leq_Pr_Mult_b : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> (w < 0)%hr -> (u ≤ v <-> v·w ≤ u·w)%hr.
Proof.
  intros. New H2. apply HR_0_less_neg in H3; auto.
  New H1. apply HR_Neg_Close in H4. split; intros.
  - apply (HR_Leq_Pr_Mult_a u v (-w)) in H5; auto.
    rewrite HR_Mult_Com,HR_Neg_and_Mult,HR_Mult_Ass,<-HR_Neg_and_Mult,
    <-HR_Mult_Ass,(HR_Mult_Com v),HR_Mult_Ass,<-HR_Neg_and_Mult in H5;
    try apply HR_Mult_Close; auto.
    apply HR_neg_leq_neg; try apply HR_Mult_Close; auto.
    rewrite HR_Mult_Com; auto.
  - apply HR_neg_leq_neg in H5; try apply HR_Mult_Close; auto.
    rewrite HR_Neg_and_Mult,HR_Mult_Com,HR_Mult_Ass,(HR_Mult_Com w),
    <-HR_Neg_and_Mult,(HR_Neg_and_Mult (v·w)),(HR_Mult_Com (-(1))),HR_Mult_Ass,
    (HR_Mult_Com w),<-HR_Neg_and_Mult in H5; try apply HR_Mult_Close; auto.
    apply HR_Leq_Pr_Mult_a in H5; auto.
Qed.


(* 乘法保持(小于) *)
Property HR_Less_Pr_Mult_a : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> (0 < w)%hr -> (u < v <-> u·w < v·w)%hr.
Proof.
  intros. assert (w <> 0). { destruct H2; auto. }
  assert (w⁻ ∈ HR). { apply ->HR_Inv_Close; split; auto. }
  split; intros. split. apply HR_Leq_Pr_Mult_a; auto. destruct H5; auto.
  intro. assert (u·w·w⁻ = v·w·w⁻). { rewrite H6; auto. }
  rewrite HR_Mult_Ass,HR_Mult_Ass,HR_r_Div_r,HR_Mult_1,HR_Mult_1 in H7; auto.
  destruct H5; auto. destruct H5. split. apply HR_Leq_Pr_Mult_a in H5; auto.
  intro. rewrite H7 in H6; auto.
Qed.

Property HR_Less_Pr_Mult_b : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> (w < 0)%hr -> (u < v <-> v·w < u·w)%hr.
Proof.
  intros. assert (w <> 0). { destruct H2; auto. }
  assert (w⁻ ∈ HR). { apply ->HR_Inv_Close; split; auto. }
  split; intros. split. apply HR_Leq_Pr_Mult_b; auto. destruct H5; auto.
  intro. assert (u·w·w⁻ = v·w·w⁻). { rewrite H6; auto. }
  rewrite HR_Mult_Ass,HR_Mult_Ass,HR_r_Div_r,HR_Mult_1,HR_Mult_1 in H7; auto.
  destruct H5; auto. destruct H5. split. apply HR_Leq_Pr_Mult_b in H5; auto.
  intro. rewrite H7 in H6; auto.
Qed.

(* 乘法保持(leq 和 less 混合) *)
Property HR_Leq_and_Less_Pr_Mult_a : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> (0 ≤ w)%hr -> (u < v \/ u ≤ v)%hr -> (u·w ≤ v·w)%hr.
Proof.
  intros. assert (u ≤ v). { destruct H3 as [[]|]; auto. }
  destruct (classic (w = 0)). rewrite H5,HR_Mult_0,HR_Mult_0; auto.
  apply HR_Leq_Reflexivity. apply HR_Zero_in_HR.
  apply HR_Leq_Pr_Mult_a; auto.
Qed.

Property HR_Leq_and_Less_Pr_Mult_b : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> (w ≤ 0)%hr -> (u < v \/ u ≤ v)%hr -> (v·w ≤ u·w)%hr.
Proof.
  intros. assert (u ≤ v). { destruct H3 as [[]|]; auto. }
  destruct (classic (w = 0)). rewrite H5,HR_Mult_0,HR_Mult_0; auto.
  apply HR_Leq_Reflexivity. apply HR_Zero_in_HR.
  apply HR_Leq_Pr_Mult_b; auto.
Qed.

Property HR_Leq_and_Less_Pr_Mult_c : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> (0 < w \/ 0 ≤ w)%hr -> (u < v)%hr -> (u·w ≤ v·w)%hr.
Proof.
  intros. destruct H2. apply (HR_Less_Pr_Mult_a u v w) in H3 as []; auto.
  apply HR_Leq_and_Less_Pr_Mult_a; auto.
Qed.

Property HR_Leq_and_Less_Pr_Mult_d : ∀ u v w, u ∈ HR -> v ∈ HR -> w ∈ HR
  -> (w < 0 \/ w ≤ 0)%hr -> (u < v)%hr -> (v·w ≤ u·w)%hr.
Proof.
  intros. destruct H2. apply (HR_Less_Pr_Mult_b u v w) in H3 as []; auto.
  apply HR_Leq_and_Less_Pr_Mult_b; auto.
Qed.


(* 序对乘法保持的推论 *)
Corollary HR_0_less_inv : ∀ u, u ∈ HR -> (0 < u <-> 0 < u⁻)%hr.
Proof.
  split; intros.
  - assert (u <> 0). { destruct H0; auto. }
    assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. } New HR_Zero_in_HR.
    New H3. apply (HR_Less_Trichotomy (u⁻)) in H4 as [H4|[]]; auto.
    apply (HR_Less_Pr_Mult_a _ _ u) in H4; auto.
    rewrite HR_0_Mult,HR_Mult_Com,HR_r_Div_r in H4; auto.
    destruct H4,HR_0_less_1. elim H5. apply HR_Leq_Asymmetry; auto.
    apply HR_One_in_HR. elim (HR_Inv_isnot_0 u); auto.
  - assert (u <> 0).
    { intro. rewrite H1,HR_Inv_0_is_universe in H0. destruct H0.
      apply AxiomII' in H0 as []. apply MKT49b in H0 as []. apply MKT39; auto. }
    assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
    New HR_One_in_HR.  New HR_Zero_in_HR. New H4.
    apply (HR_Less_Trichotomy u) in H5 as [H5|[]]; auto.
    apply (HR_Less_Pr_Mult_a _ _ (u⁻)) in H5; auto.
    rewrite HR_0_Mult,HR_r_Div_r in H5; auto. destruct H5,HR_0_less_1.
    elim H6. apply HR_Leq_Asymmetry; auto. elim H1; auto.
Qed.

Corollary HR_inv_less_0 : ∀ u, u ∈ HR -> (u < 0 <-> u⁻ < 0)%hr.
Proof.
  intros. New H. apply HR_Neg_Close in H0. split; intros. New H1. destruct H2.
  apply HR_0_less_neg in H1; auto. apply HR_0_less_inv in H1; auto.
  rewrite HR_Inv_of_neg_r_is_neg_r in H1; auto. apply HR_0_less_neg in H1; auto.
  apply ->HR_Inv_Close; auto. assert (u <> 0).
  { intro. rewrite H2,HR_Inv_0_is_universe in H1. destruct H1.
    apply AxiomII' in H1 as [H1 _]. apply MKT49b in H1 as [].
    apply MKT39; eauto. }
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
  apply HR_0_less_neg in H1; auto. rewrite <-HR_Inv_of_neg_r_is_neg_r in H1; auto.
  apply HR_0_less_inv in H1; auto. apply HR_0_less_neg; auto.
Qed.

Corollary HR_inv_leq_1 : ∀ u, u ∈ HR -> (1 ≤ u <-> (0 < u⁻ /\ u⁻ ≤ 1))%hr.
Proof.
  New HR_0_less_1. New HR_Zero_in_HR. New HR_One_in_HR. split; intros.
  assert (0 < u). { apply (HR_Less_Transitivity_Co _ 1); auto. }
  New H4. apply HR_0_less_inv in H5; auto. split; auto.
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close. destruct H4; auto. }
  apply (HR_Leq_Pr_Mult_a _ _ u⁻) in H3; auto.
  rewrite HR_1_Mult,HR_r_Div_r in H3; auto. destruct H4; auto. destruct H3.
  New H3. apply HR_0_less_inv in H5; auto.
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close. destruct H5; auto. }
  apply (HR_Leq_Pr_Mult_a _ _ u) in H4; auto.
  rewrite HR_Mult_Com,HR_r_Div_r,HR_1_Mult in H4; auto. destruct H5; auto.
Qed.

Corollary HR_inv_less_1 : ∀ u, u ∈ HR -> (1 < u <-> (0 < u⁻ /\ u⁻ < 1))%hr.
Proof.
  New HR_0_less_1. New HR_Zero_in_HR. New HR_One_in_HR. split; intros.
  assert (0 < u). { apply (HR_Less_Transitivity _ 1); auto. }
  split. apply ->HR_0_less_inv; auto. split. apply HR_inv_leq_1; auto.
  destruct H3; auto. intro. assert ((u⁻)⁻ = 1⁻). { rewrite H5; auto. }
  assert (u <> 0). { destruct H4; auto. } apply HR_Double_Inv in H7; auto.
  rewrite H7,HR_Inv_1_is_1 in H6. rewrite H6 in H3. destruct H3; auto.
  destruct H3. New H3. apply HR_0_less_inv in H5; auto.
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close. destruct H5; auto. }
  apply (HR_Less_Pr_Mult_a _ _ u) in H4; auto.
  rewrite HR_Mult_Com,HR_r_Div_r,HR_1_Mult in H4; auto. destruct H5; auto.
Qed.

Corollary HR_1_leq_inv : ∀ u, u ∈ HR -> ((0 < u /\ u ≤ 1) <-> 1 ≤ u⁻)%hr.
Proof.
  split; intros. destruct H0. apply HR_inv_leq_1. destruct H0.
  apply ->HR_Inv_Close; auto. assert (u <> 0). { destruct H0; auto. }
  apply HR_Double_Inv in H2; auto. rewrite H2; auto.
  assert (u <> 0).
  { intro. rewrite H1,HR_Inv_0_is_universe in H0. apply AxiomII' in H0 as [].
    apply MKT49b in H0 as []. apply MKT39; eauto. }
  apply HR_inv_leq_1 in H0. apply HR_Double_Inv in H1; auto.
  rewrite H1 in H0; auto. apply ->HR_Inv_Close; auto.
Qed.

Corollary HR_1_less_inv : ∀ u, u ∈ HR -> ((0 < u /\ u < 1) <-> 1 < u⁻)%hr.
Proof.
  split; intros. destruct H0. apply HR_inv_less_1. destruct H0.
  apply ->HR_Inv_Close; auto. assert (u <> 0). { destruct H0; auto. }
  apply HR_Double_Inv in H2; auto. rewrite H2; auto.
  assert (u <> 0).
  { intro. rewrite H1,HR_Inv_0_is_universe in H0. destruct H0.
    apply AxiomII' in H0 as []. apply MKT49b in H0 as []. apply MKT39; eauto. }
  apply HR_inv_less_1 in H0. apply HR_Double_Inv in H1; auto.
  rewrite H1 in H0; auto. apply ->HR_Inv_Close; auto.
Qed.

Corollary HR_inv_leq_neg1 : ∀ u, u ∈ HR -> ((-(1) ≤ u /\ u < 0) <-> u⁻ ≤ -(1))%hr.
Proof.
  New HR_One_in_HR. New H. apply HR_Neg_Close in H0. split; intros.
  destruct H2. New H2. apply HR_neg_leq_neg in H4; auto. New H3.
  apply HR_0_less_neg in H5; auto. rewrite HR_Double_Neg in H4; auto.
  assert (u <> 0). { destruct H3; auto. }
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
  New H6. apply HR_Double_Inv in H8; auto. New H1. apply HR_Neg_Close in H9.
  rewrite <-(HR_Double_Neg u),HR_Inv_of_neg_r_is_neg_r; auto.
  apply ->HR_neg_leq_neg; auto. apply HR_1_leq_inv; auto.
  rewrite HR_Inv_of_neg_r_is_neg_r; auto. apply ->HR_Neg_Close; auto.
  assert (u <> 0).
  { intro. rewrite H3,HR_Inv_0_is_universe in H2. apply AxiomII' in H2 as [].
    apply MKT49b in H2 as []. apply MKT39; eauto. }
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
  New H1. apply HR_Neg_Close in H5.
  rewrite <-(HR_Double_Neg u),HR_Inv_of_neg_r_is_neg_r in H2; auto.
  apply HR_neg_leq_neg in H2; auto. apply HR_1_leq_inv in H2 as []; auto.
  apply HR_0_less_neg in H2; auto. apply HR_neg_leq_neg in H6; auto.
  rewrite HR_Double_Neg in H6; auto. rewrite HR_Inv_of_neg_r_is_neg_r; auto.
  apply ->HR_Neg_Close; auto.
Qed.

Corollary HR_inv_less_neg1 : ∀ u, u ∈ HR -> ((-(1) < u /\ u < 0) <-> u⁻ < -(1))%hr.
Proof.
  New HR_One_in_HR. New H. apply HR_Neg_Close in H0. split; intros.
  destruct H2. New H2. apply HR_neg_less_neg in H4; auto. New H3.
  apply HR_0_less_neg in H5; auto. rewrite HR_Double_Neg in H4; auto.
  assert (u <> 0). { destruct H3; auto. }
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
  New H6. apply HR_Double_Inv in H8; auto. New H1. apply HR_Neg_Close in H9.
  rewrite <-(HR_Double_Neg u),HR_Inv_of_neg_r_is_neg_r; auto.
  apply ->HR_neg_less_neg; auto. apply HR_1_less_inv; auto.
  rewrite HR_Inv_of_neg_r_is_neg_r; auto. apply ->HR_Neg_Close; auto.
  assert (u <> 0).
  { intro. rewrite H3,HR_Inv_0_is_universe in H2. destruct H2.
    apply AxiomII' in H2 as []. apply MKT49b in H2 as []. apply MKT39; eauto. }
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
  New H1. apply HR_Neg_Close in H5.
  rewrite <-(HR_Double_Neg u),HR_Inv_of_neg_r_is_neg_r in H2; auto.
  apply HR_neg_less_neg in H2; auto. apply HR_1_less_inv in H2 as []; auto.
  apply HR_0_less_neg in H2; auto. apply HR_neg_less_neg in H6; auto.
  rewrite HR_Double_Neg in H6; auto. rewrite HR_Inv_of_neg_r_is_neg_r; auto.
  apply ->HR_Neg_Close; auto.
Qed.

Corollary HR_neg1_leq_inv : ∀ u, u ∈ HR -> (u ≤ -(1) <-> (-(1) ≤ u⁻ /\ u⁻ < 0))%hr.
Proof.
  New HR_Zero_in_HR. New HR_One_in_HR. New H0. apply HR_Neg_Close in H1.
  split; intros. apply HR_neg_leq_neg in H3; auto.
  rewrite HR_Double_Neg in H3; auto. assert (u <> 0).
  { intro. rewrite H4,HR_Neg_0 in H3. destruct HR_0_less_1. elim H6.
    apply HR_Leq_Asymmetry; auto. }
  New H2. apply HR_Neg_Close in H5. apply HR_inv_leq_1 in H3 as []; auto.
  rewrite HR_Inv_of_neg_r_is_neg_r in H3,H6; auto.
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
  New H7. apply HR_Neg_Close in H8. apply HR_neg_leq_neg in H6; auto.
  rewrite HR_Double_Neg in H6; auto. apply HR_neg_less_neg in H3; auto.
  rewrite HR_Double_Neg,HR_Neg_0 in H3; auto. destruct H3.
  assert (u <> 0).
  { intro. rewrite H5,HR_Inv_0_is_universe in H4. destruct H4.
    apply AxiomII' in H4 as []. apply MKT49b in H4 as []. apply MKT39; eauto. }
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
  New H6. apply HR_Neg_Close in H7. apply HR_neg_leq_neg in H3; auto.
  apply HR_0_less_neg in H4; auto. rewrite HR_Double_Neg in H3; auto.
  apply HR_neg_leq_neg; auto. rewrite HR_Double_Neg; auto. New H5.
  apply HR_Double_Inv in H5; auto. rewrite <-H5,<-HR_Inv_of_neg_r_is_neg_r; auto.
  apply HR_1_leq_inv; auto.
Qed.

Corollary HR_neg1_less_inv : ∀ u, u ∈ HR -> (u < -(1) <-> (-(1) < u⁻ /\ u⁻ < 0))%hr.
Proof.
  New HR_Zero_in_HR. New HR_One_in_HR. New H0. apply HR_Neg_Close in H1.
  split; intros. apply HR_neg_less_neg in H3; auto.
  rewrite HR_Double_Neg in H3; auto. assert (u <> 0).
  { intro. rewrite H4,HR_Neg_0 in H3. destruct H3,HR_0_less_1. elim H7.
    apply HR_Leq_Asymmetry; auto. }
  New H2. apply HR_Neg_Close in H5. apply HR_inv_less_1 in H3 as []; auto.
  rewrite HR_Inv_of_neg_r_is_neg_r in H3,H6; auto.
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
  New H7. apply HR_Neg_Close in H8. apply HR_neg_less_neg in H6; auto.
  rewrite HR_Double_Neg in H6; auto. apply HR_neg_less_neg in H3; auto.
  rewrite HR_Double_Neg,HR_Neg_0 in H3; auto. destruct H3.
  assert (u <> 0).
  { intro. rewrite H5,HR_Inv_0_is_universe in H4. destruct H4.
    apply AxiomII' in H4 as []. apply MKT49b in H4 as []. apply MKT39; eauto. }
  assert (u⁻ ∈ HR). { apply ->HR_Inv_Close; auto. }
  New H6. apply HR_Neg_Close in H7. apply HR_neg_less_neg in H3; auto.
  apply HR_0_less_neg in H4; auto. rewrite HR_Double_Neg in H3; auto.
  apply HR_neg_less_neg; auto. rewrite HR_Double_Neg; auto. New H5.
  apply HR_Double_Inv in H5; auto. rewrite <-H5,<-HR_Inv_of_neg_r_is_neg_r; auto.
  apply HR_1_less_inv; auto.
Qed.

Corollary HR_inv_leq_inv : ∀ u v, u ∈ HR -> v ∈ HR
  -> ((u < 0 /\ v < 0) \/ (0 < u /\ 0 < v))
  -> (u ≤ v <-> v⁻ ≤ u⁻)%hr.
Proof.
  assert (∀ u v, u ∈ HR -> v ∈ HR -> ((u < 0 /\ v < 0) \/ (0 < u /\ 0 < v))
    -> u ≤ v -> v⁻ ≤ u⁻).
  { intros. assert (u <> 0 /\ v <> 0) as [].
    { destruct H1 as [[[][]]|[[][]]]; split; auto. }
    assert (u⁻ ∈ HR /\ v⁻ ∈ HR) as []. { split; apply ->HR_Inv_Close; auto. }
    destruct H1 as [[]|[]]. apply HR_inv_less_0 in H1,H7; auto.
    apply (HR_Leq_Pr_Mult_b _ _ (u⁻)) in H2; auto. rewrite HR_r_Div_r in H2; auto.
    apply (HR_Leq_Pr_Mult_b _ _ (v⁻)) in H2; auto. rewrite HR_1_Mult,HR_Mult_Ass,
    (HR_Mult_Com (u⁻)),<-HR_Mult_Ass,HR_r_Div_r,HR_1_Mult in H2; auto.
    apply HR_Div_Close; auto. apply HR_One_in_HR.
    apply HR_0_less_inv in H1,H7; auto.
    apply (HR_Leq_Pr_Mult_a _ _ (u⁻)) in H2; auto. rewrite HR_r_Div_r in H2; auto.
    apply (HR_Leq_Pr_Mult_a _ _ (v⁻)) in H2; auto. rewrite HR_1_Mult,HR_Mult_Ass,
    (HR_Mult_Com (u⁻)),<-HR_Mult_Ass,HR_r_Div_r,HR_1_Mult in H2; auto.
    apply HR_One_in_HR. apply HR_Div_Close; auto. }
  split; intros; auto. assert (u <> 0 /\ v <> 0) as [].
  { destruct H2 as [[[][]]|[[][]]]; split; auto. }
  assert (u⁻ ∈ HR /\ v⁻ ∈ HR) as []. { split; apply ->HR_Inv_Close; auto. }
  New H4. New H5. apply HR_Double_Inv in H8,H9; auto. rewrite <-H8,<-H9.
  apply H; auto. destruct H2 as [[]|[]];
  [apply HR_inv_less_0 in H2,H10|apply HR_0_less_inv in H2,H10]; auto.
Qed.

Corollary HR_inv_less_inv : ∀ u v, u ∈ HR -> v ∈ HR
  -> ((u < 0 /\ v < 0) \/ (0 < u /\ 0 < v))
  -> (u < v <-> v⁻ < u⁻)%hr.
Proof.
  split; intros; destruct H2; split;
  [apply ->HR_inv_leq_inv| |apply HR_inv_leq_inv|]; auto; intro.
  assert (u <> 0 /\ v <> 0) as [].
  { destruct H1 as [[[][]]|[[][]]]; split; auto. }
  apply HR_Double_Inv in H5,H6; auto. rewrite <-H5,<-H6,H4 in H3; auto.
  rewrite H4 in H3; auto.
Qed.

(* 同号相乘 *)
Corollary HR_0_less_same_sign_mult : ∀ u v, u ∈ HR -> v ∈ HR
  -> ((0 < u /\ 0 < v) \/ (u < 0 /\ v < 0)) <-> 0 < u·v.
Proof.
  New HR_Zero_in_HR. New HR_One_in_HR. split; intros.
  - destruct H3 as [[]|[]]. apply (HR_Less_Pr_Mult_a 0 u v) in H3; auto.
    rewrite HR_0_Mult in H3; auto. apply (HR_Less_Pr_Mult_b u 0 v) in H3; auto.
    rewrite HR_0_Mult in H3; auto.
  - assert (u·v ∈ HR). { apply HR_Mult_Close; auto. }
    New H. apply (HR_Less_Trichotomy v) in H5 as [H5|[]]; auto.
    + New H5. apply HR_inv_less_0 in H6; auto.
      assert (v⁻ ∈ HR). { apply ->HR_Inv_Close. destruct H5; auto. }
      apply (HR_Less_Pr_Mult_b _ _ (v⁻)) in H3; auto.
      rewrite HR_Mult_Ass,HR_r_Div_r,HR_Mult_1,HR_0_Mult in H3; auto.
      destruct H5; auto.
    + New H5. apply HR_0_less_inv in H6; auto.
      assert (v⁻ ∈ HR). { apply ->HR_Inv_Close. destruct H5; auto. }
      apply (HR_Less_Pr_Mult_a _ _ (v⁻)) in H3; auto.
      rewrite HR_Mult_Ass,HR_r_Div_r,HR_Mult_1,HR_0_Mult in H3; auto.
      destruct H5; auto.
    + rewrite H5,HR_Mult_0 in H3; auto. destruct H3. elim H6; auto.
Qed.

Corollary HR_0_leq_same_sign_mult : ∀ u v, u ∈ HR -> v ∈ HR
  -> ((0 < u /\ 0 < v) \/ (0 ≤ u /\ 0 < v) \/ (0 < u /\ 0 ≤ v) \/ (0 ≤ u /\ 0 ≤ v)
   \/ (u < 0 /\ v < 0) \/ (u ≤ 0 /\ v < 0) \/ (u < 0 /\ v ≤ 0) \/ (u ≤ 0 /\ v ≤ 0))
  <-> 0 ≤ u·v.
Proof.
  New HR_Zero_in_HR. New HR_One_in_HR. split; intros.
  - assert (((0 ≤ u /\ 0 ≤ v) \/ (u ≤ 0 /\ v ≤ 0)) -> 0 ≤ u·v).
    { intros [[]|[]]; replace 0 with (0·v); try apply HR_0_Mult; auto.
      apply HR_Leq_and_Less_Pr_Mult_a; auto.
      apply HR_Leq_and_Less_Pr_Mult_b; auto. }
    apply H4. destruct H3 as [[]|[[]|[[]|[[]|[[]|[[]|[[]|[]]]]]]]]; auto;
    try destruct H3; try destruct H5; auto.
  - destruct (classic (u = 0)). New H. apply (HR_Leq_Trichotomy v) in H5 as [];
    auto. repeat right. split; auto. rewrite H4. apply HR_Leq_Reflexivity; auto.
    right. right. right. left. split; auto. rewrite H4.
    apply HR_Leq_Reflexivity; auto. destruct (classic (v = 0)). New H.
    apply (HR_Leq_Trichotomy u) in H6 as []; auto. repeat right. split; auto.
    rewrite H5. apply HR_Leq_Reflexivity; auto. right. right. right. left.
    split; auto. rewrite H5. apply HR_Leq_Reflexivity; auto.
    assert (0 < u·v).
    { split; auto. intro. assert (0·v⁻ = u·v·v⁻). { rewrite H6; auto. }
      rewrite HR_0_Mult,HR_Mult_Ass,HR_r_Div_r,HR_Mult_1 in H7; auto.
      apply ->HR_Inv_Close; auto. }
    apply HR_0_less_same_sign_mult in H6 as [[[][]]|[[][]]]; auto.
    repeat right; auto.
Qed.

Corollary HR_dif_sign_mult_less_0 : ∀ u v, u ∈ HR -> v ∈ HR
  -> ((u < 0 /\ 0 < v) \/ (0 < u /\ v < 0)) <-> u·v < 0.
Proof.
  New HR_Zero_in_HR. New HR_One_in_HR. split; intros.
  - destruct H3 as [[]|[]]. apply (HR_Less_Pr_Mult_a u 0 v) in H3; auto.
    rewrite HR_0_Mult in H3; auto. apply (HR_Less_Pr_Mult_b 0 u v) in H3; auto.
    rewrite HR_0_Mult in H3; auto.
  - assert (u·v ∈ HR). { apply HR_Mult_Close; auto. }
    New H. apply (HR_Less_Trichotomy v) in H5 as [H5|[]]; auto.
    + New H5. apply HR_inv_less_0 in H6; auto.
      assert (v⁻ ∈ HR). { apply ->HR_Inv_Close. destruct H5; auto. }
      apply (HR_Less_Pr_Mult_b _ _ (v⁻)) in H3; auto.
      rewrite HR_Mult_Ass,HR_r_Div_r,HR_Mult_1,HR_0_Mult in H3; auto.
      destruct H5; auto.
    + New H5. apply HR_0_less_inv in H6; auto.
      assert (v⁻ ∈ HR). { apply ->HR_Inv_Close. destruct H5; auto. }
      apply (HR_Less_Pr_Mult_a _ _ (v⁻)) in H3; auto.
      rewrite HR_Mult_Ass,HR_r_Div_r,HR_Mult_1,HR_0_Mult in H3; auto.
      destruct H5; auto.
    + rewrite H5,HR_Mult_0 in H3; auto. destruct H3. elim H6; auto.
Qed.

Corollary HR_dif_sign_mult_leq_0 : ∀ u v, u ∈ HR -> v ∈ HR
  -> ((u < 0 /\ 0 < v) \/ (u ≤ 0 /\ 0 < v) \/ (u < 0 /\ 0 ≤ v) \/ (u ≤ 0 /\ 0 ≤ v)
   \/ (0 < u /\ v < 0) \/ (0 ≤ u /\ v < 0) \/ (0 < u /\ v ≤ 0) \/ (0 ≤ u /\ v ≤ 0))
  <-> u·v ≤ 0.
Proof.
  New HR_Zero_in_HR. New HR_One_in_HR. split; intros.
  - assert (((u ≤ 0 /\ 0 ≤ v) \/ (0 ≤ u /\ v ≤ 0)) -> u·v ≤ 0).
    { intros [[]|[]]; replace 0 with (0·v); try apply HR_0_Mult; auto.
      apply HR_Leq_and_Less_Pr_Mult_a; auto.
      apply HR_Leq_and_Less_Pr_Mult_b; auto. }
    apply H4. destruct H3 as [[]|[[]|[[]|[[]|[[]|[[]|[[]|[]]]]]]]]; auto;
    try destruct H3; try destruct H5; auto.
  - destruct (classic (u = 0)). New H. apply (HR_Leq_Trichotomy v) in H5 as [];
    auto. repeat right. split; auto. rewrite H4. apply HR_Leq_Reflexivity; auto.
    right. right. right. left. split; auto. rewrite H4.
    apply HR_Leq_Reflexivity; auto. destruct (classic (v = 0)). New H.
    apply (HR_Leq_Trichotomy u) in H6 as []; auto. right. right. right. left.
    split; auto. rewrite H5. apply HR_Leq_Reflexivity; auto. repeat right.
    split; auto. rewrite H5. apply HR_Leq_Reflexivity; auto.
    assert (u·v < 0).
    { split; auto. intro. assert (0·v⁻ = u·v·v⁻). { rewrite H6; auto. }
      rewrite HR_0_Mult,HR_Mult_Ass,HR_r_Div_r,HR_Mult_1 in H7; auto.
      apply ->HR_Inv_Close; auto. }
    apply HR_dif_sign_mult_less_0 in H6 as [[[][]]|[[][]]]; auto.
    repeat right; auto.
Qed.



(* 绝对值性质 *)

(* 超实数中的绝对值 *)
(* 绝对值函数 *)
Definition HR_Abs := \{\ λ u v, u ∈ HR
  /\ ((0 ≤ u /\ v = u) \/ (u ≤ 0 /\ v = -u)) \}\.

Notation "∣ u ∣" := (HR_Abs[u])(u at level 5) : HR_scope.

Property HR_Abs_is_Function : Function HR_Abs.
Proof.
  split; unfold Relation; intros.
  - apply AxiomII in H as [_[x[y[]]]]; eauto.
  - apply AxiomII' in H as [_[H[[]|[]]]], H0 as [_[H0[[]|[]]]];
    try rewrite H2,H4; auto; assert (x = 0) by
    (apply HR_Leq_Asymmetry; auto; apply HR_Zero_in_HR);
    rewrite H5,HR_Neg_0; auto.
Qed.

Property HR_Abs_dom : dom(HR_Abs) = HR.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [_[H0[[]|[]]]]; auto.
  - New HR_Zero_in_HR. apply AxiomII; split; eauto.
    New H. apply HR_Neg_Close in H1.
    New H0. apply (HR_Leq_Trichotomy z) in H2 as []; auto;
    [exists (-z)|exists z]; apply AxiomII'; repeat split; auto;
    apply MKT49a; eauto.
Qed.

Property HR_Abs_ran : ran(HR_Abs) ⊂ HR.
Proof.
  red; intros. apply AxiomII in H as [H[]].
  apply AxiomII' in H0 as [_[H0[[]|[]]]]; rewrite H2; auto.
  apply ->HR_Neg_Close; auto.
Qed.

Property HR_Abs_Close : ∀ r, r ∈ HR <-> ∣r∣ ∈ HR.
Proof.
  split; intros.
  - New HR_Abs_is_Function. rewrite <-HR_Abs_dom in H.
    apply Property_Value,Property_ran in H; auto. apply HR_Abs_ran; auto.
  - apply NNPP; intro. rewrite <-HR_Abs_dom in H0. apply MKT69a in H0.
    rewrite H0 in H. apply MKT39; eauto.
Qed.

Property HR_Abs_0 : ∣0∣ = 0.
Proof.
  New HR_Zero_in_HR. rewrite <-HR_Abs_dom in H. New HR_Abs_is_Function.
  apply Property_Value,AxiomII' in H as [_[H[[]|[]]]]; auto.
  rewrite HR_Neg_0 in H2; auto.
Qed.

Property HR_Abs_nonPos : ∀ r, r ∈ HR -> r ≤ 0 <-> ∣r∣ = -r.
Proof.
  intros. rewrite <-HR_Abs_dom in H. New HR_Abs_is_Function.
  apply Property_Value,AxiomII' in H as [_[H[[]|[]]]]; auto;
  split; intros; auto.
  - assert (r = 0). { apply HR_Leq_Asymmetry; auto. apply HR_Zero_in_HR. }
    rewrite H4,HR_Neg_0. apply HR_Abs_0.
  - rewrite H2 in H3. New HR_Zero_in_HR.
    New H4. apply (HR_Less_Trichotomy r) in H5 as [H5|[|]]; auto.
    destruct H5. elim H6. apply HR_Leq_Asymmetry; auto.
    apply HR_neg_less_0 in H5; auto. rewrite <-H3 in H5. destruct H5.
    elim H6. apply HR_Leq_Asymmetry; auto. rewrite H5.
    apply HR_Leq_Reflexivity; auto.
Qed.

Property HR_Abs_nonNeg : ∀ r, r ∈ HR -> 0 ≤ r <-> ∣r∣ = r.
Proof.
  intros. rewrite <-HR_Abs_dom in H. New HR_Abs_is_Function.
  apply Property_Value,AxiomII' in H as [_[H[[]|[]]]]; auto;
  split; intros; auto.
  - assert (r = 0). { apply HR_Leq_Asymmetry; auto. apply HR_Zero_in_HR. }
    rewrite H4. apply HR_Abs_0.
  - rewrite H2 in H3. New HR_Zero_in_HR.
    New H4. apply (HR_Less_Trichotomy r) in H5 as [H5|[|]]; auto.
    apply HR_0_less_neg in H5; auto. rewrite H3 in H5. destruct H5; auto.
    destruct H5. elim H6. apply HR_Leq_Asymmetry; auto. rewrite H5.
    apply HR_Leq_Reflexivity; auto.
Qed.

Property HR_Abs_Neg : ∀ r, r ∈ HR -> r < 0 -> ∣r∣ = -r.
Proof. intros. destruct H0. apply HR_Abs_nonPos; auto. Qed.

Property HR_Abs_Pos : ∀ r, r ∈ HR -> 0 < r -> ∣r∣ = r.
Proof. intros. destruct H0. apply HR_Abs_nonNeg; auto. Qed.

Property HR_Abs_neg_eq_pos : ∀ r, ∣(-r)∣ = ∣r∣.
Proof.
  intros. destruct (classic (r ∈ HR)).
  - New H. apply HR_Neg_Close in H0. New HR_Zero_in_HR. New H1.
    apply (HR_Leq_Trichotomy r) in H2 as []; auto. New H2.
    apply HR_0_leq_neg in H3; auto. apply HR_Abs_nonPos in H2; auto.
    apply HR_Abs_nonNeg in H3; auto. rewrite H2,H3; auto.
    New H2. apply HR_neg_leq_0 in H3; auto. apply HR_Abs_nonNeg in H2; auto.
    apply HR_Abs_nonPos in H3; auto. rewrite H2,H3,HR_Double_Neg; auto.
  - unfold HR_Neg. assert (\{ λ a, a ∈ HR /\ r + a = 0 \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H0 as [H0[]].
      assert ([r,z] ∉ dom(HR_Plus_Func)).
      { intro. rewrite HR_Plus_Func_dom in H3.
        apply AxiomII' in H3 as [_[]]; auto. }
      apply MKT69a in H3. New HR_Zero_in_HR. rewrite <-H2,H3 in H4.
      elim MKT39; eauto. elim (@ MKT16 z); auto. }
    rewrite H0,MKT24. rewrite <-HR_Abs_dom in H. apply MKT69a in H.
    assert (μ ∉ dom(HR_Abs)). { intro. apply MKT39; eauto. }
    apply MKT69a in H1. rewrite H1,<-H; auto.
Qed.

Property HR_Abs_Value : ∀ r, r ∈ HR -> ∣r∣ = r \/ ∣r∣ = -r.
Proof.
  intros. New HR_Zero_in_HR. New H0.
  apply (HR_Leq_Trichotomy r) in H1 as []; auto.
  apply HR_Abs_nonPos in H1; auto. apply HR_Abs_nonNeg in H1; auto.
Qed.

Property HR_abs_eq_0 : ∀ r, ∣r∣ = 0 <-> r = 0.
Proof.
  split; intros.
  - assert (r ∈ HR).
    { apply NNPP; intro. rewrite <-HR_Abs_dom in H0.
      apply MKT69a in H0. New HR_Zero_in_HR. rewrite <-H,H0 in H1.
      apply MKT39; eauto. }
    New HR_Zero_in_HR. New H1. apply (HR_Less_Trichotomy r) in H2 as [H2|[|]];
    auto. New H2. apply HR_Abs_Neg in H3; auto. apply HR_0_less_neg in H2; auto.
    rewrite <-H3,H in H2. destruct H2. elim H4; auto. New H2.
    apply HR_Abs_Pos in H3; auto. rewrite <-H3,H in H2. destruct H2.
    elim H4; auto.
  - rewrite H,HR_Abs_0; auto.
Qed.

Property HR_0_leq_abs : ∀ r, r ∈ HR -> 0 ≤ ∣r∣.
Proof.
  intros. New HR_Zero_in_HR.
  New H0. apply (HR_Leq_Trichotomy r) in H1 as []; auto; New H1.
  - apply HR_Abs_nonPos in H2; auto. rewrite H2. apply HR_0_leq_neg; auto.
  - apply HR_Abs_nonNeg in H2; auto. rewrite H2; auto.
Qed.

Property HR_0_less_abs : ∀ r, r ∈ HR -> r <> 0 <-> 0 < ∣r∣.
Proof.
  split; intros. split. apply HR_0_leq_abs; auto. intro. apply H0,HR_abs_eq_0;
  auto. intro. rewrite H1,HR_Abs_0 in H0. destruct H0; auto.
Qed.

Property HR_r_leq_abs_r : ∀ r, r ∈ HR -> r ≤ ∣r∣.
Proof.
  intros. New HR_Zero_in_HR. New H0.
  apply (HR_Leq_Trichotomy r) in H1 as []; auto.
  New H. apply HR_0_leq_abs in H2. New H. apply HR_Abs_Close in H3.
  apply (HR_Leq_Transitivity _ 0); auto. apply HR_Abs_nonNeg in H1; auto.
  rewrite H1. apply HR_Leq_Reflexivity; auto.
Qed.

Property HR_r_less_abs_r : ∀ r, r ∈ HR -> r < 0 <-> r < ∣r∣.
Proof.
  split; intros. split. apply HR_r_leq_abs_r; auto. intro. symmetry in H1.
  apply HR_Abs_nonNeg in H1; auto. destruct H0. apply H2,HR_Leq_Asymmetry; auto.
  apply HR_Zero_in_HR. New HR_Zero_in_HR. New H1.
  apply (HR_Less_Trichotomy r) in H2 as [H2|[]]; auto.
  apply HR_Abs_Pos in H2; auto. rewrite H2 in H0. destruct H0. contradiction.
  rewrite H2,HR_Abs_0 in H0. destruct H0. contradiction.
Qed.

Property HR_Double_Abs : ∀ r, ∣∣r∣∣ = ∣r∣.
Proof.
  intros. destruct (classic (r ∈ HR)).
  - New H. apply HR_0_leq_abs in H0. New H. apply HR_Abs_Close in H1.
    apply HR_Abs_nonNeg in H0; auto.
  - rewrite <-HR_Abs_dom in H. apply MKT69a in H. rewrite H.
    assert (μ ∉ dom(HR_Abs)). { intro. apply MKT39; eauto. }
    apply MKT69a in H0; auto.
Qed.

Property HR_Abs_Pr_Mult : ∀ u v, ∣(u·v)∣ = ∣u∣·∣v∣.
Proof.
  intros. destruct (classic (u ∈ HR /\ v ∈ HR)).
  - destruct H. assert (u·v ∈ HR). { apply HR_Mult_Close; auto. }
    New HR_Zero_in_HR. New H2. New H2.
    apply (HR_Leq_Trichotomy u) in H3 as []; auto;
    apply (HR_Leq_Trichotomy v) in H4 as []; auto.
    + assert (0 ≤ u·v). { apply HR_0_leq_same_sign_mult; tauto. }
      apply HR_Abs_nonPos in H3,H4; auto. apply HR_Abs_nonNeg in H5; auto.
      rewrite H3,H4,H5,HR_neg_Mult_neg; auto.
    + assert (u·v ≤ 0). { apply HR_dif_sign_mult_leq_0; tauto. }
      apply HR_Abs_nonPos in H3,H5; auto. apply HR_Abs_nonNeg in H4; auto.
      rewrite H3,H4,H5,HR_Neg_and_Mult,<-HR_Mult_Ass,<-HR_Neg_and_Mult; auto.
    + assert (u·v ≤ 0). { apply HR_dif_sign_mult_leq_0; tauto. }
      apply HR_Abs_nonPos in H4,H5; auto. apply HR_Abs_nonNeg in H3; auto.
      rewrite H3,H4,H5,HR_Neg_and_Mult,HR_Mult_Com,HR_Mult_Ass,(HR_Mult_Com v),
      <-HR_Neg_and_Mult; auto.
    + assert (0 ≤ u·v). { apply HR_0_leq_same_sign_mult; tauto. }
      apply HR_Abs_nonNeg in H3,H4,H5; auto. rewrite H3,H4,H5; auto.
  - apply notandor in H. assert (∣u∣·∣v∣ = μ).
    { apply MKT69a. intro. rewrite HR_Mult_Func_dom in H0.
      apply AxiomII' in H0 as [_[]]. apply HR_Abs_Close in H0,H1.
      destruct H; auto. } rewrite H0.
    apply MKT69a. intro. rewrite HR_Abs_dom in H1.
    assert (u·v = μ).
    { apply MKT69a. intro. rewrite HR_Mult_Func_dom in H2.
      apply AxiomII' in H2 as [_[]]. destruct H; auto. }
    rewrite H2 in H1. apply MKT39; eauto.
Qed.

Property HR_Abs_Pr_Inv : ∀ u, ∣(u⁻)∣ = (∣u∣)⁻.
Proof.
  intros. destruct (classic (u ∈ HR)).
  - destruct (classic (u = 0)).
    + rewrite H0,HR_Abs_0,HR_Inv_0_is_universe.
      apply MKT69a. intro. apply MKT39; eauto.
    + assert (∣u∣ <> 0). { intro. apply ->HR_abs_eq_0 in H1; auto. }
      New H. apply HR_Abs_Close in H2.
      assert ((∣u∣)·(∣u∣)⁻ = 1). { apply HR_r_Div_r; auto. }
      assert ((∣u∣)·(∣u⁻∣) = 1).
      { rewrite <-HR_Abs_Pr_Mult,HR_r_Div_r; auto.
        apply HR_Abs_Pos. apply HR_One_in_HR. apply HR_0_less_1. }
      apply HR_Inv_Reasonable in H2 as [x[_]]; auto.
      assert (x = ∣u⁻∣ /\ x = (∣u∣)⁻) as [].
      { split; apply H2. split. apply ->HR_Abs_Close. apply ->HR_Inv_Close; auto.
        split; auto. intro. apply ->HR_abs_eq_0 in H5.
        apply HR_Inv_isnot_0 in H5; auto. split. apply ->HR_Inv_Close.
        apply HR_Abs_Close in H; auto. split; auto. intro.
        apply HR_Inv_isnot_0 in H5; auto. }
      rewrite <-H5,<-H6; auto.
  - assert (∣u⁻∣ = μ /\ ∣u∣ = μ) as [].
    { split; apply MKT69a; intro; rewrite HR_Abs_dom in H0; auto.
      apply HR_Inv_Close in H0 as []; auto. }
    rewrite H0,H1. assert (\{ λ a, a ∈ HR /\ a <> 0 /\ μ·a = 1 \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H2 as [_[_[_]]].
      assert (μ·z = μ).
      { apply MKT69a. intro. rewrite HR_Mult_Func_dom in H3.
        apply AxiomII' in H3 as [_[]]. apply MKT39; eauto. }
      New HR_One_in_HR. elim MKT39. rewrite <-H3,H2; eauto.
      elim (@ MKT16 z); auto. }
    unfold HR_Inv. rewrite H2,MKT24; auto.
Qed.

Property HR_Abs_Triangle_inEqu : ∀ u v, u ∈ HR -> v ∈ HR
  -> ∣(u + v)∣ ≤ ∣u∣ + ∣v∣.
Proof.
  assert (∀ u v, u ∈ HR -> v ∈ HR -> u ≤ 0 -> 0 ≤ v
    -> ∣(u + v)∣ ≤ ∣u∣ + ∣v∣).
  { intros. assert (u+v ∈ HR). { apply HR_Plus_Close; auto. }
    New HR_Zero_in_HR. New H3. apply (HR_Leq_Trichotomy 0) in H5 as []; auto.
    - apply HR_Abs_nonNeg in H2,H5; auto. New H1. apply HR_Abs_nonPos in H1;
      auto. rewrite H1,H2,H5. New H. apply HR_Neg_Close in H7.
      apply HR_Leq_Pr_Plus; auto. apply (HR_Leq_Transitivity _ 0); auto.
      apply HR_0_leq_neg; auto.
    - New H2. apply HR_Abs_nonNeg in H2; auto. apply HR_Abs_nonPos in H1,H5;
      auto. rewrite H1,H2,H5. New H. New H0. apply HR_Neg_Close in H7,H8.
      rewrite HR_Neg_and_Mult,HR_Mult_Dis_l,<-HR_Neg_and_Mult,<-HR_Neg_and_Mult,
      HR_Plus_Com,(HR_Plus_Com (-u)); auto. apply HR_Leq_Pr_Plus; auto.
      apply (HR_Leq_Transitivity _ 0); auto. apply HR_neg_leq_0; auto. }
  intros. assert (u+v ∈ HR). { apply HR_Plus_Close; auto. }
  New HR_Zero_in_HR. New H3. New H3. apply (HR_Leq_Trichotomy u) in H4; auto.
  apply (HR_Leq_Trichotomy v) in H5; auto. destruct H4,H5; auto.
  - assert (u + v ≤ 0).
    { apply (HR_Leq_Pr_Plus u 0 v) in H4; auto. rewrite HR_0_Plus in H4; auto.
      apply (HR_Leq_Transitivity _ v); auto. }
    apply HR_Abs_nonPos in H4,H5,H6; auto. rewrite H4,H5,H6,HR_Neg_and_Mult,
    HR_Mult_Dis_l,<-HR_Neg_and_Mult,<-HR_Neg_and_Mult; auto.
    apply HR_Leq_Reflexivity,HR_Plus_Close; apply ->HR_Neg_Close; auto.
  - rewrite HR_Plus_Com,(HR_Plus_Com ∣u∣). apply (H v u); auto.
  - assert (0 ≤ u + v).
    { apply (HR_Leq_Pr_Plus 0 u v) in H4; auto. rewrite HR_0_Plus in H4; auto.
      apply (HR_Leq_Transitivity _ v); auto. }
    apply HR_Abs_nonNeg in H4,H5,H6; auto. rewrite H4,H5,H6.
    apply HR_Leq_Reflexivity; auto.
Qed.





















