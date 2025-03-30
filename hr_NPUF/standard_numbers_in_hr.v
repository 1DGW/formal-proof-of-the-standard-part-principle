Require Import axiomatic_reals.seq_operations.
Require Import mk.equivalence_relation.
Require Export hr_NPUF.properties_of_hr.


(* 标准实数 *)
Definition HR_R := \{ λ u, ∃ r, r ∈ R /\ u = \[ (ConstSeq r) \] \}.

Fact HR_One_in_HR_R : 1 ∈ HR_R.
Proof.
  apply AxiomII; split. apply Hyperreal_is_set. exists 1%r.
  split; auto with real.
Qed.

Fact HR_Zero_in_HR_R : 0 ∈ HR_R.
Proof.
  apply AxiomII; split. apply Hyperreal_is_set. exists 0%r.
  split; auto with real.
Qed.

Property HR_R_subset_HR : HR_R ⊂ HR.
Proof.
  red; intros. apply AxiomII in H as [H[x[]]]. rewrite H1. apply HR_Elements.
  exists (ConstSeq x). split; auto. apply ConstSeq_is_Seq; auto.
Qed.

Property HR_R_Element_Property : ∀ u v, u ∈ R -> v ∈ R
  -> \[ ConstSeq u \] = \[ ConstSeq v \] -> u = v.
Proof.
  intros. apply equClassT1 in H1; try apply ConstSeq_is_Seq; auto.
  apply AxiomII' in H1 as [_[H1[]]]. apply NNPP; intro.
  assert (\{ λ u0, u0 ∈ N /\ (ConstSeq u)[u0] = (ConstSeq v)[u0] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H5 as [H5[]].
    rewrite ConstSeq_Value,ConstSeq_Value in H7; auto. contradiction.
    elim (@ MKT16 z); auto. }
  rewrite H5 in H3. destruct F0_is_NPUF_over_N as [[[_[]]]]; auto.
  apply Equ_NPUF_is_equRelation_over_Rᴺ.
Qed.

(* R 与 HR_R 之间的同构函数 *)
Definition R_and_HR_R := \{\ λ u v, u ∈ R /\ v = \[ (ConstSeq u) \] \}\.

Property R_and_HR_R_is_Function1_1 : Function1_1 R_and_HR_R
  /\ dom(R_and_HR_R) = R /\ ran(R_and_HR_R) = HR_R.
Proof.
  assert (Function R_and_HR_R).
  { split; intros. red; intros. apply AxiomII in H as [H[x[y[]]]]; eauto.
    apply AxiomII' in H as [_[]], H0 as [_[]]. rewrite H1,H2; auto. }
  assert (Function R_and_HR_R⁻¹).
  { split; intros. red; intros. apply AxiomII in H0 as [H0[x[y[]]]]; eauto.
    apply AxiomII' in H0 as [], H1 as [].
    apply AxiomII' in H2 as [H2[]], H3 as [H3[]]. rewrite H5 in H7.
    assert ((ConstSeq y) ∈ Rᴺ /\ (ConstSeq z) ∈ Rᴺ) as [].
    { split; apply ConstSeq_is_Seq; auto. }
    apply equClassT1,AxiomII' in H7 as [H7[H10[]]]; auto. apply NNPP; intro.
    assert (\{ λ u, u ∈ N /\ (ConstSeq y)[u] = (ConstSeq z)[u] \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H14 as [H14[]].
      rewrite ConstSeq_Value,ConstSeq_Value in H16; auto. contradiction.
      elim (@ MKT16 z0); auto. } rewrite H14 in H12.
    destruct F0_is_NPUF_over_N as [[[_[]]]]; auto.
    apply Equ_NPUF_is_equRelation_over_Rᴺ. }
  split. split; auto. split; apply AxiomI; split; intros.
  - apply AxiomII in H1 as [H1[y]]. apply AxiomII' in H2; tauto.
  - apply AxiomII; split. eauto. exists \[ (ConstSeq z) \].
    apply AxiomII'; split; auto. apply MKT49a; eauto. apply Hyperreal_is_set.
  - apply AxiomII in H1 as [H1[x]]. apply AxiomII' in H2 as [H2[]].
    rewrite H4. apply AxiomII; split; eauto. apply Hyperreal_is_set.
  - apply AxiomII in H1 as [H1[r[]]]. apply AxiomII; split. eauto.
    exists r. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Property R_and_HR_R_Value : ∀ r, r ∈ R -> R_and_HR_R[r] = \[ (ConstSeq r) \].
Proof.
  intros. destruct R_and_HR_R_is_Function1_1 as [[][]].
  rewrite <-H2 in H. apply Property_Value,AxiomII' in H; tauto.
Qed.

(* 零元和单位元保持 *)
Property R_and_HR_R_PrZero : R_and_HR_R[0%r] = 0.
Proof. rewrite R_and_HR_R_Value; auto with real. Qed.

Property R_and_HR_R_PrOne : R_and_HR_R[1%r] = 1.
Proof. rewrite R_and_HR_R_Value; auto with real. Qed.

(* 序保持(小于等于) *)
Property R_and_HR_R_PrLeq : ∀ u v, u ∈ R -> v ∈ R -> (u ≤ v)%r
  <-> R_and_HR_R[u] ≤ R_and_HR_R[v].
Proof.
  intros. rewrite R_and_HR_R_Value,R_and_HR_R_Value; auto. split; intros.
  - apply HR_Leq_Instantiate; try apply ConstSeq_is_Seq; auto.
    assert (\{ λ w, w ∈ N /\ ((ConstSeq u)[w] ≤ (ConstSeq v)[w])%r \} = N).
    { apply AxiomI; split; intros. apply AxiomII in H2; tauto.
      apply AxiomII; repeat split; eauto.
      rewrite ConstSeq_Value,ConstSeq_Value; auto. }
    rewrite H2. destruct F0_is_NPUF_over_N as [[[_[_[]]]]]; auto.
  - apply HR_Leq_Instantiate in H1; try apply ConstSeq_is_Seq; auto.
    assert (\{ λ w, w ∈ N /\ ((ConstSeq u)[w] ≤ (ConstSeq v)[w])%r \} <> Φ).
    { intro. rewrite H2 in H1.
      destruct F0_is_NPUF_over_N as [[[_[]]_]_]; auto. }
    apply NEexE in H2 as []. apply AxiomII in H2 as [_[]].
    rewrite ConstSeq_Value,ConstSeq_Value in H3; auto.
Qed.

(* 序保持(严格小于) *)
Property R_and_HR_R_PrLess : ∀ u v, u ∈ R -> v ∈ R -> (u < v)%r
  <-> R_and_HR_R[u] < R_and_HR_R[v].
Proof.
  split; intros.
  - destruct H1. split. apply R_and_HR_R_PrLeq; auto.
    intro. destruct R_and_HR_R_is_Function1_1 as [[][]].
    apply f11inj in H3; auto; rewrite H6; auto.
  - destruct H1. apply R_and_HR_R_PrLeq in H1; auto. split; auto.
    intro. rewrite H3 in H2; auto.
Qed.

(* 加法保持 *)
Property R_and_HR_R_PrPlus : ∀ u v, u ∈ R -> v ∈ R
  -> R_and_HR_R[(u + v)%r] = R_and_HR_R[u] + R_and_HR_R[v].
Proof.
  intros. repeat rewrite R_and_HR_R_Value; auto with real.
  New H. New H0. apply ConstSeq_is_Seq in H1,H2.
  rewrite HR_Plus_Instantiate; auto.
  assert (ConstSeq (u + v)%r = ((ConstSeq u) + (ConstSeq v))%seq).
  { assert (ConstSeq (u + v)%r ∈ Rᴺ /\ ((ConstSeq u) + (ConstSeq v))%seq ∈ Rᴺ).
    { split. apply ConstSeq_is_Seq; auto with real.
      apply Seq_Plus_Close; auto. } destruct H3.
    apply AxiomII in H3 as [H3[H5[]]], H4 as [H4[H8[]]].
    apply MKT71; auto. intros. destruct (classic (x ∈ N)).
    rewrite Seq_Plus_Property; auto.
    repeat rewrite ConstSeq_Value; auto with real.
    New H11. rewrite <-H6 in H11. rewrite <-H9 in H12. apply MKT69a in H11,H12.
    rewrite H11,H12; auto. }
  rewrite H3; auto.
Qed.

(* 乘法保持 *)
Property R_and_HR_R_PrMult : ∀ u v, u ∈ R -> v ∈ R
  -> R_and_HR_R[(u · v)%r] = R_and_HR_R[u] · R_and_HR_R[v].
Proof.
  intros. repeat rewrite R_and_HR_R_Value; auto with real.
  New H. New H0. apply ConstSeq_is_Seq in H1,H2.
  rewrite HR_Mult_Instantiate; auto.
  assert (ConstSeq (u · v)%r = ((ConstSeq u) · (ConstSeq v))%seq).
  { assert (ConstSeq (u · v)%r ∈ Rᴺ /\ ((ConstSeq u) · (ConstSeq v))%seq ∈ Rᴺ).
    { split. apply ConstSeq_is_Seq; auto with real.
      apply Seq_Mult_Close; auto. } destruct H3.
    apply AxiomII in H3 as [H3[H5[]]], H4 as [H4[H8[]]].
    apply MKT71; auto. intros. destruct (classic (x ∈ N)).
    rewrite Seq_Mult_Property; auto.
    repeat rewrite ConstSeq_Value; auto with real.
    New H11. rewrite <-H6 in H11. rewrite <-H9 in H12. apply MKT69a in H11,H12.
    rewrite H11,H12; auto. }
  rewrite H3; auto.
Qed.

(* 负元保持 *)
Property R_and_HR_R_PrNeg : ∀ u, u ∈ R -> R_and_HR_R[(-u)%r] = -R_and_HR_R[u].
Proof.
  intros. repeat rewrite R_and_HR_R_Value; auto with real.
  New H. apply ConstSeq_is_Seq in H0. rewrite HR_Neg_Instantiate; auto.
  assert (ConstSeq (-u)%r = (-(ConstSeq u))%seq).
  { New H0. apply Seq_Neg_Close in H1. New H. apply Plus_neg1a in H2.
    apply ConstSeq_is_Seq in H2.
    apply AxiomII in H1 as [H1[H3[]]], H2 as [H2[H6[]]].
    apply MKT71; auto. intros. destruct (classic (x ∈ N)).
    rewrite Seq_Neg_Property,ConstSeq_Value,ConstSeq_Value; auto with real.
    New H9. rewrite <-H4 in H9. rewrite <-H7 in H10.
    apply MKT69a in H9,H10. rewrite H9,H10; auto. }
  rewrite H1; auto.
Qed.

(* 减法保持 *)
Property R_and_HR_R_PrMinus : ∀ u v, u ∈ R -> v ∈ R
  -> R_and_HR_R[(u - v)%r] = R_and_HR_R[u] - R_and_HR_R[v].
Proof.
  intros. rewrite R_and_HR_R_PrPlus,R_and_HR_R_PrNeg; auto with real.
Qed.

(* 逆元保持 *)
Property R_and_HR_R_PrInv : ∀ u, u ∈ R -> R_and_HR_R[(u⁻)%r] = (R_and_HR_R[u])⁻.
Proof.
  intros. destruct (classic (u = 0%r)).
  rewrite H0,Inv_0_is_universe,R_and_HR_R_PrZero,HR_Inv_0_is_universe.
  rewrite MKT69a; auto. intro. apply MKT39; eauto.
  assert (u ∈ (R ~ [0%r])).
  { apply MKT4'; split; auto. apply AxiomII; split. eauto. intro.
    apply MKT41 in H1; eauto with real. }
  New H1. apply Mult_inv1 in H2. New H2. apply MKT4' in H3 as [].
  apply AxiomII in H4 as []. repeat rewrite R_and_HR_R_Value; auto.
  assert (\[ (ConstSeq u) \] <> 0).
  { intro. apply equClassT1,AxiomII' in H6 as [H6[H7[]]].
    assert (\{ λ u0, u0 ∈ N /\ (ConstSeq u)[u0] = (ConstSeq 0%r)[u0] \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H10 as [H10[]].
      rewrite ConstSeq_Value,ConstSeq_Value in H12; auto with real.
      elim H0; auto. elim (@ MKT16 z); auto. } rewrite H10 in H9.
    destruct F0_is_NPUF_over_N as [[[_[]]]]; auto.
    apply Equ_NPUF_is_equRelation_over_Rᴺ. apply ConstSeq_is_Seq; auto.
    apply ConstSeq_is_Seq; auto with real. }
  New H. apply ConstSeq_is_Seq in H7. apply HR_Inv_Instantiate in H6; auto.
  rewrite H6. assert (ConstSeq (u⁻)%r = /(ConstSeq u)).
  { New H3. apply ConstSeq_is_Seq in H8. New H7. apply Seq_Inv_Close in H9.
    apply AxiomII in H8 as [H8[H10[]]], H9 as [H9[H13[]]]. apply MKT71; auto.
    intros. destruct (classic (x ∈ N)).
    assert ((ConstSeq u)[x] <> 0%r).
    { intro. rewrite ConstSeq_Value in H17; auto. }
    apply Seq_Inv_Property_b in H17; auto.
    rewrite H17,ConstSeq_Value,ConstSeq_Value; auto. New H16.
    rewrite <-H11 in H16. rewrite <-H14 in H17.
    apply MKT69a in H16,H17. rewrite H16,H17; auto. }
  rewrite H8; auto.
Qed.

Lemma Div_0_is_universe : ∀ x, (x/0)%r = μ.
Proof.
  intros. rewrite Inv_0_is_universe,MKT69a; auto. intro.
  apply AxiomII in H as []. apply MKT49b in H as []. apply MKT39; auto.
Qed.

(* 除法保持 *)
Property R_and_HR_R_PrDiv : ∀ u v, u ∈ R -> v ∈ R
  -> R_and_HR_R[(u/v)%r] = (R_and_HR_R[u])/(R_and_HR_R[v]).
Proof.
  intros. destruct (classic (v = 0%r)).
  rewrite H1,Div_0_is_universe,R_and_HR_R_PrZero,HR_Div_0_is_universe,MKT69a;
  auto. intro. apply MKT39; eauto.
  assert (v ∈ (R ~ [0%r])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
    apply MKT41 in H2; eauto with real. }
  New H2. apply Mult_inv1 in H3. New H3. apply MKT4' in H4 as [].
  rewrite R_and_HR_R_PrMult,R_and_HR_R_PrInv; auto.
Qed.


(*** 验证 HR_R 中运算的封闭性 ***)
(* 加法封闭 *)
Property HR_R_Plus_Close : ∀ u v, u ∈ HR_R -> v ∈ HR_R -> (u + v) ∈ HR_R.
Proof.
  intros. apply AxiomII in H as [H[x[]]], H0 as [H0[y[]]].
  New H1. New H3. apply ConstSeq_is_Seq in H5,H6.
  rewrite H2,H4,HR_Plus_Instantiate; auto.
  assert (((ConstSeq x) + (ConstSeq y))%seq = ConstSeq (x + y)%r).
  { assert (((ConstSeq x) + (ConstSeq y))%seq ∈ Rᴺ /\ ConstSeq (x + y)%r ∈ Rᴺ).
    { split. apply Seq_Plus_Close; auto. apply ConstSeq_is_Seq; auto with real. }
    destruct H7. apply AxiomII in H7 as [H7[H9[]]], H8 as [H8[H12[]]].
    apply MKT71; auto. intros. destruct (classic (x0 ∈ N)).
    rewrite Seq_Plus_Property,ConstSeq_Value,ConstSeq_Value,ConstSeq_Value;
    auto with real. New H15. rewrite <-H10 in H15. rewrite <-H13 in H16.
    apply MKT69a in H15,H16. rewrite H15,H16; auto. }
  apply AxiomII; split. apply Hyperreal_is_set. exists (x + y)%r.
  split. auto with real. rewrite H7; auto.
Qed.

(* 乘法封闭 *)
Property HR_R_Mult_Close : ∀ u v, u ∈ HR_R -> v ∈ HR_R -> (u · v) ∈ HR_R.
Proof.
  intros. apply AxiomII in H as [H[x[]]], H0 as [H0[y[]]].
  New H1. New H3. apply ConstSeq_is_Seq in H5,H6.
  rewrite H2,H4,HR_Mult_Instantiate; auto.
  assert (((ConstSeq x) · (ConstSeq y))%seq = ConstSeq (x · y)%r).
  { assert (((ConstSeq x) · (ConstSeq y))%seq ∈ Rᴺ /\ ConstSeq (x · y)%r ∈ Rᴺ).
    { split. apply Seq_Mult_Close; auto. apply ConstSeq_is_Seq; auto with real. }
    destruct H7. apply AxiomII in H7 as [H7[H9[]]], H8 as [H8[H12[]]].
    apply MKT71; auto. intros. destruct (classic (x0 ∈ N)).
    rewrite Seq_Mult_Property,ConstSeq_Value,ConstSeq_Value,ConstSeq_Value;
    auto with real. New H15. rewrite <-H10 in H15. rewrite <-H13 in H16.
    apply MKT69a in H15,H16. rewrite H15,H16; auto. }
  apply AxiomII; split. apply Hyperreal_is_set. exists (x · y)%r.
  split. auto with real. rewrite H7; auto.
Qed.

(* 负元封闭 *)
Property HR_R_Neg_Close : ∀ r, r ∈ HR_R <-> (-r) ∈ HR_R.
Proof.
  assert (∀ r, r ∈ HR_R -> (-r) ∈ HR_R).
  { intros. apply AxiomII in H as [H[x[]]]. New H0.
    apply ConstSeq_is_Seq in H2. rewrite H1,HR_Neg_Instantiate; auto.
    assert ((-(ConstSeq x))%seq = ConstSeq (-x)%r).
    { New H0. apply Plus_neg1a,ConstSeq_is_Seq in H3.
      New H2. apply Seq_Neg_Close in H4.
      apply AxiomII in H3 as [H3[H5[]]], H4 as [H4[H8[]]].
      apply MKT71; auto. intros. destruct (classic (x0 ∈ N)).
      rewrite Seq_Neg_Property,ConstSeq_Value,ConstSeq_Value; auto with real.
      New H11. rewrite <-H6 in H11. rewrite <-H9 in H12.
      apply MKT69a in H11,H12. rewrite H11,H12; auto. }
    rewrite H3. apply AxiomII; split. apply Hyperreal_is_set.
    exists (-x)%r. split; auto with real. }
  split; intros; auto. apply H in H0. rewrite HR_Double_Neg in H0; auto.
  apply NNPP; intro. unfold HR_Neg in H0.
  assert (\{ λ u, u ∈ HR /\ r + u = 0 \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H2 as [H2[]].
    rewrite MKT69a in H4. elim MKT39. rewrite H4. apply Hyperreal_is_set.
    intro. rewrite HR_Plus_Func_dom in H5. apply AxiomII' in H5; tauto.
    elim (@ MKT16 z); auto. }
  rewrite H2,MKT24 in H0. assert (\{ λ u, u ∈ HR /\ μ + u = 0 \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H3 as [H3[]].
    rewrite MKT69a in H5. elim MKT39. rewrite H5. apply Hyperreal_is_set.
    intro. apply AxiomII in H6 as []. apply MKT49b in H6 as [].
    apply MKT39; auto. elim (@ MKT16 z); auto. }
  rewrite H3,MKT24 in H0. elim MKT39; eauto.
Qed.

(* 减法封闭 *)
Property HR_R_Minus_Close : ∀ u v, u ∈ HR_R -> v ∈ HR_R -> (u - v) ∈ HR_R.
Proof.
  intros. apply HR_R_Plus_Close; auto. apply ->HR_R_Neg_Close; auto.
Qed.

(* 逆元封闭 *)
Property HR_R_Inv_Close : ∀ r, (r ∈ HR_R /\ r <> 0) <-> (r⁻) ∈ HR_R.
Proof.
  assert (∀ r, (r ∈ HR_R /\ r <> 0) -> (r⁻) ∈ HR_R).
  { intros r []. apply AxiomII in H as [H[x[]]]. New H1.
    apply ConstSeq_is_Seq in H3. rewrite H2 in H0. New H0.
    apply HR_Inv_Instantiate in H4; auto. rewrite H2,H4.
    assert (x <> 0%r). { intro. elim H0. rewrite H5; auto. }
    assert (x ∈ (R ~ [0%r])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
      apply MKT41 in H6; eauto with real. }
    apply Mult_inv1,MKT4' in H6 as [].
    assert ((/(ConstSeq x))%seq = ConstSeq (x⁻)%r).
    { New H6. apply ConstSeq_is_Seq in H8. New H3. apply Seq_Inv_Close in H9.
      apply AxiomII in H8 as [H8[H10[]]], H9 as [H9[H13[]]].
      apply MKT71; auto. intros. destruct (classic (x0 ∈ N)).
      assert ((ConstSeq x)[x0] <> 0%r).
      { intro. rewrite ConstSeq_Value in H17; auto. }
      apply Seq_Inv_Property_b in H17; auto. rewrite H17.
      rewrite ConstSeq_Value,ConstSeq_Value; auto.
      New H16. rewrite <-H11 in H16. rewrite <-H14 in H17.
      apply MKT69a in H16,H17. rewrite H16,H17; auto. }
    rewrite H8. apply AxiomII; split; eauto. apply Hyperreal_is_set. }
  split; intros; auto. destruct (classic (r = 0)).
  rewrite H1,HR_Inv_0_is_universe in H0. elim MKT39; eauto.
  assert ((r⁻)⁻ ∈ HR_R). { apply H; auto. split; auto. apply HR_Inv_isnot_0. }
  New H1. apply HR_Double_Inv in H3. rewrite H3 in H2; auto.
  apply NNPP; intro. unfold HR_Inv in H0.
  assert (\{ λ a, a ∈ HR /\ a <> 0 /\ r·a = 1 \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H6 as [H6[H7[]]].
    rewrite MKT69a in H9. elim MKT39. rewrite H9. apply Hyperreal_is_set.
    intro. rewrite HR_Mult_Func_dom in H10. apply AxiomII' in H10 as [_[]]; auto.
    elim (@ MKT16 z); auto. }
  rewrite H6,MKT24 in H0. elim MKT39; eauto.
Qed.

(* 除法封闭 *)
Property HR_R_Div_Close : ∀ u v, u ∈ HR_R -> v ∈ HR_R -> v <> 0 <-> u/v ∈ HR_R.
Proof.
  split; intros.
  - apply HR_R_Mult_Close; auto. apply ->HR_R_Inv_Close; auto.
  - intro. rewrite H2,HR_Div_0_is_universe in H1. elim MKT39; eauto.
Qed.

(* 绝对值封闭 *)
Property HR_R_Abs_Close : ∀ r, r ∈ HR_R <-> ∣r∣ ∈ HR_R.
Proof.
  split; intros.
  - New H. apply HR_R_subset_HR in H0.
    apply HR_Abs_Value in H0 as []; rewrite H0; auto.
    apply ->HR_R_Neg_Close; auto.
  - New H. apply HR_R_subset_HR,HR_Abs_Close in H0.
    apply HR_Abs_Value in H0 as []. rewrite <-H0; auto. rewrite H0 in H.
    apply HR_R_Neg_Close; auto.
Qed.


(***  标准自然数, 整数, 有理数  ***)

Definition HR_N := \{ λ u, ∃ n, n ∈ N /\ u = \[ (ConstSeq n) \] \}.
Definition HR_Z := \{ λ u, ∃ z, z ∈ Z /\ u = \[ (ConstSeq z) \] \}.
Definition HR_Q := \{ λ u, ∃ q, q ∈ Q /\ u = \[ (ConstSeq q) \] \}.



Fact HR_N_embeded_HR_R : HR_N = ran(R_and_HR_R|(N)).
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[n[]]]. apply AxiomII; split; auto. exists n.
    assert (Ensemble ([n,z])). apply MKT49a; eauto.
    apply AxiomII; repeat split; auto. apply AxiomII'; repeat split; auto.
    apply N_Subset_R; auto. apply AxiomII'; auto.
  - apply AxiomII in H as [H[]]. apply AxiomII in H0 as [H0[]].
    apply AxiomII' in H1 as [_[]]. rewrite H3. apply AxiomII; split.
    rewrite <-H3; auto. exists x. apply AxiomII' in H2 as [_[]]; auto.
Qed.

Fact HR_Z_embeded_HR_R : HR_Z = ran(R_and_HR_R|(Z)).
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[n[]]]. apply AxiomII; split; auto. exists n.
    assert (Ensemble ([n,z])). apply MKT49a; eauto.
    apply AxiomII; repeat split; auto. apply AxiomII'; repeat split; auto.
    apply Z_Subset_R; auto. apply AxiomII'; auto.
  - apply AxiomII in H as [H[]]. apply AxiomII in H0 as [H0[]].
    apply AxiomII' in H1 as [_[]]. rewrite H3. apply AxiomII; split.
    rewrite <-H3; auto. exists x. apply AxiomII' in H2 as [_[]]; auto.
Qed.

Fact HR_Q_embeded_HR_R : HR_Q = ran(R_and_HR_R|(Q)).
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[n[]]]. apply AxiomII; split; auto. exists n.
    assert (Ensemble ([n,z])). apply MKT49a; eauto.
    apply AxiomII; repeat split; auto. apply AxiomII'; repeat split; auto.
    apply Q_Subset_R; auto. apply AxiomII'; auto.
  - apply AxiomII in H as [H[]]. apply AxiomII in H0 as [H0[]].
    apply AxiomII' in H1 as [_[]]. rewrite H3. apply AxiomII; split.
    rewrite <-H3; auto. exists x. apply AxiomII' in H2 as [_[]]; auto.
Qed.

Fact HR_N_subset_HR : HR_N ⊂ HR.
Proof.
  red; intros. apply AxiomII in H as [H[n[]]]. apply AxiomII; split. auto.
  exists (ConstSeq n). split; auto. apply ConstSeq_is_Seq; auto with real.
Qed.

Fact HR_Z_subset_HR : HR_Z ⊂ HR.
Proof.
  red; intros. apply AxiomII in H as [H[n[]]]. apply AxiomII; split. auto.
  exists (ConstSeq n). split; auto. apply ConstSeq_is_Seq; auto with real.
Qed.

Fact HR_Q_subset_HR : HR_Q ⊂ HR.
Proof.
  red; intros. apply AxiomII in H as [H[q[]]]. apply AxiomII; split. auto.
  exists (ConstSeq q). split; auto. apply ConstSeq_is_Seq; auto with real.
Qed.

Fact HR_N_subset_HR_R : HR_N ⊂ HR_R.
Proof.
  red; intros. apply AxiomII in H as [H[n[]]]. apply AxiomII; split. auto.
  exists n. split; auto. apply N_Subset_R; auto.
Qed.

Fact HR_Z_subset_HR_R : HR_Z ⊂ HR_R.
Proof.
  red; intros. apply AxiomII in H as [H[n[]]]. apply AxiomII; split. auto.
  exists n. split; auto. apply Z_Subset_R; auto.
Qed.

Fact HR_Q_subset_HR_R : HR_Q ⊂ HR_R.
Proof.
  red; intros. apply AxiomII in H as [H[n[]]]. apply AxiomII; split. auto.
  exists n. split; auto. apply Q_Subset_R; auto.
Qed.

Fact HR_N_isnot_HR_R : HR_N <> HR_R.
Proof.
  intro. New HR_Zero_in_HR.
  assert (0%hr ∈ HR_R).
  { apply AxiomII; split. eauto. exists 0%r. split; auto with real. }
  rewrite <-H in H1. apply AxiomII in H1 as [H1[x[]]]. unfold HR_Zero in H3.
  New zero_in_R. apply ConstSeq_is_Seq in H4. apply equClassT1 in H3; auto.
  apply AxiomII' in H3 as [_[H3[]]].
  assert (\{ λ u, u ∈ N /\ (ConstSeq 0%r)%seq[u] = (ConstSeq x)[u] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H7 as [H7[]].
    rewrite ConstSeq_Value,ConstSeq_Value in H9; auto with real.
    rewrite <-H9 in H2. destruct one_is_min_in_N as [_[]]. apply H11 in H2.
    destruct OrderPM_Co9. elim H13. apply Leq_P2; auto with real.
    elim (@ MKT16 z); auto. }
  rewrite H7 in H6. destruct F0_is_NPUF_over_N as [[[_[]]]].
  contradiction. apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply ConstSeq_is_Seq. apply N_Subset_R; auto.
Qed.

Fact HR_Z_isnot_HR_R : HR_Z <> HR_R.
Proof.
  intro. New Existence_of_irRational_Number. apply NEexE in H0 as [r].
  assert (\[ ConstSeq r \] ∈ HR_R).
  { apply AxiomII; split. apply Hyperreal_is_set. exists r. split; auto.
    apply MKT4' in H0; tauto. }
  rewrite <-H in H1. apply AxiomII in H1 as [H1[z[]]].
  assert (z ∈ R /\ r ∈ R) as [].
  { split. apply Z_Subset_R; auto. apply MKT4' in H0; tauto. }
  apply equClassT1 in H3; try apply ConstSeq_is_Seq; auto.
  apply AxiomII' in H3 as [H3[H6[]]].
  assert (\{ λ u, u ∈ N /\ (ConstSeq r)[u] = (ConstSeq z)[u] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H9 as [H9[]].
    rewrite ConstSeq_Value,ConstSeq_Value in H11; auto. rewrite H11 in H0.
    apply MKT4' in H0 as []. apply AxiomII in H12 as []. elim H13.
    apply Z_Subset_Q; auto. elim (@ MKT16 z0); auto. }
  rewrite H9 in H8. destruct F0_is_NPUF_over_N as [[[_[]]]]; auto.
  apply Equ_NPUF_is_equRelation_over_Rᴺ; auto.
Qed.

Fact HR_Q_isnot_HR_R : HR_Q <> HR_R.
Proof.
  intro. New Existence_of_irRational_Number. apply NEexE in H0 as [r].
  assert (\[ ConstSeq r \] ∈ HR_R).
  { apply AxiomII; split. apply Hyperreal_is_set. exists r. split; auto.
    apply MKT4' in H0; tauto. }
  rewrite <-H in H1. apply AxiomII in H1 as [H1[z[]]].
  assert (z ∈ R /\ r ∈ R) as [].
  { split. apply Q_Subset_R; auto. apply MKT4' in H0; tauto. }
  apply equClassT1 in H3; try apply ConstSeq_is_Seq; auto.
  apply AxiomII' in H3 as [H3[H6[]]].
  assert (\{ λ u, u ∈ N /\ (ConstSeq r)[u] = (ConstSeq z)[u] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H9 as [H9[]].
    rewrite ConstSeq_Value,ConstSeq_Value in H11; auto. rewrite H11 in H0.
    apply MKT4' in H0 as []. apply AxiomII in H12 as []. elim H13; auto.
    elim (@ MKT16 z0); auto. }
  rewrite H9 in H8. destruct F0_is_NPUF_over_N as [[[_[]]]]; auto.
  apply Equ_NPUF_is_equRelation_over_Rᴺ; auto.
Qed.



Fact HR_N_subset_HR_Z : HR_N ⊂ HR_Z.
Proof.
  red; intros. apply AxiomII in H as [H[n[]]]. apply AxiomII; split. auto.
  exists n. split; auto. apply N_Subset_Z; auto.
Qed.

Fact HR_Z_subset_HR_Q : HR_Z ⊂ HR_Q.
Proof.
  red; intros. apply AxiomII in H as [H[n[]]]. apply AxiomII; split. auto.
  exists n. split; auto. apply Z_Subset_Q; auto.
Qed.

Fact HR_N_subset_HR_Q : HR_N ⊂ HR_Q.
Proof.
  red; intros. apply AxiomII in H as [H[n[]]]. apply AxiomII; split. auto.
  exists n. split; auto. apply Z_Subset_Q,N_Subset_Z; auto.
Qed.

Fact HR_N_isnot_HR_Z : HR_N <> HR_Z.
Proof.
  intro. New HR_Zero_in_HR.
  assert (0%hr ∈ HR_Z).
  { apply AxiomII; split. eauto. exists 0%r. split; auto.
    apply MKT4. right. apply MKT4. right. apply MKT41; eauto with real. }
  rewrite <-H in H1. apply AxiomII in H1 as [H1[x[]]]. unfold HR_Zero in H3.
  New zero_in_R. apply ConstSeq_is_Seq in H4. apply equClassT1 in H3; auto.
  apply AxiomII' in H3 as [_[H3[]]].
  assert (\{ λ u, u ∈ N /\ (ConstSeq 0%r)%seq[u] = (ConstSeq x)[u] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H7 as [H7[]].
    rewrite ConstSeq_Value,ConstSeq_Value in H9; auto with real.
    rewrite <-H9 in H2. elim zero_not_in_N; auto. elim (@ MKT16 z); auto. }
  rewrite H7 in H6. destruct F0_is_NPUF_over_N as [[[_[]]]].
  contradiction. apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply ConstSeq_is_Seq. apply N_Subset_R; auto.
Qed.

Fact HR_Z_isnot_HR_Q : HR_Z <> HR_Q.
Proof.
  intro. New zero_in_R. New one_in_R. apply MKT4' in H1 as [H1 _].
  New OrderPM_Co9. assert (0%r ∈ Z).
  { apply MKT4; right. apply MKT4; right. apply MKT41; eauto. }
  New one_in_N. apply N_Subset_Z in H4. New H0.
  apply (Arch_P9 0%r 1%r) in H5 as [q[H5[]]]; auto.
  assert (\[ ConstSeq q \] ∈ HR_Q).
  { apply AxiomII; split; eauto. apply Hyperreal_is_set. }
  rewrite <-H in H8. apply AxiomII in H8 as [H8[z[]]].
  apply equClassT1 in H10; try apply ConstSeq_is_Seq; auto with real.
  apply AxiomII' in H10 as [H10[H11[]]].
  assert (\{ λ u, u ∈ N /\ (ConstSeq q)[u] = (ConstSeq z)[u] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H14 as [_[]].
    rewrite ConstSeq_Value,ConstSeq_Value in H15; auto with real.
    rewrite <-H15 in H9. apply Arch_P3_Lemma in H6; auto.
    rewrite Plus_P4,Plus_P1 in H6; auto. destruct H7. elim H16.
    apply Leq_P2; auto with real. elim (@ MKT16 z0); auto. }
  destruct F0_is_NPUF_over_N as [[[_[]]_]_].
  rewrite H14 in H13; auto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
Qed.

Fact HR_N_isnot_HR_Q : HR_N <> HR_Q.
Proof.
  intro. New HR_Zero_in_HR.
  assert (0%hr ∈ HR_Q).
  { apply AxiomII; split. eauto. exists 0%r. split; auto. apply Z_Subset_Q.
    apply MKT4. right. apply MKT4. right. apply MKT41; eauto with real. }
  rewrite <-H in H1. apply AxiomII in H1 as [H1[x[]]]. unfold HR_Zero in H3.
  New zero_in_R. apply ConstSeq_is_Seq in H4. apply equClassT1 in H3; auto.
  apply AxiomII' in H3 as [_[H3[]]].
  assert (\{ λ u, u ∈ N /\ (ConstSeq 0%r)%seq[u] = (ConstSeq x)[u] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H7 as [H7[]].
    rewrite ConstSeq_Value,ConstSeq_Value in H9; auto with real.
    rewrite <-H9 in H2. destruct one_is_min_in_N as [_[]]. apply H11 in H2.
    destruct OrderPM_Co9. elim H13. apply Leq_P2; auto with real.
    elim (@ MKT16 z); auto. }
  rewrite H7 in H6. destruct F0_is_NPUF_over_N as [[[_[]]]].
  contradiction. apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply ConstSeq_is_Seq. apply N_Subset_R; auto.
Qed.



Fact HR_One_in_HR_N : 1 ∈ HR_N.
Proof.
  apply AxiomII; split. apply Hyperreal_is_set. exists 1%r.
  split; auto. apply one_in_N.
Qed.

Fact HR_1_leq_n : ∀ n, n ∈ HR_N -> (1 ≤ n)%hr.
Proof.
  intros. apply AxiomII in H as [H[x[]]]. rewrite H1.
  apply HR_Leq_Instantiate; try apply ConstSeq_is_Seq; auto with real.
  assert (\{ λ w, w ∈ N /\ ((ConstSeq 1)[w] ≤ (ConstSeq x)[w])%r \} = N).
  { apply AxiomI; split; intros. apply AxiomII in H2; tauto.
    apply AxiomII; repeat split; eauto. repeat rewrite ConstSeq_Value;
    auto with real. destruct one_is_min_in_N as [_[]]; auto. }
  rewrite H2. destruct F0_is_NPUF_over_N as [[[_[_[]]]]]; auto.
Qed.

Fact HR_0_less_n : ∀ n, n ∈ HR_N -> (0 < n)%hr.
Proof.
  intros. apply (HR_Less_Transitivity_Co 0 1). apply HR_Zero_in_HR.
  apply HR_One_in_HR. apply HR_N_subset_HR; auto. left. split.
  apply HR_0_less_1. apply HR_1_leq_n; auto.
Qed.

Fact HR_Zero_notin_HR_N : 0 ∉ HR_N.
Proof.
  intro. apply AxiomII in H as [H[n[]]]. apply equClassT1 in H1;
  try apply ConstSeq_is_Seq; auto with real. apply AxiomII' in H1 as [_[H1[]]].
  assert (\{ λ u, u ∈ N /\ (ConstSeq 0%r)[u] = (ConstSeq n)[u] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H4 as [H4[]].
    rewrite ConstSeq_Value,ConstSeq_Value in H6; auto with real.
    rewrite <-H6 in H0. destruct one_is_min_in_N as [_[_]].
    apply H7 in H0. destruct OrderPM_Co9. elim H9.
    apply Leq_P2; auto with real. elim (@ MKT16 z); auto. }
  rewrite H4 in H3. destruct F0_is_NPUF_over_N as [[[_[]]_]_]; auto.
  apply Equ_NPUF_is_equRelation_over_Rᴺ.
Qed.

Fact HR_negOne_notin_HR_N : (-(1)) ∉ HR_N.
Proof.
  intro. unfold "1" in H. rewrite HR_Neg_Instantiate in H;
  [ |apply ConstSeq_is_Seq; auto with real].
  apply AxiomII in H as [H[n[]]].
  apply equClassT1 in H1; try apply Seq_Neg_Close; try apply ConstSeq_is_Seq;
  auto with real. apply AxiomII' in H1 as [H1[H2[]]].
  assert (\{ λ u, u ∈ N /\ (-(ConstSeq 1%r))%seq[u] = (ConstSeq n)[u] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H5 as [H5[]].
    rewrite Seq_Neg_Property,ConstSeq_Value,ConstSeq_Value in H7;
    try apply ConstSeq_is_Seq; auto with real.
    rewrite <-H7 in H0. destruct one_is_min_in_N as [_[_]]. apply H8 in H0.
    assert (-(1) < 0)%r. { apply OrderPM_Co2a; auto with real. }
    assert (1 < 0)%r. { apply (Order_Co2 _ (-(1))%r); auto with real. }
    destruct H10,OrderPM_Co9. elim H13. apply Leq_P2; auto with real.
    elim (@ MKT16 z); auto. }
  rewrite H5 in H4. destruct F0_is_NPUF_over_N as [[[_[]]_]_]; auto.
  apply Equ_NPUF_is_equRelation_over_Rᴺ.
Qed.

Fact HR_One_in_HR_Z : 1 ∈ HR_Z.
Proof. apply HR_N_subset_HR_Z,HR_One_in_HR_N. Qed.

Fact HR_Zero_in_HR_Z : 0 ∈ HR_Z.
Proof.
  apply AxiomII; split. apply Hyperreal_is_set. exists 0%r. split; auto.
  apply MKT4; right. apply MKT4; right. apply MKT41; eauto with real.
Qed.

Fact HR_negOne_in_HR_Z : (-(1)) ∈ HR_Z.
Proof.
  unfold "1". rewrite HR_Neg_Instantiate; try apply ConstSeq_is_Seq;
  auto with real. apply AxiomII; split. apply Hyperreal_is_set.
  exists (-(1))%r. split. apply MKT4; right. apply MKT4; left.
  apply AxiomII; split. eauto with real. rewrite PlusMult_Co3,PlusMult_Co4;
  auto with real. rewrite ConstSeq_Neg; auto with real.
Qed.

Fact HR_One_in_HR_Q : 1 ∈ HR_Q.
Proof. apply HR_Z_subset_HR_Q,HR_One_in_HR_Z. Qed.

Fact HR_Zero_in_HR_Q : 0 ∈ HR_Q.
Proof. apply HR_Z_subset_HR_Q,HR_Zero_in_HR_Z. Qed.

Fact HR_negOne_in_HR_Q : (-(1)) ∈ HR_Q.
Proof. apply HR_Z_subset_HR_Q,HR_negOne_in_HR_Z. Qed.

(* 自然数的最小值 *)
Fact HR_N_1_is_least : ∀ n, n ∈ HR_N -> 1 ≤ n.
Proof.
  intros. apply AxiomII in H as [H[x[]]]. rewrite H1.
  apply HR_Leq_Instantiate; try apply ConstSeq_is_Seq; auto with real.
  assert (\{ λ w, w ∈ N /\ ((ConstSeq 1)[w] ≤ (ConstSeq x)[w])%r \} = N).
  { apply AxiomI; split; intros. apply AxiomII in H2; tauto.
    apply AxiomII; repeat split; eauto.
    rewrite ConstSeq_Value,ConstSeq_Value; auto with real.
    destruct one_is_min_in_N as [_[_]]; auto. }
  rewrite H2. destruct F0_is_NPUF_over_N as [[[_[_[]]]_]_]; auto.
Qed.

Fact HR_N_larger_than_0 : ∀ n, n ∈ HR_N -> 0 < n.
Proof.
  intros. destruct HR_0_less_1. New H. apply HR_N_1_is_least in H2.
  assert (0 ≤ n).
  { apply (HR_Leq_Transitivity 0 1); auto. apply HR_Zero_in_HR.
    apply HR_One_in_HR. apply HR_N_subset_HR; auto. }
  split; auto. intro. rewrite <-H4 in H2. elim H1. apply HR_Leq_Asymmetry; auto.
  apply HR_Zero_in_HR. apply HR_One_in_HR.
Qed.

(* 整数具有离散型 *)
Fact HR_Z_Discrete_a : ∀ u v, u ∈ HR_Z -> v ∈ HR_Z -> u < v <-> (u + 1) ≤ v.
Proof.
  split; intros.
  - apply AxiomII in H as [H[x[]]], H0 as [H0[y[]]].
    rewrite H3,H5 in H1. apply HR_Less_Instantiate in H1;
    try apply ConstSeq_is_Seq; auto with real. unfold "1".
    rewrite H3,H5,HR_Plus_Instantiate; try apply ConstSeq_is_Seq; auto with real.
    rewrite ConstSeq_Plus; auto with real. apply HR_Leq_Instantiate;
    try apply ConstSeq_is_Seq; auto with real.
    assert (\{ λ w, w ∈ N /\ ((ConstSeq x)[w] < (ConstSeq y)[w])%r \}
      ⊂ \{ λ w, w ∈ N /\ ((ConstSeq (x + 1))[w] ≤ (ConstSeq y)[w])%r \}).
    { red; intros. apply AxiomII in H6 as [H6[]]. apply AxiomII; repeat split;
      auto. repeat rewrite ConstSeq_Value; auto with real.
      rewrite ConstSeq_Value,ConstSeq_Value in H8; auto with real.
      apply Arch_P3_Lemma; auto. }
    destruct F0_is_NPUF_over_N as [[[_[_[_[]]]]_]_].
    apply H8 in H6; auto. red; intros. apply AxiomII in H9; tauto.
  - apply HR_Z_subset_HR in H,H0. assert (u + 0 < u + 1).
    { rewrite HR_Plus_Com,(HR_Plus_Com u). apply HR_Less_Pr_Plus; auto.
      apply HR_Zero_in_HR. apply HR_One_in_HR. apply HR_0_less_1. }
    rewrite HR_Plus_0 in H2; auto.
    apply (HR_Less_Transitivity_Co _ (u + 1)); auto.
    apply HR_Plus_Close; auto. apply HR_One_in_HR.
Qed.

Fact HR_Z_Discrete_b : ∀ u v, u ∈ HR_Z -> v ∈ HR_Z -> ~ (u < v /\ v < (u + 1)).
Proof.
  intros. intro. destruct H1. apply HR_Z_Discrete_a in H1; auto.
  destruct H2. apply H3,HR_Leq_Asymmetry; try apply HR_Plus_Close;
  try apply HR_Z_subset_HR; auto. apply HR_One_in_HR_Z.
Qed.


(* 各个集合之间满足通常自然数、整数和有理数的关系 *)
Fact HR_N_and_HR_Z_a1 : HR_Z = \{ λ u, ∃ n, n ∈ HR_N /\ u = -n \} ∪ [0] ∪ HR_N.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[x[]]]. apply MKT4 in H0 as [].
    apply MKT4; right. apply MKT4; right. apply AxiomII; split; eauto.
    apply MKT4 in H0 as []. apply MKT4; left. apply AxiomII; split. auto.
    exists \[ ConstSeq (-x)%r \]. apply AxiomII in H0 as []. split.
    apply AxiomII; split; eauto. apply Hyperreal_is_set.
    rewrite HR_Neg_Instantiate,ConstSeq_Neg; try apply ConstSeq_is_Seq;
    auto with real. rewrite PlusMult_Co3,PlusMult_Co4; auto with real.
    apply MKT41 in H0; eauto with real. apply MKT4; right. apply MKT4; left.
    apply MKT41. apply Hyperreal_is_set. rewrite H0 in H1; auto.
  - apply MKT4 in H as []. apply AxiomII in H as [H[x[]]].
    apply AxiomII in H0 as [H0[n[]]].
    rewrite H3,HR_Neg_Instantiate,ConstSeq_Neg in H1; try apply ConstSeq_is_Seq;
    auto with real. apply AxiomII; split; auto. exists (-n)%r. split; auto.
    apply MKT4; right. apply MKT4; left. apply AxiomII; split.
    eauto with real. rewrite PlusMult_Co3,PlusMult_Co4; auto with real.
    apply MKT4 in H as []. apply MKT41 in H. rewrite H. apply HR_Zero_in_HR_Z.
    apply Hyperreal_is_set. apply AxiomII in H as [H[n[]]].
    apply AxiomII; split; auto. exists n. split; auto with real.
Qed.

Fact HR_N_and_HR_Z_a2 : ∀ n, n ∈ HR_N -> (-n) ∈ HR_Z.
Proof.
  intros. rewrite HR_N_and_HR_Z_a1. apply MKT4; left.
  apply AxiomII; split; eauto. apply HR_N_subset_HR in H.
  apply HR_Neg_Close in H; eauto.
Qed.

Fact HR_N_and_HR_Z_b1 : HR_N = \{ λ n, n ∈ HR_Z /\ 0 < n \}.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII; split. eauto. split. apply HR_N_subset_HR_Z; auto.
    apply HR_N_larger_than_0; auto.
  - apply AxiomII in H as [H[]]. rewrite HR_N_and_HR_Z_a1 in H0.
    apply MKT4 in H0 as []. apply AxiomII in H0 as [H0[n[]]]. rewrite H3 in H1.
    assert (-n < 0).
    { split. apply AxiomII in H2 as [H2[x[]]]. rewrite H5,HR_Neg_Instantiate,
      ConstSeq_Neg; try apply ConstSeq_is_Seq; auto with real.
      apply HR_Leq_Instantiate; try apply ConstSeq_is_Seq; auto with real.
      assert (\{ λ w, w ∈ N /\ ((ConstSeq (-x))[w] ≤ (ConstSeq 0)[w])%r \} = N).
      { apply AxiomI; split; intros. apply AxiomII in H6; tauto.
        apply AxiomII; split. eauto. split; auto.
        rewrite ConstSeq_Value,ConstSeq_Value; auto with real.
        apply OrderPM_Co2b; auto with real. destruct one_is_min_in_N as [_[_]].
        New H4. apply H7 in H8. apply (Leq_P3 _ 1%r); auto with real.
        destruct OrderPM_Co9; auto. }
      rewrite H6. destruct F0_is_NPUF_over_N as [[[_[_[]]]]]; auto.
      intro. rewrite H4 in H1. destruct H1; auto. }
    destruct H1,H4. elim H6. apply HR_Leq_Asymmetry; auto.
    apply ->HR_Neg_Close; apply HR_N_subset_HR; auto. apply HR_Zero_in_HR.
    apply MKT4 in H0 as []; auto. apply MKT41 in H0. rewrite H0 in H1.
    destruct H1. elim H2; auto. apply Hyperreal_is_set.
Qed.

Fact HR_N_and_HR_Z_b2 : ∀ n, (n ∈ HR_Z /\ 0 < n) <-> n ∈ HR_N.
Proof.
  intros. split; intros. rewrite HR_N_and_HR_Z_b1. apply AxiomII; split; auto.
  destruct H. eauto. rewrite HR_N_and_HR_Z_b1 in H. apply AxiomII in H; tauto.
Qed.

Fact HR_Z_and_HR_Q_a : HR_Q = \{ λ q, ∃ u v, u ∈ HR_Z /\ v ∈ HR_Z /\ v <> 0
  /\ q = u/v \}.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[q[]]]. apply AxiomII; split; auto.
    New H0. apply AxiomII in H2 as [H2[a[b[H3[]]]]]. apply MKT4' in H4 as [].
    apply AxiomII in H6 as [_]. assert (b <> 0%r).
    { intro. elim H6. apply MKT41; eauto with real. }
    exists \[ ConstSeq a \], \[ ConstSeq b \].
    repeat split; try (apply AxiomII; split; eauto; apply Hyperreal_is_set).
    intro. apply HR_R_Element_Property in H8; auto with real.
    assert (\[ ConstSeq b \] <> 0).
    { intro. apply HR_R_Element_Property in H8; auto with real. }
    apply HR_Inv_Instantiate in H8; try apply ConstSeq_is_Seq; auto with real.
    assert (b ∈ R ~ [0%r]).
    { apply MKT4'; split. auto with real. apply AxiomII; split. eauto. intro.
      apply MKT41 in H9; eauto with real. } apply Mult_inv1,MKT4' in H9 as [].
    rewrite H8,ConstSeq_Inv,HR_Mult_Instantiate; try apply ConstSeq_is_Seq;
    auto with real. rewrite H1,ConstSeq_Mult,H5; auto with real.
  - apply AxiomII in H as [H[a[b[H0[H1[]]]]]].
    apply AxiomII in H0 as [H0[x[]]], H1 as [H1[y[]]].
    assert (y <> 0%r). { intro. elim H2. rewrite H7,H8; auto. }
    New H6. apply Z_Subset_R,ConstSeq_is_Seq in H9.
    New H2. rewrite H7 in H10. apply HR_Inv_Instantiate in H10; auto.
    apply AxiomII; split. auto. exists (x/y)%r.
    assert (y ∈ R ~ [0%r]).
    { apply MKT4'; split; auto with real. apply AxiomII; split; eauto.
      intro. apply MKT41 in H11; eauto with real. } New H11.
    apply Mult_inv1,MKT4' in H12 as []. split. apply AxiomII; split;
    eauto with real. exists x,y. repeat split; auto. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. intro. apply MKT41 in H14; eauto with real.
    rewrite H3,H5,H7,H10,HR_Mult_Instantiate,ConstSeq_Inv;
    try apply Seq_Inv_Close; try apply ConstSeq_is_Seq; auto with real.
    rewrite ConstSeq_Mult; auto with real.
Qed.

Fact HR_Z_and_HR_Q_b : ∀ u v, u ∈ HR_Z -> v ∈ HR_Z -> v <> 0 -> u/v ∈ HR_Q.
Proof.
  intros. rewrite HR_Z_and_HR_Q_a. apply AxiomII; split.
  exists HR. apply HR_Div_Close; auto; apply HR_Z_subset_HR; auto.
  exists u,v; auto.
Qed.


(***  R_and_HR_R|(N) 即为 N 与 HR_N 之间的同构函数,
      其同构性已由 R_and_HR_R 自身的同构性得到保证,
      下面只需再验证运算在各自数集中的封闭性  ***)

(*** 验证 HR_N 中运算的封闭性 ***)
(* 加法封闭 *)
Property HR_N_Plus_Close : ∀ u v, u ∈ HR_N -> v ∈ HR_N -> (u + v) ∈ HR_N.
Proof.
  intros. apply AxiomII in H as [H[x[]]], H0 as [H0[y[]]].
  rewrite H2,H4,HR_Plus_Instantiate,ConstSeq_Plus; try apply ConstSeq_is_Seq;
  auto with real. apply AxiomII; split. apply Hyperreal_is_set.
  exists (x + y)%r. split; auto with real.
Qed.

(* 乘法封闭 *)
Property HR_N_Mult_Close : ∀ u v, u ∈ HR_N -> v ∈ HR_N -> (u · v) ∈ HR_N.
Proof.
  intros. apply AxiomII in H as [H[x[]]], H0 as [H0[y[]]].
  rewrite H2,H4,HR_Mult_Instantiate,ConstSeq_Mult; try apply ConstSeq_is_Seq;
  auto with real. apply AxiomII; split. apply Hyperreal_is_set.
  exists (x · y)%r. split; auto with real.
Qed.

(* 负元不封闭 *)
Property HR_N_Neg_notClose : ∀ r, r ∈ HR_N -> (-r) ∉ HR_N.
Proof.
  intros. rewrite HR_N_and_HR_Z_b1 in H. apply AxiomII in H as [H[]].
  New H0. apply HR_Z_subset_HR in H2. apply HR_neg_less_0 in H1; auto.
  intro. rewrite HR_N_and_HR_Z_b1 in H3. apply AxiomII in H3 as [H3[]].
  destruct H1,H5. elim H7. apply HR_Leq_Asymmetry; auto. apply HR_Zero_in_HR.
  apply ->HR_Neg_Close; auto.
Qed.

(* 逆元不封闭 *)
Property HR_N_Inv_notClose : ∀ r, r ∈ HR_N -> r <> 1 -> (r⁻) ∉ HR_N.
Proof.
  intros. New H. apply HR_1_leq_n in H1. assert (1 < r). { split; auto. }
  New H. apply HR_N_subset_HR in H3. apply HR_inv_less_1 in H2 as []; auto.
  intro. New H5. apply HR_1_leq_n in H6. destruct H4.
  apply H7,HR_Leq_Asymmetry; auto. apply HR_N_subset_HR; auto.
  apply HR_One_in_HR.
Qed.

(* 绝对值封闭 *)
Property HR_N_Abs_Close : ∀ r, r ∈ HR_N -> ∣r∣ = r.
Proof.
  intros. New H. apply HR_N_subset_HR in H0.
  apply HR_Abs_Pos; auto. apply HR_0_less_n; auto.
Qed.


(*** 验证 HR_Z 中运算的封闭性 ***)
(* 加法封闭 *)
Property HR_Z_Plus_Close : ∀ u v, u ∈ HR_Z -> v ∈ HR_Z -> (u + v) ∈ HR_Z.
Proof.
  intros. apply AxiomII in H as [H[x[]]], H0 as [H0[y[]]].
  rewrite H2,H4,HR_Plus_Instantiate,ConstSeq_Plus; try apply ConstSeq_is_Seq;
  auto with real. apply AxiomII; split. apply Hyperreal_is_set.
  exists (x + y)%r. split; auto with real.
Qed.

(* 乘法封闭 *)
Property HR_Z_Mult_Close : ∀ u v, u ∈ HR_Z -> v ∈ HR_Z -> (u · v) ∈ HR_Z.
Proof.
  intros. apply AxiomII in H as [H[x[]]], H0 as [H0[y[]]].
  rewrite H2,H4,HR_Mult_Instantiate,ConstSeq_Mult; try apply ConstSeq_is_Seq;
  auto with real. apply AxiomII; split. apply Hyperreal_is_set.
  exists (x · y)%r. split; auto with real.
Qed.

(* 负元封闭 *)
Property HR_Z_Neg_Close : ∀ r, r ∈ HR_Z <-> (-r) ∈ HR_Z.
Proof.
  assert (∀ r, r ∈ HR_Z -> -r ∈ HR_Z).
  { intros. apply AxiomII in H as [H[x[]]].
    rewrite H1,HR_Neg_Instantiate,ConstSeq_Neg; try apply ConstSeq_is_Seq;
    eauto with real. New H0. apply Int_P3 in H2 as [H2 _].
    apply AxiomII; repeat split; eauto. apply Hyperreal_is_set. }
  split; intros; auto. New H0. apply HR_Z_subset_HR,HR_Neg_Close in H1.
  apply H in H0. rewrite HR_Double_Neg in H0; auto.
Qed.

(* 负元封闭推论 *)
Corollary HR_Z_Neg_Close_Co : ∀ r, (r ∈ HR_Z /\ r < 0) <-> (-r) ∈ HR_N.
Proof.
  split; intros. destruct H. apply HR_N_and_HR_Z_b2. split.
  apply ->HR_Z_Neg_Close; auto. apply HR_0_less_neg; auto.
  apply HR_Z_subset_HR; auto. New H. apply HR_N_subset_HR in H0.
  apply HR_Neg_Close in H0. rewrite <-(HR_Double_Neg r); auto.
  apply HR_N_and_HR_Z_b2 in H as []. split. apply ->HR_Z_Neg_Close; auto.
  apply HR_neg_less_0; auto. apply ->HR_Neg_Close; auto.
Qed.

(* 减法封闭 *)
Property HR_Z_Minus_Close : ∀ u v, u ∈ HR_Z -> v ∈ HR_Z -> (u - v) ∈ HR_Z.
Proof. intros. apply HR_Z_Plus_Close; auto. apply ->HR_Z_Neg_Close; auto. Qed.

(* 减法封闭推论 *)
Corollary HR_Z_Minus_Close_Co : ∀ u v, u ∈ HR_Z -> v ∈ HR_Z -> v < u
  -> (u - v) ∈ HR_N.
Proof.
  intros. apply HR_N_and_HR_Z_b2; split. apply HR_Z_Minus_Close; auto.
  apply ->HR_Less_Pr_Plus_Co; auto; apply HR_Z_subset_HR; auto.
Qed.

(* 减法在HR_N中有条件封闭 *)
Corollary HR_N_Minus_Close : ∀ u v, u ∈ HR_N -> v ∈ HR_N -> v < u
  -> (u - v) ∈ HR_N.
Proof.
  intros. apply HR_Z_Minus_Close_Co; auto; apply HR_N_subset_HR_Z; auto.
Qed.

(* 逆元不封闭 *)
Property HR_Z_Inv_notClose : ∀ r, r ∈ HR_Z -> r <> 1 -> r <> -(1) -> (r⁻) ∉ HR_Z.
Proof.
  intros. destruct (classic (r = 0)). rewrite H2,HR_Inv_0_is_universe.
  intro. apply MKT39; eauto. New HR_One_in_HR. New HR_Zero_in_HR.
  New HR_One_in_HR. apply HR_Neg_Close in H5. New H. apply HR_Z_subset_HR in H6.
  New HR_One_in_HR_Z. New H7. apply HR_Z_Neg_Close in H8. New HR_Zero_in_HR_Z.
  assert (r < -(1) \/ 1 < r).
  { destruct (HR_Less_Trichotomy (-(1)) r) as [H10|[]]; auto.
    apply HR_Z_Discrete_a in H10; auto. rewrite HR_Plus_Com,HR_r_Minus_r in H10;
    auto. assert (0 < r). split; auto. apply HR_Z_Discrete_a in H11; auto.
    rewrite HR_0_Plus in H11; auto. elim H1; auto. }
  destruct H10; intro. apply HR_neg1_less_inv in H10 as []; auto.
  apply HR_Z_Discrete_a in H10; auto.
  rewrite HR_Plus_Com,HR_r_Minus_r in H10; auto. destruct H12. elim H13.
  apply HR_Leq_Asymmetry; auto. apply HR_Z_subset_HR; auto.
  apply HR_inv_less_1 in H10 as []; auto. apply HR_Z_Discrete_a in H10; auto.
  rewrite HR_0_Plus in H10; auto. destruct H12. apply H13,HR_Leq_Asymmetry; auto.
  apply HR_Z_subset_HR; auto.
Qed.

(* 绝对值封闭 *)
Property HR_Z_Abs_Close : ∀ r, r ∈ HR_Z <-> ∣r∣ ∈ HR_Z.
Proof.
  split; intros.
  - New H. apply HR_Z_subset_HR in H0.
    apply HR_Abs_Value in H0 as []; rewrite H0; auto.
    apply ->HR_Z_Neg_Close; auto.
  - New H. apply HR_Z_subset_HR,HR_Abs_Close in H0.
    apply HR_Abs_Value in H0 as []. rewrite <-H0; auto. rewrite H0 in H.
    apply HR_Z_Neg_Close; auto.
Qed.


(*** 验证 R_and_HR_Q 中运算的封闭性 ***)
(* 加法封闭 *)
Property HR_Q_Plus_Close : ∀ u v, u ∈ HR_Q -> v ∈ HR_Q -> (u + v) ∈ HR_Q.
Proof.
  intros. apply AxiomII in H as [H[x[]]], H0 as [H0[y[]]].
  rewrite H2,H4,HR_Plus_Instantiate,ConstSeq_Plus; try apply ConstSeq_is_Seq;
  auto with real. apply AxiomII; split. apply Hyperreal_is_set.
  exists (x + y)%r. split; auto with real.
Qed.

(* 乘法封闭 *)
Property HR_Q_Mult_Close : ∀ u v, u ∈ HR_Q -> v ∈ HR_Q -> (u · v) ∈ HR_Q.
Proof.
  intros. apply AxiomII in H as [H[x[]]], H0 as [H0[y[]]].
  rewrite H2,H4,HR_Mult_Instantiate,ConstSeq_Mult; try apply ConstSeq_is_Seq;
  auto with real. apply AxiomII; split. apply Hyperreal_is_set.
  exists (x · y)%r. split; auto with real.
Qed.

(* 负元封闭 *)
Property HR_Q_Neg_Close : ∀ r, r ∈ HR_Q <-> (-r) ∈ HR_Q.
Proof.
  assert (∀ r, r ∈ HR_Q -> -r ∈ HR_Q).
  { intros. apply AxiomII in H as [H[x[]]].
    rewrite H1,HR_Neg_Instantiate,ConstSeq_Neg; try apply ConstSeq_is_Seq;
    eauto with real. New H0. apply Rat_P3 in H2 as [H2 _].
    apply AxiomII; repeat split; eauto. apply Hyperreal_is_set. }
  split; intros; auto. New H0. apply HR_Q_subset_HR,HR_Neg_Close in H1.
  apply H in H0. rewrite HR_Double_Neg in H0; auto.
Qed.

(* 减法封闭 *)
Property HR_Q_Minus_Close : ∀ u v, u ∈ HR_Q -> v ∈ HR_Q -> (u - v) ∈ HR_Q.
Proof. intros. apply HR_Q_Plus_Close; auto. apply ->HR_Q_Neg_Close; auto. Qed.

(* 逆元有条件封闭 *)
Property HR_Q_Inv_Close : ∀ r, (r ∈ HR_Q /\ r <> 0) <-> (r⁻) ∈ HR_Q.
Proof.
  assert (∀ r, (r ∈ HR_Q /\ r <> 0) -> (r⁻) ∈ HR_Q).
  { intros. destruct H. New H. apply AxiomII in H1 as [H1[x[]]].
    New H2. apply Q_Subset_R,ConstSeq_is_Seq in H4. New H0. rewrite H3 in H5.
    apply HR_Inv_Instantiate in H5; auto. rewrite H3,H5.
    apply AxiomII; split. apply Hyperreal_is_set.
    assert (x <> 0%r).
    { intro. assert (0⁻ = \[ /ConstSeq x \]). { unfold "0". rewrite <-H6; auto. }
      rewrite HR_Inv_0_is_universe in H7. apply MKT39. rewrite H7.
      apply Hyperreal_is_set. } New H6.
    apply ConstSeq_Inv in H7; auto with real. rewrite H7. exists (x⁻)%r.
    split; auto. assert (x ∈ Q ~ [0%r]).
    { apply MKT4'; split; auto. apply AxiomII; split. eauto. intro.
      apply MKT41 in H8; eauto with real. }
    apply Rat_P7 in H8 as []; auto. }
  split; intros; auto. assert (r <> 0).
  { intro. rewrite H1,HR_Inv_0_is_universe in H0. apply MKT39; eauto. }
  split; auto. assert (r ∈ HR).
  { apply NNPP; intro.
    assert (r⁻ ∉ HR). { intro. apply HR_Inv_Close in H3 as []; auto. }
    apply H3,HR_Q_subset_HR; auto. }
  New H1. apply HR_Double_Inv in H3; auto. rewrite <-H3. apply H; split; auto.
  apply HR_Inv_isnot_0.
Qed.

(* 除法封闭 *)
Property HR_Q_Div_Close : ∀ u v, u ∈ HR_Q -> v ∈ HR_Q
  -> v <> 0 <-> (u/v) ∈ HR_Q.
Proof.
  split; intros. apply HR_Q_Mult_Close; auto. apply ->HR_Q_Inv_Close; auto.
  intro. rewrite H2,HR_Div_0_is_universe in H1. apply MKT39; eauto.
Qed.

(* 绝对值封闭 *)
Property HR_Q_Abs_Close : ∀ r, r ∈ HR_Q <-> ∣r∣ ∈ HR_Q.
Proof.
  split; intros.
  - New H. apply HR_Q_subset_HR in H0.
    apply HR_Abs_Value in H0 as []; rewrite H0; auto.
    apply ->HR_Q_Neg_Close; auto.
  - New H. apply HR_Q_subset_HR,HR_Abs_Close in H0.
    apply HR_Abs_Value in H0 as []. rewrite <-H0; auto. rewrite H0 in H.
    apply HR_Q_Neg_Close; auto.
Qed.

(* 有理数的稠密性 *)
Property HR_Q_Dense : ∀ r1 r2, r1 ∈ HR_R -> r2 ∈ HR_R -> r1 < r2
  -> ∃ q, q ∈ HR_Q /\ r1 < q /\ q < r2.
Proof.
  intros. apply AxiomII in H as [_[x1[]]], H0 as [_[x2[]]]. rewrite H2,H3 in H1.
  apply HR_Less_Instantiate in H1; try apply ConstSeq_is_Seq; auto.
  assert (\{ λ w, w ∈ N /\ ((ConstSeq x1)[w] < (ConstSeq x2)[w])%r \} <> Φ).
  { destruct F0_is_NPUF_over_N as [[[_[]]_]_].
    intro. rewrite H6 in H1; auto. }
  apply NEexE in H4 as []. apply AxiomII in H4 as [_[]].
  rewrite ConstSeq_Value,ConstSeq_Value in H5; auto.
  apply Arch_P9 in H5 as [q0[H5[]]]; auto. exists \[ ConstSeq q0 \].
  split. apply AxiomII. split; eauto. apply Hyperreal_is_set.
  rewrite H2,H3. apply Q_Subset_R in H5.
  assert (\{ λ w, w ∈ N /\ ((ConstSeq x1)[w] < (ConstSeq q0)[w])%r \} = N
    /\ \{ λ w, w ∈ N /\ ((ConstSeq q0)[w] < (ConstSeq x2)[w])%r \} = N) as [].
  { split; apply AxiomI; split; intros; try (apply AxiomII in H8; tauto);
    apply AxiomII; split; eauto; split; auto;
    rewrite ConstSeq_Value,ConstSeq_Value; auto. }
  destruct F0_is_NPUF_over_N as [[[_[_[]]]_]_].
  split; apply HR_Less_Instantiate; try apply ConstSeq_is_Seq; auto;
  [rewrite H8|rewrite H9]; auto.
Qed.


(* 实数的阿基米德性 *)

Property HR_R_Arch_a : ∀ r, r ∈ HR_R
  -> ∃ z, z ∈ HR_Z /\ z ≤ r /\ r < z + 1.
Proof.
  intros. apply AxiomII in H as [H[x[]]].
  New H0. apply Arch_P10 in H2 as [y[[H2[]]_]]. exists \[ ConstSeq y \].
  split. apply AxiomII; split; eauto. apply Hyperreal_is_set. rewrite H1.
  New H0. New H2. apply Z_Subset_R in H6. New one_in_R_Co.
  apply ConstSeq_is_Seq in H5,H6,H7.
  destruct F0_is_NPUF_over_N as [[[_[_[H8 _]]]_]_]. split.
  - apply HR_Leq_Instantiate; auto.
    assert (\{ λ w, w ∈ N /\ ((ConstSeq y)[w] ≤ (ConstSeq x)[w])%r \} = N).
    { apply AxiomI; split; intros. apply AxiomII in H9; tauto.
      apply AxiomII; repeat split; eauto.
      rewrite ConstSeq_Value,ConstSeq_Value; auto with real. }
    rewrite H9; auto.
  - unfold "1". rewrite HR_Plus_Instantiate,ConstSeq_Plus; auto with real.
    apply HR_Less_Instantiate; auto. apply ConstSeq_is_Seq; auto with real.
    assert (\{ λ w, w ∈ N /\ ((ConstSeq x)[w] < (ConstSeq (y + 1))[w])%r \} = N).
    { apply AxiomI; split; intros. apply AxiomII in H9; tauto.
      apply AxiomII; split. eauto. split; eauto.
      rewrite ConstSeq_Value,ConstSeq_Value; auto with real. }
    rewrite H9; auto.
Qed.

Property HR_R_Arch_b : ∀ r, r ∈ HR_R
  -> ∃ n, (n = 0 \/ n ∈ HR_N) /\ n ≤ ∣r∣ /\ ∣r∣ < n + 1.
Proof.
  intros. New H. apply HR_R_Abs_Close in H0. apply HR_R_Arch_a in H0 as [x[H0[]]].
  New H. apply HR_R_subset_HR in H3. New H3. apply HR_Abs_Close in H4.
  New HR_Zero_in_HR_Z. New HR_Zero_in_HR. New HR_One_in_HR.
  assert (0 ≤ x).
  { New H0. apply HR_Z_subset_HR in H8. New H6. apply (HR_Leq_Trichotomy x)
    in H9 as []; auto. assert (0 < x + 1).
    { apply (HR_Less_Transitivity_Co _ ∣r∣); auto. apply HR_Plus_Close; auto.
      right. split; auto. apply HR_0_leq_abs; auto. }
    apply HR_Z_Discrete_a in H10; auto. apply HR_Leq_Pr_Plus in H10; auto.
    apply HR_Z_Plus_Close; auto. apply HR_One_in_HR_Z. }
  exists x. split; auto. destruct (classic (x = 0)); auto. right.
  apply HR_N_and_HR_Z_b2; auto.
Qed.

Property HR_R_Arch_c : ∀ r, r ∈ HR_R -> ∃ n, n ∈ HR_N /\ ∣r∣ < n.
Proof.
  intros. New H. apply HR_R_Arch_b in H0 as [n[H0[]]]. exists (n + 1).
  split; auto. destruct H0. rewrite H0,HR_0_Plus. apply HR_One_in_HR_N.
  apply HR_One_in_HR. apply HR_N_Plus_Close; auto. apply HR_One_in_HR_N.
Qed.


(* 实数的完备性 *)

(* 实数集的上界和下界 *)
Definition HR_R_Up r A := r ∈ HR_R /\ A ⊂ HR_R /\ (∀ x, x ∈ A -> x ≤ r).
Definition HR_R_Low r A := r ∈ HR_R /\ A ⊂ HR_R /\ (∀ x, x ∈ A -> r ≤ x).

(* 实数集的最大值和最小值 *)
Definition HR_R_Max r A := HR_R_Up r A /\ r ∈ A.
Definition HR_R_Min r A := HR_R_Low r A /\ r ∈ A.

(* 实数集的上确界和下确界 *)
Definition HR_R_Sup r A := HR_R_Up r A
  /\ (∀ x, x ∈ HR_R -> x < r -> (∃ y, y ∈ A /\ x < y)).
Definition HR_R_Inf r A := HR_R_Low r A
  /\ (∀ x, x ∈ HR_R -> r < x -> (∃ y, y ∈ A /\ y < x)).

(* 确界存在性 *)
Property HR_R_Sup_Exists : ∀ r A, A <> Φ -> HR_R_Up r A -> (∃ s, HR_R_Sup s A).
Proof.
  intros. destruct H0 as [H0[]]. New H0. apply AxiomII in H3 as [H3[x[]]].
  destruct R_and_HR_R_is_Function1_1 as [[][]]. set (B := ran(R_and_HR_R⁻¹|(A))).
  assert (B ⊂ R /\ B <> Φ) as [].
  { split. red; intros. apply AxiomII in H10 as [_[]].
    apply AxiomII in H10 as [H10[]]. apply AxiomII' in H11 as [_].
    apply AxiomII' in H11; tauto. apply NEexE in H as []. apply NEexE.
    exists (R_and_HR_R⁻¹)[x0]. assert (x0 ∈ dom(R_and_HR_R⁻¹|(A))).
    { rewrite MKT126b,deqri,MKT61,H9; auto. apply MKT4'; auto.
      destruct H6; auto. } New H10.
    apply Property_Value,Property_ran in H10. rewrite MKT126c in H10; auto.
    apply MKT126a; auto. }
  assert (∃ c, Upper B c).
  { exists x. repeat split; auto. intros.
    assert (R_and_HR_R[x0] ∈ A).
    { apply AxiomII in H12 as [_[]]. apply MKT4' in H12 as [].
      apply AxiomII' in H12 as [_]. apply Property_Fun in H12; auto.
      rewrite <-H12. apply AxiomII' in H13; tauto. } New H13.
    apply H2 in H14. rewrite H5,<-R_and_HR_R_Value in H14; auto.
    apply R_and_HR_R_PrLeq in H14; auto. }
  apply SupT in H12 as [s[[[H12[]]]_]]; auto. exists R_and_HR_R[s].
  repeat split; intros; auto.
  - rewrite R_and_HR_R_Value; auto. apply AxiomII; split; eauto.
    apply Hyperreal_is_set.
  - assert (x0 ∈ dom(R_and_HR_R⁻¹|(A))).
    { rewrite MKT126b,<-reqdi,H9; auto. apply MKT4'; auto. }
    assert (R_and_HR_R⁻¹[x0] ∈ B).
    { rewrite <-MKT126c with (x := A); auto.
      apply (@Property_ran x0),Property_Value; auto. apply MKT126a; auto. }
    apply H14,R_and_HR_R_PrLeq in H18; auto. rewrite f11vi in H18; auto.
    rewrite H9; auto. rewrite <-H8,deqri.
    apply (@Property_ran x0),Property_Value; auto. rewrite <-reqdi,H9; auto.
  - New H16. apply AxiomII in H18 as [_[x1[]]].
    rewrite <-R_and_HR_R_Value in H19; auto. rewrite H19 in H17.
    apply R_and_HR_R_PrLess,H15 in H17 as [y[]]; auto. exists R_and_HR_R[y].
    split. apply AxiomII in H17 as [_[]]. apply MKT4' in H17 as [].
    apply AxiomII' in H17 as [_]. apply Property_Fun in H17; auto.
    rewrite H17 in H21. apply AxiomII' in H21; tauto. rewrite H19.
    apply R_and_HR_R_PrLess; auto.
Qed.

Property HR_R_Inf_Exists : ∀ r A, A <> Φ -> HR_R_Low r A -> (∃ i, HR_R_Inf i A).
Proof.
  intros. destruct H0 as [H0[]]. New H0. apply AxiomII in H3 as [H3[x[]]].
  destruct R_and_HR_R_is_Function1_1 as [[][]]. set (B := ran(R_and_HR_R⁻¹|(A))).
  assert (B ⊂ R /\ B <> Φ) as [].
  { split. red; intros. apply AxiomII in H10 as [_[]].
    apply AxiomII in H10 as [H10[]]. apply AxiomII' in H11 as [_].
    apply AxiomII' in H11; tauto. apply NEexE in H as []. apply NEexE.
    exists (R_and_HR_R⁻¹)[x0]. assert (x0 ∈ dom(R_and_HR_R⁻¹|(A))).
    { rewrite MKT126b,deqri,MKT61,H9; auto. apply MKT4'; auto.
      destruct H6; auto. } New H10.
    apply Property_Value,Property_ran in H10. rewrite MKT126c in H10; auto.
    apply MKT126a; auto. }
  assert (∃ c, Lower B c).
  { exists x. repeat split; auto. intros.
    assert (R_and_HR_R[x0] ∈ A).
    { apply AxiomII in H12 as [_[]]. apply MKT4' in H12 as [].
      apply AxiomII' in H12 as [_]. apply Property_Fun in H12; auto.
      rewrite <-H12. apply AxiomII' in H13; tauto. } New H13.
    apply H2 in H14. rewrite H5,<-R_and_HR_R_Value in H14; auto.
    apply R_and_HR_R_PrLeq in H14; auto. }
  apply InfT in H12 as [s[[[H12[]]]_]]; auto. exists R_and_HR_R[s].
  repeat split; intros; auto.
  - rewrite R_and_HR_R_Value; auto. apply AxiomII; split; eauto.
    apply Hyperreal_is_set.
  - assert (x0 ∈ dom(R_and_HR_R⁻¹|(A))).
    { rewrite MKT126b,<-reqdi,H9; auto. apply MKT4'; auto. }
    assert (R_and_HR_R⁻¹[x0] ∈ B).
    { rewrite <-MKT126c with (x := A); auto.
      apply (@Property_ran x0),Property_Value; auto. apply MKT126a; auto. }
    apply H14,R_and_HR_R_PrLeq in H18; auto. rewrite f11vi in H18; auto.
    rewrite H9; auto. rewrite <-H8,deqri.
    apply (@Property_ran x0),Property_Value; auto. rewrite <-reqdi,H9; auto.
  - New H16. apply AxiomII in H18 as [_[x1[]]].
    rewrite <-R_and_HR_R_Value in H19; auto. rewrite H19 in H17.
    apply R_and_HR_R_PrLess,H15 in H17 as [y[]]; auto. exists R_and_HR_R[y].
    split. apply AxiomII in H17 as [_[]]. apply MKT4' in H17 as [].
    apply AxiomII' in H17 as [_]. apply Property_Fun in H17; auto.
    rewrite H17 in H21. apply AxiomII' in H21; tauto. rewrite H19.
    apply R_and_HR_R_PrLess; auto.
Qed.

(* 戴德金定理 *)
Theorem HR_R_Dedkind : ∀ X Y, X ⊂ HR_R -> Y ⊂ HR_R
  -> (∀ x y, x ∈ X -> y ∈ Y -> x ≤ y)
  -> ∃ c, c ∈ HR_R /\ (∀ x y, x ∈ X -> y ∈ Y -> (x ≤ c /\ c ≤ y)).
Proof.
  intros. destruct (classic (X <> Φ /\ Y <> Φ)).
  - destruct H2. New H3. apply NEexE in H4 as [y].
    assert (HR_R_Up y X). { repeat split; auto. }
    apply HR_R_Sup_Exists in H5 as [s[[H5[_]]]]; auto. exists s. split; auto.
    intros. split; auto. destruct (HR_Less_Trichotomy y0 s) as [H10|[]];
    try apply HR_R_subset_HR; auto.
    + apply H7 in H10 as [x0[H10[]]]; auto. New H9. apply (H1 x0) in H9; auto.
      elim H12. apply HR_Leq_Asymmetry; auto; apply HR_R_subset_HR; auto.
    + destruct H10; auto.
    + rewrite H10. apply HR_Leq_Reflexivity,HR_R_subset_HR; auto.
  - apply notandor in H2. exists 0. split. apply HR_Zero_in_HR_R.
    intros. assert (X = Φ \/ Y = Φ). { destruct H2; apply ->NNPP in H2; auto. }
    destruct H5;
    [rewrite H5 in H3; elim (@MKT16 x)|rewrite H5 in H4; elim (@MKT16 y)]; auto.
Qed.







