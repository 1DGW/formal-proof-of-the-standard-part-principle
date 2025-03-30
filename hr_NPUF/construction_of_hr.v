(** hyper_reals_construction_with_NPUF *)

Require Export filters.filter.
Require Export axiomatic_reals.R_axioms.
Require Import axiomatic_reals.seq_operations.
Require Import axiomatic_reals.R_is_infinite.
Require Import mk.equivalence_relation.

Fact N_is_Set : Ensemble N.
Proof. apply (MKT33 R). apply Ensemble_R. apply N_Subset_R. Qed.

Check N_is_Infinite.

Section construction_with_NPUF.

(* 以下两个声明作用为: 声明出N上的自由超滤F0;
   能够保证这种直接声明式的'构造'不会引起矛盾的是：
       1. filter.v 中的定理'Existence_of_free_ultraFilter',
   该定理确保了任意无限集上自由超滤的存在性;
       2. 上面一个Fact确保了N是一个无限集. *)
Variable F0 : Class.
Hypothesis F0_is_NPUF_over_N : free_ultraFilter F0 N.

(* 一下部分定义在 function_operation 中 *)
(* (* 实数列 *)
Definition R_Seq f := Function f /\ dom(f) = N /\ ran(f) ⊂ R.

(* 全体实数列集 *)
Definition Rᴺ := \{ λ u, R_Seq u \}.

Fact Rᴺ_is_Set : Ensemble Rᴺ.
Proof.
  apply (MKT33 pow(N × R)). apply MKT38a,MKT74; auto.
  apply N_is_Set. apply Ensemble_R. unfold Included; intros.
  apply AxiomII in H as [H[H0[]]].
  apply AxiomII; split; unfold Included; intros; auto.
  New H3. rewrite MKT70 in H4; auto.
  apply AxiomII in H4 as [H4[x[y[]]]]. rewrite H5 in *.
  apply AxiomII'; repeat split; auto.
  rewrite <-H1. apply Property_dom in H3; auto.
  apply Property_ran in H3; auto.
Qed. *)

(* 定义一种Rᴺ上的等价关系: 关于F0几乎相等 *)
Definition Equ_NPUF := \{\ λ f g, f ∈ Rᴺ /\ g ∈ Rᴺ
  /\ (\{ λ u, u ∈ N /\ f[u] = g[u] \}) ∈ F0 \}\.

Fact Equ_NPUF_is_equRelation_over_Rᴺ : equRelation Equ_NPUF Rᴺ.
Proof.
  destruct F0_is_NPUF_over_N as [[[H[H0[H1[]]]]]].
  repeat split; intros; red; intros.
  - apply AxiomII in H6 as [H6[x[y[H7[H8[]]]]]].
    subst. apply AxiomII'; auto.
  - apply AxiomII'; repeat split; auto.
    apply MKT49a; eauto. apply AxiomII in H6 as [].
    assert (\{ λ u, u ∈ N /\ x[u] = x[u] \} = N).
    { apply AxiomI; split; intros. apply AxiomII in H8; tauto.
      apply AxiomII; split; eauto. }
    rewrite H8; auto.
  - apply AxiomII' in H8 as [H8[H9[]]].
    apply AxiomII'; repeat split; auto.
    apply MKT49b in H8 as []. apply MKT49a; auto.
    assert (\{ λ u, u ∈ N /\ x[u] = y[u] \}
      = \{ λ u, u ∈ N /\ y[u] = x[u] \}).
    { apply AxiomI; split; intros; apply AxiomII in H12 as [H12[]];
      apply AxiomII; auto. }
    rewrite <-H12; auto.
  - apply AxiomII' in H9 as [H9[H11[]]], H10 as [H10[H14[]]].
    apply AxiomII'; split. apply MKT49b in H9 as [], H10 as [].
    apply MKT49a; auto. repeat split; auto.
    assert (\{ λ u, u ∈ N /\ x[u] = y[u] \} ∩ \{ λ u, u ∈ N
      /\ y[u] = z[u] \} ⊂ \{ λ u, u ∈ N /\ x[u] = z[u] \}).
    { unfold Included; intros. apply MKT4' in H17 as [].
      apply AxiomII in H17 as [_[]], H18 as [_[]].
      apply AxiomII; repeat split; eauto. rewrite H19; auto. }
    apply H3 in H17; auto. unfold Included; intros.
    apply AxiomII in H18; tauto.
Qed.

Local Notation "\[ f \]" := (equClass f Equ_NPUF Rᴺ).

(* 超实数 *)
Definition HR := (Rᴺ / Equ_NPUF)%ec.

Fact HR_Elements : ∀ x, x ∈ HR <-> ∃ f, f ∈ Rᴺ /\ x = \[ f \].
Proof.
  split; intros. apply AxiomII in H as []; eauto.
  destruct H as [f[]]. apply AxiomII in H as [H[H1[]]].
  apply AxiomII. split. apply (MKT33 (Rᴺ)). apply Rᴺ_is_Set.
  red; intros. apply AxiomII. split. eauto. rewrite H0 in H4.
  apply AxiomII in H4 as [H4[]]. apply AxiomII in H5 as []; auto.
  exists f. split; auto. apply AxiomII; split. apply MKT75; auto.
  rewrite H2. apply (MKT33 R). apply Ensemble_R. apply N_Subset_R. split; auto.
Qed.

Fact Hyperreal_is_set : ∀ f, Ensemble \[ f \].
Proof.
  intros. apply (MKT33 (Rᴺ)). apply Rᴺ_is_Set. red; intros.
  apply AxiomII in H; tauto.
Qed.

(* Ltac destructR' H := apply HR_Elements in H as [?[]]. *)

(****  定义 超实数中的基本元素(零元和单位元)  *****)

Definition HR_Zero := \[ (ConstSeq 0) \].
Definition HR_One := \[ (ConstSeq 1) \].

Local Notation "0" := HR_Zero.
Local Notation "1" := HR_One.

Property HR_Zero_in_HR : 0 ∈ HR.
Proof.
  apply HR_Elements. exists (ConstSeq 0%r). split; auto.
  apply ConstSeq_is_Seq; auto with real.
Qed.

Property HR_One_in_HR : 1 ∈ HR.
Proof.
  apply HR_Elements. exists (ConstSeq 1%r). split; auto.
  apply ConstSeq_is_Seq; auto with real.
Qed.

Property HR_Zero_isnot_One : 0 <> 1.
Proof.
  intro. apply equClassT1 in H; try apply ConstSeq_is_Seq; auto with real.
  apply AxiomII' in H as [_[_[]]].
  assert (\{ λ u, u ∈ N /\ (ConstSeq 0%r)[u] = (ConstSeq 1%r)[u] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H1 as [_[]].
    rewrite ConstSeq_Value,ConstSeq_Value in H2; auto with real.
    destruct OrderPM_Co9. elim H4; auto. elim (@ MKT16 z); auto. }
  rewrite H1 in H0. destruct F0_is_NPUF_over_N as [[[_[]]]]; auto.
  apply Equ_NPUF_is_equRelation_over_Rᴺ.
Qed.

(****  定义 超实数中的序(小于等于)  ****)

Definition HR_Leq := \{\ λ u v, ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ
  -> u = \[ f \] -> v = \[ g \] -> \{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \} ∈ F0 \}\.

Local Notation "u ≤ v" := (Rrelation u HR_Leq v).
Local Notation "u < v" := (u ≤ v /\ u <> v).

(* 具体化 *)
Property HR_Leq_Instantiate : ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ
  -> \[ f \] ≤ \[ g \] <-> \{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \} ∈ F0.
Proof.
  split; intros.
  - apply AxiomII' in H1 as []. apply H2; auto.
  - apply AxiomII'; split; intros. apply MKT49a; apply Hyperreal_is_set.
    apply equClassT1 in H4,H5; auto; try apply Equ_NPUF_is_equRelation_over_Rᴺ.
    apply AxiomII' in H4 as [_[_[_]]], H5 as [_[_[_]]].
    assert (\{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \}
      ∩ \{ λ u, u ∈ N /\ f[u] = f0[u] \} ∩ \{ λ u, u ∈ N /\ g[u] = g0[u] \}
      ⊂ \{ λ w, w ∈ N /\ (f0[w] ≤ g0[w])%r \}).
    { red; intros. apply MKT4' in H6 as []. apply MKT4' in H7 as [].
      apply AxiomII in H6 as [_[]], H7 as [_[]], H8 as [H8[]].
      apply AxiomII. rewrite <-H10,<-H12; auto. }
    destruct F0_is_NPUF_over_N as [[[_[_[H7[]]]]_]_].
    apply H9 in H6; auto. red; intros. apply AxiomII in H10; tauto.
Qed.

Property HR_Less_Instantiate : ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ
  -> \[ f \] < \[ g \] <-> \{ λ w, w ∈ N /\ (f[w] < g[w])%r \} ∈ F0.
Proof.
  destruct F0_is_NPUF_over_N as [[[_[_[H[]]]]_]_]. split; intros.
  assert (∀ f x, f ∈ Rᴺ -> x ∈ N -> f[x] ∈ R).
  { intros. apply AxiomII in H5 as [_[H5[]]].
    apply H8,(@ Property_ran x),Property_Value; auto. rewrite H7; auto. }
  - destruct H4. apply HR_Leq_Instantiate in H4; auto.
    assert (\{ λ w, w ∈ N /\ f[w] = g[w] \}
      ∪ \{ λ w, w ∈ N /\ f[w] <> g[w] \} = N).
    { apply AxiomI; split; intros.
      apply MKT4 in H7 as []; apply AxiomII in H7; tauto. apply MKT4.
      destruct (classic (f[z] = g[z])); [left|right];
      apply AxiomII; split; eauto. } rewrite <-H7 in H.
    apply (FT1 _ N) in H as []; [ | |apply F0_is_NPUF_over_N].
    elim H6. apply equClassT1; auto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    assert (\{ λ w, w ∈ N /\ f[w] <> g[w] \}
      ∩ \{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \}
      ⊂ \{ λ w, w ∈ N /\ (f[w] < g[w])%r \}).
    { red; intros. apply MKT4' in H8 as [].
      apply AxiomII in H8 as [_[]], H9 as [_[]].
      apply AxiomII; repeat split; eauto. }
    apply H1 in H8; auto. red; intros. apply AxiomII in H9; tauto.
  - split. apply HR_Leq_Instantiate; auto.
    assert (\{ λ w, w ∈ N /\ (f[w] < g[w])%r \}
       ⊂ \{ λ w, w ∈ N /\ (f[w] ≤ g[w])%r \}).
    { red; intros. apply AxiomII in H5 as [_[]].
      apply AxiomII; repeat split; eauto. destruct H6; auto. }
    apply H1 in H5; auto. red; intros. apply AxiomII in H6; tauto.
    intro. apply equClassT1 in H5; auto; try apply Equ_NPUF_is_equRelation_over_Rᴺ.
    apply AxiomII' in H5 as [_[_[_]]].
    assert (\{ λ w, w ∈ N /\ (f[w] < g[w])%r \}
      ∩ \{ λ u, u ∈ N /\ f[u] = g[u] \} = Φ).
    { apply AxiomI; split; intros. apply MKT4' in H6 as [].
      apply AxiomII in H6 as [_[]], H7 as [_[]]. destruct H8. elim H10; auto.
      elim (@ MKT16 z); auto. }
    destruct F0_is_NPUF_over_N as [[[_[]]_]_]. elim H7.
    rewrite <-H6. apply H0; auto.
Qed.

(* 合理性 超实数中序关系与等价类代表的选取无关 *)
Property HR_Leq_Reasonable : ∀ f1 f2 g1 g2, f1 ∈ Rᴺ -> f2 ∈ Rᴺ
  -> g1 ∈ Rᴺ -> g2 ∈ Rᴺ -> \[ f1 \] = \[ f2 \] -> \[ g1 \] = \[ g2 \]
  -> \[ f1 \] ≤ \[ g1 \] <-> \[ f2 \] ≤ \[ g2 \].
Proof.
  assert (∀ f1 f2 g1 g2, f1 ∈ Rᴺ -> f2 ∈ Rᴺ
    -> g1 ∈ Rᴺ -> g2 ∈ Rᴺ -> \[ f1 \] = \[ f2 \] -> \[ g1 \] = \[ g2 \]
    -> \[ f1 \] ≤ \[ g1 \] -> \[ f2 \] ≤ \[ g2 \]).
  { intros. apply HR_Leq_Instantiate in H5; auto.
    apply HR_Leq_Instantiate; auto.
    apply equClassT1 in H3,H4; auto; try apply Equ_NPUF_is_equRelation_over_Rᴺ.
    apply AxiomII' in H3 as [_[_[_]]], H4 as [_[_[_]]].
    assert (\{ λ w, w ∈ N /\ (f1[w] ≤ g1[w])%r \}
      ∩ \{ λ u, u ∈ N /\ f1[u] = f2[u] \} ∩ \{ λ u, u ∈ N /\ g1[u] = g2[u] \}
      ⊂ \{ λ w, w ∈ N /\ (f2[w] ≤ g2[w])%r \}).
    { red; intros. apply MKT4' in H6 as []. apply MKT4' in H7 as [].
      apply AxiomII in H6 as [_[]], H7 as [_[]], H8 as [H8[]].
      apply AxiomII. rewrite <-H10,<-H12; auto. }
    destruct F0_is_NPUF_over_N as [[[_[_[H7[]]]]_]_].
    apply H9 in H6; auto. red; intros. apply AxiomII in H10; tauto. }
  split; intros. apply (H f1 f2 g1 g2); auto. apply (H f2 f1 g2 g1); auto.
Qed.

(***  定义 超实数中的加法  ****)
(* 合理性 超实数加法的结果与等价类代表的选取无关 *)
Lemma HR_Plus_Reasonable : ∀ f1 f2 g1 g2, f1 ∈ Rᴺ -> f2 ∈ Rᴺ
  -> g1 ∈ Rᴺ -> g2 ∈ Rᴺ -> \[ f1 \] = \[ f2 \] -> \[ g1 \] = \[ g2 \]
  -> \[ (f1 + g1)%seq \] = \[ (f2 + g2)%seq \].
Proof.
  intros. apply equClassT1. apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply Seq_Plus_Close; auto. apply Seq_Plus_Close; auto.
  apply AxiomII'. split. apply MKT49a; exists Rᴺ; apply Seq_Plus_Close; auto.
  repeat split; try apply Seq_Plus_Close; auto.
  apply equClassT1 in H3,H4; auto; try apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply AxiomII' in H3 as [_[_[_]]], H4 as [_[_[_]]].
  assert (\{ λ u, u ∈ N /\ f1[u] = f2[u] \} ∩ \{ λ u, u ∈ N /\ g1[u] = g2[u] \}
    ⊂ \{ λ u, u ∈ N /\ (f1 + g1)[u] = (f2 + g2)[u] \}).
  { red; intros. apply MKT4' in H5 as [].
    apply AxiomII in H5 as [_[]], H6 as [_[]].
    apply AxiomII. repeat split; eauto.
    rewrite Seq_Plus_Property,Seq_Plus_Property,H7,H8; auto. }
  destruct F0_is_NPUF_over_N as [[[_[_[H8[]]]]_]_].
  apply H7 in H5; auto. red; intros. apply AxiomII in H9; tauto.
Qed.

(* Definition HR_Plus u v := ∩(\{ λ a, ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ
  -> u = \[ f \] -> v = \[ g \] -> a = \[ (f + g)%seq \] \}). *)

(* 加法函数 *)
Definition HR_Plus_Func := \{\ λ u v, u ∈ HR × HR
  /\ (∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ -> u = [\[ f \],\[ g \]]
    -> v = \[ (f + g)%seq \]) \}\.

(* 加法函数是定义域为 HR × HR, 值域包含于 HR 的 *)
Property HR_Plus_Func_is_Function : Function HR_Plus_Func.
Proof.
  split; intros. red; intros. apply AxiomII in H as [_[x[y[H[]]]]]; eauto.
  apply AxiomII' in H as [H[]], H0 as [H0[]].
  apply AxiomII in H1 as [H1[x0[y0[H5[]]]]].
  apply HR_Elements in H6 as [f[]], H7 as [g[]]. rewrite H8,H9 in H5.
  rewrite (H2 f g H6 H7 H5), (H4 f g H6 H7 H5); auto.
Qed.

Property HR_Plus_Func_dom : dom(HR_Plus_Func) = HR × HR.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [H0[]]; auto.
  - New H. apply AxiomII in H as [H[x[y[H1[]]]]]. apply AxiomII; split; auto.
    apply HR_Elements in H2 as [f[]], H3 as [g[]]. exists \[ (f + g)%seq \].
    apply AxiomII'; split. apply MKT49a; auto. apply Hyperreal_is_set.
    split. auto. intros. rewrite H8 in H1.
    apply MKT55 in H1 as []; try apply Hyperreal_is_set.
    apply HR_Plus_Reasonable; auto; subst; auto.
Qed.

Property HR_Plus_Func_ran : ran(HR_Plus_Func) ⊂ HR.
Proof.
  red; intros. apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [H0[]].
  apply AxiomII in H1 as [H1[x0[y0[H3[]]]]].
  apply HR_Elements in H4 as [f[]], H5 as [g[]]. rewrite H6,H7 in H3.
  rewrite (H2 f g H4 H5 H3). apply HR_Elements. exists (f + g)%seq.
  split; auto. apply Seq_Plus_Close; auto.
Qed.

Local Notation "u + v" := (HR_Plus_Func[[u,v]]).

Property HR_Plus_Instantiate : ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ
  -> \[ f \] + \[ g \] = \[ (f + g)%seq \].
Proof.
  intros. assert (\[ f \] ∈ HR /\ \[ g \] ∈ HR) as [].
  { split; apply HR_Elements; eauto. }
  assert ([\[ f \],\[ g \]] ∈ dom(HR_Plus_Func)).
  { rewrite HR_Plus_Func_dom. apply AxiomII'; repeat split; auto.
    apply MKT49a; apply Hyperreal_is_set. }
  New HR_Plus_Func_is_Function. apply Property_Value in H3; auto.
  apply AxiomII' in H3 as [H3[]]. apply (H6 f g); auto.
Qed.

Property HR_Plus_Close : ∀ u v, u ∈ HR -> v ∈ HR -> u + v ∈ HR.
Proof.
  intros. apply HR_Plus_Func_ran,(@ Property_ran [u,v]),Property_Value.
  apply HR_Plus_Func_is_Function. rewrite HR_Plus_Func_dom.
  apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.



(****  定义 超实数中的负元(减法)  ****)
(* 合理性: 负元唯一性 *)
Lemma HR_Neg_Reasonable : ∀ r, r ∈ HR -> (∃! r0, r0 ∈ HR /\ r + r0 = 0).
Proof.
  intros. New H. apply HR_Elements in H0 as [f[]].
  New H0. apply Seq_Neg_Close in H2. exists (\[ (-f)%seq \]).
  assert (f + (-f) ∈ Rᴺ)%seq. { apply Seq_Plus_Close; auto. } split.
  - split. apply HR_Elements; eauto. rewrite H1.
    rewrite HR_Plus_Instantiate; auto. apply equClassT1; auto.
    apply Equ_NPUF_is_equRelation_over_Rᴺ. apply ConstSeq_is_Seq; eauto with real.
    apply AxiomII'. repeat split; auto. apply MKT49a; eauto. exists Rᴺ.
    apply ConstSeq_is_Seq; eauto with real.
    apply ConstSeq_is_Seq; eauto with real.
    assert (\{ λ u, u ∈ N /\ ((f + (-f))%seq)[u] = (ConstSeq 0%r)[u] \} = N).
    { apply AxiomI; split; intros. apply AxiomII in H4; tauto.
      apply AxiomII; repeat split; eauto. rewrite Seq_Plus_Property; auto.
      rewrite ConstSeq_Value; eauto with real. rewrite Seq_Neg_Property; auto.
      apply Minus_P1. apply AxiomII in H0 as [H0[H5[]]].
      apply H7,(@ Property_ran z),Property_Value; auto. rewrite H6; auto. }
    rewrite H4. destruct F0_is_NPUF_over_N as [[[_[_[]]]_]_]; auto.
  - intros r0 []. New H4. apply HR_Elements in H6 as [g[]].
    rewrite H1,H7,HR_Plus_Instantiate in H5; auto. rewrite H7.
    apply equClassT1; auto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
    apply equClassT1,AxiomII' in H5 as [H5[H8[]]].
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    assert (\{ λ u, u ∈ N /\ ((f + g)%seq)[u] = (ConstSeq 0%r)[u] \}
      ⊂ \{ λ u, u ∈ N /\ (-f)[u] = g[u] \}).
    { red; intros. apply AxiomII. apply AxiomII in H11 as [H11[]].
      repeat split; auto. rewrite Seq_Plus_Property in H13; auto.
      rewrite ConstSeq_Value in H13; eauto with real.
      rewrite Seq_Neg_Property; auto.
      assert (f[z] ∈ R /\ g[z] ∈ R) as [].
      { apply AxiomII in H0 as [H0[H14[]]], H6 as [H6[H17[]]].
        split; [apply H16|apply H19]; apply (@ Property_ran z),Property_Value;
        auto; [rewrite H15|rewrite H18]; auto. }
      apply Plus_Co3 in H13; eauto with real.
      rewrite Plus_P4,Plus_P1 in H13; eauto with real. }
    destruct F0_is_NPUF_over_N as [[[_[_[H12[]]]]_]_].
    apply H14 in H11; auto. red; intros. apply AxiomII in H15; tauto.
    apply Equ_NPUF_is_equRelation_over_Rᴺ. apply Seq_Plus_Close; auto.
    apply ConstSeq_is_Seq; eauto with real.
Qed.

Definition HR_Neg r := ∩(\{ λ a, a ∈ HR /\ r + a = 0 \}).

Local Notation "- u" := (HR_Neg u).
Local Notation "u - v" := (u + (-v)).

Property HR_Neg_Instantiate : ∀ f, f ∈ Rᴺ -> - \[ f \] = \[ (-f)%seq \].
Proof.
  intros. assert (\[ f \] ∈ HR). { apply HR_Elements; eauto. }
  New H. apply Seq_Neg_Close in H1.
  assert (\[ (-f)%seq \] ∈ HR). { apply HR_Elements; eauto. }
  assert (((f + (-f))%seq) ∈ Rᴺ /\ (ConstSeq 0%r) ∈ Rᴺ) as [].
  { split. apply Seq_Plus_Close; auto. apply ConstSeq_is_Seq; eauto with real. }
  assert (\[ f \] + \[ (-f)%seq \] = 0).
  { rewrite HR_Plus_Instantiate; auto. apply equClassT1; auto.
    apply Equ_NPUF_is_equRelation_over_Rᴺ. apply AxiomII'; repeat split; auto.
    apply MKT49a; eauto.
    assert (\{ λ u, u ∈ N /\ ((f + (-f))%seq)[u] = (ConstSeq 0%r)[u] \} = N).
    { apply AxiomI; split; intros. apply AxiomII in H5; tauto.
      apply AxiomII; repeat split; eauto.
      rewrite Seq_Plus_Property,Seq_Neg_Property,ConstSeq_Value,Minus_P1;
      auto with real. apply AxiomII in H as [H[H6[]]].
      apply H8,(@ Property_ran z),Property_Value; auto. rewrite H7; auto. }
    rewrite H5. destruct F0_is_NPUF_over_N as [[[_[_[]]]]]; auto. }
  assert (\{ λ a, a ∈ HR /\ \[ f \] + a = 0 \} = [\[ (-f)%seq \]]).
  { apply AxiomI; split; intros. apply AxiomII in H6 as [H6[]].
    apply MKT41. apply Hyperreal_is_set. New H0.
    apply HR_Neg_Reasonable in H9 as [x[[]]].
    assert (x = \[ (-f)%seq \] /\ x = z) as []. { split; apply H11; auto. }
    rewrite <-H12,<-H13; auto. apply MKT41 in H6. apply AxiomII; repeat split.
    rewrite H6. apply Hyperreal_is_set. rewrite H6. apply HR_Elements; eauto.
    rewrite H6. auto. apply Hyperreal_is_set. }
  unfold HR_Neg. rewrite H6. New (Hyperreal_is_set (-f)%seq).
  apply MKT44 in H7 as []. rewrite H7; auto.
Qed.

Property HR_Neg_Close : ∀ r, r ∈ HR <-> -r ∈ HR.
Proof.
  split; intros. New H. apply HR_Elements in H0 as [f[]].
  rewrite H1,HR_Neg_Instantiate; auto. apply HR_Elements.
  exists (-f)%seq. split; auto. apply Seq_Neg_Close; auto.
  apply NNPP; intro. assert (\{ λ a, a ∈ HR /\ r + a = 0 \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H1 as [H1[]].
    assert ([r,z] ∉ dom(HR_Plus_Func)).
    { intro. rewrite HR_Plus_Func_dom in H4.
      apply AxiomII' in H4 as [_[]]; auto. }
    apply MKT69a in H4. elim MKT39. rewrite <-H4,H3. apply Hyperreal_is_set.
    elim (@ MKT16 z); auto. }
  unfold HR_Neg in H. rewrite H1,MKT24 in H. elim MKT39; eauto.
Qed.



(* 注: (u ∈ HR /\ v ∈ HR) <-> (u - v) ∈ HR 是可证的, 其他运算也如此,
       但感觉没必要, 若需要可考虑如此描述. *)
Property HR_Minus_Close : ∀ u v, u ∈ HR -> v ∈ HR -> (u - v) ∈ HR.
Proof. intros. apply HR_Plus_Close; auto. apply ->HR_Neg_Close; auto. Qed.


(***  定义 超实数中的乘法  ****)
(* 合理性 超实数乘法的结果与等价类代表的选取无关 *)
Lemma HR_Mult_Reasonable : ∀ f1 f2 g1 g2, f1 ∈ Rᴺ -> f2 ∈ Rᴺ
  -> g1 ∈ Rᴺ -> g2 ∈ Rᴺ -> \[ f1 \] = \[ f2 \] -> \[ g1 \] = \[ g2 \]
  -> \[ (f1·g1)%seq \] = \[ (f2·g2)%seq \].
Proof.
  intros. apply equClassT1. apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply Seq_Mult_Close; auto. apply Seq_Mult_Close; auto.
  apply AxiomII'. split. apply MKT49a; exists Rᴺ; apply Seq_Mult_Close; auto.
  repeat split; try apply Seq_Mult_Close; auto.
  apply equClassT1 in H3,H4; auto; try apply Equ_NPUF_is_equRelation_over_Rᴺ.
  apply AxiomII' in H3 as [_[_[_]]], H4 as [_[_[_]]].
  assert (\{ λ u, u ∈ N /\ f1[u] = f2[u] \} ∩ \{ λ u, u ∈ N /\ g1[u] = g2[u] \}
    ⊂ \{ λ u, u ∈ N /\ (f1·g1)[u] = (f2·g2)[u] \}).
  { red; intros. apply MKT4' in H5 as [].
    apply AxiomII in H5 as [_[]], H6 as [_[]].
    apply AxiomII. repeat split; eauto.
    rewrite Seq_Mult_Property,Seq_Mult_Property,H7,H8; auto. }
  destruct F0_is_NPUF_over_N as [[[_[_[H8[]]]]_]_].
  apply H7 in H5; auto. red; intros. apply AxiomII in H9; tauto.
Qed.

(* Definition HR_Mult u v := ∩(\{ λ a, ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ
  -> u = \[ f \] -> v = \[ g \] -> a = \[ (f·g)%seq \] \}). *)

(* 乘法函数 *)
Definition HR_Mult_Func := \{\ λ u v, u ∈ HR × HR
  /\ (∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ -> u = [\[ f \],\[ g \]]
    -> v = \[ (f·g)%seq \]) \}\.

(* 乘法函数是定义域为 HR × HR, 值域包含于 HR 的 *)
Property HR_Mult_Func_is_Function : Function HR_Mult_Func.
Proof.
  split; intros. red; intros. apply AxiomII in H as [_[x[y[H[]]]]]; eauto.
  apply AxiomII' in H as [H[]], H0 as [H0[]].
  apply AxiomII in H1 as [H1[x0[y0[H5[]]]]].
  apply HR_Elements in H6 as [f[]], H7 as [g[]]. rewrite H8,H9 in H5.
  rewrite (H2 f g H6 H7 H5), (H4 f g H6 H7 H5); auto.
Qed.

Property HR_Mult_Func_dom : dom(HR_Mult_Func) = HR × HR.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [H0[]]; auto.
  - New H. apply AxiomII in H as [H[x[y[H1[]]]]]. apply AxiomII; split; auto.
    apply HR_Elements in H2 as [f[]], H3 as [g[]]. exists \[ (f·g)%seq \].
    apply AxiomII'; split. apply MKT49a; auto. apply Hyperreal_is_set.
    split. auto. intros. rewrite H8 in H1.
    apply MKT55 in H1 as []; try apply Hyperreal_is_set.
    apply HR_Mult_Reasonable; auto; subst; auto.
Qed.

Property HR_Mult_Func_ran : ran(HR_Mult_Func) ⊂ HR.
Proof.
  red; intros. apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [H0[]].
  apply AxiomII in H1 as [H1[x0[y0[H3[]]]]].
  apply HR_Elements in H4 as [f[]], H5 as [g[]]. rewrite H6,H7 in H3.
  rewrite (H2 f g H4 H5 H3). apply HR_Elements. exists (f·g)%seq.
  split; auto. apply Seq_Mult_Close; auto.
Qed.

Local Notation "u · v" := (HR_Mult_Func[[u,v]]).

Property HR_Mult_Instantiate : ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ
  -> \[ f \]·\[ g \] = \[ (f·g)%seq \].
Proof.
  intros. assert (\[ f \] ∈ HR /\ \[ g \] ∈ HR) as [].
  { split; apply HR_Elements; eauto. }
  assert ([\[ f \],\[ g \]] ∈ dom(HR_Mult_Func)).
  { rewrite HR_Mult_Func_dom. apply AxiomII'; repeat split; auto.
    apply MKT49a; apply Hyperreal_is_set. }
  New HR_Mult_Func_is_Function. apply Property_Value in H3; auto.
  apply AxiomII' in H3 as [H3[]]. apply (H6 f g); auto.
Qed.

Property HR_Mult_Close : ∀ u v, u ∈ HR -> v ∈ HR -> u·v ∈ HR.
Proof.
  intros. apply HR_Mult_Func_ran,(@ Property_ran [u,v]),Property_Value.
  apply HR_Mult_Func_is_Function. rewrite HR_Mult_Func_dom.
  apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.




(* 以下减法定义方式不便于将HR以外的元素做运算时将结果排除为全域,
   对应至除法时, 不便于将0的逆元排除称为全域(按如下思路会让0的逆元任为0).  *)
(***  定义 超实数中的减法  ****)
(* Definition HR_Minus u v := ∩(\{ λ a, ∀ f g, f ∈ Rᴺ -> g ∈ Rᴺ
  -> u = \[ f \] -> v = \[ g \] -> a = \[ (f - g)%seq \] \}). *)


(* 如下定义的逆元会使0的逆元仍为0 *)
(*
Definition HR_Inv u := ∩(\{ λ a, ∀ f, f ∈ Rᴺ -> \[ f \] <> \[ (ConstSeq 0%r) \]
  -> u = \[ f \] -> a = \[ (/f)%seq \] \}). *)


(****  定义 超实数中的逆元(除法)  ****)
(* 合理性: 逆元唯一性 *)
Lemma HR_Inv_Reasonable : ∀ r, r ∈ HR -> r <> 0
  -> (∃! r1, r1 ∈ HR /\ r1 <> 0 /\ r·r1 = 1).
Proof.
  intros. New H. apply HR_Elements in H1 as [f[]].
  New H1. apply Seq_Inv_Close in H3. exists (\[ (/f)%seq \]).
  assert (f·(/f) ∈ Rᴺ)%seq. { apply Seq_Mult_Close; auto. } split.
  - repeat split. apply HR_Elements; eauto.
    + intro. apply equClassT1,AxiomII' in H5 as [H5[H6[]]]; auto. elim H0.
      rewrite H2. apply equClassT1; auto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
      apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
      assert (\{ λ u, u ∈ N /\ (/f)[u] = (ConstSeq 0%r)[u] \}
         ⊂ \{ λ u, u ∈ N /\ f[u] = (ConstSeq 0%r)[u] \}).
      { red; intros. apply AxiomII in H9 as [H9[]].
        apply AxiomII; repeat split; auto.
        rewrite ConstSeq_Value in H11; eauto with real.
        rewrite ConstSeq_Value; eauto with real.
        apply AxiomII in H3 as [H3[H12[]]]. rewrite <-H13 in H10.
        apply Property_Value,AxiomII' in H10 as [H10[H15[[]|[]]]]; auto.
        rewrite H11 in H17. apply AxiomII in H1 as [H1[H18[]]].
        rewrite <-H19 in H15. apply Property_Value,Property_ran in H15; auto.
        assert (f[z] ∈ (R ~ [0%r])).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto.
          intro. apply MKT41 in H21; eauto with real. }
        apply Mult_inv1,MKT4' in H21 as []. apply AxiomII in H22 as [].
        elim H23. apply MKT41; eauto with real. }
      destruct F0_is_NPUF_over_N as [[[_[_[H12[]]]]_]_].
      apply H11 in H9; auto. red; intros. apply AxiomII in H13; tauto.
      apply Equ_NPUF_is_equRelation_over_Rᴺ. apply ConstSeq_is_Seq; auto with real.
    + rewrite H2. rewrite HR_Mult_Instantiate; auto. apply equClassT1; auto.
      apply Equ_NPUF_is_equRelation_over_Rᴺ. apply ConstSeq_is_Seq; auto with real.
      apply AxiomII'. repeat split; auto. apply MKT49a; eauto. exists Rᴺ.
      apply ConstSeq_is_Seq; auto with real.
      apply ConstSeq_is_Seq; auto with real.
      assert (\{ λ u, u ∈ N /\ f[u] <> 0%r \} ∈ F0).
      { apply NNPP; intro. elim H0. rewrite H2. apply equClassT1; auto.
        apply Equ_NPUF_is_equRelation_over_Rᴺ.
        apply ConstSeq_is_Seq; auto with real.
        apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
        exists Rᴺ. apply ConstSeq_is_Seq; auto with real.
        apply ConstSeq_is_Seq; auto with real.
        assert (\{ λ u, u ∈ N /\ f[u] <> 0%r \}
            ∪ \{ λ u, u ∈ N /\ f[u] = (ConstSeq 0%r)[u] \} = N).
        { apply AxiomI; split; intros.
          apply MKT4 in H6 as []; apply AxiomII in H6; tauto.
          apply MKT4. destruct (classic (f[z] = 0%r)); [right|left];
          apply AxiomII; repeat split; eauto.
          rewrite ConstSeq_Value; auto with real. }
        destruct F0_is_NPUF_over_N as [[[_[_[H12[]]]]_]_].
        rewrite <-H6 in H12. apply (FT1 F0 N) in H12 as []; auto.
        contradiction. destruct F0_is_NPUF_over_N; auto. }
      assert (\{ λ u, u ∈ N /\ f[u] <> 0%r \}
         ⊂ \{ λ u, u ∈ N /\ ((f·(/f))%seq)[u] = (ConstSeq 1%r)[u] \}).
      { red; intros. apply AxiomII in H6 as [H6[]].
        apply AxiomII; repeat split; auto.
        rewrite ConstSeq_Value,Seq_Mult_Property; auto with real.
        New H8. apply Seq_Inv_Property_b in H9; auto. rewrite H9.
        apply Divide_P1. apply AxiomII in H1 as [H1[H10[]]].
        rewrite <-H11 in H7. apply Property_Value,Property_ran in H7; auto.
        apply MKT4'; split; auto. apply AxiomII; split. eauto. intro.
        apply MKT41 in H13; eauto with real. }
      destruct F0_is_NPUF_over_N as [[[_[_[H12[]]]]_]_].
      apply H8 in H6; auto. red; intros. apply AxiomII in H9; tauto.
  - intros r1 [H5[]]. New H5. apply HR_Elements in H8 as [g[]].
    rewrite H2,H9,HR_Mult_Instantiate in H7; auto. rewrite H9.
    apply equClassT1; auto. apply Equ_NPUF_is_equRelation_over_Rᴺ.
    apply equClassT1,AxiomII' in H7 as [H7[H10[]]].
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    assert (\{ λ u, u ∈ N /\ ((f·g)%seq)[u] = (ConstSeq 1%r)[u] \}
      ⊂ \{ λ u, u ∈ N /\ (/f)[u] = g[u] \}).
    { red; intros. apply AxiomII. apply AxiomII in H13 as [H13[]].
      repeat split; auto. rewrite Seq_Mult_Property in H15; auto.
      rewrite ConstSeq_Value in H15; auto with real.
      assert (f[z] ∈ R /\ g[z] ∈ R) as [].
      { apply AxiomII in H1 as [H1[H16[]]], H8 as [H8[H19[]]].
        split; [apply H18|apply H21]; apply (@ Property_ran z),Property_Value;
        auto; [rewrite H17|rewrite H20]; auto. }
      assert (f[z] ∈ (R ~ [0%r])).
      { apply MKT4'; split; auto. apply AxiomII; split. eauto. intro.
        apply MKT41 in H18; eauto with real.
        rewrite H18,Mult_P4,PlusMult_Co1 in H15; auto with real.
        destruct OrderPM_Co9; auto. }
      apply Mult_Co3 in H15; auto with real. New H18.
      apply Mult_inv1,MKT4' in H19 as [].
      rewrite Mult_P4,Mult_P1 in H15; auto with real. apply MKT4' in H18 as [].
      apply AxiomII in H21 as []. assert (f[z] <> 0%r).
      { intro. apply H22,MKT41; eauto with real. }
      apply Seq_Inv_Property_b in H23; auto. rewrite H23; auto. }
    destruct F0_is_NPUF_over_N as [[[_[_[H14[]]]]_]_].
    apply H16 in H13; auto. red; intros. apply AxiomII in H17; tauto.
    apply Equ_NPUF_is_equRelation_over_Rᴺ. apply Seq_Mult_Close; auto.
    apply ConstSeq_is_Seq; auto with real.
Qed.

Definition HR_Inv r := ∩(\{ λ a, a ∈ HR /\ a <> 0 /\ r·a = 1 \}).

Local Notation "u ⁻" := (HR_Inv u).
Local Notation "u / v" := (u·(v⁻)).

Property HR_Inv_0_is_universe : 0⁻ = μ.
Proof.
  assert (\{ λ a, a ∈ HR /\ a <> 0 /\ 0 · a = 1 \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H as [H[H0[]]].
    New H0. apply HR_Elements in H3 as [f[]]. unfold "0" in H2.
    assert ((ConstSeq 0%r) ∈ Rᴺ /\ (ConstSeq 1%r) ∈ Rᴺ) as [].
    { split; apply ConstSeq_is_Seq; auto with real. }
    rewrite H4,HR_Mult_Instantiate in H2; auto.
    apply equClassT1,AxiomII' in H2 as [H2[H7[]]]; auto.
    assert (\{ λ u, u ∈ N /\ (((ConstSeq 0%r)·f)%seq)[u]
      = (ConstSeq 1%r)[u] \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H10 as [H10[]]. New H3.
      apply AxiomII in H13 as [H13[H14[]]]. New H11. rewrite <-H15 in H17.
      apply Property_Value,Property_ran in H17; auto. rewrite Seq_Mult_Property,
      ConstSeq_Value,ConstSeq_Value,Mult_P4,PlusMult_Co1 in H12; auto with real.
      destruct OrderPM_Co9. elim H19; auto. elim (@ MKT16 z0); auto. }
    rewrite H10 in H9. destruct F0_is_NPUF_over_N as [[[_[]]]].
    contradiction. apply Equ_NPUF_is_equRelation_over_Rᴺ.
    apply Seq_Mult_Close; auto. elim (@ MKT16 z); auto. }
  unfold HR_Inv. rewrite H,MKT24; auto.
Qed.

Property HR_Inv_Instantiate : ∀ f, f ∈ Rᴺ
  -> \[ f \] <> 0 <-> (\[ f \])⁻ = \[ (/f)%seq \].
Proof.
  split; intros.
  - assert (\[ f \] ∈ HR). { apply HR_Elements; eauto. }
    New H. apply Seq_Inv_Close in H2.
    assert (\[ (/f)%seq \] ∈ HR). { apply HR_Elements; eauto. }
    assert (((f·(/f))%seq) ∈ Rᴺ /\ (ConstSeq 0%r) ∈ Rᴺ /\ (ConstSeq 1%r) ∈ Rᴺ).
    { split. apply Seq_Mult_Close; auto.
      split; apply ConstSeq_is_Seq; eauto with real. } destruct H4 as [H4[]].
    assert (\[ f \]·\[ (/f)%seq \] = 1).
    { rewrite HR_Mult_Instantiate; auto. apply equClassT1; auto.
      apply Equ_NPUF_is_equRelation_over_Rᴺ. apply AxiomII'; repeat split; auto.
      apply MKT49a; eauto. assert (\{ λ u, u ∈ N /\ f[u] <> 0%r \} ∈ F0).
      { apply NNPP; intro. elim H0. apply equClassT1; auto.
        apply Equ_NPUF_is_equRelation_over_Rᴺ.
        apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
        assert (\{ λ u, u ∈ N /\ f[u] <> 0%r \}
           ∪ \{ λ u, u ∈ N /\ f[u] = (ConstSeq 0%r)[u] \} = N).
        { apply AxiomI; split; intros.
          apply MKT4 in H8 as []; apply AxiomII in H8; tauto.
          apply MKT4. destruct (classic (f[z] = 0%r)); [right|left];
          apply AxiomII; repeat split; eauto.
          rewrite ConstSeq_Value; auto with real. }
        destruct F0_is_NPUF_over_N as [[[_[_[H9[]]]]_]_].
        rewrite <-H8 in H9. apply (FT1 F0 N) in H9 as []; auto.
        contradiction. destruct F0_is_NPUF_over_N; auto. }
      assert (\{ λ u, u ∈ N /\ f[u] <> 0%r \}
         ⊂ \{ λ u, u ∈ N /\ ((f·(/f))%seq)[u] = (ConstSeq 1%r)[u] \}).
      { red; intros. apply AxiomII in H8 as [H8[]].
        apply AxiomII; repeat split; auto.
        rewrite ConstSeq_Value,Seq_Mult_Property; auto with real.
        New H10. apply Seq_Inv_Property_b in H11; auto. rewrite H11.
        apply Divide_P1. apply AxiomII in H as [H[H12[]]].
        rewrite <-H13 in H9. apply Property_Value,Property_ran in H9; auto.
        apply MKT4'; split; auto. apply AxiomII; split. eauto. intro.
        apply MKT41 in H15; eauto with real. }
      destruct F0_is_NPUF_over_N as [[[_[_[H9[]]]]_]_].
      apply H11 in H8; auto. red; intros. apply AxiomII in H12; tauto. }
    assert (\[ (/f)%seq \] <> 0).
    { intro. rewrite H8 in H7. unfold "0" in H7.
      rewrite HR_Mult_Instantiate in H7; auto.
      apply equClassT1,AxiomII' in H7 as [H7[H9[]]]; auto.
      assert (\{ λ u, u ∈ N /\ ((f·(ConstSeq 0%r))%seq)[u]
        = (ConstSeq 1%r)[u] \} = Φ).
      { apply AxiomI; split; intros. apply AxiomII in H12 as [H12[]].
        rewrite Seq_Mult_Property,ConstSeq_Value,ConstSeq_Value,PlusMult_Co1
        in H14; auto with real. destruct OrderPM_Co9. contradiction.
        apply AxiomII in H as [H[H15[]]]. rewrite <-H16 in H13.
        apply Property_Value,Property_ran in H13; auto. elim (@ MKT16 z); auto. }
      rewrite H12 in H11. destruct F0_is_NPUF_over_N as [[[_[]]]];
      auto. apply Equ_NPUF_is_equRelation_over_Rᴺ. apply Seq_Mult_Close; auto. }
    assert (\{ λ a, a ∈ HR /\ a <> 0 /\ \[ f \]·a = 1 \}
      = [\[ (/f)%seq \]]).
    { apply AxiomI; split; intros. apply AxiomII in H9 as [H9[H10[]]].
      apply MKT41. apply Hyperreal_is_set. New H1.
      apply HR_Inv_Reasonable in H13 as [x[[H13[]]]]; auto.
      assert (x = \[ (/f)%seq \] /\ x = z) as []. { split; apply H16; auto. }
      rewrite <-H17,<-H18; auto. apply MKT41 in H9; eauto. rewrite H9.
      apply AxiomII; split; eauto. }
    unfold HR_Inv. rewrite H9. assert (Ensemble (\[ (/f)%seq \])). eauto.
    apply MKT44 in H10 as []; auto.
  - intro. rewrite H1,HR_Inv_0_is_universe in H0. apply MKT39.
    rewrite H0. apply Hyperreal_is_set.
Qed.

Property HR_Inv_Close : ∀ r, (r ∈ HR /\ r <> 0) <-> r⁻ ∈ HR.
Proof.
  split; intros. destruct H. New H. apply HR_Elements in H1 as [f[]].
  rewrite H2 in H0. apply HR_Inv_Instantiate in H0; auto. rewrite H2,H0.
  New H1. apply Seq_Inv_Close in H3. apply HR_Elements; eauto.
  assert (r <> 0).
  { intro. rewrite H0,HR_Inv_0_is_universe in H. elim MKT39. eauto. }
  split; auto. apply NNPP; intro.
  assert (\{ λ a, a ∈ HR /\ a <> 0 /\ r · a = 1 \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H2 as [H2[H3[]]].
    assert ([r,z] ∉ dom(HR_Mult_Func)).
    { intro. rewrite HR_Mult_Func_dom in H6.
      apply AxiomII' in H6 as [H6[]]; auto. }
    apply MKT69a in H6. elim MKT39. rewrite <-H6,H5. exists HR.
    apply HR_One_in_HR. elim (@ MKT16 z); auto. }
  unfold HR_Inv in H. rewrite H2,MKT24 in H. elim MKT39; eauto.
Qed.

Property HR_Div_0_is_universe : ∀ u, u/0 = μ.
Proof.
  intros. apply MKT69a. intro. rewrite HR_Inv_0_is_universe in H.
  apply AxiomII in H as []. apply MKT49b in H as []. apply MKT39; auto.
Qed.

Property HR_Div_Close : ∀ u v, u ∈ HR -> v ∈ HR -> v <> 0 <-> u/v ∈ HR.
Proof.
  split; intros.
  - apply HR_Mult_Close; auto. apply ->HR_Inv_Close; auto.
  - intro. rewrite H2,HR_Div_0_is_universe in H1. elim MKT39; eauto.
Qed.

End construction_with_NPUF.



(* 超实数实例化 *)
Module instantiate_hr_with_NPUF.

Parameter F0 : Class.
Parameter F0_is_NPUF_over_N : free_ultraFilter F0 N.

Declare Scope HR_scope.
Delimit Scope HR_scope with hr.
Open Scope HR_scope.

Notation Equ_NPUF := (Equ_NPUF F0).
Definition Equ_NPUF_is_equRelation_over_Rᴺ :=
  (Equ_NPUF_is_equRelation_over_Rᴺ F0 F0_is_NPUF_over_N).

Notation "\[ f \]" := (equClass f Equ_NPUF Rᴺ) : HR_scope.

Notation HR := (HR F0).

Notation HR_Zero := (HR_Zero F0).
Notation HR_One := (HR_One F0).
Notation HR_Leq := (HR_Leq F0).
Notation HR_Plus_Func := (HR_Plus_Func F0).
Notation HR_Neg := (HR_Neg F0).
Notation HR_Mult_Func := (HR_Mult_Func F0).
Notation HR_Inv := (HR_Inv F0).

Notation "0" := HR_Zero : HR_scope.
Notation "1" := HR_One : HR_scope.
Notation "u ≤ v" := (Rrelation u HR_Leq v) : HR_scope.
Notation "u < v" := (u ≤ v /\ u <> v)%hr : HR_scope.
Notation "u + v" := (HR_Plus_Func[[u,v]]) : HR_scope.
Notation "- u" := (HR_Neg u) : HR_scope.
Notation "u - v" := (u + (-v))%hr : HR_scope.
Notation "u · v" := (HR_Mult_Func[[u,v]]) : HR_scope.
Notation "u ⁻" := (HR_Inv u) : HR_scope.
Notation "u / v" := (u · (v⁻))%hr : HR_scope.

Definition HR_Elements := (HR_Elements F0).
Definition Hyperreal_is_set := (Hyperreal_is_set F0).
Definition HR_Zero_in_HR := (HR_Zero_in_HR F0).
Definition HR_One_in_HR := (HR_One_in_HR F0).
Definition HR_Zero_isnot_One := (HR_Zero_isnot_One F0 F0_is_NPUF_over_N).
Definition HR_Leq_Instantiate := (HR_Leq_Instantiate F0 F0_is_NPUF_over_N).
Definition HR_Less_Instantiate := (HR_Less_Instantiate F0 F0_is_NPUF_over_N).
Definition HR_Leq_Reasonable := (HR_Leq_Reasonable F0 F0_is_NPUF_over_N).
Definition HR_Plus_Reasonable := (HR_Plus_Reasonable F0 F0_is_NPUF_over_N).
Definition HR_Plus_Func_is_Function := (HR_Plus_Func_is_Function F0).
Definition HR_Plus_Func_dom := (HR_Plus_Func_dom F0 F0_is_NPUF_over_N).
Definition HR_Plus_Func_ran := (HR_Plus_Func_ran F0).
Definition HR_Plus_Instantiate := (HR_Plus_Instantiate F0 F0_is_NPUF_over_N).
Definition HR_Plus_Close := (HR_Plus_Close F0 F0_is_NPUF_over_N).
Definition HR_Neg_Reasonable := (HR_Neg_Reasonable F0 F0_is_NPUF_over_N).
Definition HR_Neg_Instantiate := (HR_Neg_Instantiate F0 F0_is_NPUF_over_N).
Definition HR_Neg_Close := (HR_Neg_Close F0 F0_is_NPUF_over_N).
Definition HR_Minus_Close := (HR_Minus_Close F0 F0_is_NPUF_over_N).
Definition HR_Mult_Reasonable := (HR_Mult_Reasonable F0 F0_is_NPUF_over_N).
Definition HR_Mult_Func_is_Function := (HR_Mult_Func_is_Function F0).
Definition HR_Mult_Func_dom := (HR_Mult_Func_dom F0 F0_is_NPUF_over_N).
Definition HR_Mult_Func_ran := (HR_Mult_Func_ran F0).
Definition HR_Mult_Instantiate := (HR_Mult_Instantiate F0 F0_is_NPUF_over_N).
Definition HR_Mult_Close := (HR_Mult_Close F0 F0_is_NPUF_over_N).
Definition HR_Inv_Reasonable := (HR_Inv_Reasonable F0 F0_is_NPUF_over_N).
Definition HR_Inv_0_is_universe := (HR_Inv_0_is_universe F0 F0_is_NPUF_over_N).
Definition HR_Inv_Instantiate := (HR_Inv_Instantiate F0 F0_is_NPUF_over_N).
Definition HR_Inv_Close := (HR_Inv_Close F0 F0_is_NPUF_over_N).
Definition HR_Div_0_is_universe := (HR_Div_0_is_universe F0 F0_is_NPUF_over_N).
Definition HR_Div_Close := (HR_Div_Close F0 F0_is_NPUF_over_N).

End instantiate_hr_with_NPUF.
