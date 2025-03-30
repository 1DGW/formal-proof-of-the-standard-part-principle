(***********************************************************************)
(*   This is part of axioms of real number, it is distributed under    *)
(*    the terms of the GNU Lesser General Public License version 3     *)
(*                (see file LICENSE for more details)                  *)
(*                                                                     *)
(*                       Copyright 2023-2026                           *)
(*          Ning Chen, Guowei Dou, Shukun Len and Wensheng Yu          *)
(***********************************************************************)

(** R_Axioms *)

Require Import mk.mk_theorems.

Close Scope nat_scope.

Declare Scope R_scope.
Delimit Scope R_scope with r.
Open Scope R_scope.

(* 实数集 *)
Parameter R : Class.

Axiom Ensemble_R : Ensemble R.

(* 加法函数 *)
Parameter fp : Class.

Axiom PlusR : (Function fp) /\ (dom(fp) = R × R) /\ (ran(fp) ⊂ R).

(* 加法 *)
Notation "x + y" := fp[[x, y]] : R_scope.

Corollary Plus_close : ∀ x y, x ∈ R -> y ∈ R -> (x + y) ∈ R.
Proof.
  intros. destruct PlusR as [H1[]].
  apply H3,(@ Property_ran ([x,y])),Property_Value; auto.
  rewrite H2. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Global Hint Resolve Plus_close : real.

(* 加法公理 *)
(* 加法单位元 *)
Parameter zeroR : Class.

Notation "0" := zeroR : R_scope.

Axiom zero_in_R : 0 ∈ R.

Global Hint Resolve zero_in_R : real.

Axiom Plus_P1 : ∀ x, x ∈ R -> x + 0 = x.

Axiom Plus_P2 : ∀ x, x ∈ R -> ∃ y, y ∈ R /\ x + y = 0.

Axiom Plus_P3 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> x + (y + z) = (x + y) + z.

Axiom Plus_P4 : ∀ x y, x ∈ R -> y ∈ R -> x + y = y + x.

(* 乘法函数 *)
Parameter fm : Class.

Axiom MultR : (Function fm) /\ (dom(fm) = R × R) /\ (ran(fm) ⊂ R).

(* 乘法 *)
Notation "x · y" := fm[[x, y]](at level 40) : R_scope.

Corollary Mult_close : ∀ x y, x ∈ R -> y ∈ R -> (x · y) ∈ R.
Proof.
  intros. destruct MultR as [H1[]].
  apply H3,(@ Property_ran ([x,y])),Property_Value; auto.
  rewrite H2. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Global Hint Resolve Mult_close : real.

(* 乘法公理 *)
(* 乘法单位元 *)
Parameter oneR : Class.

Notation "1" := oneR : R_scope.

Axiom one_in_R : 1 ∈ (R ~ [0]).

Corollary one_in_R_Co : 1 ∈ R.
Proof.
  pose proof one_in_R. apply MKT4' in H as []; auto.
Qed.

Global Hint Resolve one_in_R one_in_R_Co : real.

Axiom Mult_P1 : ∀ x, x ∈ R -> x · 1 = x.

Axiom Mult_P2 : ∀ x, x ∈ (R ~ [0])
  -> ∃ y, y ∈ (R ~ [0]) /\ x · y = 1.

Axiom Mult_P3 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> x · (y · z) = (x · y) · z.

Axiom Mult_P4 : ∀ x y, x ∈ R -> y ∈ R -> x · y = y · x.

Axiom Mult_P5 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> (x + y) · z = (x · z) + (y · z).

(* 序公理 *)
Parameter Leq : Class.

Axiom LeqR : Leq ⊂ R × R.

Notation "x ≤ y" := ([x, y] ∈ Leq)(at level 60) : R_scope.

Axiom Leq_P1 : ∀ x, x ∈ R -> x ≤ x.

Axiom Leq_P2 : ∀ x y, x ∈ R -> y ∈ R -> x ≤ y -> y ≤ x -> x = y.

Axiom Leq_P3 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y -> y ≤ z
  -> x ≤ z.

Axiom Leq_P4 : ∀ x y, x ∈ R -> y ∈ R -> x ≤ y \/ y ≤ x.

Axiom Plus_Leq : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y
  -> x + z ≤ y + z.

Axiom Mult_Leq : ∀ x y, x ∈ R -> y ∈ R -> 0 ≤ x -> 0 ≤ y
  -> 0 ≤ x · y.

(* 完备性公理 *)
Axiom Completeness : ∀ X Y, X ⊂ R -> Y ⊂ R -> X <> Φ -> Y <> Φ
  -> (∀ x y, x ∈ X -> y ∈ Y -> x ≤ y) -> ∃ c, c ∈ R
    /\ (∀ x y, x ∈ X -> y ∈ Y -> (x ≤ c /\ c ≤ y)).

(* 推论 加法公理的推论 *)
Corollary Plus_Co1 : ∀ x, x ∈ R -> (∀ y, y ∈ R -> y + x = y)
  -> x = 0.
Proof.
  intros. pose proof zero_in_R. pose proof (Plus_P1 x H).
  rewrite <-H2,Plus_P4; auto.
Qed.

Corollary Plus_Co2 : ∀ x, x ∈ R -> (exists ! x0, x0 ∈ R
  /\ x + x0 = 0).
Proof.
  intros. pose proof H. apply Plus_P2 in H0 as [x0[]].
  exists x0. split; auto. intros x1 []. rewrite <-H1 in H3.
  assert ((x + x0) + x1 = (x + x0) + x0).
  { rewrite <- Plus_P3,(Plus_P4 x0 x1),Plus_P3,H3; auto. }
  rewrite H1,Plus_P4,Plus_P1,Plus_P4,Plus_P1 in H4; auto;
  apply zero_in_R.
Qed.

Notation "- a" := (∩(\{ λ u, u ∈ R /\ u + a = 0 \})) : R_scope.

Corollary Plus_neg1a : ∀ a, a ∈ R -> (-a) ∈ R.
Proof.
  intros. pose proof H. apply Plus_Co2 in H0 as [a0[[]]].
  assert (\{ λ u, u ∈ R /\ u + a = 0 \} = [a0]).
  { apply AxiomI; split; intros. apply AxiomII in H3 as [H3[]].
    apply MKT41; eauto. symmetry. apply H2. rewrite Plus_P4; auto.
    apply MKT41 in H3; eauto. apply AxiomII.
    rewrite H3,Plus_P4; auto. split; eauto. }
  rewrite H3. assert (∩[a0] = a0). { apply MKT44; eauto. }
  rewrite H4; auto.
Qed.

Corollary Plus_neg1b : ∀ a, (-a) ∈ R -> a ∈ R.
Proof.
  intros. apply NNPP. intro.
  assert (\{ λ u, u ∈ R /\ u + a = 0 \} = Φ).
  { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply AxiomII in H1 as [H1[]].
    assert ([z,a] ∉ dom(fp)).
    { destruct PlusR as [H4[]]. intro. rewrite H5 in H7.
      apply AxiomII' in H7 as [H7[]]; auto. }
    apply MKT69a in H4. elim MKT39.
    rewrite <-H4,H3; eauto with real. }
  rewrite H1,MKT24 in H. elim MKT39; eauto.
Qed.

Corollary Plus_neg2 : ∀ a, a ∈ R -> a + (-a) = 0.
Proof.
  intros. pose proof H. apply Plus_Co2 in H0 as [a0[[]]].
  assert (\{ λ u, u ∈ R /\ u + a = 0 \} = [a0]).
  { apply AxiomI; split; intros. apply AxiomII in H3 as [H3[]].
    apply MKT41; eauto. symmetry. apply H2. rewrite Plus_P4; auto.
    apply MKT41 in H3; eauto. apply AxiomII.
    rewrite H3,Plus_P4; auto. split; eauto. }
  rewrite H3. assert (∩[a0] = a0). { apply MKT44; eauto. }
  rewrite H4; auto.
Qed.

Notation "x - y" := (x + (-y)) : R_scope.

Corollary Minus_P1 : ∀ a, a ∈ R -> a - a = 0.
Proof.
  intros. apply Plus_neg2; auto.
Qed.

Corollary Minus_P2 : ∀ a, a ∈ R -> a - 0 = a.
Proof.
  intros. pose proof zero_in_R.
  assert (\{ λ u, u ∈ R /\ u + 0 = 0 \} = [0]).
  { apply AxiomI; split; intros. apply AxiomII in H1 as [H1[]].
    apply MKT41; eauto. rewrite Plus_P1 in H3; auto.
    apply MKT41 in H1; eauto. rewrite H1. apply AxiomII;
    repeat split; eauto. rewrite Plus_P1; auto. }
  rewrite H1. assert (∩[0] = 0). { apply MKT44; eauto. }
  rewrite H2,Plus_P1; auto.
Qed.

Global Hint Resolve Plus_neg1a Plus_neg1b Plus_neg2 Minus_P1
  Minus_P2 : real.

Corollary Plus_Co3 : ∀ a x b, a ∈ R -> x ∈ R -> b ∈ R -> a + x = b
  -> x = b + (-a).
Proof.
  intros. pose proof H. apply Plus_Co2 in H3 as [a0[[]]].
  assert (x + a + a0 = b + a0). { rewrite (Plus_P4 x),H2; auto. }
  rewrite <-Plus_P3,H4,Plus_P1 in H6; auto.
  assert (\{ λ u, u ∈ R /\ u + a = 0 \} = [a0]).
  { apply AxiomI; split; intros. apply AxiomII in H7 as [H7[]].
    apply MKT41; eauto. symmetry. apply H5. rewrite Plus_P4; auto.
    apply MKT41 in H7; eauto. rewrite H7. rewrite Plus_P4 in H4;
    auto. apply AxiomII; split; eauto. }
  assert (Ensemble a0); eauto. apply MKT44 in H8 as [H8 _].
  rewrite H7,H8; auto.
Qed.

(* 推论 乘法公理的推论 *)
Corollary Mult_Co1 : ∀ x, x ∈ (R ~ [0]) -> (∀ y, y ∈ R
  -> y · x = y) -> x = 1.
Proof.
  intros. pose proof H. apply MKT4' in H1 as [].
  pose proof one_in_R. apply MKT4' in H3 as [].
  pose proof (Mult_P1 x H1). rewrite <-H5,Mult_P4; auto.
Qed.

Corollary Mult_Co2 : ∀ x, x ∈ (R ~ [0])
  -> (exists ! x0, x0 ∈ (R ~ [0]) /\ x · x0 = 1).
Proof.
  intros. pose proof H. pose proof zero_in_R.
  apply Mult_P2 in H0 as [x0[]]. exists x0.
  split; auto. intros x1 []. apply MKT4' in H as [H _].
  apply MKT4' in H3 as [H3 _]. apply MKT4' in H0 as [H0 _].
  assert (x0 · (x · x1) = x1).
  { rewrite Mult_P3,(Mult_P4 x0),H2,Mult_P4,Mult_P1;
    auto with real. }
  rewrite H4,Mult_P1 in H5; auto.
Qed.

Notation "a ⁻" := (∩(\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \}))
  (at level 5) : R_scope.

Corollary Mult_inv1 : ∀ a, a ∈ (R ~ [0]) -> (a⁻) ∈ (R ~ [0]).
Proof.
  intros. pose proof H. apply Mult_Co2 in H0 as [a1[[]]].
  pose proof H. pose proof H0. apply MKT4' in H3 as [H3 _].
  apply MKT4' in H4 as [H4 _].
  assert (\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \} = [a1]).
  { apply AxiomI; split; intros. apply AxiomII in H5 as [H5[]].
    apply MKT41; eauto. symmetry. apply H2. rewrite Mult_P4; auto.
    apply MKT4' in H6; tauto. apply MKT41 in H5; eauto.
    rewrite H5. apply AxiomII. rewrite Mult_P4; auto. split; eauto. }
  rewrite H5. assert (∩[a1] = a1). { apply MKT44; eauto. }
  rewrite H6; auto.
Qed.

Corollary Mult_inv2 : ∀ a, a ∈ (R ~ [0]) -> a · (a⁻) = 1.
Proof.
  intros. pose proof H. apply Mult_Co2 in H0 as [a1[[]]].
  pose proof H. pose proof H0. apply MKT4' in H3 as [H3 _].
  apply MKT4' in H4 as [H4 _].
  assert (\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \} = [a1]).
  { apply AxiomI; split; intros. apply AxiomII in H5 as [H5[]].
    apply MKT41; eauto. symmetry. apply H2. rewrite Mult_P4; auto.
    apply MKT4' in H6; tauto. apply MKT41 in H5; eauto.
    rewrite H5. apply AxiomII. rewrite Mult_P4; auto. split; eauto. }
  rewrite H5. assert (∩[a1] = a1). { apply MKT44; eauto. }
  rewrite H6; auto.
Qed.

Notation "m / n" := (m · (n⁻)) : R_scope.

Corollary Divide_P1 : ∀ a, a ∈ (R ~ [0]) -> a / a = 1.
Proof.
  intros. apply Mult_inv2; auto.
Qed.

Corollary Divide_P2 : ∀ a, a ∈ R -> a / 1 = a.
Proof.
  intros. assert (\{ λ u, u ∈ (R ~ [0]) /\ u · 1 = 1 \} = [1]).
  { apply AxiomI; split; intros. apply AxiomII in H0 as [H0[]].
    apply MKT41; eauto with real. rewrite Mult_P1 in H2; auto.
    apply MKT4' in H1; tauto. apply MKT41 in H0; eauto with real.
    rewrite H0. apply AxiomII; repeat split; eauto with real.
    rewrite Mult_P1; auto with real. }
  rewrite H0. assert (∩[1] = 1). { apply MKT44; eauto with real. }
  rewrite H1,Mult_P1; auto.
Qed.

Global Hint Resolve Mult_inv1 Mult_inv2 Divide_P1 Divide_P2 : real.

Corollary Mult_Co3 : ∀ a x b, a ∈ (R ~ [0]) -> x ∈ R -> b ∈ R
  -> a · x = b -> x = b · (a⁻).
Proof.
  intros. pose proof H. apply Mult_Co2 in H3 as [a0[[]]].
  apply MKT4' in H as []. pose proof H3. apply MKT4' in H3 as[].
  assert (x · a · a0 = b · a0). 
  { rewrite (Mult_P4 x), H2; auto. }
  rewrite <-Mult_P3,H4,Mult_P1 in H9; auto.
  assert (\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1\} = [a0]).
  { apply AxiomI; split; intros. apply AxiomII in H10 as [H10[]].
    apply MKT41; eauto. symmetry. apply H5. rewrite Mult_P4; auto.
    apply MKT4' in H11 as []; auto. apply MKT41 in H10; eauto. 
    rewrite H10. rewrite Mult_P4 in H4; auto. 
    apply AxiomII; split; eauto. }
  assert (Ensemble a0); eauto. apply MKT44 in H11 as [H11 _].
  rewrite H10,H11; auto.
Qed.

(* 推论 加法与乘法联系的公理推论 *)
Corollary PlusMult_Co1 : ∀ x, x ∈ R -> x · 0 = 0.
Proof.
  intros. pose proof zero_in_R.
  pose proof (Mult_P5 0 0 x H0 H0 H).
  rewrite Plus_P1 in H1; auto.
  assert (0 · x = ((0 · x) + (0 · x)) - (0 · x)).
  { rewrite <-Plus_P3,Minus_P1,Plus_P1; auto with real. }
  rewrite <-H1,Minus_P1,Mult_P4 in H2; auto with real.
Qed.

Corollary PlusMult_Co2 : ∀ x y, x ∈ R -> y ∈ R -> x · y = 0
  -> x = 0 \/ y = 0.
Proof.
  intros. destruct (classic (y = 0)); auto.
  assert (y ∈ (R ~ [0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H3; eauto with real. }
  rewrite Mult_P4 in H1; auto with real.
  apply Mult_Co3 in H1; auto with real.
  apply Mult_inv1,MKT4' in H3 as [H3 _].
  rewrite Mult_P4,PlusMult_Co1 in H1; auto with real.
Qed.

Corollary PlusMult_Co3 : ∀ x, x ∈ R -> -x = (-(1)) · x.
Proof.
  intros. assert (x - x = 0 /\ x + ((-(1)) · x) = 0) as [].
  { split; auto with real. replace (x + (-(1)) · x)
    with (1 · x + (-(1)) · x). rewrite <-Mult_P5,Minus_P1,
    Mult_P4,PlusMult_Co1; auto with real.
    rewrite Mult_P4,Mult_P1; auto with real. }
  pose proof H. apply Plus_Co2 in H2 as [x0[[]]].
  assert (x0 = - (1) · x /\ x0 = -x) as [].
  { split; apply H4; split; auto with real. }
  rewrite <-H5,H6; auto.
Qed.

Corollary PlusMult_Co4 : ∀ x, x ∈ R -> (-(1)) · (-x) = x.
Proof.
  intros. rewrite <-PlusMult_Co3; auto with real.
  assert ((-x) + (- -x) = 0). auto with real.
  assert ((-x) + x = 0).
  { rewrite Plus_P4; auto with real. }
  pose proof H. apply Plus_neg1a,Plus_Co2 in H2 as [x0[_]].
  assert (x0 = - -x). { apply H2; split; auto with real. }
  assert (x0 = x). { apply H2; auto. }
  rewrite <-H3,<-H4; auto.
Qed.

Corollary PlusMult_Co5 : ∀ x, x ∈ R -> (-x) · (-x) = x · x.
Proof.
  intros. rewrite PlusMult_Co3,<-Mult_P3,(Mult_P3 x),
  (Mult_P4 x),<-Mult_P3,<-(PlusMult_Co3 (x · x)),
  PlusMult_Co4; auto with real.
Qed.

Corollary PlusMult_Co6 : ∀ x, x ∈ (R ~ [0]) <-> (x⁻) ∈ (R ~ [0]).
Proof.
  split; intros; auto with real.
  assert (x ∈ R).
  { apply NNPP; intro.
    assert (\{ λ u, u ∈ (R ~ [0]) /\ u · x = 1 \} = Φ).
    { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
      apply AxiomII in H1 as [H1[]].
      assert (fm[[z,x]] = μ).
      { apply MKT69a. intro. destruct MultR as [H5[]].
        rewrite H6 in H4. apply AxiomII' in H4 as [_[]]; auto. }
      elim MKT39. rewrite <-H4,H3; eauto with real. }
    elim MKT39. rewrite <-MKT24,<-H1; eauto. }
  apply MKT4'; split; auto. apply AxiomII; split; eauto.
  intro. apply MKT41 in H1; eauto with real.
  assert (\{ λ u, u ∈ (R ~ [0]) /\ u · 0 = 1 \} = Φ).
  { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply AxiomII in H2 as [H2[]]. pose proof H3.
    apply MKT4' in H5 as [H5 _]. rewrite PlusMult_Co1 in H4; auto.
    pose proof one_in_R. apply MKT4' in H6 as [_].
    apply AxiomII in H6 as []. elim H7.
    apply MKT41; eauto with real. }
  elim MKT39. rewrite <-MKT24,<-H2. rewrite H1 in H. eauto.
Qed.

Definition lt x y := x ≤ y /\ x <> y.

Notation "x < y" := (lt x y) : R_scope.

(* 推论 序公理推论 *)
Corollary Order_Co1 : ∀ x y, x ∈ R -> y ∈ R
  -> x < y \/ y < x \/ x = y.
Proof.
  intros. pose proof H. apply (Leq_P4 x y) in H1 as []; auto;
  destruct (classic (x = y)); auto; [left|right; left]; split; auto.
Qed.

Corollary Order_Co2 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> (x < y /\ y ≤ z) \/ (x ≤ y /\ y < z) -> x < z.
Proof.
  intros. destruct H2 as [[[]]|[H2[]]];
  split; try apply (Leq_P3 x y z); auto; intro;
  [rewrite H5 in H2,H3; elim H3|rewrite <-H5 in H3,H4; elim H4];
  apply Leq_P2; auto.
Qed.

(* 推论 序与加法及乘法联系的公理推论 *)
Corollary OrderPM_Co1 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> x < y -> x + z < y + z.
Proof.
  intros. destruct H2. split. apply Plus_Leq; auto.
  intro. assert (x + z - z = y + z - z). { rewrite H4; auto. }
  rewrite <-Plus_P3,<-Plus_P3,Minus_P1,Plus_P1,Plus_P1 in H5;
  auto with real.
Qed.

Corollary OrderPM_Co2a : ∀ x, x ∈ R -> 0 < x -> (-x) < 0.
Proof.
  intros. apply (OrderPM_Co1 0 x (-x)) in H0; auto with real.
  rewrite Minus_P1,Plus_P4,Plus_P1 in H0; auto with real.
Qed.

Corollary OrderPM_Co2b : ∀ x, x ∈ R -> 0 ≤ x -> (-x) ≤ 0.
Proof.
  intros. destruct (classic (x = 0)).
  rewrite H1,PlusMult_Co3,PlusMult_Co1; auto with real.
  apply Leq_P1; auto with real.
  assert (-x < 0) as []; auto.
  { apply OrderPM_Co2a; auto. split; auto. }
Qed.

Corollary OrderPM_Co3 : ∀ x y z w, x ∈ R -> y ∈ R -> z ∈ R
  -> w ∈ R -> x ≤ y -> z ≤ w -> x + z ≤ y + w.
Proof.
  intros. assert (x + z ≤ y + z). { apply Plus_Leq; auto. }
  assert (y + z ≤ y + w).
  { rewrite Plus_P4,(Plus_P4 y); auto. apply Plus_Leq; auto. }
  apply (Leq_P3 _ (y + z)); auto with real.
Qed.

Corollary OrderPM_Co4 : ∀ x y z w, x ∈ R -> y ∈ R -> z ∈ R
  -> w ∈ R -> x ≤ y -> z < w -> x + z < y + w.
Proof.
  intros. assert (x + z ≤ y + z). { apply Plus_Leq; auto. }
  assert (y + z < y + w).
  { rewrite Plus_P4,(Plus_P4 y); auto. apply OrderPM_Co1; auto. }
  destruct H6. split. apply (Leq_P3 _ (y + z)); auto with real.
  intro. rewrite H8 in H5. elim H7. apply Leq_P2; auto with real.
Qed.

Corollary OrderPM_Co5 : ∀ x y, x ∈ R -> y ∈ R
  -> (0 < x /\ 0 < y) \/ (x < 0 /\ y < 0) -> 0 < x · y.
Proof.
  intros. destruct H1 as [[[][]]|[[][]]]; split;
  try (intro; symmetry in H5; apply PlusMult_Co2 in H5 as []; auto).
  apply Mult_Leq; auto. apply (Plus_Leq x 0 (-x)) in H1;
  auto with real. apply (Plus_Leq y 0 (-y)) in H3; auto with real.
  rewrite Minus_P1 in H1,H3; auto.
  rewrite Plus_P4,Plus_P1 in H1,H3; auto with real.
  apply (Mult_Leq (-x)) in H3; auto with real.
  rewrite PlusMult_Co3,(PlusMult_Co3 y),Mult_P3,<-(Mult_P3 (-(1))),
  (Mult_P4 x),Mult_P3,PlusMult_Co4,(Mult_P4 1),Mult_P1 in H3;
  auto with real.
Qed.

Corollary OrderPM_Co6 : ∀ x y, x ∈ R -> y ∈ R -> x < 0 -> 0 < y
  -> x · y < 0.
Proof.
  intros. apply (OrderPM_Co1 x 0 (-x)) in H1; auto with real.
  rewrite Minus_P1,Plus_P4,Plus_P1 in H1; auto with real.
  assert (0 < (-x) · y). { apply OrderPM_Co5; auto with real. }
  rewrite PlusMult_Co3,<-Mult_P3,<-PlusMult_Co3 in H3;
  auto with real. apply (OrderPM_Co1 _ _ (x · y)) in H3;
  auto with real. rewrite Plus_P4,Plus_P1,Plus_P4,Minus_P1 in H3;
  auto with real.
Qed.

Corollary OrderPM_Co7a : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x < y
  -> 0 < z -> x · z < y · z.
Proof.
  intros. apply (OrderPM_Co1 x y (-x)) in H2; auto with real.
  rewrite Minus_P1 in H2; auto.
  assert (0 < (y - x) · z). { apply OrderPM_Co5; auto with real. }
  rewrite Mult_P5 in H4; auto with real.
  apply (OrderPM_Co1 _ _ (x · z)) in H4; auto with real.
  rewrite Plus_P4,Plus_P1,<-Plus_P3,PlusMult_Co3,<-Mult_P3,
  <-PlusMult_Co3,(Plus_P4 (- (x · z))),Minus_P1,Plus_P1 in H4;
  auto with real.
Qed.

Corollary OrderPM_Co7b : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y
  -> 0 ≤ z -> x · z ≤ y · z.
Proof.
  intros. pose proof H0. apply (Order_Co1 x) in H4 as [H4|[]]; auto.
  pose proof H1. apply (Order_Co1 0) in H5 as [H5|[]];
  auto with real. apply (OrderPM_Co7a _ _ z) in H4; auto.
  destruct H4; auto. destruct H5. elim H6. apply Leq_P2;
  auto with real. rewrite <-H5,PlusMult_Co1,PlusMult_Co1; auto.
  apply Leq_P1; auto with real. destruct H4. elim H5.
  apply Leq_P2; auto. rewrite H4. apply Leq_P1; auto with real.
Qed.

Corollary OrderPM_Co8a : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x < y
  -> z < 0 -> y · z < x · z.
Proof.
  intros. apply (OrderPM_Co1 z 0 (-z)) in H3; auto with real.
  rewrite Minus_P1,Plus_P4,Plus_P1 in H3; auto with real.
  apply (OrderPM_Co1 x y (-x)) in H2; auto with real.
  rewrite Minus_P1 in H2; auto.
  assert (0 < (y - x) · (-z)). { apply OrderPM_Co5; auto with real. }
  rewrite (PlusMult_Co3 z),Mult_P4,<-Mult_P3,<-PlusMult_Co3 in H4;
  auto with real. apply (OrderPM_Co1 _ _ (z · (y - x))) in H4;
  auto with real. rewrite Plus_P4,Plus_P1,
  (Plus_P4 (-(z · (y - x)))),Minus_P1 in H4; auto with real.
  rewrite Mult_P4,Mult_P5 in H4; auto with real.
  apply (OrderPM_Co1 _ _ (x · z)) in H4; auto with real.
  rewrite <-Plus_P3,(Plus_P4 (- x · z)),PlusMult_Co3,
  <-Mult_P3,<-PlusMult_Co3,Minus_P1,Plus_P1,Plus_P4,Plus_P1 in H4;
  auto with real.
Qed.

Corollary OrderPM_Co8b : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y
  -> z ≤ 0 -> y · z ≤ x · z.
Proof.
  intros. assert (0 ≤ (-z)).
  { pose proof zero_in_R. apply (Order_Co1 (-z)) in H4 as [H4|[]];
    auto with real. apply (OrderPM_Co1 _ _ z) in H4; auto with real.
    rewrite Plus_P4,Minus_P1,Plus_P4,Plus_P1 in H4; auto with real.
    destruct H4. elim H5. apply Leq_P2; auto with real.
    destruct H4; auto. rewrite H4. apply Leq_P1; auto with real. }
  apply (OrderPM_Co7b _ _ (-z)) in H2; auto with real.
  apply (OrderPM_Co3 _ _ (x · z) (x · z)) in H2; auto with real;
  [ |apply Leq_P1; auto with real].
  rewrite Mult_P4,(Mult_P4 x),<-Mult_P5,Plus_P4,Minus_P1,
  Mult_P4,PlusMult_Co1 in H2; auto with real.
  apply (OrderPM_Co3 _ _ (y · z) (y · z)) in H2; auto with real;
  [ |apply Leq_P1; auto with real].
  rewrite Plus_P4,Plus_P1,Plus_P4,Plus_P3,Mult_P4,(Mult_P4 y),
  <-Mult_P5,Plus_P4,Minus_P1,(Mult_P4 0),PlusMult_Co1,Plus_P1,
  Mult_P4,(Mult_P4 z) in H2; auto with real.
Qed.

Corollary OrderPM_Co9 : 0 < 1.
Proof.
  pose proof zero_in_R. pose proof one_in_R.
  apply MKT4' in H0 as []. apply AxiomII in H1 as [].
  pose proof H. apply (Order_Co1 0 1) in H3 as [H3|[|]]; auto.
  - assert (0 < 1 · 1). { apply OrderPM_Co5; auto. }
    rewrite Mult_P1 in H4; auto.
  - elim H2. apply MKT41; eauto.
Qed.

Global Hint Resolve OrderPM_Co9 : real.

Corollary OrderPM_Co10 : ∀ x, x ∈ R -> 0 < x -> 0 < (x⁻).
Proof.
  intros. assert (x <> 0).
  { intro. rewrite H1 in H0. destruct H0; auto. }
  assert (x ∈ (R ~ [0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H2; eauto with real. }
  assert (x · (x⁻) = 1). { apply Divide_P1; auto. }
  assert ((x⁻) ∈ R).
  { apply Mult_inv1 in H2. apply MKT4' in H2; tauto. }
  pose proof zero_in_R. apply (Order_Co1 0 (x⁻)) in H5 as [H5|[|]];
  auto. apply (OrderPM_Co6 (x⁻) x) in H5; auto.
  rewrite Mult_P4,H3 in H5; auto. destruct H5.
  destruct OrderPM_Co9. elim H8. apply Leq_P2; auto with real.
  rewrite <-H5,PlusMult_Co1 in H3; auto. pose proof one_in_R.
  apply MKT4' in H6 as []. apply AxiomII in H7 as []. elim H8.
  apply MKT41; eauto with real.
Qed.

Corollary OrderPM_Co11 : ∀ x y, x ∈ R -> y ∈ R -> 0 < x -> x < y
  -> 0 < (y⁻) /\ (y⁻) < (x⁻).
Proof.
  intros. assert (0 < y).
  { destruct H1,H2. split. apply (Leq_P3 0 x y); auto with real.
    intro. rewrite H5 in H1. elim H4. apply Leq_P2; auto. }
  split. apply OrderPM_Co10; auto.
  assert (0 < (x⁻) /\ 0 < (y⁻)) as [].
  { split; apply OrderPM_Co10; auto. }
  assert (x ∈ (R ~ [0]) /\ y ∈ (R ~ [0])) as [].
  { split; apply MKT4'; split; auto; apply AxiomII; split; eauto;
    intro; apply MKT41 in H6; eauto with real;
    [rewrite H6 in H1; destruct H1|rewrite H6 in H3; destruct H3];
    auto. }
  pose proof H6; pose proof H7. apply Mult_inv1 in H8,H9.
  apply MKT4' in H8 as [H8 _]. apply MKT4' in H9 as [H9 _].
  pose proof H2. apply (OrderPM_Co7a x y (x⁻)) in H10; auto.
  rewrite Divide_P1 in H10; auto.
  apply (OrderPM_Co7a _ _ (y⁻)) in H10; auto with real.
  rewrite Mult_P4,Mult_P1,Mult_P4,Mult_P3,(Mult_P4 _ y),
  Divide_P1,Mult_P4,Mult_P1 in H10; auto with real.
Qed.

(* 完备公理与数集确界的存在性 *)
Definition Upper X c := X ⊂ R /\ c ∈ R /\ (∀ x, x ∈ X -> x ≤ c).

Definition Lower X c := X ⊂ R /\ c ∈ R /\ (∀ x, x ∈ X -> c ≤ x).

Definition Bounded X := ∃ c1 c2, Upper X c1 /\ Lower X c2.

Definition Max X c := X ⊂ R /\ c ∈ X /\ (∀ x, x ∈ X -> x ≤ c).

Definition Min X c := X ⊂ R /\ c ∈ X /\ (∀ x, x ∈ X -> c ≤ x).

Corollary Max_Corollary : ∀ X c1 c2, Max X c1 -> Max X c2
  -> c1 = c2.
Proof.
  intros. destruct H as [H[]],H0 as [H0[]].
  pose proof H1. pose proof H3. apply H2 in H5.
  apply H4 in H6. apply Leq_P2; auto.
Qed.

Corollary Min_Corollary : ∀ X c1 c2, Min X c1 -> Min X c2
  -> c1 = c2.
Proof.
  intros. destruct H as [H[]],H0 as [H0[]].
  pose proof H1. pose proof H3. apply H2 in H5.
  apply H4 in H6. apply Leq_P2; auto.
Qed.

Definition Sup1 X s := Upper X s /\ (∀ s1, s1 ∈ R -> s1 < s
  -> (∃ x1, x1 ∈ X /\ s1 < x1)).

Definition Sup2 X s := Min (\{ λ u, Upper X u \}) s.

Corollary Sup_Corollary : ∀ X s, Sup1 X s <-> Sup2 X s.
Proof.
  split; intros; destruct H.
  - destruct H as [H[]]. repeat split. unfold Included; intros.
    apply AxiomII in H3 as [_[_[]]]; auto. apply AxiomII; split;
    eauto. split; auto. intros. apply AxiomII in H3 as [H3[H4[]]].
    pose proof H5. apply (Order_Co1 x s) in H7 as [H7|[|]]; auto.
    apply H0 in H7 as [x1[]]; auto. pose proof H7. apply H6 in H7.
    destruct H8. elim H10. apply Leq_P2; auto. destruct H7; auto.
    rewrite H7. apply Leq_P1; auto.
  - destruct H0. apply AxiomII in H0 as [H0[H2[]]].
    repeat split; auto. intros. apply NNPP; intro.
    assert (∀ x1, x1 ∈ X -> x1 ≤ s1).
    { intros. apply NNPP; intro. elim H7. exists x1. split; auto.
      pose proof H5. apply (Order_Co1 x1 s1) in H10 as [H10|[|]];
      auto. destruct H10. elim H9; auto. rewrite H10 in H9.
      elim H9. apply Leq_P1; auto. }
    assert (s1 ∈ \{ λ u, Upper X u \}).
    { apply AxiomII; split; eauto. split; auto. }
    apply H1 in H9. destruct H6. elim H10. apply Leq_P2; auto.
Qed.

Definition Inf1 X i := Lower X i /\ (∀ i1, i1 ∈ R -> i < i1
  -> (∃ x1, x1 ∈ X /\ x1 < i1)).

Definition Inf2 X i := Max (\{ λ u, Lower X u \}) i.

Corollary Inf_Corollary : ∀ X i, Inf1 X i <-> Inf2 X i.
Proof.
  split; intros; destruct H.
  - destruct H as [H[]]. repeat split. unfold Included; intros.
    apply AxiomII in H3 as [_[_[]]]; auto. apply AxiomII; split;
    eauto. split; auto. intros. apply AxiomII in H3 as [H3[H4[]]].
    pose proof H5. apply (Order_Co1 x i) in H7 as [H7|[|]]; auto.
    destruct H7; auto. apply H0 in H7 as [x1[]]; auto.
    pose proof H7. apply H6 in H7. destruct H8. elim H10.
    apply Leq_P2; auto. rewrite H7. apply Leq_P1; auto.
  - destruct H0. apply AxiomII in H0 as [H0[H2[]]].
    repeat split; auto. intros. apply NNPP; intro.
    assert (∀ x1, x1 ∈ X -> i1 ≤ x1).
    { intros. apply NNPP; intro. elim H7. exists x1. split; auto.
      pose proof H5. apply (Order_Co1 x1 i1) in H10 as [H10|[|]];
      auto. destruct H10. elim H9; auto. rewrite H10 in H9.
      elim H9. apply Leq_P1; auto. }
    assert (i1 ∈ \{ λ u, Lower X u \}).
    { apply AxiomII; split; eauto. split; auto. }
    apply H1 in H9. destruct H6. elim H10. apply Leq_P2; auto.
Qed.

Theorem SupT : ∀ X, X ⊂ R -> X <> Φ -> (∃ c, Upper X c)
  -> exists ! s, Sup1 X s.
Proof.
  intros. destruct H1 as [x]. set (Y := \{ λ u, Upper X u \}).
  assert (Y <> Φ).
  { apply NEexE. exists x. apply AxiomII; split; auto.
    destruct H1 as [_[]]. eauto. }
  assert (Y ⊂ R).
  { unfold Included; intros. apply AxiomII in H3 as [_[_[]]]; auto. }
  assert (∃ c, c ∈ R /\ (∀ x y, x ∈ X -> y ∈ Y
    -> (x ≤ c /\ c ≤ y))) as [c[]].
  { apply Completeness; auto. intros. apply AxiomII in H5
    as [_[_[]]]; auto. }
  assert (c ∈ Y).
  { apply AxiomII; split; eauto. repeat split; auto. intros.
    apply NEexE in H2 as [y]. apply (H5 x0 y) in H6; tauto. }
  assert (Sup2 X c).
  { repeat split; auto. intros. apply NEexE in H0 as [x1].
    apply (H5 x1 x0) in H7; tauto. }
  exists c. split. apply Sup_Corollary; auto. intros.
  apply Sup_Corollary in H8. apply (Min_Corollary Y); auto.
Qed.

Theorem InfT : ∀ X, X ⊂ R -> X <> Φ -> (∃ c, Lower X c)
  -> exists ! i, Inf1 X i.
Proof.
  intros. destruct H1 as [x]. set (Y := \{ λ u, Lower X u \}).
  assert (Y <> Φ).
  { apply NEexE. exists x. apply AxiomII; split; auto.
    destruct H1 as [_[]]. eauto. }
  assert (Y ⊂ R).
  { unfold Included; intros. apply AxiomII in H3 as [_[_[]]]; auto. }
  assert (∃ c, c ∈ R /\ (∀ y x, y ∈ Y -> x ∈ X
    -> (y ≤ c /\ c ≤ x))) as [c[]].
  { apply Completeness; auto. intros. apply AxiomII in H4
    as [_[_[]]]; auto. }
  assert (c ∈ Y).
  { apply AxiomII; split; eauto. repeat split; auto. intros.
    apply NEexE in H2 as [y]. apply (H5 y x0) in H6; tauto. }
  assert (Inf2 X c).
  { repeat split; auto. intros. apply NEexE in H0 as [x1].
    apply (H5 x0 x1) in H7; tauto. }
  exists c. split. apply Inf_Corollary; auto. intros.
  apply Inf_Corollary in H8. apply (Max_Corollary Y); auto.
Qed.

(* 自然数集的定义 *)
(* 归纳集的定义 *)
Definition IndSet X := X ⊂ R /\ (∀ x, x ∈ X -> (x + 1) ∈ X).

Proposition IndSet_P1 : ∀ X, X <> Φ -> (∀ x, x ∈ X -> IndSet x)
  -> IndSet (∩X).
Proof.
  intros. apply NEexE in H as [x]. split; unfold Included; intros.
  apply AxiomII in H1 as []. pose proof H. apply H0 in H as [].
  apply H2 in H3; auto. apply AxiomII in H1 as []. pose proof H.
  apply H2,H0 in H3; auto. apply AxiomII; split; eauto. intros.
  pose proof H4. apply H0 in H4 as []. apply H2 in H5; auto.
Qed.

(* 自然数集 *)
Definition N := ∩(\{ λ u, IndSet u /\ 1 ∈ u \}).

Corollary N_Subset_R : N ⊂ R.
Proof.
  unfold Included; intros. apply AxiomII in H as [].
  assert (R ∈ \{ λ u, IndSet u /\ 1 ∈ u \}).
  { apply AxiomII; repeat split; auto with real. apply Ensemble_R. }
  apply H0 in H1; auto.
Qed.

Corollary one_in_N : 1 ∈ N.
Proof.
  apply AxiomII; split; eauto with real; intros.
  apply AxiomII in H as [H[]]; auto.
Qed.

Corollary zero_not_in_N : 0 ∉ N.
Proof.
  intro. apply AxiomII in H as [].
  assert (\{ λ u, u ∈ R /\ 0 < u \} ⊂ R).
  { unfold Included; intros. apply AxiomII in H1 as []; tauto. }
  assert (\{ λ u, u ∈ R /\ 0 < u \}
    ∈ \{ λ u, IndSet u /\ 1 ∈ u \}).
  { apply AxiomII; repeat split; auto. apply (MKT33 R); auto.
    apply Ensemble_R. intros. apply AxiomII in H2 as [H2[]].
    apply AxiomII; split; eauto with real. split; auto with real.
    destruct H4. apply (OrderPM_Co4 0 x 0 1) in H4; auto with real.
    rewrite Plus_P1 in H4; auto with real.
    apply AxiomII; split; [ |split]; eauto with real. }
  apply H0,AxiomII in H2 as [_[_[]]]; auto.
Qed.

Corollary IndSet_N : IndSet N.
Proof.
  apply IndSet_P1; intros. apply NEexE. exists R.
  apply AxiomII; repeat split; eauto with real.
  apply Ensemble_R. apply AxiomII in H as [_[]]; auto.
Qed.

Global Hint Resolve N_Subset_R one_in_N : real.

(* 数学归纳原理 *)
Theorem MathInd : ∀ E, E ⊂ N -> 1 ∈ E -> (∀ x, x ∈ E
  -> (x + 1) ∈ E) -> E = N.
Proof.
  intros. assert (IndSet E).
  { split; auto. unfold Included; intros. apply N_Subset_R; auto. }
  apply MKT27; split; auto. unfold Included; intros.
  apply AxiomII in H3 as []. apply H4. apply AxiomII; split; auto.
  apply (MKT33 N); auto. apply (MKT33 R). apply Ensemble_R.
  apply N_Subset_R.
Qed.

(* 自然数的性质 *)
Proposition Nat_P1a : ∀ m n, m ∈ N -> n ∈ N
  -> (m + n) ∈ N.
Proof.
  intros. set (E := \{ λ u, u ∈ N /\ ∀ v, v ∈ N -> (u + v) ∈ N \}).
  assert (1 ∈ E).
  { apply AxiomII; repeat split; eauto with real. intros.
    destruct IndSet_N. rewrite Plus_P4; auto with real. }
  assert (E = N).
  { apply MathInd; unfold Included; intros; auto.
    apply AxiomII in H2 as []; tauto. apply AxiomII in H2 as [H2[]].
    apply AxiomII; repeat split; eauto with real. intros.
    pose proof H5. apply H4 in H5.
    rewrite <-Plus_P3,(Plus_P4 1),Plus_P3; auto with real.
    destruct IndSet_N. apply H8; auto with real. }
  rewrite <-H2 in H. apply AxiomII in H as [H[]]; auto.
Qed.

Proposition Nat_P1b : ∀ m n, m ∈ N -> n ∈ N
  -> (m · n) ∈ N.
Proof.
  intros. set (E := \{ λ u, u ∈ N /\ ∀ v, v ∈ N -> (u · v) ∈ N \}).
  assert (1 ∈ E).
  { apply AxiomII; repeat split; eauto with real. intros.
    rewrite Mult_P4,Mult_P1; auto with real. }
  assert (E = N).
  { apply MathInd; unfold Included; intros; auto.
    apply AxiomII in H2 as []; tauto. apply AxiomII in H2 as [H2[]].
    apply AxiomII; repeat split; eauto with real.
    apply Nat_P1a; auto with real. intros.
    rewrite Mult_P5,(Mult_P4 1),Mult_P1; auto with real.
    apply Nat_P1a; auto. }
  rewrite <-H2 in H. apply AxiomII in H as [H[]]; auto.
Qed.

Global Hint Resolve Nat_P1a Nat_P1b : real.

Proposition Nat_P2 : ∀ n, n ∈ N -> n <> 1 -> (n - 1) ∈ N.
Proof.
  intros. set (E := \{ λ u, u ∈ N /\ ∃ v, v ∈ N /\ u = v + 1 \}
    ∪ [1]).
  assert (1 ∈ E).
  { apply MKT4; right. apply MKT41; eauto with real. }
  assert (E = N).
  { assert (E ⊂ N).
    { unfold Included; intros. apply MKT4 in H2 as [].
      apply AxiomII in H2; tauto. apply MKT41 in H2; eauto with real.
      rewrite H2. auto with real. }
    apply MathInd; auto. intros. apply MKT4; left.
    apply AxiomII; repeat split; eauto with real. }
  rewrite <-H2 in H. apply MKT4 in H as [].
  apply AxiomII in H as [H[H3[m[]]]].
  rewrite H5,<-Plus_P3,Minus_P1,Plus_P1; auto with real.
  apply MKT41 in H; eauto. elim H0; auto.
Qed.

(* 书打错集合里的n应该是x *)
Proposition Nat_P3 : ∀ n, n ∈ N
  -> Min (\{ λ u, u ∈ N /\ n < u \}) (n + 1).
Proof.
  intros. set (E := \{ λ u, u ∈ N
    /\ Min (\{ λ v, v ∈ N /\ u < v \}) (u + 1) \}).
  set (M := \{ λ u, u ∈ N /\ (u = 1 \/ (1 + 1) ≤ u) \}).
  assert (1 ∈ M).
  { apply AxiomII; repeat split; eauto with real. }
  assert (M = N).
  { apply MathInd; unfold Included; intros; auto.
    apply AxiomII in H1; tauto. apply AxiomII in H1 as [H1[]].
    apply AxiomII; repeat split; eauto with real. right.
    destruct H3. rewrite H3. apply Leq_P1; auto with real.
    apply (OrderPM_Co3 _ _ 0 1) in H3; auto with real.
    rewrite Plus_P1 in H3; auto with real.
    destruct OrderPM_Co9; auto. }
  assert (1 ∈ E).
  { apply AxiomII; repeat split; unfold Included; eauto with real;
    intros. apply AxiomII in H2 as [_[]]; auto with real.
    apply AxiomII; repeat split; eauto with real.
    destruct OrderPM_Co9. apply (OrderPM_Co3 0 1 1 1) in H2;
    auto with real. rewrite Plus_P4,Plus_P1 in H2; auto with real.
    apply Leq_P1; auto with real. intro.
    assert (1 - 1 = 1 + 1 - 1). { rewrite <-H2; auto. }
    rewrite Minus_P1,<-Plus_P3,Minus_P1,Plus_P1 in H3;
    auto with real. destruct OrderPM_Co9; auto.
    apply AxiomII in H2 as [H2[]]. rewrite <-H1 in H3.
    apply AxiomII in H3 as [_[H3[]]]; auto. destruct H4.
    elim H6; auto. }
  assert (E = N).
  { apply MathInd; unfold Included; intros; auto.
    apply AxiomII in H3; tauto. apply AxiomII in H3 as [H3[]].
    destruct H5 as [H5[]]. apply AxiomII; repeat split;
    unfold Included; intros; eauto with real.
    apply AxiomII in H8 as [_[]]; auto with real.
    apply AxiomII; repeat split; eauto with real.
    apply AxiomII in H6 as [_[]]. destruct H8.
    apply (OrderPM_Co3 _ _ 1 1) in H8; auto with real.
    apply Leq_P1; auto with real. intro.
    apply AxiomII in H6 as [_[_[]]]. elim H9.
    assert (x + 1 - 1 = x + 1 + 1 - 1). { rewrite <-H8; auto. }
    rewrite <-Plus_P3,<-Plus_P3,Minus_P1,Plus_P1,Plus_P1 in H10;
    auto with real. apply AxiomII in H8 as [H8[]].
    assert (x + 1 ≤ x0 - 1).
    { apply H7. assert ((x0 - 1) ∈ N).
      { apply Nat_P2; auto. intro. rewrite H11 in H10.
        destruct H10. apply (OrderPM_Co3 _ _ (-(1)) (-(1))) in H10;
        auto with real. rewrite <-Plus_P3,Minus_P1,Plus_P1 in H10;
        auto with real. rewrite <-H1 in H4. apply AxiomII in H4
        as [_[H4[]]]. rewrite H13 in H10. destruct OrderPM_Co9.
        elim H15. apply Leq_P2; auto with real.
        apply (Leq_P3 (1 + 1)) in H10; auto with real.
        destruct OrderPM_Co9. apply (OrderPM_Co4 0 1 0 1) in H14;
        auto with real. rewrite Plus_P1 in H14; auto with real.
        destruct H14. elim H16. apply Leq_P2; auto with real.
        apply Leq_P1; auto with real. }
      apply AxiomII; split; eauto. split; auto.
      apply (OrderPM_Co4 (-(1)) (-(1)) (x + 1) x0) in H10;
      auto with real. rewrite Plus_P4,<-Plus_P3,Minus_P1,
      Plus_P1,Plus_P4 in H10; auto with real.
      apply Leq_P1; auto with real. }
    apply (OrderPM_Co3 _ _ 1 1) in H11; auto with real.
    rewrite <-(Plus_P3 x0),(Plus_P4 (-(1))),Minus_P1,Plus_P1
    in H11; auto with real. apply Leq_P1; auto with real. }
  rewrite <-H3 in H. apply AxiomII in H; tauto.
Qed.

Proposition Nat_P4 : ∀ m n, m ∈ N -> n ∈ N -> n < m -> (n + 1) ≤ m.
Proof.
  intros. assert (Min (\{ λ u, u ∈ N /\ n < u \}) (n + 1)).
  { apply Nat_P3; auto. }
  destruct H2 as [H2[]]. apply H4. apply AxiomII; split; eauto.
Qed.

Proposition Nat_P5 : ∀ n, n ∈ N
  -> ~ (∃ x, x ∈ N /\ n < x /\ x < (n + 1)).
Proof.
  intros. intro. destruct H0 as [x[H0[]]].
  apply Nat_P4 in H1; auto. destruct H2. elim H3.
  apply Leq_P2; auto with real.
Qed.

(* 书上和性质2有重复 *)
Proposition Nat_P6 : ∀ n, n ∈ N -> n <> 1
  -> ~ (∃ x, x ∈ N /\ (n - 1) < x /\ x < n).
Proof.
  intros. intro. destruct H1 as [x[H1[]]].
  apply Nat_P4 in H2; auto; [ |apply Nat_P2]; auto.
  rewrite <-Plus_P3,(Plus_P4 (-(1))),Minus_P1,Plus_P1 in H2;
  auto with real. destruct H3. elim H4.
  apply Leq_P2; auto with real.
Qed.

Lemma one_is_min_in_N : Min N 1.
Proof.
  repeat split. apply N_Subset_R. apply one_in_N.
  intros. set (E := \{ λ u, u ∈ N /\ 1 ≤ u \}).
  assert (1 ∈ E).
  { apply AxiomII; repeat split; eauto with real.
    apply Leq_P1; auto with real. }
  assert (E = N).
  { apply MathInd; unfold Included; intros; auto.
    apply AxiomII in H1; tauto. apply AxiomII in H1 as [H1[]].
    apply AxiomII; repeat split; eauto with real.
    apply (OrderPM_Co3 1 x0 0 1) in H3; auto with real.
    rewrite Plus_P1 in H3; auto with real.
    destruct OrderPM_Co9; auto. }
  rewrite <-H1 in H. apply AxiomII in H; tauto.
Qed.

Proposition Nat_P7 : ∀ E, E ⊂ N -> E <> Φ -> ∃ n, Min E n.
Proof.
  intros. assert (∃ n, Lower E n).
  { exists 1. repeat split; unfold Included; auto with real.
    intros. apply one_is_min_in_N; auto. }
  apply InfT in H1 as [e[H1 _]]; unfold Included; auto with real.
  destruct (classic (e ∈ E)). exists e. repeat split;
  unfold Included; intros; auto with real.
  destruct H1 as [[_[]]]; auto.
  assert (∀ x, x ∈ E -> e < x).
  { intros. destruct H1 as [[_[]]]. split; auto. intro.
    elim H2. rewrite H6; auto. }
  assert (e ∈ R). { destruct H1 as [[_[]]]; auto. }
  assert (e < e + 1).
  { pose proof H4. apply Leq_P1 in H5.
    apply (OrderPM_Co3 _ _ 0 1) in H5; auto with real.
    rewrite Plus_P1 in H5; auto. split; auto. intro.
    assert (e - e = e + 1 - e). { rewrite <-H6; auto. }
    rewrite Minus_P1,(Plus_P4 e),<-Plus_P3,Minus_P1,Plus_P1 in H7;
    auto with real. destruct OrderPM_Co9; auto.
    destruct OrderPM_Co9; auto. }
  destruct H1. apply H6 in H5 as [m[]]; auto with real.
  exists m. repeat split; unfold Included; intros; auto with real.
  assert (m ∈ R /\ x ∈ R) as []. { split; auto with real. }
  pose proof H9. apply (Order_Co1 x m) in H11 as [H11|[|]]; auto.
  assert (x + 1 ≤ m). { apply Nat_P4; auto. }
  assert (x + 1 < e + 1).
  { apply (Order_Co2 _ m); auto with real. }
  apply (OrderPM_Co4 (-(1)) (-(1))) in H13; auto with real.
  rewrite Plus_P4,<-Plus_P3,Minus_P1,Plus_P1,Plus_P4,<-Plus_P3,
  Minus_P1,Plus_P1 in H13; auto with real. apply H3 in H8.
  destruct H8,H13. elim H15. apply Leq_P2; auto.
  apply Leq_P1; auto with real. destruct H11; auto.
  rewrite H11. apply Leq_P1; auto.
Qed.

(* 整数的定义 *)
Definition Z := N ∪ \{ λ u, (-u) ∈ N \} ∪ [0].

(* 整数的性质 *)
Corollary N_Subset_Z : N ⊂ Z.
Proof.
  unfold Included; intros. apply AxiomII; split; eauto.
Qed.

Corollary Z_Subset_R : Z ⊂ R.
Proof.
  unfold Included; intros. apply MKT4 in H as []; auto with real. 
  apply MKT4 in H as []. apply AxiomII in H as [].
  apply N_Subset_R in H0. apply NNPP. intro.
  assert (\{ λ u, u ∈ R /\ u + z = 0 \} = Φ).
  { apply AxiomI; split; intros; elim (@ MKT16 z0); auto.
    apply AxiomII in H2 as [H2[]].
    assert ([z0,z] ∉ dom(fp)).
    { destruct PlusR as [H5[]]. intro. rewrite H6 in H8.
      apply AxiomII' in H8 as [H8[]]; auto. } 
    apply MKT69a in H5. rewrite H4 in H5. elim MKT39.
    rewrite <-H5; eauto with real. }
  assert (∩(\{ λ u, u ∈ R /\ u + z = 0 \}) = μ).
  { rewrite H2. apply MKT24. }
  elim MKT39. rewrite <-H3; eauto. apply MKT41 in H;
  eauto with real. rewrite H. apply zero_in_R.
Qed.

Lemma Int_P1_Lemma : ∀ m n, m ∈ N -> n ∈ N -> m < n 
  -> (n - m) ∈ N.
Proof.
  intros. set (E := \{ λ u, u ∈ N /\ ∀ v, v ∈ N -> u < v
    -> (v - u) ∈ N \}).
  assert (1 ∈ E).
  { apply AxiomII; repeat split; eauto with real. intros.
    apply Nat_P2; auto. intro. destruct H3; auto. }
  assert (E = N).
  { apply MathInd; unfold Included; intros; auto.
    apply AxiomII in H3 as []; tauto. apply AxiomII in H3 as [H3[]].
    apply AxiomII; repeat split; eauto with real. intros.
    apply (OrderPM_Co1 _ _ (-(1))) in H7; auto with real.
    rewrite <-Plus_P3,Minus_P1,Plus_P1 in H7; auto with real.
    apply H5 in H7; auto. rewrite PlusMult_Co3,Mult_P4,Mult_P5,
    Mult_P4,<-PlusMult_Co3,Mult_P4,Mult_P1,(Plus_P4 (-x)),Plus_P3;
    auto with real. apply Nat_P2; auto. intro.
    rewrite H8,Minus_P1 in H7; auto with real.
    destruct one_is_min_in_N as [_[_]]. pose proof H4.
    apply H9 in H10. assert (x < x).
    { apply (Order_Co2 _ 0); auto with real. left. split; auto.
      apply (Order_Co2 _ 1); auto with real. }
    destruct H11; auto. }
  rewrite <-H3 in H. apply AxiomII in H as [H[]]; auto.
Qed.

Proposition Int_P1a : ∀ m n, m ∈ Z -> n ∈ Z -> (m + n) ∈ Z.
Proof.
  intros. pose proof H. pose proof H0. apply Z_Subset_R in H1,H2.
  assert (Ensemble (m + n)); eauto with real.
  assert (∀ a b, Ensemble (a + b) -> a ∈ \{ λ u, (-u) ∈ N \}
    -> b ∈ Z -> a + b ∈ Z).
  { intros a b H' H4 H5. apply AxiomII in H4 as [].
    apply MKT4 in H5 as [].
    assert (b < -a \/ -a < b \/ b = -a) as [H7|[]].
    { apply Order_Co1; auto with real. }
    - pose proof (Int_P1_Lemma b (-a) H5 H6 H7).
      rewrite PlusMult_Co3,(PlusMult_Co3 b),
      Mult_P4,(Mult_P4 _ b), <-Mult_P5, Mult_P4, 
      <-PlusMult_Co3 in H8; auto with real.
      apply MKT4. right. apply MKT4. left.
      apply AxiomII; auto.
    - pose proof (Int_P1_Lemma (-a) b H6 H5 H7).
      assert (a = --a).
      { rewrite PlusMult_Co3,PlusMult_Co4; auto with real. }
      rewrite <-H9,Plus_P4 in H8; auto with real.
      apply N_Subset_Z; auto.
    - rewrite H7,Minus_P1; auto with real. repeat
      (apply MKT4; right). apply MKT41; eauto with real.
    - apply MKT4 in H5 as []. apply AxiomII in H5 as [].
      apply MKT4. right. apply MKT4. left. apply AxiomII.
      split; auto. rewrite PlusMult_Co3,Mult_P4,Mult_P5,
      Mult_P4,(Mult_P4 b),<-PlusMult_Co3,<-PlusMult_Co3;
      auto with real. apply MKT41 in H5; eauto with real.
      rewrite H5,Plus_P1; auto with real. apply MKT4. right.
      apply MKT4. left. apply AxiomII; auto. }
  apply MKT4 in H as []. apply MKT4 in H0 as []. apply N_Subset_Z.
  apply Nat_P1a; auto with real. apply MKT4 in H0 as [].
  rewrite Plus_P4; auto. apply (H4 n m); auto.
  rewrite Plus_P4; auto. apply N_Subset_Z; auto.
  apply MKT41 in H0; eauto with real. rewrite H0,Plus_P1;
  auto with real. apply N_Subset_Z; auto. apply MKT4 in H as [];
  auto. apply MKT41 in H; eauto with real. rewrite H.
  rewrite Plus_P4,Plus_P1; auto with real. 
Qed.

Proposition Int_P1b : ∀ m n, m ∈ Z -> n ∈ Z -> (m · n) ∈ Z.
Proof.
  intros. pose proof H. pose proof H0. apply Z_Subset_R in H1,H2.
  assert (Ensemble (m · n)); eauto with real.
  assert (∀ a b, Ensemble (a · b) -> a ∈ [0]
    -> b ∈ Z -> a · b ∈ Z).
  { intros a b H' H4 H5. pose proof H5. apply Z_Subset_R in H5.
    apply MKT41 in H4; eauto with real.
    rewrite H4,Mult_P4,PlusMult_Co1; auto with real.
    repeat (apply MKT4; right). apply MKT41; eauto with real. }
  assert (∀ a b, Ensemble (a · b) -> a ∈ \{ λ u, (-u) ∈ N \}
    -> b ∈ Z -> a · b ∈ Z).
  { intros a b H' H5 H6. apply AxiomII in H5 as [].
    pose proof H6. apply Z_Subset_R in H8. apply MKT4 in H6 as [].
    pose proof (Nat_P1b (-a) b H7 H6).
    rewrite PlusMult_Co3,<-Mult_P3,<-PlusMult_Co3 in H9;
    auto with real. apply MKT4; right. apply MKT4; left.
    apply AxiomII; auto. apply MKT4 in H6 as [].
    apply AxiomII in H6 as []. pose proof (Nat_P1b (-a) (-b) H7 H9).
    rewrite PlusMult_Co3 in H10; auto with real.
    rewrite (Mult_P4 _ a),<-Mult_P3,(PlusMult_Co4 b) in H10;
    auto with real. apply MKT4. left; auto.
    rewrite Mult_P4; auto with real. apply (H4 b a); auto.
    rewrite Mult_P4; auto with real. apply MKT4. right.
    apply MKT4. left. apply AxiomII; auto. }
  apply MKT4 in H as []. apply MKT4 in H0 as [].
  apply N_Subset_Z; auto with real. apply MKT4 in H0 as [].
  rewrite Mult_P4; auto. apply (H5 n m); eauto with real.
  apply N_Subset_Z in H; auto. rewrite Mult_P4; auto.
  apply (H4 n m); eauto with real. apply N_Subset_Z; auto.
  apply MKT4 in H as []; auto.
Qed.

Global Hint Resolve N_Subset_Z Z_Subset_R Int_P1a Int_P1b : real.

Proposition Int_P2 : ∀ n, n ∈ Z -> n + 0 = n /\ 0 + n = n.
Proof.
  intros; split; [ |rewrite Plus_P4]; auto with real;
  rewrite Plus_P1; auto with real.
Qed.

Proposition Int_P3 : ∀ n, n ∈ Z -> (-n) ∈ Z /\ n + (-n) = 0
  /\ (-n) + n = 0.
Proof.
  intros; split. apply AxiomII in H as [H[]]. apply MKT4; right.
  apply MKT4; left. apply AxiomII; split; eauto with real.
  rewrite PlusMult_Co3,PlusMult_Co4; auto with real.
  apply MKT4 in H0 as []. apply AxiomII in H0 as [].
  apply MKT4; auto. apply MKT41 in H0; eauto with real.
  rewrite H0,PlusMult_Co3,PlusMult_Co1; auto with real.
  repeat (apply MKT4; right). apply MKT41; eauto with real.
  split; [ |rewrite Plus_P4]; auto with real.
Qed.

Proposition Int_P4 : ∀ m n k, m ∈ Z -> n ∈ Z -> k ∈ Z
  -> m + (n + k) = (m + n) + k.
Proof.
  intros. apply Plus_P3; auto with real.
Qed.

Proposition Int_P5 : ∀ m n, m ∈ Z -> n ∈ Z -> m + n = n + m.
Proof.
  intros. apply Plus_P4; auto with real.
Qed.

(* 有理数的定义 *)
Definition Q := \{ λ u, ∃ m n, m ∈ Z /\ n ∈ (Z ~ [0])
  /\ u = m / n \}.

Corollary Z_Subset_Q : Z ⊂ Q.
Proof.
  unfold Included; intros. apply AxiomII; split; eauto.
  exists z,1; split; auto. split. apply MKT4'; split.
  auto with real. apply AxiomII; split; eauto with real.
  intro. apply MKT41 in H0; eauto with real.
  destruct OrderPM_Co9; auto. rewrite Divide_P2; auto with real.
Qed.

Corollary Q_Subset_R : Q ⊂ R.
Proof.
  unfold Included; intros. apply AxiomII in H as [H[m[n[H0[]]]]].
  rewrite H2. apply Mult_close; auto with real.
  assert (n ∈ R ~ [0]).
  { apply MKT4' in H1 as []. apply MKT4'; split; auto with real. }
  apply Mult_inv1 in H3. apply MKT4' in H3; tauto.
Qed.

Proposition Frac_P1 : ∀ m n k, m ∈ R -> n ∈ (R ~ [0])
  -> k ∈ (R ~ [0]) -> m / n = (m · k) / (n · k).
Proof.
  intros. pose proof H0; pose proof H1.
  apply MKT4' in H2 as [H2 _]. apply MKT4' in H3 as [H3 _].
  assert (n ∈ (R ~ [0]) /\ k ∈ (R ~ [0])) as [].
  { split; apply MKT4'; split; auto with real;
    apply AxiomII; split; eauto; intro; [apply MKT4' in H0 as [_];
    apply AxiomII in H0 as []|apply MKT4' in H1 as [_];
    apply AxiomII in H1 as []]; auto. }
  pose proof H4; pose proof H5.
  apply MKT4' in H6 as [H6 _]. apply MKT4' in H7 as [H7 _].
  assert (m / n · (n · k) = m · k).
  { pose proof H4. apply Mult_inv1,MKT4' in H8 as [H8 _].
    rewrite <-Mult_P3,(Mult_P3 n⁻),(Mult_P4 n⁻),Divide_P1,
    (Mult_P4 1),Mult_P1; auto with real. }
  pose proof H4. apply Mult_inv1,MKT4' in H9 as [H9 _].
  assert (n · k ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real.
    apply AxiomII; split; eauto with real. intro.
    apply MKT41 in H10; eauto with real.
    apply PlusMult_Co2 in H10 as []; auto;
    [rewrite H10 in H4; apply MKT4' in H4 as [_];
    apply AxiomII in H4 as []|rewrite H10 in H5;
    apply MKT4' in H5 as [_]; apply AxiomII in H5 as []];
    apply H11; apply MKT41; auto. }
  rewrite <-H8,<-Mult_P3,Divide_P1,Mult_P1; auto with real.
  apply Mult_inv1,MKT4' in H10; tauto.
Qed.

Proposition Frac_P2 : ∀ m n k t, m ∈ R -> n ∈ (R ~ [0])
  -> k ∈ R -> t ∈ (R ~ [0])
  -> (m / n) · (k / t) = (m · k) / (n · t).
Proof.
  intros. pose proof H0; pose proof H2.
  apply Mult_inv1 in H3,H4.
  pose proof H0. apply MKT4' in H5 as [H5 _].
  pose proof H2. apply MKT4' in H6 as [H6 _].
  pose proof H3. apply MKT4' in H7 as [H7 _].
  pose proof H4. apply MKT4' in H8 as [H8 _].
  rewrite <-Mult_P3,(Mult_P4 n⁻),<-Mult_P3,(Mult_P3 m);
  auto with real. assert (n · t ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real.
    apply AxiomII; split; eauto with real. intro.
    apply MKT41 in H9; eauto with real.
    apply PlusMult_Co2 in H9 as []; auto;
    [rewrite H9 in H0; apply MKT4' in H0 as [_];
    apply AxiomII in H0 as []|rewrite H9 in H2;
    apply MKT4' in H2 as [_]; apply AxiomII in H2 as []];
    apply H10,MKT41; auto. }
  assert (t⁻ / n = (n · t)⁻).
  { assert ((n · t) · (t⁻ / n) = (n · t) · (n · t)⁻).
    { rewrite Divide_P1,<-Mult_P3,(Mult_P3 t),Divide_P1,
      Mult_P3,Mult_P1,Divide_P1; auto with real. }
    assert (n · t / (n · t) = 1).
    { rewrite Divide_P1; auto with real. }
    rewrite H11 in H10. pose proof H9.
    apply Mult_Co2 in H12 as [x[_]].
    assert (x = t⁻ / n).
    { apply H12; split; auto. apply MKT4'; split; auto with real.
      apply AxiomII; split; eauto with real. intro.
      apply MKT41 in H13; eauto with real.
      apply PlusMult_Co2 in H13 as []; auto;
      [rewrite H13 in H4; apply MKT4' in H4 as [_];
      apply AxiomII in H4 as []|rewrite H13 in H3;
      apply MKT4' in H3 as [_]; apply AxiomII in H3 as []];
      apply H14,MKT41; auto. }
    assert (x = (n · t)⁻).
    { apply H12; split; auto. apply Mult_inv1; auto. }
    rewrite <-H13,<-H14; auto. }
  rewrite H10; auto.
Qed.

Proposition Rat_P1a : ∀ x y, x ∈ Q -> y ∈ Q -> (x + y) ∈ Q.
Proof.
  intros. apply AxiomII in H as [_[x1[x2[H[]]]]].
  apply AxiomII in H0 as [_[y1[y2[H0[]]]]].
  apply MKT4' in H1 as []. apply MKT4' in H3 as [].
  rewrite H2,(Frac_P1 x1 x2 y2),H4,(Frac_P1 y1 y2 x2);
  try (apply MKT4'; split); auto with real.
  rewrite (Mult_P4 x2); auto with real.
  assert ((y2 · x2)⁻ ∈ (R ~ [0])).
  { apply Mult_inv1. apply MKT4'; split; auto with real.
    apply AxiomII; split; eauto with real. intro.
    apply MKT41 in H7; eauto with real.
    apply PlusMult_Co2 in H7 as []; auto with real;
    [rewrite H7 in H6; apply AxiomII in H6 as []|
    rewrite H7 in H5; apply AxiomII in H5 as []];
    apply H8,MKT41; auto with real. }
  pose proof H7. apply PlusMult_Co6 in H8.
  apply MKT4' in H7 as []. rewrite <-Mult_P5; auto with real.
  apply AxiomII; split. exists R. auto with real.
  exists (x1 · y2 + y1 · x2),(y2 · x2); repeat split;
  auto with real. apply MKT4'; split; auto with real.
  apply AxiomII; split; eauto with real.
  apply MKT4' in H8 as []; auto. apply AxiomII in H10; tauto.
Qed.

Proposition Rat_P1b : ∀ x y, x ∈ Q -> y ∈ Q -> (x · y) ∈ Q.
Proof.
  intros. apply AxiomII in H as [_[x1[x2[H[]]]]].
  apply AxiomII in H0 as [_[y1[y2[H0[]]]]]. rewrite H2,H4.
  pose proof H1; pose proof H3. apply MKT4' in H5 as [].
  apply MKT4' in H6 as []. rewrite Frac_P2;
  try (apply MKT4'; split); auto with real.
  assert ((x2 · y2) ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII; split;
    eauto with real. intro. apply MKT41 in H9; eauto with real.
    apply PlusMult_Co2 in H9 as []; auto with real;
    [rewrite H9 in H7; apply AxiomII in H7 as []|
    rewrite H9 in H8; apply AxiomII in H8 as []];
    apply H10,MKT41; auto. }
  pose proof H9. apply Mult_inv1 in H10.
  pose proof H10. apply MKT4' in H11 as [].
  apply AxiomII; split. exists R. auto with real.
  exists (x1 · y1),(x2 · y2). repeat split; auto with real.
  apply MKT4'; split; auto with real. apply MKT4' in H9; tauto.
Qed.

Global Hint Resolve Z_Subset_Q Q_Subset_R Rat_P1a Rat_P1b : real.

Proposition Rat_P2 : ∀ x, x ∈ Q -> x + 0 = x /\ 0 + x = x.
Proof.
  intros. split; [rewrite Plus_P1|rewrite Plus_P4,Plus_P1];
  auto with real.
Qed.

Proposition Rat_P3 : ∀ n, n ∈ Q -> (-n) ∈ Q /\ n + (-n) = 0
  /\ (-n) + n = 0.
Proof.
  intros. repeat split; [ |rewrite Minus_P1|
  rewrite Plus_P4,Minus_P1]; auto with real.
  pose proof H. apply AxiomII in H0 as [H0[n1[n2[H1[]]]]].
  rewrite PlusMult_Co3,H3; auto with real.
  replace (-(1)) with ((-(1)) / 1). apply MKT4' in H2 as [].
  assert (n2 ∈ (R ~ [0])). { apply MKT4'; split; auto with real. }
  rewrite Frac_P2,<-PlusMult_Co3,(Mult_P4 1),Mult_P1;
  auto with real. apply AxiomII; split. exists R.
  apply Mult_inv1,MKT4' in H5 as []. auto with real.
  exists (-n1),n2. repeat split; auto. apply Int_P3; auto.
  apply MKT4'; auto. apply Divide_P2; auto with real.
Qed.

Proposition Rat_P4 : ∀ x y z, x ∈ Q -> y ∈ Q -> z ∈ Q
  -> x + (y + z) = (x + y) + z.
Proof.
  intros. apply Plus_P3; auto with real.
Qed.

Proposition Rat_P5 : ∀ x y, x ∈ Q -> y ∈ Q -> x + y = y + x.
Proof.
  intros. apply Plus_P4; auto with real.
Qed.

Proposition Rat_P6 : ∀ x, x ∈ Q -> x · 1 = x /\ 1 · x = x.
Proof.
  intros. split; [ |rewrite Mult_P4; auto with real];
  rewrite Mult_P1; auto with real.
Qed.

Proposition Rat_P7 : ∀ x, x ∈ (Q ~ [0])
  -> (x⁻) ∈ Q /\ x · (x⁻) = 1.
Proof.
  intros. apply MKT4' in H as [].
  assert (x ∈ (R ~ [0])). { apply MKT4'; split; auto with real. }
  split; [ |apply Divide_P1]; auto with real. pose proof H.
  apply AxiomII in H2 as [_[x1[x2[H2[]]]]].
  assert (x / x = 1). { apply Divide_P1; auto. }
  assert (x2 ∈ (R ~ [0])).
  { apply MKT4' in H3 as []. apply MKT4'; split; auto with real. }
  assert (x1 ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII; split;
    eauto. intro. apply MKT41 in H7; eauto with real.
    apply Mult_inv1,MKT4' in H6 as [].
    rewrite H7,Mult_P4,PlusMult_Co1 in H4; auto with real.
    apply AxiomII in H0 as []. apply H9.
    apply MKT41; eauto with real. }
  pose proof H6; pose proof H7. apply MKT4' in H8 as [],H9 as [].
  assert (x · (x2 / x1) = 1).
  { rewrite H4,Frac_P2,(Mult_P4 x1),Divide_P1; auto.
    apply MKT4'; split; auto with real. apply AxiomII;
    split; eauto with real. intro. apply MKT41 in H12;
    eauto with real. apply PlusMult_Co2 in H12 as []; auto;
    [rewrite H12 in H10; apply AxiomII in H10 as []|
    rewrite H12 in H11; apply AxiomII in H11 as []];
    apply H13,MKT41; auto with real. }
  apply Mult_Co2 in H1 as [x'[_]].
  assert (x' = x⁻).
  { apply H1; split; auto.
    apply Mult_inv1,MKT4'; split; auto with real. }
  assert (x' = x2 / x1).
  { apply H1; split; auto. apply Mult_inv1,MKT4' in H7 as [].
    apply MKT4'; split; auto with real. apply AxiomII; split;
    eauto with real. intro. apply MKT41 in H15; eauto with real.
    apply PlusMult_Co2 in H15 as []; auto;
    [rewrite H15 in H10; apply AxiomII in H10 as []|
    rewrite H15 in H14; apply AxiomII in H14 as []];
    apply H16,MKT41; auto. }
  rewrite <-H13,H14. apply AxiomII; split. exists R.
  apply Mult_inv1,MKT4' in H7 as []. auto with real.
  exists x2,x1. repeat split; auto. apply MKT4' in H3; tauto.
  apply MKT4'; auto.
Qed.

Proposition Rat_P8 : ∀ x y z, x ∈ Q -> y ∈ Q -> z ∈ Q
  -> x · (y · z) = (x · y) · z.
Proof.
  intros. apply Mult_P3; auto with real.
Qed.

Proposition Rat_P9 : ∀ x y, x ∈ Q -> y ∈ Q -> x · y = y · x.
Proof.
  intros. apply Mult_P4; auto with real.
Qed.

Proposition Rat_P10 : ∀ x y z, x ∈ Q -> y ∈ Q -> z ∈ Q
  -> (x + y) · z = (x · z) + (y · z).
Proof.
  intros. apply Mult_P5; auto with real.
Qed.

Definition Even n := ∃ k, k ∈ Z /\ n = (1 + 1) · k.

Definition Odd n := ∃ k, k ∈ Z /\ n = (1 + 1) · k + 1.

Proposition Even_and_Odd_P1 : ∀ n, n ∈ N -> Even n \/ Odd n.
Proof.
  intros. set (E := \{ λ u, u ∈ N /\ (Even u \/ Odd u) \}).
  assert (E ⊂ N).
  { unfold Included; intros. apply AxiomII in H0; tauto. }
  assert (1 ∈ E).
  { apply AxiomII; repeat split; eauto with real. right. exists 0.
    rewrite PlusMult_Co1,(Plus_P4 0),Plus_P1; auto with real.
    split; auto. apply MKT4; right. apply MKT4; right.
    apply MKT41; eauto with real. }
  assert (E = N).
  { apply MathInd; intros; auto. apply AxiomII in H2 as [_[]].
    apply AxiomII; repeat split; eauto with real.
    destruct H3 as [[k[]]|[k[]]]; [right|left]. exists k.
    rewrite H4; auto. exists (k + 1).
    rewrite H4,(Mult_P4 (1 + 1) (k + 1)),(Mult_P5 k 1),
    (Mult_P4 k),(Mult_P4 1),Mult_P1,Plus_P3; auto with real. }
  rewrite <-H2 in H. apply AxiomII in H; tauto.
Qed.

Lemma Even_and_Odd_P2_Lemma : ∀ m n, m ∈ Z -> n ∈ Z -> n < m
  -> (n + 1) ≤ m.
Proof.
  intros. pose proof H. apply Z_Subset_R,(Order_Co1 m (n + 1))
  in H2 as [H2|[]]; auto with real;
  [ |destruct H2|rewrite H2; apply Leq_P1]; auto with real.
  apply (OrderPM_Co1 _ _ (-n)) in H1,H2; auto with real.
  rewrite Minus_P1 in H1; auto with real. rewrite (Plus_P4 n),
  <-Plus_P3,Minus_P1,Plus_P1 in H2; auto with real.
  assert ((m - n) ∈ Z).
  { apply Int_P1a; auto. apply Int_P3; auto. }
  apply MKT4 in H3 as []. elim (Nat_P5 1); auto with real.
  exists (m - n + 1). split; auto with real.
  apply (OrderPM_Co1 _ _ 1) in H1,H2; auto with real.
  rewrite Plus_P4,Plus_P1 in H1; auto with real.
  apply MKT4 in H3 as []. apply AxiomII in H3 as [].
  assert (-(m - n) < 0).
  { rewrite PlusMult_Co3; auto with real. apply OrderPM_Co6;
    auto with real. apply OrderPM_Co2a; auto with real. }
  pose proof H4. apply one_is_min_in_N in H6.
  assert (-(m - n) < -(m - n)).
  { apply (Order_Co2 _ 1); auto with real. left. split; auto.
    apply (Order_Co2 _ 0); auto with real. left; split; auto.
    destruct OrderPM_Co9; auto. }
  destruct H7; elim H8; auto. apply MKT41 in H3; eauto with real.
  rewrite H3 in H1. destruct H1; elim H4; auto.
Qed.

Proposition Even_and_Odd_P2 : ∀ n, n ∈ Z -> ~ (Even n /\ Odd n).
Proof.
  intros. intro. destruct H0 as [[a[]][b[]]].
  assert (0 < (1 + 1)).
  { apply (Order_Co2 _ 1); auto with real. left.
    split; auto with real. pose proof OrderPM_Co9.
    apply (OrderPM_Co1 _ _ 1) in H4; auto with real.
    rewrite Plus_P4,Plus_P1 in H4; auto with real.
    destruct H4; auto. }
  assert ((1 + 1) ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII; split;
    eauto with real. intro. apply MKT41 in H5; eauto with real.
    rewrite H5 in H4. destruct H4; auto. }
  pose proof H5. apply Mult_inv1,MKT4' in H6 as [H6 _].
  assert (a - b = 1 / (1 + 1)).
  { assert (((1 + 1) · a) - ((1 + 1) · b) = (1 + 1) · b + 1
      - ((1 + 1) · b)). { rewrite <-H1,<-H3; auto. }
    rewrite PlusMult_Co3,(Mult_P4 _ b),(Mult_P4 _ a),Mult_P3,
    <-PlusMult_Co3,<-Mult_P5,(Plus_P4 (b · (1 + 1))),
    <-Plus_P3,PlusMult_Co3,<-Mult_P3,<-PlusMult_Co3,<-PlusMult_Co3,
    Minus_P1,Plus_P1 in H7; auto with real.
    assert (((a - b) · (1 + 1)) / (1 + 1) = 1 / (1 + 1)).
    { rewrite H7; auto. }
    rewrite <-Mult_P3,Divide_P1,Mult_P1 in H8; auto with real. }
  assert ((a - b) ∈ Z).
  { apply Int_P1a; auto. apply Int_P3; auto. }
  rewrite Mult_P4,Mult_P1 in H7; auto with real.
  assert (0 < (a - b)).
  { rewrite H7. apply OrderPM_Co10; auto with real. }
  assert ((a - b) < 1).
  { rewrite H7. assert (1 < 1 + 1).
    { pose proof OrderPM_Co9. apply (OrderPM_Co1 _ _ 1)
      in H10; auto with real. rewrite Plus_P4,Plus_P1 in H10;
      auto with real. }
    apply (OrderPM_Co7a _ _ ((1 + 1)⁻)) in H10; auto with real.
    rewrite Divide_P1,Mult_P4,Mult_P1 in H10; auto with real.
    apply OrderPM_Co10; auto with real. }
  apply Even_and_Odd_P2_Lemma in H9; auto. rewrite Plus_P4,
  Plus_P1 in H9; auto with real. destruct H10. apply H11,Leq_P2;
  auto with real. repeat (apply MKT4; right).
  apply MKT41; eauto with real.
Qed.

Proposition Even_and_Odd_P3 : ∀ r, r ∈ N -> Even (r · r)
  -> Even r.
Proof.
  intros. pose proof H. apply Even_and_Odd_P1 in H1 as []; auto.
  destruct H1 as [k[]].
  assert (r · r = ((1 + 1) · k + 1) · ((1 + 1) · k + 1)).
  { rewrite H2; auto. }
  rewrite Mult_P5,(Mult_P4 1),Mult_P1,(Mult_P4 ((1 + 1) · k)),
  Mult_P5,(Mult_P4 1),Mult_P1,Plus_P3,(Mult_P4 _ k),Mult_P3,
  <-Mult_P5,<-Mult_P5,(Mult_P4 ((k · (1 + 1)) · k + k + k)) in H3;
  auto with real; [ |apply Plus_close; auto with real].
  assert (Odd (r · r)).
  { exists ((k · (1 + 1)) · k + k + k). split; auto.
    repeat apply Int_P1a; auto with real. }
  elim (Even_and_Odd_P2 (r · r)); auto with real.
Qed.

Lemma Existence_of_irRational_Number_Lemma1 :
  ∀ a b, a ∈ R -> b ∈ R -> a <> b
  -> (((b · b) - (a · a)) < ((1 + 1) · b · (b - a))).
Proof.
  intros. assert (0 < (b - a) · (b - a)).
  { apply OrderPM_Co5; auto with real.
    pose proof zero_in_R. apply (Order_Co1 (b - a)) in H2
    as [H2|[]]; auto with real. assert (b - a + a = a).
    { rewrite H2,Plus_P4,Plus_P1; auto with real. }
    rewrite <-Plus_P3,(Plus_P4 (-a)),Minus_P1,Plus_P1 in H3;
    auto with real. elim H1; auto. }
  rewrite Mult_P5,Mult_P4,Mult_P5,(Mult_P4 _ (b - a)),
  Mult_P5,PlusMult_Co5,Plus_P3 in H2; auto with real.
  apply (OrderPM_Co1 _ _ (-(a · a))) in H2; auto with real;
  [ |apply Plus_close; auto with real].
  rewrite <-Plus_P3,Minus_P1,Plus_P1 in H2; auto with real.
  apply (OrderPM_Co1 _ _ (b · b)) in H2; auto with real.
  rewrite Plus_P4,(Plus_P4 0),Plus_P1 in H2; auto with real.
  rewrite Mult_P5,(Mult_P4 1),Mult_P1,Mult_P5,
  (Mult_P4 b (b - a)),Mult_P5; auto with real.
  rewrite <-Plus_P3,(Plus_P4 (b · -a)),(Mult_P4 b (-a)) in H2;
  auto with real.
Qed.

Lemma Existence_of_irRational_Number_Lemma2 : ∀ x y,
  x ∈ R -> y ∈ R -> x < y -> ∃ r, r ∈ R /\ x < r /\ r < y.
Proof.
  intros. assert (0 < 1 + 1).
  { apply (Order_Co2 _ 1); auto with real. left.
    pose proof OrderPM_Co9. split; auto.
    apply (OrderPM_Co1 _ _ 1) in H2; auto with real.
    rewrite Plus_P4,Plus_P1 in H2; auto with real.
    destruct H2; auto. }
  assert ((1 + 1) ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII;
    split; eauto with real. intro. apply MKT41 in H3;
    eauto with real. rewrite H3 in H2. destruct H2; auto. }
  pose proof H3. apply Mult_inv1,MKT4' in H3 as [H3 _].
  pose proof H2. apply OrderPM_Co10 in H5; auto with real.
  exists ((x + y) / (1 + 1)). split. auto with real.
  split. apply (OrderPM_Co1 _ _ x) in H1; auto.
  replace (x + x) with (x · (1 + 1)) in H1.
  apply (OrderPM_Co7a _ _ ((1 + 1)⁻)) in H1; auto with real.
  rewrite <-Mult_P3,Divide_P1,Mult_P1,Plus_P4 in H1;
  auto with real. rewrite Mult_P4,Mult_P5,Mult_P4,Mult_P1;
  auto with real. apply (OrderPM_Co1 _ _ y) in H1; auto.
  replace (y + y) with (y · (1 + 1)) in H1.
  apply (OrderPM_Co7a _ _ ((1 + 1)⁻)) in H1; auto with real.
  rewrite <-Mult_P3,Divide_P1,Mult_P1 in H1; auto with real.
  rewrite Mult_P4,Mult_P5,Mult_P4,Mult_P1; auto with real.
Qed.

Lemma Existence_of_irRational_Number_Lemma3 : ∀ x y,
  x ∈ R -> y ∈ R -> 0 < y -> (y · y) < x
  -> ∃ r, r ∈ R /\ y < r /\ 0 < r /\ (r · r) < x.
Proof.
  intros. pose proof H1. destruct H3.
  apply (OrderPM_Co4 _ _ 0 1) in H3; auto with real.
  rewrite Plus_P1 in H3; auto with real. pose proof H3.
  assert (0 < 1 + 1) as Ha.
  { apply (Order_Co2 _ 1); auto with real. right.
    pose proof OrderPM_Co9. split. destruct H6; auto.
    apply (OrderPM_Co1 _ _ 1) in H6; auto with real.
    rewrite Plus_P4,Plus_P1 in H6; auto with real. }
  apply (OrderPM_Co7a _ _ (1 + 1)) in H5; auto with real.
  rewrite (Mult_P4 0),PlusMult_Co1,Mult_P4 in H5; auto with real.
  assert (((1 + 1) · (y + 1)) ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real.
    apply AxiomII; split. exists R. auto with real.
    intro. apply MKT41 in H6; eauto with real.
    destruct H5; auto. }
  pose proof H6 as H6a. apply Mult_inv1,MKT4' in H6 as [H6 _].
  pose proof H5. apply OrderPM_Co10 in H7; auto with real.
  assert (0 < x - (y · y)).
  { apply (OrderPM_Co1 _ _ (-(y · y))) in H2; auto with real.
    rewrite Minus_P1 in H2; auto with real. }
  set (A := (x - (y · y)) / ((1 + 1) · (y + 1))).
  assert (A ∈ R /\ 0 < A) as [].
  { split. unfold A; auto with real.
    apply OrderPM_Co5; auto with real. }
  assert (∃ e, e ∈ R /\ 0 < e /\ e < 1 /\ e < A)
  as [e[H11[H12[]]]].
  { pose proof OrderPM_Co9. pose proof H9.
    apply (Order_Co1 1) in H12 as []; auto with real.
    apply Existence_of_irRational_Number_Lemma2 in H11
    as [e[H11[]]]; auto with real. exists e.
    split; [ |split; [ |split]]; auto. destruct H12.
    apply (Order_Co2 _ 1); auto with real.
    apply Existence_of_irRational_Number_Lemma2 in H10
    as [e[H10[]]]; auto with real. exists e.
    split; [ |split; [ |split]]; auto. destruct H12.
    destruct H12. apply (Order_Co2 _ A); auto with real.
    rewrite H12; auto. }
  pose proof H12 as H14a. apply (OrderPM_Co1 _ _ y) in H14a;
  auto with real. rewrite Plus_P4,Plus_P1,Plus_P4 in H14a;
  auto with real. pose proof H0.
  apply (Existence_of_irRational_Number_Lemma1 _ (y + e))
  in H15; auto with real; [ |destruct H14a; auto].
  rewrite (Plus_P4 y e),<-(Plus_P3 e y (-y)),Minus_P1,
  Plus_P1,(Plus_P4 e y) in H15; auto with real.
  assert ((y + e) · (y + e) - y · y < ((1 + 1) · (y + 1)) · e).
  { apply (Order_Co2 _ (((1 + 1) · (y + e)) · e));
    auto with real. right. split. destruct H15; auto.
    apply OrderPM_Co7a; auto with real.
    rewrite Mult_P4,(Mult_P4 (1 + 1)); auto with real.
    apply OrderPM_Co7a; auto with real.
    rewrite Plus_P4,(Plus_P4 y); auto with real.
    apply OrderPM_Co1; auto with real. }
  assert ((((1 + 1) · (y + 1)) · e) < (x - y · y)).
  { apply (OrderPM_Co7a _ _ ((1 + 1) · (y + 1))) in H14;
    auto with real. unfold A in H14. rewrite <-Mult_P3,
    (Mult_P4 (((1 + 1) · (y + 1))⁻)),Divide_P1,Mult_P1,
    Mult_P4 in H14; auto with real. }
  assert ((y + e) · (y + e) - y · y < x - y · y).
  { apply (Order_Co2 _ (((1 + 1) · (y + 1)) · e));
    auto with real. left. split; destruct H17; auto. }
  apply (OrderPM_Co1 _ _ (y · y)) in H18; auto with real.
  rewrite <-Plus_P3,<-Plus_P3,(Plus_P4 _ (y · y)),
  Minus_P1,Plus_P1,Plus_P1 in H18; auto with real.
  assert (0 < y + e).
  { apply (Order_Co2 _ y); auto with real.
    left. destruct H14a; auto. }
  exists (y + e); auto with real.
Qed.

Lemma Existence_of_irRational_Number_Lemma4 : ∀ x y,
  x ∈ R -> y ∈ R -> 0 < y -> 0 < x -> x < (y · y)
  -> ∃ r, r ∈ R /\ r < y /\ 0 < r /\ x < (r · r).
Proof.
  intros. assert (0 < 1 + 1).
  { apply (Order_Co2 _ 1); auto with real. right.
    pose proof OrderPM_Co9. split. destruct H4; auto.
    apply (OrderPM_Co1 _ _ 1) in H4; auto with real.
    rewrite Plus_P4,Plus_P1 in H4; auto with real. }
  pose proof H1. apply (OrderPM_Co7a _ _ (1 + 1)) in H5;
  auto with real. rewrite (Mult_P4 0),PlusMult_Co1,Mult_P4
  in H5; auto with real.
  assert (((1 + 1) · y) ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real.
    apply AxiomII; split. exists R. auto with real.
    intro. apply MKT41 in H6; eauto with real.
    destruct H5; auto. }
  pose proof H6. apply Mult_inv1,MKT4' in H6 as [H6 _].
  pose proof H5. apply OrderPM_Co10 in H8; auto with real.
  assert (0 < (y · y) - x).
  { apply (OrderPM_Co1 _ _ (-x)) in H3; auto with real.
    rewrite Minus_P1 in H3; auto with real. }
  set (A := ((y · y) - x) / ((1 + 1) · y)).
  assert (A ∈ R /\ 0 < A /\ A < y) as [H10[]].
  { split. unfold A; auto with real. split.
    apply OrderPM_Co5; auto with real.
    assert (-x < y · y).
    { apply (Order_Co2 _ x); auto with real. right. split; auto.
      apply (Order_Co2 _ 0); auto with real. right. pose proof H2.
      apply OrderPM_Co2a in H2 as []; auto. }
    apply (OrderPM_Co1 _ _ (y · y)) in H10; auto with real.
    replace (y · y + y · y) with ((1 + 1) · y · y) in H10.
    rewrite Plus_P4,(Mult_P4 ((1 + 1) · y)) in H10;
    auto with real. apply (OrderPM_Co7a _ _ (((1 + 1) · y)⁻))
    in H10; auto with real. rewrite <-Mult_P3,Divide_P1,
    Mult_P1 in H10; auto with real.
    rewrite <-Mult_P3,Mult_P5,Mult_P4,Mult_P1; auto with real. }
  pose proof H11. apply OrderPM_Co2a,(OrderPM_Co1 _ _ y) in H13;
  auto with real. rewrite Plus_P4,(Plus_P4 0),Plus_P1 in H13;
  auto with real. pose proof H0.
  apply (Existence_of_irRational_Number_Lemma1 (y - A))
  in H14; auto with real; [ |destruct H13; auto].
  replace (y - (y - A)) with A in H14.
  replace (((1 + 1) · y) · A) with (y · y - x) in H14.
  apply (OrderPM_Co1 _ _ x) in H14; auto with real;
  [ |apply Plus_close; auto with real].
  rewrite <-(Plus_P3 _ (-x)),(Plus_P4 (-x)),Minus_P1,
  Plus_P1,Plus_P4,Plus_P3 in H14; auto with real;
  [ |apply Plus_close; auto with real].
  apply (OrderPM_Co1 _ _ ((y - A) · (y - A))) in H14;
  auto with real; [ |apply Plus_close; auto with real].
  rewrite <-Plus_P3,(Plus_P4 (-((y - A) · (y - A)))),
  Minus_P1,Plus_P1,(Plus_P4 (y · y)) in H14; auto with real.
  apply (OrderPM_Co1 _ _ (-(y · y))) in H14; auto with real.
  rewrite <-Plus_P3,<-Plus_P3,Minus_P1,Plus_P1,Plus_P1 in H14;
  auto with real. pose proof H12.
  apply (OrderPM_Co1 _ _ (-A)) in H15; auto with real.
  rewrite Minus_P1 in H15; auto. exists (y - A). auto with real.
  rewrite (Mult_P4 _ A); auto with real. unfold A.
  rewrite <-Mult_P3,(Mult_P4 (((1 + 1) · y)⁻)),Divide_P1,
  Mult_P1; auto with real. rewrite PlusMult_Co3; auto with real.
  rewrite Mult_P4,Mult_P5,Mult_P4,<-PlusMult_Co3,Mult_P4,
  PlusMult_Co4,Plus_P3,Minus_P1,Plus_P4,Plus_P1; auto with real.
Qed.

Lemma Existence_of_irRational_Number_Lemma5 : ∀ r, r ∈ R
  -> 0 < r -> (∃ x, x ∈ R /\ 0 < x /\ x · x = r).
Proof.
  assert (∀ r, r ∈ R -> 1 < r -> r < r · r).
  { intros. apply (OrderPM_Co7a _ _ r) in H0; auto with real.
    rewrite Mult_P4,Mult_P1 in H0; auto with real.
    destruct H0. apply (Order_Co2 _ 1); auto with real. }
  intros. set (X := \{ λ u, u ∈ R /\ 0 < u /\ u · u < r \}).
  assert (X ⊂ R).
  { unfold Included; intros. apply AxiomII in H2; tauto. }
  assert (X <> Φ /\ ∃ c, Upper X c) as [].
  { pose proof one_in_R_Co. apply (Order_Co1 _ r) in H3 as [];
    auto. split. apply NEexE. exists 1. apply AxiomII.
    rewrite Mult_P1; auto with real. split; eauto with real.
    exists r. repeat split; auto. intros. apply AxiomII
    in H4 as [_[H4[]]]. pose proof H4.
    apply (Order_Co1 r) in H7 as [H7|[]]; auto.
    assert (r < x · x).
    { apply (Order_Co2 _ x); auto with real. right. split.
      destruct H7; auto. apply H; auto. destruct H7.
      apply (Order_Co2 _ r); auto with real. }
    destruct H6,H8. elim H10. apply Leq_P2; auto with real.
    destruct H7; auto. rewrite H7. apply Leq_P1; auto.
    apply Existence_of_irRational_Number_Lemma2 in H1
    as [x[H1[]]]; auto with real. split. apply NEexE.
    exists x. apply AxiomII; split; [ |split; [ |split]];
    eauto. apply (Order_Co2 _ x); auto with real. left.
    split; [ |destruct H5; auto].
    assert (x < 1).
    { apply (Order_Co2 _ r); auto with real. left. split; auto.
      destruct H3. destruct H3; auto. rewrite H3.
      apply Leq_P1; auto. }
    apply (OrderPM_Co7a _ _ x) in H6; auto with real.
    rewrite (Mult_P4 1),Mult_P1 in H6; auto with real.
    exists 1. repeat split; auto with real. intros.
    apply AxiomII in H6 as [_[H6[]]]. pose proof H6.
    apply (Order_Co1 1) in H9 as []; auto with real.
    apply H in H9; auto. assert (x0 < 1) as []; auto.
    { apply (Order_Co2 _ r); auto with real. left. split.
      destruct H9. apply (Order_Co2 _ (x0 · x0)); auto with real.
      destruct H3. destruct H3; auto. rewrite H3.
      apply Leq_P1; auto. }
    destruct H9. destruct H9; auto.
    rewrite H9. apply Leq_P1; auto. }
  apply SupT in H4 as [s[[[_[]]]]]; auto.
  assert (0 < s).
  { apply NEexE in H3 as [x]. pose proof H3.
    apply AxiomII in H8 as [_[H8[]]]. apply H5 in H3.
    apply (Order_Co2 _ x); auto with real. }
  exists s. split; [ |split]; auto. pose proof H0.
  apply (Order_Co1 (s · s)) in H9 as [H9|[]]; auto with real.
  - apply Existence_of_irRational_Number_Lemma3 in H9
    as [x[H9[H10[]]]]; auto.
    assert (x ∈ X). { apply AxiomII; split; eauto. }
    apply H5 in H13. destruct H10. elim H14. apply Leq_P2; auto.
  - apply Existence_of_irRational_Number_Lemma4 in H9
    as [x[H9[H10[]]]]; auto. apply H6 in H10 as [y[]]; auto.
    apply AxiomII in H10 as [_[H10[]]].
    pose proof H13. apply (OrderPM_Co7a _ _ y) in H16; auto.
    pose proof H13. apply (OrderPM_Co7a _ _ x) in H17; auto.
    assert (r < y · y).
    { apply (Order_Co2 _ (x · x)); auto with real. right.
      split. destruct H12; auto. apply (Order_Co2 _ (x · y));
      auto with real. left. split. rewrite (Mult_P4 _ y); auto.
      destruct H16; auto. }
    destruct H15,H18. elim H20. apply Leq_P2; auto with real.
Qed.

Lemma Existence_of_irRational_Number_Lemma6 : ∀ r, r ∈ Q
  -> 0 < r -> ∃ a b, a ∈ N /\ b ∈ N /\ r = a / b.
Proof.
  assert (∀ n, n ∈ Z -> 0 < n -> n ∈ N).
  { intros. pose proof H. apply MKT4 in H1 as []; auto.
    apply MKT4 in H1 as []; [apply AxiomII in H1 as []|
    apply MKT41 in H1; eauto with real; rewrite H1 in H0;
    destruct H0; elim H2; auto].
    destruct one_is_min_in_N as [_[_]]. apply H3 in H2.
    assert (0 < -n).
    { apply (Order_Co2 _ 1); auto with real. }
    apply OrderPM_Co2a in H0; auto with real. destruct H0,H4.
    elim H6. apply Leq_P2; auto with real. }
  intros. pose proof H0. apply AxiomII in H0 as [_[m[n[H0[]]]]].
  assert (n ∈ (R ~ [0])).
  { apply MKT4' in H3 as []. apply MKT4'; split; auto with real. }
  apply MKT4' in H3 as [H3 _]. pose proof H5.
  apply Mult_inv1,MKT4' in H6 as [H6 _]. pose proof H0.
  apply Z_Subset_R,(Order_Co1 0) in H7 as [H7|[]]; auto with real.
  exists m,n. repeat split; auto. apply H; auto. pose proof H3.
  apply Z_Subset_R,(Order_Co1 0) in H8 as [H8|[]]; auto with real.
  rewrite H4 in H1. apply (OrderPM_Co8a _ _ n) in H1;
  auto with real. rewrite <-Mult_P3,(Mult_P4 _ n),Divide_P1,Mult_P1,
  Mult_P4,PlusMult_Co1 in H1; auto with real. destruct H1,H7.
  elim H10. apply Leq_P2; auto with real. apply MKT4' in H5 as [_].
  apply AxiomII in H5 as []. elim H9. apply MKT41; eauto with real.
  assert (n < 0).
  { pose proof H3. apply Z_Subset_R,(Order_Co1 0) in H8 as [H8|[]];
    auto with real. rewrite H4 in H1. apply (OrderPM_Co7a _ _ n)
    in H1; auto with real. rewrite <-Mult_P3,(Mult_P4 n⁻),
    Divide_P1,Mult_P1,Mult_P4,PlusMult_Co1 in H1; auto with real.
    destruct H1,H7. elim H10. apply Leq_P2; auto with real.
    apply MKT4' in H5 as [_]. apply AxiomII in H5 as []. elim H9.
    apply MKT41; eauto with real. }
  pose proof OrderPM_Co9. apply (OrderPM_Co1 _ _ (-(1))) in H9;
  auto with real. rewrite Minus_P1,Plus_P4,Plus_P1 in H9;
  auto with real. apply (OrderPM_Co8a _ _ (-(1))) in H7,H8;
  auto with real. rewrite Mult_P4,PlusMult_Co1,Mult_P4,
  <-PlusMult_Co3 in H7,H8; auto with real.
  exists (-m),(-n). repeat split; try apply H; auto;
  try apply Int_P3; auto. rewrite PlusMult_Co3,(PlusMult_Co3 n),
  (Mult_P4 _ m),(Mult_P4 _ n),<-Frac_P1; auto with real.
  apply MKT4'; split; auto with real. apply AxiomII; split;
  eauto with real. intro. apply MKT41 in H10; eauto with real.
  rewrite H10 in H9. destruct H9; auto. rewrite <-H7,Mult_P4,
  PlusMult_Co1 in H4; auto with real. rewrite H4 in H1.
  destruct H1. elim H8; auto.
Qed.

Theorem Existence_of_irRational_Number : (R ~ Q) <> Φ.
Proof.
  assert (0 < (1 + 1)) as Ha.
  { apply (Order_Co2 _ (0 + 1)); auto with real.
    right. pose proof OrderPM_Co9. split.
    rewrite Plus_P4,Plus_P1; auto with real.
    destruct H; auto. apply OrderPM_Co1; auto with real. }
  pose proof Ha. apply Existence_of_irRational_Number_Lemma5
  in H as [r[H[]]]; auto with real.
  apply NEexE. exists r. apply MKT4'; split; auto.
  apply AxiomII; split; eauto. intro.
  set (A := \{ λ u, u ∈ N /\ ∃ v, v ∈ N /\ r = u / v \}).
  assert (A ⊂ N /\ A <> Φ) as [].
  { split; unfold Included; intros. apply AxiomII in H3; tauto.
    apply Existence_of_irRational_Number_Lemma6 in H0
    as [a[b[H0[]]]]; auto. apply NEexE. exists a.
    apply AxiomII; split; eauto. }
  pose proof H3. apply Nat_P7 in H5 as [a[H5[]]]; auto.
  apply AxiomII in H6 as [_[H6[b[]]]].
  assert (∀ n, n ∈ N -> 0 < n).
  { intros. destruct one_is_min_in_N as [H11[]].
    pose proof H10. apply H13 in H14.
    apply (Order_Co2 _ 1); auto with real. }
  assert (b ∈ (R ~ [0]) /\ (b · b) ∈ (R ~ [0])) as [].
  { split; apply MKT4'; split; auto with real; apply AxiomII;
    split; eauto with real; intro; apply MKT41 in H11;
    eauto with real; [ |apply PlusMult_Co2 in H11 as [];
    auto with real]; rewrite H11 in H8;
    apply H10 in H8 as []; auto. }
  assert ((1 + 1) ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real.
    apply AxiomII; split; eauto with real. intro.
    apply MKT41 in H13; eauto with real.
    rewrite H13 in Ha. destruct Ha; auto. }
  rewrite H9,Frac_P2 in H1; auto with real.
  pose proof H11; pose proof H12; pose proof H13.
  apply Mult_inv1,MKT4' in H14 as [H14 _],H15 as [H15 _],
  H16 as [H16 _]. assert (a · a = (1 + 1) · (b · b)).
  { rewrite <-H1,<-(Mult_P3),(Mult_P4 _ (b · b)),
    Divide_P1,Mult_P1; auto with real. }
  assert (Even a) as [k[]].
  { apply Even_and_Odd_P3; auto. exists (b · b); auto with real. }
  rewrite H19,Mult_P3,<-(Mult_P3 _ k),(Mult_P4 k),Mult_P3,
  <-(Mult_P3 _ k),<-Mult_P3 in H17; auto with real.
  apply Mult_Co3 in H17; auto with real.
  rewrite (Mult_P4 _ (b · b)),<-(Mult_P3 (b · b)),Divide_P1,
  Mult_P1 in H17; auto with real.
  assert (Even b) as [t[]].
  { apply Even_and_Odd_P3; auto. exists (k · k); auto with real. }
  pose proof H6; pose proof H8. apply H10 in H22,H23.
  rewrite H19 in H22. rewrite H21 in H23.
  apply (OrderPM_Co7a _ _ (1 + 1)⁻) in H22,H23; auto with real;
  try apply OrderPM_Co10; auto with real.
  rewrite Mult_P4,PlusMult_Co1,(Mult_P4 (1 + 1)),<-Mult_P3,
  Divide_P1,Mult_P1 in H22,H23; auto with real.
  assert (k ∈ N /\ t ∈ N) as [].
  { pose proof H18; pose proof H20.
    split; [apply MKT4 in H18 as []|apply MKT4 in H20 as []];
    auto; [apply MKT4 in H18 as [];[apply AxiomII in H18 as [];
    apply H10 in H26; apply OrderPM_Co2a in H22; auto with real;
    destruct H22,H26|apply MKT41 in H18; eauto with real;
    rewrite H18 in H22; destruct H22; elim H26; auto]|
    apply MKT4 in H20 as []; [apply AxiomII in H20 as [];
    apply H10 in H26; apply OrderPM_Co2a in H23; auto with real;
    destruct H23,H26|apply MKT41 in H20; eauto with real;
    rewrite H20 in H23; destruct H23; elim H26; auto]];
    elim H28; apply Leq_P2; auto with real. }
  assert (k ∈ A).
  { apply AxiomII; repeat split; eauto. exists t. split; auto.
    rewrite H9,H19,H21,(Mult_P4 (1 + 1)),(Mult_P4 (1 + 1)),
    <-Frac_P1; auto with real. apply MKT4'; split; auto with real.
    apply AxiomII; split; eauto. intro. apply MKT41 in H26;
    eauto with real. rewrite H26 in H23. destruct H23; auto. }
  apply H7 in H26. assert (k < a) as [].
  { rewrite <-(Plus_P1 k),Plus_P4,H19,Mult_P5,Mult_P4,Mult_P1;
    auto with real. apply OrderPM_Co1; auto with real. }
  apply H28,Leq_P2; auto with real.
Qed.

(* 阿基米德原理 *)
Proposition Arch_P1 : ∀ E, E ⊂ N -> E <> Φ -> Bounded E
  -> ∃ n, Max E n.
Proof.
  intros. destruct H1 as [m1[m2[H1 _]]]. pose proof H0.
  apply SupT in H2 as [c[[]_]]; unfold Included; eauto with real.
  clear dependent m1. clear dependent m2. destruct H2 as [H1[]].
  destruct (classic (c ∈ E)). exists c. split; auto.
  assert (∀ x, x ∈ E -> x < c).
  { intros. split; auto. intro. rewrite <-H7 in H5; auto. }
  assert ((c - 1) < c).
  { pose proof OrderPM_Co9. apply (OrderPM_Co1 0 1 c) in H7;
    auto with real. rewrite Plus_P4,Plus_P1,Plus_P4 in H7;
    auto with real. apply (OrderPM_Co1 _ _ (-(1))) in H7;
    auto with real. rewrite <-Plus_P3,Minus_P1,Plus_P1 in H7;
    auto with real. }
  apply H3 in H7 as [x1[]]; auto with real. pose proof H7.
  apply H6,H3 in H9 as [x2[]]; auto. apply Nat_P4 in H10; auto.
  apply (OrderPM_Co1 _ _ 1) in H8; auto with real.
  rewrite <-Plus_P3,(Plus_P4 _ 1),Minus_P1,Plus_P1 in H8;
  auto with real. assert (c < x2).
  { apply (Order_Co2 _ (x1 + 1)); auto with real. }
  pose proof H9. apply H6 in H12. destruct H11,H12.
  elim H14. apply Leq_P2; auto.
Qed.

Proposition Arch_P2 : ~ ∃ n, Upper N n.
Proof.
  intro. destruct H as [m]. assert (Bounded N).
  { exists m,1. split; auto. repeat split; auto with real.
    intros. destruct one_is_min_in_N as [_[]]; auto. }
  apply Arch_P1 in H0 as [n[H0[]]]; auto.
  assert (n + 1 ∈ N). auto with real.
  pose proof H3. apply H2 in H3. pose proof OrderPM_Co9.
  apply (OrderPM_Co1 0 1 n) in H5; auto with real.
  rewrite Plus_P4,Plus_P1,Plus_P4 in H5; auto with real.
  destruct H5. apply H6,Leq_P2; auto with real.
  apply NEexE. eauto with real.
Qed.

Lemma Arch_P3_Lemma : ∀ m n, m ∈ Z -> n ∈ Z -> n < m
  -> (n + 1) ≤ m.
Proof.
  intros. pose proof H. apply Z_Subset_R,(Order_Co1 m (n + 1))
  in H2 as [H2|[]]; auto with real;
  [ |destruct H2|rewrite H2; apply Leq_P1]; auto with real.
  apply (OrderPM_Co1 _ _ (-n)) in H1,H2; auto with real.
  rewrite Minus_P1 in H1; auto with real. rewrite (Plus_P4 n),
  <-Plus_P3,Minus_P1,Plus_P1 in H2; auto with real.
  assert ((m - n) ∈ Z).
  { apply Int_P1a; auto. apply Int_P3; auto. }
  apply MKT4 in H3 as []. elim (Nat_P5 1); auto with real.
  exists (m - n + 1). split; auto with real.
  apply (OrderPM_Co1 _ _ 1) in H1,H2; auto with real.
  rewrite Plus_P4,Plus_P1 in H1; auto with real.
  apply MKT4 in H3 as []. apply AxiomII in H3 as [].
  assert (-(m - n) < 0).
  { rewrite PlusMult_Co3; auto with real. apply OrderPM_Co6;
    auto with real. apply OrderPM_Co2a; auto with real. }
  pose proof H4. apply one_is_min_in_N in H6.
  assert (-(m - n) < -(m - n)).
  { apply (Order_Co2 _ 1); auto with real. left. split; auto.
    apply (Order_Co2 _ 0); auto with real. left; split; auto.
    destruct OrderPM_Co9; auto. }
  destruct H7; elim H8; auto. apply MKT41 in H3; eauto with real.
  rewrite H3 in H1. destruct H1; elim H4; auto.
Qed.

Proposition Arch_P3a : ∀ E, E ⊂ Z -> E <> Φ -> (∃ x, Upper E x)
  -> ∃ n, Max E n.
Proof.
  intros. destruct H1 as [m1]. pose proof H0.
  apply SupT in H2 as [c[[]_]]; unfold Included; eauto with real.
  clear dependent m1. destruct H2 as [H1[]].
  destruct (classic (c ∈ E)). exists c. split; auto.
  assert (∀ x, x ∈ E -> x < c).
  { intros. split; auto. intro. rewrite <-H7 in H5; auto. }
  assert ((c - 1) < c).
  { pose proof OrderPM_Co9. apply (OrderPM_Co1 0 1 c) in H7;
    auto with real. rewrite Plus_P4,Plus_P1,Plus_P4 in H7;
    auto with real. apply (OrderPM_Co1 _ _ (-(1))) in H7;
    auto with real. rewrite <-Plus_P3,Minus_P1,Plus_P1 in H7;
    auto with real. }
  apply H3 in H7 as [x1[]]; auto with real. pose proof H7.
  apply H6,H3 in H9 as [x2[]]; auto. apply Arch_P3_Lemma in H10;
  auto. apply (OrderPM_Co1 _ _ 1) in H8; auto with real.
  rewrite <-Plus_P3,(Plus_P4 _ 1),Minus_P1,Plus_P1 in H8;
  auto with real. assert (c < x2).
  { apply (Order_Co2 _ (x1 + 1)); auto with real. }
  pose proof H9. apply H6 in H12. destruct H11,H12.
  elim H14. apply Leq_P2; auto.
Qed.

Proposition Arch_P3b : ∀ E, E ⊂ Z -> E <> Φ -> (∃ x, Lower E x)
  -> ∃ n, Min E n.
Proof.
  intros. destruct H1 as [m1]. pose proof H0.
  apply InfT in H2 as [c[[]_]]; unfold Included; eauto with real.
  clear dependent m1. destruct H2 as [H1[]].
  destruct (classic (c ∈ E)). exists c. split; auto.
  assert (∀ x, x ∈ E -> c < x).
  { intros. split; auto. intro. rewrite H7 in H5; auto. }
  assert (c < c + 1).
  { pose proof OrderPM_Co9. apply (OrderPM_Co1 0 1 c) in H7;
    auto with real. rewrite Plus_P4,Plus_P1,Plus_P4 in H7;
    auto with real. }
  apply H3 in H7 as [x1[]]; auto with real. pose proof H7.
  apply H6,H3 in H9 as [x2[]]; auto. apply Arch_P3_Lemma in H10;
  auto. assert (x2 + 1 < c + 1).
  { apply (Order_Co2 _ x1); auto with real. }
  apply (OrderPM_Co1 _ _ (-(1))) in H11; auto with real.
  rewrite <-Plus_P3,<-Plus_P3,Minus_P1,Plus_P1,Plus_P1 in H11;
  auto with real. pose proof H9. apply H6 in H12. destruct H11,H12.
  elim H14. apply Leq_P2; auto.
Qed.

Proposition Arch_P4 : ∀ E, E ⊂ N -> E <> Φ -> Bounded E
  -> ∃ n, Min E n.
Proof.
  intros. apply Nat_P7; auto.
Qed.

Proposition Arch_P5 : ~ (∃ n, Lower Z n) /\ ~ (∃ n, Upper Z n).
Proof.
  split; intro; [apply Arch_P3b in H|apply Arch_P3a in H]; auto;
  try apply NEexE; eauto with real; destruct H as [m[H[]]].
  assert (m - 1 ∈ Z).
  { apply Int_P1a; auto. apply Int_P3; auto with real. }
  pose proof H2. apply H1 in H3.
  assert (m - 1 < m) as [].
  { pose proof OrderPM_Co9. apply (OrderPM_Co1 0 1 m) in H4;
    auto with real. rewrite Plus_P4,Plus_P1,Plus_P4 in H4;
    auto with real. apply (OrderPM_Co1 _ _ (-(1))) in H4;
    auto with real. rewrite <-Plus_P3,Minus_P1,Plus_P1 in H4;
    auto with real. }
  elim H5. apply Leq_P2; auto.
  assert (m + 1 ∈ Z); auto with real.
  pose proof H2. apply H1 in H3.
  assert (m < m + 1) as [].
  { pose proof OrderPM_Co9. apply (OrderPM_Co1 0 1 m) in H4;
    auto with real. rewrite Plus_P4,Plus_P1,Plus_P4 in H4;
    auto with real. }
  elim H5. apply Leq_P2; auto.
Qed.

Proposition Arch_P6 : ∀ h x, h ∈ R -> 0 < h -> x ∈ R
  -> (exists ! k, k ∈ Z /\ (k - 1) · h ≤ x /\ x < k · h).
Proof.
  intros. assert (h⁻ ∈ (R ~ [0])).
  { apply Mult_inv1,MKT4'; split; auto.
    apply AxiomII; split; eauto. intro.
    apply MKT41 in H2; eauto with real. destruct H0; auto. }
  assert ((x / h) ∈ R).
  { destruct H0. apply Mult_close; auto. apply MKT4' in H2; tauto. }
  set (E := \{ λ u, u ∈ Z /\ (x / h) < u \}).
  assert (E ⊂ Z).
  { unfold Included; intros. apply AxiomII in H4; tauto. }
  assert (∃ n, Min E n) as [n[H5[]]].
  { apply Arch_P3b; auto. intro. destruct Arch_P5 as [_].
    elim H6. exists (x / h). repeat split; auto with real.
    intros. pose proof H3. apply (Order_Co1 x0) in H8 as [H8|[]];
    auto with real. destruct H8; auto. elim (@ MKT16 x0).
    rewrite <-H5. apply AxiomII; split; eauto. rewrite H8.
    apply Leq_P1; auto. exists (x / h).
    repeat split; unfold Included; intros; auto with real.
    apply AxiomII in H5 as [_[_[]]]; auto. }
  exists n. apply AxiomII in H6 as [_[]].
  assert ((n - 1) ≤ (x / h)).
  { pose proof H3. apply (Order_Co1 (n - 1)) in H9 as [H9|[]];
    auto with real. destruct H9; auto.
    assert ((n - 1) ∈ E).
    { apply AxiomII; split. exists R. auto with real. split; auto.
      apply Int_P1a; auto. apply Int_P3; auto with real. }
    apply H7 in H10. apply (OrderPM_Co3 _ _ (-n) (-n)) in H10;
    auto with real. rewrite Minus_P1,(Plus_P4 n),<-Plus_P3,
    Minus_P1,Plus_P1 in H10; auto with real.
    apply (OrderPM_Co3 _ _ 1 1) in H10; auto with real.
    rewrite Plus_P4,Plus_P1,Plus_P4,Minus_P1 in H10; auto with real.
    destruct OrderPM_Co9. elim H12. apply Leq_P2; auto with real.
    apply Leq_P1; auto with real. apply Leq_P1; auto with real.
    rewrite H9. apply Leq_P1; auto. }
  assert (x < n · h).
  { apply (OrderPM_Co7a _ _ h) in H8; auto with real.
    pose proof H2. apply MKT4' in H10 as [].
    rewrite <-Mult_P3,(Mult_P4 _ h),Divide_P1,Mult_P1 in H8;
    auto with real; apply PlusMult_Co6; auto. }
  assert ((n - 1) · h ≤ x).
  { apply (OrderPM_Co7b _ _ h) in H9; auto with real;
    [ |destruct H0; auto]. pose proof H2.
    apply MKT4' in H11 as [H11 _].
    rewrite <-Mult_P3,(Mult_P4 h⁻),Divide_P1,Mult_P1 in H9;
    auto with real. apply PlusMult_Co6; auto. }
  split; auto. intros m [H12[]]. pose proof H2.
  apply MKT4' in H15 as [H15 _]. pose proof H0.
  apply OrderPM_Co10 in H16; auto.
  apply (OrderPM_Co7a _ _ h⁻) in H10,H14; auto with real.
  rewrite <-Mult_P3,Divide_P1,Mult_P1 in H10,H14;
  try apply PlusMult_Co6; auto with real.
  apply (OrderPM_Co7b _ _ h⁻) in H13; auto with real;
  [ |destruct H16; auto].
  rewrite <-Mult_P3,Divide_P1,Mult_P1 in H13; auto with real;
  [ |apply PlusMult_Co6; auto].
  assert (∀ u v, u ∈ Z -> v ∈ Z -> u - 1 ≤ x / h -> x / h < u
    -> v - 1 ≤ x / h -> x / h < v -> ~ u < v).
  { intros. intro. apply Arch_P3_Lemma in H23; auto.
    apply (OrderPM_Co3 _ _ (-(1)) (-(1))) in H23;
    try apply Leq_P1; auto with real.
    rewrite <-Plus_P3,Minus_P1,Plus_P1 in H23; auto with real.
    assert (x / h < x / h) as []; auto.
    { apply (Order_Co2 _ u); auto with real. left. split; auto.
      apply (Leq_P3 _ (v - 1)); auto with real. } }
  pose proof H6. apply Z_Subset_R in H18.
  apply (Order_Co1 m) in H18 as [H18|[]]; auto with real;
  apply H17 in H18; auto; destruct H18.
Qed.

Proposition Arch_P7 : ∀ x, x ∈ R -> 0 < x
  -> (∃ n, n ∈ N /\ 0 < 1 / n /\ 1 / n < x).
Proof.
  intros. pose proof H0. apply (Arch_P6 x 1) in H1 as [m[[H1[_]]_]];
  auto with real. pose proof OrderPM_Co9.
  assert (0 < m · x).
  { apply (Order_Co2 0 1); auto with real. destruct H2; auto. }
  assert (0 < m).
  { apply Z_Subset_R in H1. pose proof H1.
    apply (Order_Co1 0) in H5 as [H5|[]]; auto with real.
    apply (OrderPM_Co6 m x) in H5; auto with real.
    destruct H4,H5. elim H7. apply Leq_P2; auto with real.
    rewrite <-H5,Mult_P4,PlusMult_Co1 in H4; auto with real.
    destruct H4. elim H6; auto. }
  pose proof H5. apply OrderPM_Co10 in H5; auto with real.
  assert (m ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII; split;
    eauto. intro. apply MKT41 in H7; eauto with real.
    rewrite H7 in H6. destruct H6; auto. }
  pose proof H7 as H7a. apply Mult_inv1,MKT4' in H7 as [H7 _].
  exists m. split. pose proof H1. apply MKT4 in H1 as []; auto.
  apply MKT4 in H1 as []. apply AxiomII in H1 as [_].
  destruct one_is_min_in_N as [_[_]]. apply H9 in H1.
  assert (0 ≤ -m). { apply (Order_Co2 0 1); auto with real. }
  apply (OrderPM_Co3 _ _ m m) in H10; auto with real;
  [ |apply Leq_P1; auto with real]. rewrite Plus_P4,Plus_P1,
  Plus_P4,Minus_P1 in H10; auto with real. destruct H6.
  elim H11. apply Leq_P2; auto with real. apply MKT41 in H1;
  eauto with real. rewrite H1 in H6. destruct H6. destruct H9; auto.
  split. rewrite Mult_P4,Mult_P1; auto with real.
  apply (OrderPM_Co7a _ _ (m⁻)) in H2; auto with real.
  rewrite (Mult_P4 m),<-Mult_P3,Divide_P1,Mult_P1 in H2;
  auto with real.
Qed.

Proposition Arch_P8 : ∀ x, x ∈ R -> 0 ≤ x
  -> (∀ n, n ∈ N -> x < 1 / n) -> x = 0.
Proof.
  intros. pose proof H. apply (Order_Co1 0) in H2 as [H2|[]];
  auto with real. apply Arch_P7 in H2 as [m[H2[]]]; auto.
  pose proof H2. apply H1 in H5. destruct H4,H5. elim H7.
  apply Leq_P2; auto. apply Mult_close; auto with real.
  assert (m ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII; split; eauto.
    intro. apply MKT41 in H8; eauto with real.
    destruct one_is_min_in_N as [_[]]. rewrite H8 in H2.
    apply H10 in H2. destruct OrderPM_Co9. elim H12.
    apply Leq_P2; auto with real. }
  apply Mult_inv1,MKT4' in H8; tauto.
  destruct H2. apply Leq_P2; auto with real.
Qed.

Proposition Arch_P9 : ∀ a b, a ∈ R -> b ∈ R -> a < b
  -> (∃ r, r ∈ Q /\ a < r /\ r < b).
Proof.
  intros. assert (0 < (b - a)).
  { apply (OrderPM_Co1 a b (-a)) in H1; auto with real.
    rewrite Minus_P1 in H1; auto. }
  assert ((b - a) ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII;
    split; eauto with real. intro. apply MKT41 in H3;
    eauto with real. rewrite H3 in H2. destruct H2; auto. }
  pose proof H3. apply Mult_inv1,MKT4' in H4 as [H4 _].
  pose proof H2. apply OrderPM_Co10 in H5; auto with real.
  assert (∃ n, n ∈ N /\ (b - a)⁻ < n) as [n[]].
  { apply NNPP; intro. elim Arch_P2. exists ((b - a)⁻).
    repeat split; auto with real. intros. apply NNPP; intro.
    elim H6. exists x. pose proof H4.
    apply (Order_Co1 x) in H9 as [H9|[]]; auto with real.
    destruct H9. elim H8; auto. rewrite H9 in H8. elim H8.
    apply Leq_P1; auto. }
  assert (0 < n).
  { apply (Order_Co2 _ ((b - a)⁻)); auto with real.
    destruct H7; auto. }
  apply (OrderPM_Co7a _ _ (b - a)) in H7; auto with real.
  rewrite Mult_P4,Divide_P1,Mult_P4,Mult_P5,PlusMult_Co3,
  <-Mult_P3,<-PlusMult_Co3 in H7; auto with real.
  apply (OrderPM_Co1 _ _ (a · n)) in H7; auto with real.
  rewrite <-Plus_P3,(Plus_P4 (- (a · n))),Minus_P1,Plus_P1 in H7;
  auto with real.
  set (E := \{ λ u, u ∈ Z /\ a · n < u \}).
  assert (E ⊂ Z).
  { unfold Included; intros. apply AxiomII in H9; tauto. }
  assert (∃ m, Min E m) as [m[H10[]]].
  { apply Arch_P3b; auto. intro. destruct Arch_P5. elim H12.
    exists (a · n). repeat split; auto with real. intros.
    apply NNPP; intro. elim (@ MKT16 x). rewrite <-H10.
    apply AxiomII; split; eauto. split; auto. pose proof H13.
    apply Z_Subset_R in H15. apply (Order_Co1 (a · n)) in H15
    as [H15|[]]; auto with real. destruct H15. elim H14; auto.
    rewrite H15 in H14. elim H14. apply Leq_P1; auto with real.
    exists (a · n). repeat split; unfold Included; auto with real.
    intros. apply AxiomII in H10 as [_[_[]]]; auto. }
  apply AxiomII in H11 as [_[]].
  assert (m - 1 ≤ a · n).
  { assert ((m - 1) ∈ R). auto with real.
    apply (Order_Co1 (a · n)) in H14 as [H14|[]]; auto with real.
    assert ((m - 1) ∈ E).
    { apply AxiomII; split. exists R. auto with real. split; auto.
      apply Int_P1a; auto. apply Int_P3; auto with real. }
    apply H12 in H15. apply (OrderPM_Co3 _ _ 1 1) in H15;
    auto with real; [ |apply Leq_P1; auto with real].
    rewrite <-Plus_P3,(Plus_P4 (-(1))),Minus_P1,Plus_P1 in H15;
    auto with real. apply (OrderPM_Co3 _ _ (-m) (-m)) in H15;
    auto with real; [ |apply Leq_P1; auto with real].
    rewrite Minus_P1,(Plus_P4 m),<-Plus_P3,Minus_P1,Plus_P1 in H15;
    auto with real. destruct OrderPM_Co9. elim H17.
    apply Leq_P2; auto with real. destruct H14; auto.
    rewrite <-H14. apply Leq_P1; auto with real. }
  assert (m < b · n).
  { apply (Order_Co2 _ (1 + a · n)); auto with real. right.
    split; auto. apply (OrderPM_Co3 _ _ 1 1) in H14;
    auto with real; [ |apply Leq_P1; auto with real].
    rewrite <-Plus_P3,(Plus_P4 (-(1))),Minus_P1,Plus_P1,
    Plus_P4 in H14; auto with real. }
  assert (n ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII; split;
    eauto. intro. apply MKT41 in H16; eauto with real.
    rewrite H16 in H8. destruct H8; auto. }
  pose proof H16. apply Mult_inv1,MKT4' in H17 as [H17 _].
  pose proof H8. apply OrderPM_Co10 in H18; auto with real.
  apply (OrderPM_Co7a _ _ (n⁻)) in H13,H15; auto with real.
  rewrite <-Mult_P3,Divide_P1,Mult_P1 in H13,H15; auto with real.
  exists (m / n). split; auto. apply AxiomII; split.
  eauto with real. exists m,n. repeat split; auto.
  apply MKT4'; split; auto with real. apply AxiomII; split;
  eauto with real. intro. apply MKT41 in H19; eauto with real.
  rewrite H19 in H8. destruct H8; auto.
Qed.

Proposition Arch_P10 : ∀ x, x ∈ R
  -> (exists ! k, k ∈ Z /\ k ≤ x /\ x < k + 1).
Proof.
  intros. pose proof H. apply (Arch_P6 1 x) in H0 as [m[[H0[]]]];
  auto with real. rewrite Mult_P1 in H1,H2; auto with real.
  exists (m - 1). split. rewrite <-Plus_P3,(Plus_P4 (-(1))),
  Minus_P1,Plus_P1; auto with real. split; auto.
  apply Int_P1a; auto. apply Int_P3; auto with real.
  intros y [H4[]]. assert (m = y + 1).
  { apply H3. rewrite Mult_P1,Mult_P1,<-Plus_P3,Minus_P1,Plus_P1;
    auto with real. }
  rewrite H7,<-Plus_P3,Minus_P1,Plus_P1; auto with real.
Qed.

(* 实数的几何解释 *)
(* 有界区间 *)
(* 开区间 *)
Notation "］ a , b ［" := (\{ λ x, x ∈ R /\ a < x /\ x < b \})
  (at level 5, a at level 0, b at level 0) : R_scope.

(* 闭区间 *)
Notation "［ a , b ］" := (\{ λ x, x ∈ R /\ a ≤ x /\ x ≤ b \})
  (at level 5, a at level 0, b at level 0) : R_scope.

(* 左开右闭 *)
Notation "］ a , b ］" := (\{ λ x, x ∈ R /\ a < x /\ x ≤ b \})
  (at level 5, a at level 0, b at level 0) : R_scope.

(* 左闭右开 *)
Notation "［ a , b ［" := (\{ λ x, x ∈ R /\ a ≤ x /\ x < b \})
  (at level 5, a at level 0, b at level 0) : R_scope.

(* 无界区间 *)
Notation "］ a , +∞［" := (\{ λ x, x ∈ R /\ a < x \})
  (at level 5, a at level 0) : R_scope.

Notation "［ a , +∞［" := (\{ λ x, x ∈ R /\ a ≤ x \})
  (at level 5, a at level 0) : R_scope.

Notation "］-∞ , b ］" := (\{ λ x, x ∈ R /\ x ≤ b \})
  (at level 5, b at level 0) : R_scope.

Notation "］-∞ , b ［" := (\{ λ x, x ∈ R /\ x < b \})
  (at level 5, b at level 0) : R_scope.

Notation "]-∞ , +∞[" := (R)(at level 0) : R_scope.

(* 邻域 *)
Definition Neighbourhood x δ := x ∈ R /\ δ ∈ R
  /\ x ∈ ］(x - δ),(x + δ)［.

(* 绝对值函数 *)
Definition Abs := \{\ λ u v, u ∈ R
  /\ ((0 ≤ u /\ v = u) \/ (u < 0 /\ v = (-u))) \}\.

Corollary Abs_is_Function : Function Abs /\ dom(Abs) = R
  /\ ran(Abs) = \{ λ x, x ∈ R /\ 0 ≤ x \}.
Proof.
  repeat split; unfold Relation; try (apply AxiomI; split); intros.
  - apply AxiomII in H as [H[x[y[]]]]; eauto.
  - intros. apply AxiomII' in H as [H[H1[[]|[]]]],
    H0 as [H0[H4[[]|[]]]]; try rewrite H3,H6; auto;
    [destruct H5|destruct H2]; elim H7; apply Leq_P2;
    auto with real.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H0; tauto.
  - apply AxiomII; split; eauto. pose proof zero_in_R.
    pose proof (Order_Co1 0 z H0 H) as [H1|[]]. exists z.
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    left; split; auto. destruct H1; auto. exists (-z).
    apply AxiomII'; repeat split; auto. apply MKT49a;
    eauto with real. exists 0. apply AxiomII'; repeat split; auto.
    apply MKT49a; eauto. left; split; auto. rewrite <-H1.
    apply Leq_P1; auto.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H0
    as [H0[H1[[]|[]]]]. rewrite H3. apply AxiomII; eauto.
    apply AxiomII; split; auto. rewrite H3. split; auto with real.
    apply (OrderPM_Co1 _ _ (-x)) in H2; auto with real.
    rewrite Minus_P1,Plus_P4,Plus_P1 in H2; auto with real.
    destruct H2; auto.
  - apply AxiomII; split; eauto. exists z. apply AxiomII in H
    as [H[]]. apply AxiomII'; repeat split; auto.
Qed.

Corollary Abs_in_R : ∀ x, x ∈ R -> Abs[x] ∈ R.
Proof.
  intros. destruct Abs_is_Function as [H0[]]. rewrite <-H1 in H.
  apply Property_Value,Property_ran in H; auto. rewrite H2 in H.
  apply AxiomII in H; tauto.
Qed.

Global Hint Resolve Abs_in_R : real.

Notation "｜ x ｜" := (Abs[x])(at level 5, x at level 0) : R_scope.

Definition Distance x y := ｜(x - y)｜.

(* 绝对值的性质 *)
Proposition me_zero_Abs : ∀ x, x ∈ R -> 0 ≤ x -> ｜x｜ = x.
Proof.
  intros. destruct Abs_is_Function as [H1[]]. rewrite <-H2 in H.
  apply Property_Value,AxiomII' in H as [_[H[[]|[]]]]; auto.
  destruct H4. elim H6. apply Leq_P2; auto with real.
Qed.

Proposition le_zero_Abs : ∀ x, x ∈ R -> x ≤ 0 -> ｜x｜ = -x.
Proof.
  intros. destruct Abs_is_Function as [H1[]]. rewrite <-H2 in H.
  apply Property_Value,AxiomII' in H as [_[H[[]|[]]]]; auto.
  assert (x = 0). { apply Leq_P2; auto with real. }
  rewrite H6 in *. rewrite H5,PlusMult_Co3,PlusMult_Co1;
  auto with real.
Qed.

Proposition Abs_P1 : ∀ x, x ∈ R -> 0 ≤ ｜x｜ /\ (｜x｜ = 0 <-> x = 0).
Proof.
  intros. destruct Abs_is_Function as [H0[]]. rewrite <-H1 in H.
  apply Property_Value,AxiomII' in H as [_[H3[[]|[]]]]; auto;
  rewrite H4. repeat split; auto.
  apply (OrderPM_Co8a _ _ (-(1))) in H; auto with real.
  rewrite Mult_P4,PlusMult_Co1,Mult_P4,<-PlusMult_Co3 in H;
  auto with real. destruct H. repeat split; intros; auto.
  elim H5; auto. rewrite H6,PlusMult_Co3,PlusMult_Co1;
  auto with real. pose proof OrderPM_Co9.
  apply (OrderPM_Co1 _ _ (-(1))) in H5; auto with real.
  rewrite Minus_P1,Plus_P4,Plus_P1 in H5; auto with real.
Qed.

Proposition Abs_P2 : ∀ x, x ∈ R -> ｜x｜ = ｜(-x)｜ /\ -｜x｜ ≤ x
  /\ x ≤ ｜x｜.
Proof.
  intros. destruct Abs_is_Function as [H0[]]. rewrite <-H1 in H.
  apply Property_Value,AxiomII' in H as [_[H[[]|[]]]]; auto;
  rewrite H4. pose proof H3. apply (OrderPM_Co3 _ _ (-x) (-x))
  in H5; auto with real; [ |apply Leq_P1; auto with real].
  rewrite Minus_P1,Plus_P4,Plus_P1 in H5; auto with real.
  pose proof H5. apply le_zero_Abs in H6; auto with real.
  rewrite H6,(PlusMult_Co3 (-x)),PlusMult_Co4; auto with real.
  repeat split; auto. apply (Leq_P3 _ 0); auto with real.
  apply Leq_P1; auto. pose proof H3.
  apply (OrderPM_Co1 _ _ (-x)) in H5; auto with real.
  rewrite Minus_P1,Plus_P4,Plus_P1 in H5; auto with real.
  pose proof H5. destruct H6. apply me_zero_Abs in H6;
  auto with real. rewrite H6,(PlusMult_Co3 (-x)),PlusMult_Co4;
  auto with real. repeat split. apply Leq_P1; auto. destruct H3,H5.
  apply (Leq_P3 _ 0); auto with real.
Qed.

Proposition Abs_P3 : ∀ x y, x ∈ R -> y ∈ R -> ｜(x · y)｜ = ｜x｜ · ｜y｜.
Proof.
  intros. pose proof H. pose proof H0.
  apply (Leq_P4 0) in H1 as [],H2 as []; auto with real.
  - pose proof H1. apply (OrderPM_Co7b _ _ y) in H3; auto with real.
    rewrite Mult_P4,PlusMult_Co1 in H3; auto with real.
    apply me_zero_Abs in H1,H2,H3; auto with real.
    rewrite H1,H2,H3; auto.
  - pose proof H1. apply (OrderPM_Co8b _ _ y) in H3; auto with real.
    rewrite (Mult_P4 0),PlusMult_Co1 in H3; auto with real.
    apply me_zero_Abs in H1; auto. apply le_zero_Abs in H2,H3;
    auto with real. rewrite H1,H2,H3,PlusMult_Co3,Mult_P3,
    (Mult_P4 _ x),<-Mult_P3,<-PlusMult_Co3; auto with real.
  - pose proof H1. apply (OrderPM_Co7b _ _ y) in H3; auto with real.
    rewrite (Mult_P4 0),PlusMult_Co1 in H3; auto with real.
    apply le_zero_Abs in H1,H3; auto with real.
    apply me_zero_Abs in H2; auto. rewrite H1,H2,H3,PlusMult_Co3,
    Mult_P3,<-PlusMult_Co3; auto with real.
  - pose proof H1. apply (OrderPM_Co8b _ _ y) in H3; auto with real.
    rewrite (Mult_P4 0),PlusMult_Co1 in H3; auto with real.
    apply le_zero_Abs in H1,H2; auto.
    apply me_zero_Abs in H3; auto with real.
    rewrite H1,H2,H3,PlusMult_Co3,(PlusMult_Co3 y),Mult_P3,
    <-(Mult_P3 _ x),(Mult_P4 x (-(1))),<-(PlusMult_Co3 x),
    PlusMult_Co4; auto with real.
Qed.

Proposition Abs_P4 : ∀ x y, x ∈ R -> y ∈ R -> 0 ≤ y
  -> ｜x｜ ≤ y <-> (-y ≤ x /\ x ≤ y).
Proof.
  intros. pose proof H. apply (Leq_P4 0) in H2 as [];
  auto with real.
  - pose proof H2. apply me_zero_Abs in H3; auto.
    rewrite H3. split; intros; [ |destruct H4]; auto.
    split; auto. apply (OrderPM_Co8b _ _ (-(1))) in H1;
    auto with real. rewrite Mult_P4,<-PlusMult_Co3,Mult_P4,
    PlusMult_Co1 in H1; auto with real. apply (Leq_P3 _ 0);
    auto with real. pose proof OrderPM_Co9.
    apply OrderPM_Co2a in H5; auto with real. destruct H5; auto.
  - pose proof H2. apply le_zero_Abs in H3; auto. rewrite H3.
    assert (∀ u v, u ∈ R -> v ∈ R -> -u ≤ v -> -v ≤ u).
    { intros. apply (OrderPM_Co8b _ _ (-(1))) in H6;
      auto with real. rewrite Mult_P4,<-PlusMult_Co3,Mult_P4,
      PlusMult_Co4 in H6; auto with real. pose proof OrderPM_Co9.
      apply OrderPM_Co2a in H7; auto with real. destruct H7; auto. }
    split; intros; [ |destruct H5]; auto. split; auto.
    apply (Leq_P3 _ 0); auto with real.
Qed.

Proposition Abs_P5 : ∀ x y, x ∈ R -> y ∈ R -> ｜(x + y)｜ ≤ ｜x｜ + ｜y｜
  /\ ｜(x - y)｜ ≤ ｜x｜ + ｜y｜ /\ ｜(｜x｜ - ｜y｜)｜ ≤ ｜(x - y)｜.
Proof.
  intros. assert (∀ u v, u ∈ R -> v ∈ R -> ｜(u + v)｜ ≤ ｜u｜ + ｜v｜).
  { intros. pose proof H1. pose proof H2.
    apply Abs_P2 in H3 as [H3[]],H4 as [H4[]].
    apply (OrderPM_Co3 _ _ v ｜v｜) in H6; auto with real.
    apply (OrderPM_Co3 _ _ (-｜v｜) v) in H5; auto with real.
    rewrite PlusMult_Co3,(PlusMult_Co3 ｜v｜),Mult_P4,
    (Mult_P4 (-(1))),<-Mult_P5,Mult_P4,<-PlusMult_Co3 in H5;
    auto with real. apply Abs_P4; auto with real.
    pose proof H1; pose proof H2.
    apply Abs_P1 in H9 as [H9 _],H10 as [H10 _].
    apply (OrderPM_Co3 _ _ 0 ｜v｜) in H9; auto with real.
    rewrite Plus_P1 in H9; auto with real. }
  split; auto. split. pose proof H0. apply Abs_P2 in H2 as [].
  rewrite H2. apply H1; auto with real.
  assert (∀ u v, u ∈ R -> v ∈ R -> 0 ≤ (｜u｜ - ｜v｜)
    -> ｜(｜u｜ - ｜v｜)｜ ≤ ｜(u - v)｜).
  { intros. pose proof H4. apply me_zero_Abs in H5; auto with real.
    rewrite H5. assert (｜((u - v) + v)｜ ≤ ｜(u - v)｜ + ｜v｜).
    { apply H1; auto with real. }
    rewrite <-Plus_P3,(Plus_P4 (-v)),Minus_P1,Plus_P1 in H6;
    auto with real. apply (Plus_Leq _ _ (-｜v｜)) in H6;
    auto with real. rewrite <-Plus_P3,Minus_P1,Plus_P1 in H6;
    auto with real. }
  pose proof zero_in_R. apply (Leq_P4 (｜x｜ - ｜y｜)) in H3 as [];
  auto with real.
  apply (Plus_Leq _ _ (｜y｜)) in H3; auto with real.
  rewrite <-Plus_P3,(Plus_P4 (-｜y｜)),Minus_P1,Plus_P1,
  Plus_P4,Plus_P1 in H3; auto with real.
  apply (Plus_Leq _ _ (-｜x｜)) in H3; auto with real.
  rewrite Minus_P1 in H3; auto with real.
  assert (∀ u v, u ∈ R -> v ∈ R -> ｜(u - v)｜ = ｜(v - u)｜).
  { intros. assert ((u - v) ∈ R); auto with real.
    apply Abs_P2 in H6 as [H6 _].
    rewrite (PlusMult_Co3 (u - v)),Mult_P4,Mult_P5,Mult_P4,
    <-PlusMult_Co3,Mult_P4,PlusMult_Co4,(Plus_P4 _ v) in H6;
    auto with real. }
  rewrite H4,(H4 x y); auto with real.
Qed.

Proposition Abs_P6 : ∀ x y, x ∈ R -> y ∈ R
  -> ｜(x - y)｜ = 0 <-> x = y.
Proof.
  intros. assert ((x - y) ∈ R); auto with real.
  apply Abs_P1 in H1 as [_]. split; intros. apply H1 in H2.
  assert (x - y + y = 0 + y). { rewrite H2; auto. }
  rewrite <-Plus_P3,(Plus_P4 _ y),Minus_P1,Plus_P1,Plus_P4,Plus_P1
  in H3; auto with real. rewrite H2,Minus_P1; auto.
  pose proof zero_in_R. apply Abs_P1 in H3 as []. apply H4; auto.
Qed.

Proposition Abs_P7 : ∀ x y, x ∈ R -> y ∈ R -> ｜(x - y)｜ = ｜(y - x)｜.
Proof.
  intros. assert ((x - y) ∈ R); auto with real.
  apply Abs_P2 in H1 as [H1 _].
  rewrite (PlusMult_Co3 (x - y)),Mult_P4,Mult_P5,Mult_P4,
  <-PlusMult_Co3,Mult_P4,PlusMult_Co4,(Plus_P4 _ y) in H1;
  auto with real.
Qed.

Proposition Abs_P8 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> ｜(x - y)｜ ≤ ｜(x - z)｜ + ｜(z - y)｜.
Proof.
  intros. assert (x - y = (x - z) + (z - y)).
  { rewrite Plus_P3,<-(Plus_P3 x),(Plus_P4 _ z),Minus_P1,
    Plus_P1; auto with real. }
  rewrite H2. apply Abs_P5; auto with real.
Qed.

























