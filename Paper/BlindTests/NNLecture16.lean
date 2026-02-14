/-
Copyright (c) 2026 Xiong Jiangkai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiong Jiangkai, Codex
-/
import Mathlib
import MLTheory

/-!
# Paper.BlindTests.NNLecture16

Blind-test formalization for Lecture 16 style NN theorems:
- Theorem 42 (universality): dense neural family approximates any target uniformly.
- Theorem 43 (Rademacher upper bound): composition + contraction + single-unit bound.

This file remains paper-local and only consumes generic interfaces from `MLTheory`.
-/

namespace Paper.BlindTests

open MLTheory.Core.Learning
open MLTheory.Methods.Learning
open MeasureTheory

open scoped BigOperators

/-- Finite-dimensional input vector (`R^d`) encoded as functions on `Fin d`. -/
abbrev InputVec (d : Nat) := Fin d -> Real

/-- Dot product on `InputVec d`. -/
def dot {d : Nat} (u v : InputVec d) : Real :=
  ∑ i : Fin d, u i * v i

/-- Two-layer neural predictor with hidden width `m`. -/
def twoLayerNN {d m : Nat}
    (act : Real -> Real) (w : Fin m -> InputVec d) (b : Fin m -> Real) (α : Fin m -> Real)
    (x : InputVec d) : Real :=
  ∑ j : Fin m, α j * act (dot (w j) x + b j)

/--
Explicit universal-approximation property in sup norm.
This is a concrete epsilon-style interface that can replace direct `DenseRange` use.
-/
def UniversalApproxProperty {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real)) : Prop :=
  ∀ f : C(X, Real), ∀ ε : Real, 0 < ε -> ∃ θ : Θ, ‖NN θ - f‖ ≤ ε

/--
Algorithmic universal approximation interface:
provides an explicit parameter selector `approx f ε` with an error guarantee.
-/
structure UniversalApproxAlgorithm {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real)) where
  approx : C(X, Real) -> Real -> Θ
  spec : ∀ f : C(X, Real), ∀ ε : Real, 0 < ε -> ‖NN (approx f ε) - f‖ ≤ ε

/--
Theorem 42 (universal approximation, abstract form):
if the NN family is dense in `C(X, R)`, then every target can be approximated uniformly.
-/
theorem theorem42_neural_networks_are_universal
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real))
    (hDense : DenseRange NN)
    (fStar : C(X, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε := by
  have hBallNe : (Metric.ball fStar ε).Nonempty := by
    refine ⟨fStar, ?_⟩
    simpa [Metric.mem_ball] using hε
  obtain ⟨θ, hθball⟩ := DenseRange.exists_mem_open hDense Metric.isOpen_ball hBallNe
  refine ⟨θ, ?_⟩
  have hdist : dist (NN θ) fStar < ε := by
    simpa [Metric.mem_ball] using hθball
  have hnorm : ‖NN θ - fStar‖ < ε := by
    simpa [dist_eq_norm] using hdist
  exact le_of_lt hnorm

/-- Convert dense-range premise into the explicit epsilon-style property. -/
theorem universalApproxProperty_of_denseRange
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real))
    (hDense : DenseRange NN) :
    UniversalApproxProperty NN := by
  intro f ε hε
  exact theorem42_neural_networks_are_universal (NN := NN) hDense f hε

/-- Any algorithmic approximator induces the existential universal property. -/
theorem universalApproxProperty_of_algorithm
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real))
    (A : UniversalApproxAlgorithm NN) :
    UniversalApproxProperty NN := by
  intro f ε hε
  refine ⟨A.approx f ε, ?_⟩
  exact A.spec f ε hε

/--
Theorem 42 in de-assumed interface form:
use `UniversalApproxProperty` directly, without taking `hDense` as input.
-/
theorem theorem42_neural_networks_are_universal_deassumed
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real))
    (hU : UniversalApproxProperty NN)
    (fStar : C(X, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε := by
  exact hU fStar ε hε

/-- Theorem 42 from an explicit approximation algorithm. -/
theorem theorem42_neural_networks_are_universal_from_algorithm
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real))
    (A : UniversalApproxAlgorithm NN)
    (fStar : C(X, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε := by
  exact theorem42_neural_networks_are_universal_deassumed
    (NN := NN) (hU := universalApproxProperty_of_algorithm NN A) fStar hε

/-- Unit-cube domain `[0,1]^d` encoded as a subtype of `Fin d -> Real`. -/
abbrev UnitCube (d : Nat) := {x : InputVec d // ∀ i : Fin d, x i ∈ Set.Icc (0 : Real) 1}

/-- Theorem 42 specialized to the unit-cube domain. -/
theorem theorem42_on_unit_cube
    {d : Nat} {Θ : Type*}
    [CompactSpace (UnitCube d)]
    (NN : Θ -> C(UnitCube d, Real))
    (hDense : DenseRange NN)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε :=
  theorem42_neural_networks_are_universal (NN := NN) hDense fStar hε

/-- Unit-cube Theorem 42 in de-assumed interface form. -/
theorem theorem42_on_unit_cube_deassumed
    {d : Nat} {Θ : Type*}
    [CompactSpace (UnitCube d)]
    (NN : Θ -> C(UnitCube d, Real))
    (hU : UniversalApproxProperty NN)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε := by
  exact theorem42_neural_networks_are_universal_deassumed (NN := NN) hU fStar hε

/-- Unit-cube Theorem 42 from an explicit approximation algorithm. -/
theorem theorem42_on_unit_cube_from_algorithm
    {d : Nat} {Θ : Type*}
    [CompactSpace (UnitCube d)]
    (NN : Θ -> C(UnitCube d, Real))
    (A : UniversalApproxAlgorithm NN)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε := by
  exact theorem42_on_unit_cube_deassumed
    (NN := NN) (hU := universalApproxProperty_of_algorithm NN A) fStar hε

/--
Theorem 43 (Rademacher upper bound, abstract form):
compose standard-to-absolute bridge, contraction, and single-unit bound.
-/
theorem theorem43_rademacher_complexity_upper_bound
    {H X : Type*} [Fintype H] [Nonempty H]
    (n m : Nat) (F : HypothesisClass H X) (x : Sample X n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2' : 0 ≤ B2')
    (hSingleUnit : radAbs n F x ≤ B2 * C2 / Real.sqrt (n : Real))
    (hContractAbs :
      ∀ σ : SignVector n,
        empiricalRadAbs n (fun h t => act (F h t)) x σ ≤
          (2 * B2' * Real.sqrt (m : Real)) * empiricalRadAbs n F x σ) :
    radStd n (fun h t => act (F h t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real)) := by
  have hStdToAbs :
      radStd n (fun h t => act (F h t)) x ≤ radAbs n (fun h t => act (F h t)) x :=
    radStd_le_radAbs n (fun h t => act (F h t)) x
  have hContract :
      radAbs n (fun h t => act (F h t)) x ≤
        (2 * B2' * Real.sqrt (m : Real)) * radAbs n F x :=
    lip_contraction_abs n F x act (2 * B2' * Real.sqrt (m : Real)) hContractAbs
  have hCoeffNonneg : 0 ≤ 2 * B2' * Real.sqrt (m : Real) := by
    have hsqrt : 0 ≤ Real.sqrt (m : Real) := Real.sqrt_nonneg (m : Real)
    nlinarith
  have hPipe :
      radStd n (fun h t => act (F h t)) x ≤
        (2 * B2' * Real.sqrt (m : Real)) * radAbs n F x :=
    hStdToAbs.trans hContract
  exact hPipe.trans (mul_le_mul_of_nonneg_left hSingleUnit hCoeffNonneg)

/-- Pointwise sample bound implies a bound on a signed average. -/
private lemma signedAverage_abs_le_of_sample_bound
    {X : Type*} {n : Nat} (hn : 0 < n)
    (f : X -> Real) (x : Sample X n) (σ : SignVector n)
    (M : Real)
    (hfx : ∀ i : Fin n, |f (x i)| ≤ M) :
    |signedAverage n x f σ| ≤ M := by
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hcoef_nonneg : 0 ≤ (1 / (n : Real)) := by positivity
  have hsumAbs :
      |∑ i : Fin n, rademacherSign (σ i) * f (x i)| ≤
        ∑ i : Fin n, |rademacherSign (σ i) * f (x i)| := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hterm :
      ∀ i : Fin n, |rademacherSign (σ i) * f (x i)| ≤ M := by
    intro i
    calc
      |rademacherSign (σ i) * f (x i)| = |rademacherSign (σ i)| * |f (x i)| := by
        simp [abs_mul]
      _ = |f (x i)| := by simp [MLTheory.Core.Learning.abs_rademacherSign]
      _ ≤ M := hfx i
  have hsumBound :
      ∑ i : Fin n, |rademacherSign (σ i) * f (x i)| ≤
        ∑ i : Fin n, M :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hsumBound' :
      ∑ i : Fin n, |rademacherSign (σ i) * f (x i)| ≤ (n : Real) * M := by
    simpa using hsumBound
  calc
    |signedAverage n x f σ|
        = |(1 / (n : Real)) * ∑ i : Fin n, rademacherSign (σ i) * f (x i)| := by
            rfl
    _ = (1 / (n : Real)) * |∑ i : Fin n, rademacherSign (σ i) * f (x i)| := by
          simp [abs_mul]
    _ ≤ (1 / (n : Real)) * ((n : Real) * M) := by
          exact mul_le_mul_of_nonneg_left (hsumAbs.trans hsumBound') hcoef_nonneg
    _ = M := by
          have hnNe : (n : Real) ≠ 0 := by exact ne_of_gt hnR
          field_simp [hnNe, mul_assoc]

/-- Pointwise sample bound implies empirical absolute Rademacher bound. -/
private lemma empiricalRadAbs_le_of_sample_bound
    {H X : Type*} [Fintype H] [Nonempty H]
    {n : Nat} (hn : 0 < n)
    (F : HypothesisClass H X) (x : Sample X n) (σ : SignVector n)
    (M : Real)
    (hPointwise : ∀ h : H, ∀ i : Fin n, |F h (x i)| ≤ M) :
    empiricalRadAbs n F x σ ≤ M := by
  classical
  unfold empiricalRadAbs
  exact Finset.sup'_le
    (s := Finset.univ)
    (f := fun h : H => |signedAverage n x (F h) σ|)
    Finset.univ_nonempty
    (by
      intro h hh
      exact signedAverage_abs_le_of_sample_bound (hn := hn) (f := F h) (x := x) (σ := σ)
        (M := M) (hPointwise h))

/-- Pointwise sample bound implies absolute Rademacher bound. -/
private lemma radAbs_le_of_sample_bound
    {H X : Type*} [Fintype H] [Nonempty H]
    {n : Nat} (hn : 0 < n)
    (F : HypothesisClass H X) (x : Sample X n)
    (M : Real)
    (hPointwise : ∀ h : H, ∀ i : Fin n, |F h (x i)| ≤ M) :
    radAbs n F x ≤ M := by
  unfold radAbs
  have hcoef_nonneg : 0 ≤ (1 / (Fintype.card (SignVector n) : Real)) := by positivity
  have hsum_le :
      ∑ σ : SignVector n, empiricalRadAbs n F x σ ≤ ∑ _σ : SignVector n, M :=
    Finset.sum_le_sum (fun σ _ =>
      empiricalRadAbs_le_of_sample_bound (hn := hn) (F := F) (x := x) (σ := σ)
        (M := M) hPointwise)
  calc
    (1 / (Fintype.card (SignVector n) : Real)) *
        ∑ σ : SignVector n, empiricalRadAbs n F x σ
      ≤ (1 / (Fintype.card (SignVector n) : Real)) *
        ∑ _σ : SignVector n, M := by
          exact mul_le_mul_of_nonneg_left hsum_le hcoef_nonneg
    _ = M := by
          simp [Finset.sum_const]

/-- One-Lipschitz-at-zero implies `|act z| ≤ |z|`. -/
private lemma act_abs_le_of_oneLipschitzAtZero
    (act : Real -> Real)
    (hLip0 : OneLipschitzAtZero act) :
    ∀ z : Real, |act z| ≤ |z| := by
  intro z
  rcases hLip0 with ⟨h0, hLip⟩
  have h := hLip z 0
  simpa [h0] using h

/-- If `|act z| ≤ |z|`, then any scale `L ≥ 1` gives `|act z| ≤ L*|z|`. -/
private lemma act_abs_le_scaled
    (act : Real -> Real)
    (hAct1 : ∀ z : Real, |act z| ≤ |z|)
    (L : Real) (hL : 1 ≤ L) :
    ∀ z : Real, |act z| ≤ L * |z| := by
  intro z
  have hz : 0 ≤ |z| := abs_nonneg z
  calc
    |act z| ≤ |z| := hAct1 z
    _ ≤ L * |z| := by nlinarith

/-- Pointwise bound for linear predictors from norm bounds on weights and samples. -/
private lemma pointwise_linear_bound_of_norm_bounds
    {H : Type*}
    {d n : Nat}
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (B2 C2 : Real) (hB2 : 0 ≤ B2)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    ∀ h : H, ∀ i : Fin n,
      |(fun h t => inner ℝ (w h) t) h (x i)| ≤ B2 * C2 / Real.sqrt (n : Real) := by
  intro h i
  have hInner : |inner ℝ (w h) (x i)| ≤ ‖w h‖ * ‖x i‖ :=
    abs_real_inner_le_norm (w h) (x i)
  have hStep1 : ‖w h‖ * ‖x i‖ ≤ B2 * ‖x i‖ := by
    exact mul_le_mul_of_nonneg_right (hW h) (norm_nonneg _)
  have hStep2 : B2 * ‖x i‖ ≤ B2 * (C2 / Real.sqrt (n : Real)) := by
    exact mul_le_mul_of_nonneg_left (hX i) hB2
  have hStep3 :
      B2 * (C2 / Real.sqrt (n : Real)) ≤ B2 * C2 / Real.sqrt (n : Real) := by
    simp [div_eq_mul_inv, mul_assoc]
  exact (hInner.trans hStep1).trans (hStep2.trans hStep3)

/--
Theorem 43 (de-assumed version):
derive the final bound from pointwise sample control + activation growth control,
without directly assuming `hSingleUnit` / `hContractAbs`.
-/
theorem theorem43_rademacher_complexity_upper_bound_deassumed
    {H X : Type*} [Fintype H] [Nonempty H]
    (n m : Nat) (hn : 0 < n)
    (F : HypothesisClass H X) (x : Sample X n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2' : 0 ≤ B2') (hC2 : 0 ≤ C2)
    (hActGrowth :
      ∀ z : Real, |act z| ≤ (2 * B2' * Real.sqrt (m : Real)) * |z|)
    (hPointwise :
      ∀ h : H, ∀ i : Fin n, |F h (x i)| ≤ B2 * C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (F h t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real)) := by
  let L : Real := 2 * B2' * Real.sqrt (m : Real)
  let Base : Real := B2 * C2 / Real.sqrt (n : Real)
  have hL_nonneg : 0 ≤ L := by
    unfold L
    have h2B_nonneg : 0 ≤ 2 * B2' := by nlinarith
    exact mul_nonneg h2B_nonneg (Real.sqrt_nonneg (m : Real))
  have hBase_nonneg : 0 ≤ Base := by
    unfold Base
    exact div_nonneg (mul_nonneg hB2 hC2) (Real.sqrt_nonneg (n : Real))
  have hPointwiseAct :
      ∀ h : H, ∀ i : Fin n, |(fun h t => act (F h t)) h (x i)| ≤ L * Base := by
    intro h i
    have hGrowth := hActGrowth (F h (x i))
    have hBaseVal := hPointwise h i
    have hMul := mul_le_mul_of_nonneg_left hBaseVal hL_nonneg
    simpa [L, Base, abs_mul, mul_assoc, mul_left_comm, mul_comm] using hGrowth.trans hMul
  have hAbsBound :
      radAbs n (fun h t => act (F h t)) x ≤ L * Base :=
    radAbs_le_of_sample_bound (hn := hn) (F := fun h t => act (F h t)) (x := x)
      (M := L * Base) hPointwiseAct
  have hStdToAbs :
      radStd n (fun h t => act (F h t)) x ≤ radAbs n (fun h t => act (F h t)) x :=
    radStd_le_radAbs n (fun h t => act (F h t)) x
  simpa [L, Base, mul_assoc, mul_left_comm, mul_comm] using hStdToAbs.trans hAbsBound

/--
Theorem 43 (further de-assumed):
derive bounds from
1) one-Lipschitz-at-zero activation (plus scale lower bound),
2) linear predictor norm controls (`‖w_h‖` and `‖x_i‖`).
-/
theorem theorem43_rademacher_linear_from_norm_bounds
    {H : Type*} [Fintype H] [Nonempty H]
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2' : 0 ≤ B2') (hC2 : 0 ≤ C2)
    (hLip0 : OneLipschitzAtZero act)
    (hScale : 1 ≤ 2 * B2' * Real.sqrt (m : Real))
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real)) := by
  have hActBase : ∀ z : Real, |act z| ≤ |z| :=
    act_abs_le_of_oneLipschitzAtZero act hLip0
  have hActGrowth :
      ∀ z : Real, |act z| ≤ (2 * B2' * Real.sqrt (m : Real)) * |z| :=
    act_abs_le_scaled act hActBase (2 * B2' * Real.sqrt (m : Real)) hScale
  have hPointwise :
      ∀ h : H, ∀ i : Fin n,
        |(fun h t => inner ℝ (w h) t) h (x i)| ≤ B2 * C2 / Real.sqrt (n : Real) :=
    pointwise_linear_bound_of_norm_bounds w x B2 C2 hB2 hW hX
  exact theorem43_rademacher_complexity_upper_bound_deassumed
    (n := n) (m := m) (hn := hn)
    (F := fun h t => inner ℝ (w h) t) (x := x)
    (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2' hC2 hActGrowth hPointwise

/-- Natural sufficient condition for the scale lower bound. -/
private lemma scale_lower_bound_of_half_and_width
    (B2' : Real) (m : Nat)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m) :
    1 ≤ 2 * B2' * Real.sqrt (m : Real) := by
  have hB2'Nonneg : 0 ≤ B2' := by nlinarith
  have hTwo : (1 : Real) ≤ 2 * B2' := by nlinarith
  have hmR : (1 : Real) ≤ (m : Real) := by exact_mod_cast hm
  have hSqrt : (1 : Real) ≤ Real.sqrt (m : Real) := (Real.one_le_sqrt).2 hmR
  calc
    (1 : Real) = 1 * 1 := by ring
    _ ≤ (2 * B2') * Real.sqrt (m : Real) := by
      refine mul_le_mul hTwo hSqrt (by positivity) ?_
      have : 0 ≤ (2 : Real) := by positivity
      exact mul_nonneg this hB2'Nonneg

/--
Theorem 43 with natural scale assumptions:
replace explicit `hScale` by `B2' ≥ 1/2` and `m ≥ 1`.
-/
theorem theorem43_rademacher_linear_from_norm_bounds_natural_scale
    {H : Type*} [Fintype H] [Nonempty H]
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (hLip0 : OneLipschitzAtZero act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real)) := by
  have hB2' : 0 ≤ B2' := by nlinarith
  have hScale : 1 ≤ 2 * B2' * Real.sqrt (m : Real) :=
    scale_lower_bound_of_half_and_width B2' m hB2'Half hm
  exact theorem43_rademacher_linear_from_norm_bounds
    (n := n) (m := m) (d := d) (hn := hn)
    (w := w) (x := x) (act := act)
    (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2' hC2 hLip0 hScale hW hX

/-- Theorem 43 constant written in the factored product-over-sqrt form. -/
theorem theorem43_rademacher_complexity_upper_bound_factored
    {H X : Type*} [Fintype H] [Nonempty H]
    (n m : Nat) (F : HypothesisClass H X) (x : Sample X n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2' : 0 ≤ B2')
    (hSingleUnit : radAbs n F x ≤ B2 * C2 / Real.sqrt (n : Real))
    (hContractAbs :
      ∀ σ : SignVector n,
        empiricalRadAbs n (fun h t => act (F h t)) x σ ≤
          (2 * B2' * Real.sqrt (m : Real)) * empiricalRadAbs n F x σ) :
    radStd n (fun h t => act (F h t)) x ≤
      ((2 * B2' * Real.sqrt (m : Real)) * B2 * C2) / Real.sqrt (n : Real) := by
  have hMain :
      radStd n (fun h t => act (F h t)) x ≤
        (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real)) :=
    theorem43_rademacher_complexity_upper_bound
      (n := n) (m := m) (F := F) (x := x) (act := act)
      (B2 := B2) (B2' := B2') (C2 := C2) hB2' hSingleUnit hContractAbs
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hMain

/-- Theorem 43 bridge when base class is symmetric (`radAbs = radStd`). -/
theorem theorem43_rademacher_symmetric_base
    {H X : Type*} [Fintype H] [Nonempty H]
    (n : Nat) (F : HypothesisClass H X) (x : Sample X n)
    (act : Real -> Real) (L : Real)
    (hSymm : NegClosed F)
    (hContractAbs :
      ∀ σ : SignVector n,
        empiricalRadAbs n (fun h t => act (F h t)) x σ ≤ L * empiricalRadAbs n F x σ) :
    radStd n (fun h t => act (F h t)) x ≤ L * radStd n F x := by
  have hPipe :
      radStd n (fun h t => act (F h t)) x ≤ L * radAbs n F x := by
    have hStdToAbs :
        radStd n (fun h t => act (F h t)) x ≤ radAbs n (fun h t => act (F h t)) x :=
      radStd_le_radAbs n (fun h t => act (F h t)) x
    have hContract :
        radAbs n (fun h t => act (F h t)) x ≤ L * radAbs n F x :=
      lip_contraction_abs n F x act L hContractAbs
    exact hStdToAbs.trans hContract
  have hEq : radAbs n F x = radStd n F x :=
    radAbs_eq_radStd_of_symmetric n F x hSymm
  simpa [hEq] using hPipe

/--
Theorem 43 + PAC concentration bridge:
adds a finite-class bad-event bound to the Rademacher complexity estimate.
-/
theorem theorem43_with_pac_concentration
    {Ω H X : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (δ : ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ δ)
    (n m : Nat) (F : HypothesisClass H X) (x : Sample X n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2' : 0 ≤ B2')
    (hSingleUnit : radAbs n F x ≤ B2 * C2 / Real.sqrt (n : Real))
    (hContractAbs :
      ∀ σ : SignVector n,
        empiricalRadAbs n (fun h t => act (F h t)) x σ ≤
          (2 * B2' * Real.sqrt (m : Real)) * empiricalRadAbs n F x σ) :
    radStd n (fun h t => act (F h t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  constructor
  · exact theorem43_rademacher_complexity_upper_bound
      (n := n) (m := m) (F := F) (x := x) (act := act)
      (B2 := B2) (B2' := B2') (C2 := C2) hB2' hSingleUnit hContractAbs
  · exact pac_badEvent_uniform_bound μ bad δ hTail

/--
Theorem 43 + PAC (de-assumed):
uses pointwise sample control and activation growth control directly,
then appends the finite-class PAC union bound.
-/
theorem theorem43_with_pac_concentration_deassumed
    {Ω H X : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (δ : ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ δ)
    (n m : Nat) (hn : 0 < n)
    (F : HypothesisClass H X) (x : Sample X n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2' : 0 ≤ B2') (hC2 : 0 ≤ C2)
    (hActGrowth :
      ∀ z : Real, |act z| ≤ (2 * B2' * Real.sqrt (m : Real)) * |z|)
    (hPointwise :
      ∀ h : H, ∀ i : Fin n, |F h (x i)| ≤ B2 * C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (F h t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  constructor
  · exact theorem43_rademacher_complexity_upper_bound_deassumed
      (n := n) (m := m) (hn := hn) (F := F) (x := x) (act := act)
      (B2 := B2) (B2' := B2') (C2 := C2)
      hB2 hB2' hC2 hActGrowth hPointwise
  · exact pac_badEvent_uniform_bound μ bad δ hTail

/--
Theorem 43 + PAC with natural scale assumptions:
replace explicit `hScale` by `B2' ≥ 1/2` and `m ≥ 1`.
-/
theorem theorem43_with_pac_concentration_natural_scale
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (δ : ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ δ)
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (hLip0 : OneLipschitzAtZero act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  constructor
  · exact theorem43_rademacher_linear_from_norm_bounds_natural_scale
      (n := n) (m := m) (d := d) (hn := hn)
      (w := w) (x := x) (act := act)
      (B2 := B2) (B2' := B2') (C2 := C2)
      hB2 hB2'Half hC2 hm hLip0 hW hX
  · exact pac_badEvent_uniform_bound μ bad δ hTail

/--
Theorem 43 + PAC from concentration premises (natural scale version):
replace direct `hTail` with a two-step concentration assumption
`μ(bad h) ≤ tail h ≤ δ`.
-/
theorem theorem43_with_pac_from_concentration_natural_scale
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (tail : H -> ENNReal) (δ : ENNReal)
    (hConc : ∀ h : H, μ (bad h) ≤ tail h)
    (hTailLe : ∀ h : H, tail h ≤ δ)
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (hLip0 : OneLipschitzAtZero act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  constructor
  · exact theorem43_rademacher_linear_from_norm_bounds_natural_scale
      (n := n) (m := m) (d := d) (hn := hn)
      (w := w) (x := x) (act := act)
      (B2 := B2) (B2' := B2') (C2 := C2)
      hB2 hB2'Half hC2 hm hLip0 hW hX
  · calc
      μ (⋃ h : H, bad h) ≤ ∑ h : H, tail h :=
        pac_badEvent_from_concentration μ bad tail hConc
      _ ≤ ∑ h : H, δ :=
        Finset.sum_le_sum (fun h _ => hTailLe h)
      _ = (Fintype.card H : ENNReal) * δ := by
        simp

end Paper.BlindTests
