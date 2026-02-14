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

end Paper.BlindTests
