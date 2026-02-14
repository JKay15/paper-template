/-
Copyright (c) 2026 Xiong Jiangkai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiong Jiangkai, Codex
-/
import Mathlib
import MLTheory

/-!
# Paper.CaseStudies.NN_Th42_Th43

Case-study formalization for the NN Theorem 42/43 workflow.
This file is intentionally paper-local and only consumes reusable tools from `MLTheory`.
-/

namespace Paper.CaseStudies

open MLTheory.Core.Learning
open MLTheory.Methods.Learning

abbrev ContinuousFamily (X H : Type*) [TopologicalSpace X] := H -> C(X, Real)

/-- Case-study theorem 42 shape: instantiate a universal-approximation axiom at a target `f*`. -/
theorem theorem42_from_universal_approx_axiom
    {X H : Type*} [TopologicalSpace X] [CompactSpace X]
    (F : ContinuousFamily X H)
    (hUniversal : ∀ f : C(X, Real), ∀ ε : Real, 0 < ε -> ∃ h : H, ‖F h - f‖ ≤ ε)
    (fStar : C(X, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ h : H, ‖F h - fStar‖ ≤ ε := by
  exact hUniversal fStar ε hε

/-- Case-study theorem 43 pipeline: `radStd ≤ radAbs` + absolute contraction bridge. -/
theorem theorem43_pipeline_abs
    {H X : Type*} [Fintype H] [Nonempty H]
    (n : Nat) (F : HypothesisClass H X) (x : Sample X n) (φ : Real -> Real) (L : Real)
    (hContractAbs :
      ∀ σ : SignVector n,
        empiricalRadAbs n (fun h t => φ (F h t)) x σ ≤ L * empiricalRadAbs n F x σ) :
    radStd n (fun h t => φ (F h t)) x ≤ L * radAbs n F x := by
  have hStdToAbs :
      radStd n (fun h t => φ (F h t)) x ≤ radAbs n (fun h t => φ (F h t)) x :=
    radStd_le_radAbs n (fun h t => φ (F h t)) x
  have hContract :
      radAbs n (fun h t => φ (F h t)) x ≤ L * radAbs n F x :=
    lip_contraction_abs n F x φ L hContractAbs
  exact hStdToAbs.trans hContract

/-- Symmetric classes identify the standard and absolute Rademacher variants. -/
theorem theorem43_symmetry_bridge
    {H X : Type*} [Fintype H] [Nonempty H]
    (n : Nat) (F : HypothesisClass H X) (x : Sample X n) (hSymm : NegClosed F) :
    radAbs n F x = radStd n F x :=
  radAbs_eq_radStd_of_symmetric n F x hSymm

end Paper.CaseStudies
