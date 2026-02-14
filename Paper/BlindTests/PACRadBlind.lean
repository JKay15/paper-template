/-
Copyright (c) 2026 Xiong Jiangkai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiong Jiangkai, Codex
-/
import Mathlib
import MLTheory

/-!
# Paper.BlindTests.PACRadBlind

Blind-test theorem assembly:
- PAC bad-event bound (finite class union bound)
- Rademacher contraction pipeline bound

This file stays in `paper-template` and does not add problem-specific theorems into `MLTheory`.
-/

namespace Paper.BlindTests

open MLTheory.Core.Learning
open MLTheory.Methods.Learning

open MeasureTheory

/--
A blind-test combined bound:
1) transformed class standard Rademacher complexity is bounded by a contracted base bound;
2) finite-class bad event probability is bounded by uniform tails.
-/
theorem pac_rademacher_combined_bound
    {Ω H X : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (δ : ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ δ)
    (n : Nat) (F : HypothesisClass H X) (x : Sample X n)
    (φ : Real -> Real) (L B : Real)
    (hL : 0 ≤ L)
    (hBase : radAbs n F x ≤ B)
    (hContractAbs :
      ∀ σ : SignVector n,
        empiricalRadAbs n (fun h t => φ (F h t)) x σ ≤ L * empiricalRadAbs n F x σ) :
    radStd n (fun h t => φ (F h t)) x ≤ L * B ∧
    μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  constructor
  · have hStdToAbs :
      radStd n (fun h t => φ (F h t)) x ≤ radAbs n (fun h t => φ (F h t)) x :=
      radStd_le_radAbs n (fun h t => φ (F h t)) x
    have hContract :
      radAbs n (fun h t => φ (F h t)) x ≤ L * radAbs n F x :=
      lip_contraction_abs n F x φ L hContractAbs
    have hPipe :
      radStd n (fun h t => φ (F h t)) x ≤ L * radAbs n F x :=
      hStdToAbs.trans hContract
    exact hPipe.trans (mul_le_mul_of_nonneg_left hBase hL)
  · exact pac_badEvent_uniform_bound μ bad δ hTail

/-- Variant using heterogeneous concentration tails. -/
theorem pac_rademacher_with_tail_function
    {Ω H X : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (tail : H -> ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ tail h)
    (n : Nat) (F : HypothesisClass H X) (x : Sample X n)
    (φ : Real -> Real) (L : Real)
    (hContractAbs :
      ∀ σ : SignVector n,
        empiricalRadAbs n (fun h t => φ (F h t)) x σ ≤ L * empiricalRadAbs n F x σ) :
    radStd n (fun h t => φ (F h t)) x ≤ L * radAbs n F x ∧
    μ (⋃ h : H, bad h) ≤ ∑ h : H, tail h := by
  constructor
  · have hStdToAbs :
      radStd n (fun h t => φ (F h t)) x ≤ radAbs n (fun h t => φ (F h t)) x :=
      radStd_le_radAbs n (fun h t => φ (F h t)) x
    have hContract :
      radAbs n (fun h t => φ (F h t)) x ≤ L * radAbs n F x :=
      lip_contraction_abs n F x φ L hContractAbs
    exact hStdToAbs.trans hContract
  · exact pac_badEvent_from_concentration μ bad tail hTail

end Paper.BlindTests
