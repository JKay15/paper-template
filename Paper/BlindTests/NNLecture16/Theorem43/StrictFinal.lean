/-
Copyright (c) 2026 Xiong Jiangkai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiong Jiangkai, Codex
-/
import Paper.BlindTests.NNLecture16.Theorem43.PrimitiveModel

/-!
# Paper.BlindTests.NNLecture16.Theorem43.StrictFinal

Strict final entrypoint for Theorem 43.
-/

namespace Paper.BlindTests

open MLTheory.Core.Learning
open MLTheory.Methods.Learning

/--
Strict final theorem-43 interface: from primitive model assumptions,
derive the Rademacher upper bound and PAC bad-event probability bound.
-/
theorem theorem43_strict_final
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (M : Theorem43PrimitiveModel (Ω := Ω) (H := H))
    (ε : Real) (hε : 0 ≤ ε) :
    radStd M.sample.nSamples (fun h t => M.act (inner ℝ (M.linear.w h) t)) M.linear.x ≤
      (2 * M.B2' * Real.sqrt (M.m : Real)) *
        (M.linear.B2 * M.linear.C2 / Real.sqrt (M.sample.nSamples : Real))
    ∧ M.μ (⋃ h : H, {ω | ε ≤ ∑ i ∈ Finset.range M.sample.nSamples, M.sample.X h i ω}) ≤
      (Fintype.card H : ENNReal) *
        ENNReal.ofReal
          (Real.exp
            (-(ε ^ 2) /
              (2 * (M.sample.nSamples : Real) *
                (↑M.sample.subgaussianParam)))) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := M.isProbability
  simpa [Theorem43PrimitiveModel] using
    theorem43_with_pac_from_bounded_family_data_bundle_natural_scale_activationData
      (μ := M.μ) (S := M.sample)
      (ε := ε) hε
      (m := M.m) (d := M.d) (hn := M.hn)
      (D := M.linear)
      (act := M.act) (B2' := M.B2')
      M.hB2'Half M.hm M.activation

end Paper.BlindTests
