/-
Copyright (c) 2026 Xiong Jiangkai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiong Jiangkai, Codex
-/
import Paper.BlindTests.NNLecture16.Core.Defs

/-!
# Paper.BlindTests.NNLecture16.Theorem43.PrimitiveModel

Primitive-model packaging for strict Theorem 43 interfaces.
-/

namespace Paper.BlindTests

/--
Primitive assumptions for Theorem 43:
probability model, bounded mean-zero sample family, linear-class norm bounds,
and activation regularity.
-/
structure Theorem43PrimitiveModel
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H] where
  μ : MeasureTheory.Measure Ω
  isProbability : MeasureTheory.IsProbabilityMeasure μ
  sample : BoundedMeanZeroSampleFamilyData (H := H) μ
  d : Nat
  linear : LinearClassData H d sample.nSamples
  act : Real -> Real
  B2' : Real
  hB2'Half : (1 / 2 : Real) ≤ B2'
  m : Nat
  hm : 1 ≤ m
  hn : 0 < sample.nSamples
  activation : ActivationLipschitzData act

end Paper.BlindTests
