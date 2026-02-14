/-
Copyright (c) 2026 Xiong Jiangkai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiong Jiangkai, Codex
-/
import Mathlib
import Paper.BlindTests.NNLecture16.Core.Defs

/-!
# Paper.BlindTests.NNLecture16.Theorem42.StoneRoute

Stone-Weierstrass route tools for strict Theorem 42 assembly.
-/

namespace Paper.BlindTests

/--
Stone-route witness for strict Theorem 42 on `UnitCube d`.
`hRepresent` states that every function in the witness algebra is realizable
by a two-layer parameter tuple.
-/
structure TwoLayerStoneRouteData (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  witnessAlg : Subalgebra ℝ C(UnitCube d, Real)
  hSep : witnessAlg.SeparatesPoints
  hRepresent :
    ∀ g : witnessAlg, ∃ p : TwoLayerParams d m, realizeC p = g

/--
Epsilon-level approximation obtained by Stone-Weierstrass on the witness algebra,
then transferred back to the two-layer parameterization via `hRepresent`.
-/
theorem TwoLayerStoneRouteData.exists_uniform_near
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ < ε := by
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      A.witnessAlg A.hSep fStar ε hε
  obtain ⟨p, hp⟩ := A.hRepresent g
  refine ⟨p, ?_⟩
  simpa [hp] using hg

/-- Non-strict epsilon variant (`≤ ε`) derived from the strict one (`< ε`). -/
theorem TwoLayerStoneRouteData.exists_uniform_le
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε := by
  obtain ⟨p, hp⟩ := A.exists_uniform_near fStar hε
  exact ⟨p, le_of_lt hp⟩

end Paper.BlindTests
