/-
Copyright (c) 2026 Xiong Jiangkai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiong Jiangkai, Codex
-/
import Paper.BlindTests.NNLecture16.Theorem42.StoneRoute

/-!
# Paper.BlindTests.NNLecture16.Theorem42.StrictFinal

Strict final entrypoints for Theorem 42.
-/

namespace Paper.BlindTests

/--
Strict final theorem-42 interface:
for every target continuous function on `UnitCube d`, two-layer networks admit
uniform approximation up to any `ε > 0`, via the Stone-route witness.
-/
theorem theorem42_strict_final
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε :=
  A.exists_uniform_le fStar hε

/--
Formula-level strict variant: additionally exposes the concrete two-layer formula
realized by the returned parameter tuple.
-/
theorem theorem42_strict_final_formula
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m,
      ‖A.realizeC p - fStar‖ ≤ ε
      ∧ (∀ x : UnitCube d, A.realizeC p x = evalTwoLayerParams A.act p x.1) := by
  obtain ⟨p, hp⟩ := theorem42_strict_final (A := A) fStar hε
  refine ⟨p, hp, ?_⟩
  intro x
  simpa using A.realize_eq p x

end Paper.BlindTests
