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
    (A : TwoLayerStoneRouteClosureData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε :=
  A.exists_uniform_le fStar hε

/--
Compatibility wrapper: exact-representation witnesses can be downgraded to
closure-level witnesses and fed into `theorem42_strict_final`.
-/
theorem theorem42_strict_final_of_exact_representation
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε := by
  exact theorem42_strict_final (A := A.toClosureData) fStar hε

/--
Compatibility wrapper: primitive dense-range witnesses can be downgraded to
closure-level witnesses and fed into `theorem42_strict_final`.
-/
theorem theorem42_strict_final_of_primitive
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRoutePrimitiveData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε := by
  exact theorem42_strict_final (A := A.toClosureData) fStar hε

/--
Compatibility wrapper: generated witnesses (using `adjoin (range realizeC)`) can be
automatically lowered to closure-level witnesses and fed into `theorem42_strict_final`.
-/
theorem theorem42_strict_final_of_generated
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteGeneratedData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε := by
  exact theorem42_strict_final (A := A.toClosureData) fStar hε

/--
Compatibility wrapper: generated witnesses with parameter-level point separation
can be lowered automatically to strict-final route.
-/
theorem theorem42_strict_final_of_generated_param_sep
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteGeneratedParamSepData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε := by
  exact theorem42_strict_final (A := A.toClosureData) fStar hε

/--
Compatibility wrapper: if the realized family is algebra-closed (constants/add/mul)
and separates points, strict final follows with no explicit density witness input.
-/
theorem theorem42_strict_final_of_algebra_closed
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraClosedData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε := by
  exact theorem42_strict_final_of_exact_representation (A := A.toStoneRouteData) fStar hε

/--
Compatibility wrapper: algebra-closed witnesses with parameter-level point separation
can be lowered automatically to strict-final route.
-/
theorem theorem42_strict_final_of_algebra_closed_param_sep
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraClosedParamSepData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε := by
  exact theorem42_strict_final_of_algebra_closed (A := A.toAlgebraClosedData) fStar hε

/--
Compatibility wrapper: structured algebraic-generator witness with parameter-level
separation can be lowered automatically to strict-final route.
-/
theorem theorem42_strict_final_of_algebraic_generator_param_sep
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraicGeneratorParamSepData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.ops.realizeC p - fStar‖ ≤ ε := by
  exact theorem42_strict_final_of_algebra_closed_param_sep
    (A := A.toAlgebraClosedParamSepData) fStar hε

/--
Compatibility wrapper: existential algebraic assumptions + parameter-level separation
can be lifted noncomputably to strict-final route.
-/
theorem theorem42_strict_final_of_algebraic_exists_param_sep
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraicExistsParamSepData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε := by
  exact theorem42_strict_final (A := A.toClosureData) fStar hε

/--
Compatibility wrapper: eval-level existential algebraic assumptions
can be lifted to strict-final route.
-/
theorem theorem42_strict_final_of_eval_exists_param_sep
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteEvalExistsParamSepData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε := by
  exact theorem42_strict_final (A := A.toClosureData) fStar hε

/--
Compatibility wrapper: constructive eval-level algebraic operations
can be lowered to strict-final route.
-/
theorem theorem42_strict_final_of_eval_constructive_param_sep
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteEvalConstructiveParamSepData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.ops.realizeC p - fStar‖ ≤ ε := by
  exact theorem42_strict_final (A := A.toClosureData) fStar hε

/--
Formula-level strict variant: additionally exposes the concrete two-layer formula
realized by the returned parameter tuple.
-/
theorem theorem42_strict_final_formula
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteClosureData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m,
      ‖A.realizeC p - fStar‖ ≤ ε
      ∧ (∀ x : UnitCube d, A.realizeC p x = evalTwoLayerParams A.act p x.1) := by
  obtain ⟨p, hp⟩ := theorem42_strict_final (A := A) fStar hε
  refine ⟨p, hp, ?_⟩
  intro x
  simpa using A.realize_eq p x

end Paper.BlindTests
