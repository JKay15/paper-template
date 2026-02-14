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
Stone-route witness where the two-layer family only needs to be dense on the witness algebra:
every witness-algebra element lies in the closure of `Set.range realizeC`.
-/
structure TwoLayerStoneRouteClosureData (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  witnessAlg : Subalgebra ℝ C(UnitCube d, Real)
  hSep : witnessAlg.SeparatesPoints
  hWitnessInClosure :
    ∀ g : witnessAlg, (g : C(UnitCube d, Real)) ∈ closure (Set.range realizeC)

/--
Primitive Stone-route witness:
`realizeC` values lie in `witnessAlg` and are dense there.
This lets us automatically derive closure-level representability.
-/
structure TwoLayerStoneRoutePrimitiveData (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  witnessAlg : Subalgebra ℝ C(UnitCube d, Real)
  hSep : witnessAlg.SeparatesPoints
  hRangeInWitness : ∀ p : TwoLayerParams d m, realizeC p ∈ witnessAlg
  hDenseInWitness :
    DenseRange (fun p : TwoLayerParams d m => (⟨realizeC p, hRangeInWitness p⟩ : witnessAlg))

/-- Exact representability implies closure-level representability. -/
def TwoLayerStoneRouteData.toClosureData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteData d m) :
    TwoLayerStoneRouteClosureData d m where
  act := A.act
  realizeC := A.realizeC
  realize_eq := A.realize_eq
  witnessAlg := A.witnessAlg
  hSep := A.hSep
  hWitnessInClosure := by
    intro g
    obtain ⟨p, hp⟩ := A.hRepresent g
    have hmem : (g : C(UnitCube d, Real)) ∈ Set.range A.realizeC := by
      exact ⟨p, by simpa using hp⟩
    exact subset_closure hmem

/--
Primitive witness implies closure-level witness by converting dense range in the witness algebra
to closure of `Set.range realizeC` in ambient `C(UnitCube d, Real)`.
-/
def TwoLayerStoneRoutePrimitiveData.toClosureData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRoutePrimitiveData d m) :
    TwoLayerStoneRouteClosureData d m where
  act := A.act
  realizeC := A.realizeC
  realize_eq := A.realize_eq
  witnessAlg := A.witnessAlg
  hSep := A.hSep
  hWitnessInClosure := by
    intro g
    refine Metric.mem_closure_iff.2 ?_
    intro ε hε
    have hBallNe : (Metric.ball g ε).Nonempty := by
      refine ⟨g, ?_⟩
      simpa [Metric.mem_ball] using hε
    obtain ⟨p, hpBall⟩ :=
      DenseRange.exists_mem_open A.hDenseInWitness Metric.isOpen_ball hBallNe
    have hpDistSubtype :
        dist (⟨A.realizeC p, A.hRangeInWitness p⟩ : A.witnessAlg) g < ε := by
      simpa [Metric.mem_ball] using hpBall
    have hpDist :
        dist (g : C(UnitCube d, Real)) (A.realizeC p) < ε := by
      simpa [dist_comm] using hpDistSubtype
    refine ⟨A.realizeC p, ?_, hpDist⟩
    exact ⟨p, rfl⟩

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

/--
Epsilon-level approximation from Stone-Weierstrass plus closure-level representability:
the witness algebra is dense by separation, and each witness is approximable by `realizeC`.
-/
theorem TwoLayerStoneRouteClosureData.exists_uniform_near
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteClosureData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ < ε := by
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      A.witnessAlg A.hSep fStar (ε / 2) hε2
  have hgClosure :
      ((g : C(UnitCube d, Real)) ∈ closure (Set.range A.realizeC)) := A.hWitnessInClosure g
  obtain ⟨y, hyRange, hyDist⟩ := (Metric.mem_closure_iff.mp hgClosure) (ε / 2) hε2
  rcases hyRange with ⟨p, rfl⟩
  have hdist :
      dist (A.realizeC p) fStar ≤
        dist (A.realizeC p) (g : C(UnitCube d, Real)) +
          dist (g : C(UnitCube d, Real)) fStar :=
    dist_triangle _ _ _
  have hpyDist : dist (A.realizeC p) (g : C(UnitCube d, Real)) < ε / 2 := by
    simpa [dist_comm] using hyDist
  have hgfDist : dist (g : C(UnitCube d, Real)) fStar < ε / 2 := by
    simpa [dist_eq_norm] using hg
  have hsumDist : dist (A.realizeC p) fStar < ε := by
    have hlt :
        dist (A.realizeC p) (g : C(UnitCube d, Real)) +
            dist (g : C(UnitCube d, Real)) fStar <
          ε := by
      linarith [hpyDist, hgfDist]
    exact lt_of_le_of_lt hdist hlt
  exact ⟨p, by simpa [dist_eq_norm] using hsumDist⟩

/-- Non-strict epsilon variant (`≤ ε`) derived from the strict one (`< ε`). -/
theorem TwoLayerStoneRouteClosureData.exists_uniform_le
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteClosureData d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m, ‖A.realizeC p - fStar‖ ≤ ε := by
  obtain ⟨p, hp⟩ := A.exists_uniform_near fStar hε
  exact ⟨p, le_of_lt hp⟩

end Paper.BlindTests
