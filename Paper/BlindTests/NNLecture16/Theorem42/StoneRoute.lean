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

/--
If the raw two-layer family separates points, then the subalgebra adjoined by that
family also separates points.
-/
theorem sepRange_of_sepParams
    {d m : Nat} [CompactSpace (UnitCube d)]
    (realizeC : TwoLayerParams d m -> C(UnitCube d, Real))
    (hSepParam :
      ∀ x y : UnitCube d, x ≠ y ->
        ∃ p : TwoLayerParams d m, realizeC p x ≠ realizeC p y) :
    Set.SeparatesPoints
      ((fun f : C(UnitCube d, Real) => (f : UnitCube d -> Real)) '' (Set.range realizeC)) := by
  intro x y hxy
  rcases hSepParam x y hxy with ⟨p, hp⟩
  refine ⟨(realizeC p : UnitCube d -> Real), ?_, hp⟩
  refine ⟨realizeC p, ?_, rfl⟩
  exact ⟨p, rfl⟩

/--
If the raw two-layer family separates points, then the subalgebra adjoined by that
family also separates points.
-/
theorem adjoin_separatesPoints_of_range
    {d m : Nat} [CompactSpace (UnitCube d)]
    (realizeC : TwoLayerParams d m -> C(UnitCube d, Real))
    (hSepRange :
      Set.SeparatesPoints
        ((fun f : C(UnitCube d, Real) => (f : UnitCube d -> Real)) '' (Set.range realizeC))) :
    (Algebra.adjoin ℝ (Set.range realizeC)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨f, hf, hneq⟩ := hSepRange hxy
  rcases hf with ⟨g, hg, rfl⟩
  rcases hg with ⟨p, rfl⟩
  refine ⟨(realizeC p : UnitCube d -> Real), ?_, hneq⟩
  refine ⟨realizeC p, ?_, rfl⟩
  exact Algebra.subset_adjoin ⟨p, rfl⟩

/--
Generated Stone-route witness:
`witnessAlg` is fixed to `adjoin (range realizeC)`.
Users provide only range-level separation and density in this adjoin space.
-/
structure TwoLayerStoneRouteGeneratedData (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  hSepRange :
    Set.SeparatesPoints
      ((fun f : C(UnitCube d, Real) => (f : UnitCube d -> Real)) '' (Set.range realizeC))
  hDenseInAdjoin :
    DenseRange
      (fun p : TwoLayerParams d m =>
        (⟨realizeC p, Algebra.subset_adjoin (s := Set.range realizeC) ⟨p, rfl⟩⟩ :
          Algebra.adjoin ℝ (Set.range realizeC)))

/--
Generated witness with parameter-level point separation:
use direct statement `∀ x ≠ y, ∃ p, realizeC p x ≠ realizeC p y`
instead of `Set.SeparatesPoints` on range image.
-/
structure TwoLayerStoneRouteGeneratedParamSepData
    (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  hSepParam :
    ∀ x y : UnitCube d, x ≠ y ->
      ∃ p : TwoLayerParams d m, realizeC p x ≠ realizeC p y
  hDenseInAdjoin :
    DenseRange
      (fun p : TwoLayerParams d m =>
        (⟨realizeC p, Algebra.subset_adjoin (s := Set.range realizeC) ⟨p, rfl⟩⟩ :
          Algebra.adjoin ℝ (Set.range realizeC)))

/--
Algebra-closed generated witness:
`realizeC` can realize constants and is closed under pointwise `+` and `*`.
Hence `adjoin (range realizeC)` is exactly representable by `realizeC`.
-/
structure TwoLayerStoneRouteAlgebraClosedData (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  hSepRange :
    Set.SeparatesPoints
      ((fun f : C(UnitCube d, Real) => (f : UnitCube d -> Real)) '' (Set.range realizeC))
  hConst :
    ∀ c : Real,
      ∃ p : TwoLayerParams d m, realizeC p = algebraMap ℝ C(UnitCube d, Real) c
  hAdd :
    ∀ p q : TwoLayerParams d m,
      ∃ r : TwoLayerParams d m, realizeC r = realizeC p + realizeC q
  hMul :
    ∀ p q : TwoLayerParams d m,
      ∃ r : TwoLayerParams d m, realizeC r = realizeC p * realizeC q

/--
Algebra-closed witness with parameter-level point separation.
-/
structure TwoLayerStoneRouteAlgebraClosedParamSepData
    (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  hSepParam :
    ∀ x y : UnitCube d, x ≠ y ->
      ∃ p : TwoLayerParams d m, realizeC p x ≠ realizeC p y
  hConst :
    ∀ c : Real,
      ∃ p : TwoLayerParams d m, realizeC p = algebraMap ℝ C(UnitCube d, Real) c
  hAdd :
    ∀ p q : TwoLayerParams d m,
      ∃ r : TwoLayerParams d m, realizeC r = realizeC p + realizeC q
  hMul :
    ∀ p q : TwoLayerParams d m,
      ∃ r : TwoLayerParams d m, realizeC r = realizeC p * realizeC q

/--
Structured algebra operations for a two-layer realization map.
This replaces existential algebra-closure assumptions by explicit constructors.
-/
structure TwoLayerRealizationAlgebraOps
    (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  constParam : Real -> TwoLayerParams d m
  addParam : TwoLayerParams d m -> TwoLayerParams d m -> TwoLayerParams d m
  mulParam : TwoLayerParams d m -> TwoLayerParams d m -> TwoLayerParams d m
  realize_const :
    ∀ c : Real, realizeC (constParam c) = algebraMap ℝ C(UnitCube d, Real) c
  realize_add :
    ∀ p q : TwoLayerParams d m, realizeC (addParam p q) = realizeC p + realizeC q
  realize_mul :
    ∀ p q : TwoLayerParams d m, realizeC (mulParam p q) = realizeC p * realizeC q

/--
Param-separation witness built from structured algebra operations.
-/
structure TwoLayerStoneRouteAlgebraicGeneratorParamSepData
    (d m : Nat) [CompactSpace (UnitCube d)] where
  ops : TwoLayerRealizationAlgebraOps d m
  hSepParam :
    ∀ x y : UnitCube d, x ≠ y ->
      ∃ p : TwoLayerParams d m, ops.realizeC p x ≠ ops.realizeC p y

/--
Existential version of algebraic-generator assumptions:
users provide only existence of parameters for constants/addition/multiplication,
and the concrete algebra operations are selected noncomputably.
-/
structure TwoLayerStoneRouteAlgebraicExistsParamSepData
    (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  hSepParam :
    ∀ x y : UnitCube d, x ≠ y ->
      ∃ p : TwoLayerParams d m, realizeC p x ≠ realizeC p y
  hConstExists :
    ∀ c : Real,
      ∃ p : TwoLayerParams d m, realizeC p = algebraMap ℝ C(UnitCube d, Real) c
  hAddExists :
    ∀ p q : TwoLayerParams d m,
      ∃ r : TwoLayerParams d m, realizeC r = realizeC p + realizeC q
  hMulExists :
    ∀ p q : TwoLayerParams d m,
      ∃ r : TwoLayerParams d m, realizeC r = realizeC p * realizeC q

/--
Eval-level existential algebraic assumptions:
users only prove closure properties directly on `evalTwoLayerParams`,
and function-level equalities in `C(UnitCube d, Real)` are derived automatically.
-/
structure TwoLayerStoneRouteEvalExistsParamSepData
    (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  hSepParam :
    ∀ x y : UnitCube d, x ≠ y ->
      ∃ p : TwoLayerParams d m, realizeC p x ≠ realizeC p y
  hConstEvalExists :
    ∀ c : Real,
      ∃ p : TwoLayerParams d m, ∀ x : InputVec d, evalTwoLayerParams act p x = c
  hAddEvalExists :
    ∀ p q : TwoLayerParams d m,
      ∃ r : TwoLayerParams d m,
        ∀ x : InputVec d,
          evalTwoLayerParams act r x =
            evalTwoLayerParams act p x + evalTwoLayerParams act q x
  hMulEvalExists :
    ∀ p q : TwoLayerParams d m,
      ∃ r : TwoLayerParams d m,
        ∀ x : InputVec d,
          evalTwoLayerParams act r x =
            evalTwoLayerParams act p x * evalTwoLayerParams act q x

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
Generated witness implies primitive witness by instantiating
`witnessAlg := adjoin (range realizeC)` and deriving separation automatically.
-/
def TwoLayerStoneRouteGeneratedData.toPrimitiveData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteGeneratedData d m) :
    TwoLayerStoneRoutePrimitiveData d m where
  act := A.act
  realizeC := A.realizeC
  realize_eq := A.realize_eq
  witnessAlg := Algebra.adjoin ℝ (Set.range A.realizeC)
  hSep := adjoin_separatesPoints_of_range A.realizeC A.hSepRange
  hRangeInWitness := by
    intro p
    exact Algebra.subset_adjoin ⟨p, rfl⟩
  hDenseInWitness := A.hDenseInAdjoin

/--
Parameter-separation generated witness can be converted to
range-separation generated witness.
-/
def TwoLayerStoneRouteGeneratedParamSepData.toGeneratedData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteGeneratedParamSepData d m) :
    TwoLayerStoneRouteGeneratedData d m where
  act := A.act
  realizeC := A.realizeC
  realize_eq := A.realize_eq
  hSepRange := sepRange_of_sepParams A.realizeC A.hSepParam
  hDenseInAdjoin := A.hDenseInAdjoin

/-- Parameter-separation generated witness implies closure-level witness. -/
def TwoLayerStoneRouteGeneratedParamSepData.toClosureData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteGeneratedParamSepData d m) :
    TwoLayerStoneRouteClosureData d m :=
  A.toGeneratedData.toPrimitiveData.toClosureData

/-- Generated witness implies closure-level witness by chaining previous adapters. -/
def TwoLayerStoneRouteGeneratedData.toClosureData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteGeneratedData d m) :
    TwoLayerStoneRouteClosureData d m :=
  A.toPrimitiveData.toClosureData

/--
If `realizeC` is algebra-closed (constants, addition, multiplication), then every element of
`adjoin (range realizeC)` is exactly representable by some parameter tuple.
-/
theorem TwoLayerStoneRouteAlgebraClosedData.adjoin_subset_range
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraClosedData d m) :
    (Algebra.adjoin ℝ (Set.range A.realizeC) : Set C(UnitCube d, Real)) ⊆
      Set.range A.realizeC := by
  intro f hf
  refine
    (Algebra.adjoin_induction
      (s := Set.range A.realizeC)
      (p := fun g _ => g ∈ Set.range A.realizeC)
      (mem := fun g hg => hg)
      (algebraMap := fun c => ?_ )
      (add := fun g h hg hh hgR hhR => ?_)
      (mul := fun g h hg hh hgR hhR => ?_)
      hf)
  · rcases A.hConst c with ⟨p, hp⟩
    exact ⟨p, hp⟩
  · rcases hgR with ⟨pg, hpg⟩
    rcases hhR with ⟨ph, hph⟩
    rcases A.hAdd pg ph with ⟨pr, hpr⟩
    refine ⟨pr, ?_⟩
    simpa [hpg, hph] using hpr
  · rcases hgR with ⟨pg, hpg⟩
    rcases hhR with ⟨ph, hph⟩
    rcases A.hMul pg ph with ⟨pr, hpr⟩
    refine ⟨pr, ?_⟩
    simpa [hpg, hph] using hpr

/--
Algebra-closed data can be converted to exact Stone-route data with witness algebra
`adjoin (range realizeC)`.
-/
def TwoLayerStoneRouteAlgebraClosedData.toStoneRouteData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraClosedData d m) :
    TwoLayerStoneRouteData d m where
  act := A.act
  realizeC := A.realizeC
  realize_eq := A.realize_eq
  witnessAlg := Algebra.adjoin ℝ (Set.range A.realizeC)
  hSep := adjoin_separatesPoints_of_range A.realizeC A.hSepRange
  hRepresent := by
    intro g
    have hsubset := A.adjoin_subset_range
    rcases hsubset g.property with ⟨p, hp⟩
    exact ⟨p, by simpa using hp⟩

/--
Parameter-separation algebra-closed witness can be converted to
range-separation algebra-closed witness.
-/
def TwoLayerStoneRouteAlgebraClosedParamSepData.toAlgebraClosedData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraClosedParamSepData d m) :
    TwoLayerStoneRouteAlgebraClosedData d m where
  act := A.act
  realizeC := A.realizeC
  realize_eq := A.realize_eq
  hSepRange := sepRange_of_sepParams A.realizeC A.hSepParam
  hConst := A.hConst
  hAdd := A.hAdd
  hMul := A.hMul

/--
Structured algebraic-generator witness converts to algebra-closed param-separation witness.
-/
def TwoLayerStoneRouteAlgebraicGeneratorParamSepData.toAlgebraClosedParamSepData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraicGeneratorParamSepData d m) :
    TwoLayerStoneRouteAlgebraClosedParamSepData d m where
  act := A.ops.act
  realizeC := A.ops.realizeC
  realize_eq := A.ops.realize_eq
  hSepParam := A.hSepParam
  hConst := by
    intro c
    exact ⟨A.ops.constParam c, A.ops.realize_const c⟩
  hAdd := by
    intro p q
    exact ⟨A.ops.addParam p q, A.ops.realize_add p q⟩
  hMul := by
    intro p q
    exact ⟨A.ops.mulParam p q, A.ops.realize_mul p q⟩

/--
Build structured algebra operations from existential assumptions by choice.
-/
noncomputable def TwoLayerStoneRouteAlgebraicExistsParamSepData.toAlgebraOps
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraicExistsParamSepData d m) :
    TwoLayerRealizationAlgebraOps d m where
  act := A.act
  realizeC := A.realizeC
  realize_eq := A.realize_eq
  constParam := fun c => Classical.choose (A.hConstExists c)
  addParam := fun p q => Classical.choose (A.hAddExists p q)
  mulParam := fun p q => Classical.choose (A.hMulExists p q)
  realize_const := by
    intro c
    exact Classical.choose_spec (A.hConstExists c)
  realize_add := by
    intro p q
    exact Classical.choose_spec (A.hAddExists p q)
  realize_mul := by
    intro p q
    exact Classical.choose_spec (A.hMulExists p q)

/--
Existential algebraic assumptions imply structured algebraic-generator witness.
-/
noncomputable def TwoLayerStoneRouteAlgebraicExistsParamSepData.toAlgebraicGeneratorParamSepData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraicExistsParamSepData d m) :
    TwoLayerStoneRouteAlgebraicGeneratorParamSepData d m where
  ops := A.toAlgebraOps
  hSepParam := A.hSepParam

/-- Parameter-separation algebra-closed witness implies closure-level witness. -/
def TwoLayerStoneRouteAlgebraClosedParamSepData.toClosureData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraClosedParamSepData d m) :
    TwoLayerStoneRouteClosureData d m :=
  A.toAlgebraClosedData.toStoneRouteData.toClosureData

/--
Structured algebraic-generator witness implies closure-level witness.
-/
def TwoLayerStoneRouteAlgebraicGeneratorParamSepData.toClosureData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraicGeneratorParamSepData d m) :
    TwoLayerStoneRouteClosureData d m :=
  A.toAlgebraClosedParamSepData.toClosureData

/-- Existential algebraic assumptions imply closure-level Stone witness. -/
noncomputable def TwoLayerStoneRouteAlgebraicExistsParamSepData.toClosureData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraicExistsParamSepData d m) :
    TwoLayerStoneRouteClosureData d m :=
  A.toAlgebraicGeneratorParamSepData.toClosureData

/--
Eval-level existential assumptions imply function-level existential algebraic assumptions.
-/
def TwoLayerStoneRouteEvalExistsParamSepData.toAlgebraicExistsParamSepData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteEvalExistsParamSepData d m) :
    TwoLayerStoneRouteAlgebraicExistsParamSepData d m where
  act := A.act
  realizeC := A.realizeC
  realize_eq := A.realize_eq
  hSepParam := A.hSepParam
  hConstExists := by
    intro c
    rcases A.hConstEvalExists c with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    ext x
    calc
      A.realizeC p x = evalTwoLayerParams A.act p x.1 := A.realize_eq p x
      _ = c := hp x.1
      _ = (algebraMap ℝ C(UnitCube d, Real) c) x := by simp
  hAddExists := by
    intro p q
    rcases A.hAddEvalExists p q with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    ext x
    calc
      A.realizeC r x = evalTwoLayerParams A.act r x.1 := A.realize_eq r x
      _ = evalTwoLayerParams A.act p x.1 + evalTwoLayerParams A.act q x.1 := hr x.1
      _ = A.realizeC p x + A.realizeC q x := by
        simpa [A.realize_eq p x, A.realize_eq q x]
  hMulExists := by
    intro p q
    rcases A.hMulEvalExists p q with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    ext x
    calc
      A.realizeC r x = evalTwoLayerParams A.act r x.1 := A.realize_eq r x
      _ = evalTwoLayerParams A.act p x.1 * evalTwoLayerParams A.act q x.1 := hr x.1
      _ = A.realizeC p x * A.realizeC q x := by
        simpa [A.realize_eq p x, A.realize_eq q x]

/-- Eval-level existential assumptions imply closure-level Stone witness. -/
noncomputable def TwoLayerStoneRouteEvalExistsParamSepData.toClosureData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteEvalExistsParamSepData d m) :
    TwoLayerStoneRouteClosureData d m :=
  (A.toAlgebraicExistsParamSepData).toClosureData

/-- Algebra-closed data yields closure-level Stone witness automatically. -/
def TwoLayerStoneRouteAlgebraClosedData.toClosureData
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerStoneRouteAlgebraClosedData d m) :
    TwoLayerStoneRouteClosureData d m :=
  A.toStoneRouteData.toClosureData

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
