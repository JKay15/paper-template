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
Explicit universal-approximation property in sup norm.
This is a concrete epsilon-style interface that can replace direct `DenseRange` use.
-/
def UniversalApproxProperty {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real)) : Prop :=
  ∀ f : C(X, Real), ∀ ε : Real, 0 < ε -> ∃ θ : Θ, ‖NN θ - f‖ ≤ ε

/--
Algorithmic universal approximation interface:
provides an explicit parameter selector `approx f ε` with an error guarantee.
-/
structure UniversalApproxAlgorithm {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real)) where
  approx : C(X, Real) -> Real -> Θ
  spec : ∀ f : C(X, Real), ∀ ε : Real, 0 < ε -> ‖NN (approx f ε) - f‖ ≤ ε

/-- Build an explicit approximator from the existential universal property. -/
noncomputable def universalApproxAlgorithm_of_property
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X] [Inhabited Θ]
    (NN : Θ -> C(X, Real))
    (hU : UniversalApproxProperty NN) :
    UniversalApproxAlgorithm NN where
  approx := fun f ε => if hε : 0 < ε then Classical.choose (hU f ε hε) else default
  spec := by
    intro f ε hε
    simpa [hε] using (Classical.choose_spec (hU f ε hε))

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

/-- Convert dense-range premise into the explicit epsilon-style property. -/
theorem universalApproxProperty_of_denseRange
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real))
    (hDense : DenseRange NN) :
    UniversalApproxProperty NN := by
  intro f ε hε
  exact theorem42_neural_networks_are_universal (NN := NN) hDense f hε

/-- Any algorithmic approximator induces the existential universal property. -/
theorem universalApproxProperty_of_algorithm
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real))
    (A : UniversalApproxAlgorithm NN) :
    UniversalApproxProperty NN := by
  intro f ε hε
  refine ⟨A.approx f ε, ?_⟩
  exact A.spec f ε hε

/-- Build an explicit approximator directly from dense range. -/
noncomputable def universalApproxAlgorithm_of_denseRange
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X] [Inhabited Θ]
    (NN : Θ -> C(X, Real))
    (hDense : DenseRange NN) :
    UniversalApproxAlgorithm NN :=
  universalApproxAlgorithm_of_property NN (universalApproxProperty_of_denseRange NN hDense)

/--
Theorem 42 in de-assumed interface form:
use `UniversalApproxProperty` directly, without taking `hDense` as input.
-/
theorem theorem42_neural_networks_are_universal_deassumed
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real))
    (hU : UniversalApproxProperty NN)
    (fStar : C(X, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε := by
  exact hU fStar ε hε

/-- Theorem 42 from an explicit approximation algorithm. -/
theorem theorem42_neural_networks_are_universal_from_algorithm
    {X Θ : Type*} [TopologicalSpace X] [CompactSpace X]
    (NN : Θ -> C(X, Real))
    (A : UniversalApproxAlgorithm NN)
    (fStar : C(X, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε := by
  exact theorem42_neural_networks_are_universal_deassumed
    (NN := NN) (hU := universalApproxProperty_of_algorithm NN A) fStar hε

/-- Unit-cube domain `[0,1]^d` encoded as a subtype of `Fin d -> Real`. -/
abbrev UnitCube (d : Nat) := {x : InputVec d // ∀ i : Fin d, x i ∈ Set.Icc (0 : Real) 1}

/-- Explicit parameter bundle for width-`m` two-layer networks on `R^d`. -/
structure TwoLayerParams (d m : Nat) where
  w : Fin m -> InputVec d
  b : Fin m -> Real
  α : Fin m -> Real

instance instInhabitedTwoLayerParams (d m : Nat) : Inhabited (TwoLayerParams d m) where
  default :=
    { w := fun _ _ => 0
      b := fun _ => 0
      α := fun _ => 0 }

/-- Evaluate a two-layer parameter bundle on an input vector. -/
def evalTwoLayerParams {d m : Nat}
    (act : Real -> Real) (p : TwoLayerParams d m) (x : InputVec d) : Real :=
  twoLayerNN act p.w p.b p.α x

/--
Concrete two-layer universal-approximation interface on the unit cube.
`realizeC` connects parameters to continuous functions and `realize_eq` pins the formula.
-/
structure TwoLayerUniversalApproxAlgorithm (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  approx : C(UnitCube d, Real) -> Real -> TwoLayerParams d m
  spec :
    ∀ f : C(UnitCube d, Real), ∀ ε : Real, 0 < ε ->
      ‖realizeC (approx f ε) - f‖ ≤ ε

/-- Convert concrete two-layer approximation interface to generic algorithm interface. -/
def TwoLayerUniversalApproxAlgorithm.toUniversalApproxAlgorithm
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerUniversalApproxAlgorithm d m) :
    UniversalApproxAlgorithm A.realizeC where
  approx := A.approx
  spec := A.spec

/--
Any concrete two-layer approximation algorithm induces the existential
universal-approximation property on `UnitCube d`.
-/
theorem TwoLayerUniversalApproxAlgorithm.universalApproxProperty
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerUniversalApproxAlgorithm d m) :
    UniversalApproxProperty A.realizeC := by
  exact universalApproxProperty_of_algorithm A.realizeC A.toUniversalApproxAlgorithm

/-- Construct a two-layer approximation algorithm from dense range (nonconstructive choice). -/
noncomputable def twoLayerUniversalApproxAlgorithm_of_denseRange
    {d m : Nat} [CompactSpace (UnitCube d)]
    (act : Real -> Real)
    (realizeC : TwoLayerParams d m -> C(UnitCube d, Real))
    (realize_eq :
      ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
        realizeC p x = evalTwoLayerParams act p x.1)
    (hDense : DenseRange realizeC) :
    TwoLayerUniversalApproxAlgorithm d m where
  act := act
  realizeC := realizeC
  realize_eq := realize_eq
  approx := (universalApproxAlgorithm_of_denseRange realizeC hDense).approx
  spec := (universalApproxAlgorithm_of_denseRange realizeC hDense).spec

/--
Packaged dense two-layer realization data:
formula link (`realize_eq`) + dense-range hypothesis (`hDense`).
-/
structure TwoLayerDenseRealization (d m : Nat) [CompactSpace (UnitCube d)] where
  act : Real -> Real
  realizeC : TwoLayerParams d m -> C(UnitCube d, Real)
  realize_eq :
    ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
      realizeC p x = evalTwoLayerParams act p x.1
  hDense : DenseRange realizeC

/-- Convert packaged dense two-layer realization data to an explicit approximation algorithm. -/
noncomputable def TwoLayerDenseRealization.toAlgorithm
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerDenseRealization d m) :
    TwoLayerUniversalApproxAlgorithm d m :=
  twoLayerUniversalApproxAlgorithm_of_denseRange
    (d := d) (m := m) A.act A.realizeC A.realize_eq A.hDense

/-- Dense two-layer realization data induces a generic universal-approximation algorithm. -/
noncomputable def TwoLayerDenseRealization.toUniversalApproxAlgorithm
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerDenseRealization d m) :
    UniversalApproxAlgorithm A.realizeC :=
  A.toAlgorithm.toUniversalApproxAlgorithm

/-- Dense two-layer realization data induces the universal-approximation property. -/
theorem TwoLayerDenseRealization.universalApproxProperty
    {d m : Nat} [CompactSpace (UnitCube d)]
    (A : TwoLayerDenseRealization d m) :
    UniversalApproxProperty A.realizeC := by
  exact universalApproxProperty_of_algorithm A.realizeC A.toUniversalApproxAlgorithm

/-- Theorem 42 specialized to the unit-cube domain. -/
theorem theorem42_on_unit_cube
    {d : Nat} {Θ : Type*}
    [CompactSpace (UnitCube d)]
    (NN : Θ -> C(UnitCube d, Real))
    (hDense : DenseRange NN)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε :=
  theorem42_neural_networks_are_universal (NN := NN) hDense fStar hε

/-- Unit-cube Theorem 42 in de-assumed interface form. -/
theorem theorem42_on_unit_cube_deassumed
    {d : Nat} {Θ : Type*}
    [CompactSpace (UnitCube d)]
    (NN : Θ -> C(UnitCube d, Real))
    (hU : UniversalApproxProperty NN)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε := by
  exact theorem42_neural_networks_are_universal_deassumed (NN := NN) hU fStar hε

/-- Unit-cube Theorem 42 from an explicit approximation algorithm. -/
theorem theorem42_on_unit_cube_from_algorithm
    {d : Nat} {Θ : Type*}
    [CompactSpace (UnitCube d)]
    (NN : Θ -> C(UnitCube d, Real))
    (A : UniversalApproxAlgorithm NN)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ θ : Θ, ‖NN θ - fStar‖ ≤ ε := by
  exact theorem42_on_unit_cube_deassumed
    (NN := NN) (hU := universalApproxProperty_of_algorithm NN A) fStar hε

/--
Theorem 42 for concrete two-layer parameterization:
produces explicit parameters and keeps the standard two-layer formula link.
-/
theorem theorem42_on_unit_cube_from_twoLayer_algorithm
    {d m : Nat}
    [CompactSpace (UnitCube d)]
    (A : TwoLayerUniversalApproxAlgorithm d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m,
      ‖A.realizeC p - fStar‖ ≤ ε
      ∧ ∀ x : UnitCube d, A.realizeC p x = evalTwoLayerParams A.act p x.1 := by
  refine ⟨A.approx fStar ε, ?_⟩
  constructor
  · exact A.spec fStar ε hε
  · intro x
    exact A.realize_eq (A.approx fStar ε) x

/--
Theorem 42 on unit cube directly from dense range of a concrete two-layer realization map.
This removes the need to manually provide an algorithm spec.
-/
theorem theorem42_on_unit_cube_from_twoLayer_denseRange
    {d m : Nat}
    [CompactSpace (UnitCube d)]
    (act : Real -> Real)
    (realizeC : TwoLayerParams d m -> C(UnitCube d, Real))
    (realize_eq :
      ∀ p : TwoLayerParams d m, ∀ x : UnitCube d,
        realizeC p x = evalTwoLayerParams act p x.1)
    (hDense : DenseRange realizeC)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m,
      ‖realizeC p - fStar‖ ≤ ε
      ∧ ∀ x : UnitCube d, realizeC p x = evalTwoLayerParams act p x.1 := by
  let A := twoLayerUniversalApproxAlgorithm_of_denseRange
    (d := d) (m := m) act realizeC realize_eq hDense
  refine ⟨A.approx fStar ε, ?_⟩
  constructor
  · exact A.spec fStar ε hε
  · intro x
    exact A.realize_eq (A.approx fStar ε) x

/--
Theorem 42 on unit cube from packaged dense two-layer realization data.
This keeps theorem inputs compact while preserving explicit formula witnesses.
-/
theorem theorem42_on_unit_cube_from_twoLayer_denseFamily
    {d m : Nat}
    [CompactSpace (UnitCube d)]
    (A : TwoLayerDenseRealization d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m,
      ‖A.realizeC p - fStar‖ ≤ ε
      ∧ ∀ x : UnitCube d, A.realizeC p x = evalTwoLayerParams A.act p x.1 := by
  exact theorem42_on_unit_cube_from_twoLayer_denseRange
    (d := d) (m := m) A.act A.realizeC A.realize_eq A.hDense fStar hε

/--
Theorem 42 from a dense two-layer family, routed through the explicit
algorithm interface (same conclusion as denseFamily direct version).
-/
theorem theorem42_on_unit_cube_from_twoLayer_denseFamily_via_algorithm
    {d m : Nat}
    [CompactSpace (UnitCube d)]
    (A : TwoLayerDenseRealization d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m,
      ‖A.realizeC p - fStar‖ ≤ ε
      ∧ ∀ x : UnitCube d, A.realizeC p x = evalTwoLayerParams A.act p x.1 := by
  let Alg : TwoLayerUniversalApproxAlgorithm d m := A.toAlgorithm
  refine ⟨Alg.approx fStar ε, ?_⟩
  constructor
  · exact Alg.spec fStar ε hε
  · intro x
    exact Alg.realize_eq (Alg.approx fStar ε) x

/--
Theorem 42 from a dense two-layer family, routed through the explicit
universal-approximation property interface.
-/
theorem theorem42_on_unit_cube_from_twoLayer_denseFamily_via_property
    {d m : Nat}
    [CompactSpace (UnitCube d)]
    (A : TwoLayerDenseRealization d m)
    (fStar : C(UnitCube d, Real)) {ε : Real} (hε : 0 < ε) :
    ∃ p : TwoLayerParams d m,
      ‖A.realizeC p - fStar‖ ≤ ε
      ∧ ∀ x : UnitCube d, A.realizeC p x = evalTwoLayerParams A.act p x.1 := by
  have hU : UniversalApproxProperty A.realizeC := A.universalApproxProperty
  obtain ⟨p, hp⟩ := theorem42_on_unit_cube_deassumed
    (NN := A.realizeC) hU fStar hε
  refine ⟨p, hp, ?_⟩
  intro x
  exact A.realize_eq p x

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

/-- Pointwise sample bound implies a bound on a signed average. -/
private lemma signedAverage_abs_le_of_sample_bound
    {X : Type*} {n : Nat} (hn : 0 < n)
    (f : X -> Real) (x : Sample X n) (σ : SignVector n)
    (M : Real)
    (hfx : ∀ i : Fin n, |f (x i)| ≤ M) :
    |signedAverage n x f σ| ≤ M := by
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hcoef_nonneg : 0 ≤ (1 / (n : Real)) := by positivity
  have hsumAbs :
      |∑ i : Fin n, rademacherSign (σ i) * f (x i)| ≤
        ∑ i : Fin n, |rademacherSign (σ i) * f (x i)| := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hterm :
      ∀ i : Fin n, |rademacherSign (σ i) * f (x i)| ≤ M := by
    intro i
    calc
      |rademacherSign (σ i) * f (x i)| = |rademacherSign (σ i)| * |f (x i)| := by
        simp [abs_mul]
      _ = |f (x i)| := by simp [MLTheory.Core.Learning.abs_rademacherSign]
      _ ≤ M := hfx i
  have hsumBound :
      ∑ i : Fin n, |rademacherSign (σ i) * f (x i)| ≤
        ∑ i : Fin n, M :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hsumBound' :
      ∑ i : Fin n, |rademacherSign (σ i) * f (x i)| ≤ (n : Real) * M := by
    simpa using hsumBound
  calc
    |signedAverage n x f σ|
        = |(1 / (n : Real)) * ∑ i : Fin n, rademacherSign (σ i) * f (x i)| := by
            rfl
    _ = (1 / (n : Real)) * |∑ i : Fin n, rademacherSign (σ i) * f (x i)| := by
          simp [abs_mul]
    _ ≤ (1 / (n : Real)) * ((n : Real) * M) := by
          exact mul_le_mul_of_nonneg_left (hsumAbs.trans hsumBound') hcoef_nonneg
    _ = M := by
          have hnNe : (n : Real) ≠ 0 := by exact ne_of_gt hnR
          field_simp [hnNe, mul_assoc]

/-- Pointwise sample bound implies empirical absolute Rademacher bound. -/
private lemma empiricalRadAbs_le_of_sample_bound
    {H X : Type*} [Fintype H] [Nonempty H]
    {n : Nat} (hn : 0 < n)
    (F : HypothesisClass H X) (x : Sample X n) (σ : SignVector n)
    (M : Real)
    (hPointwise : ∀ h : H, ∀ i : Fin n, |F h (x i)| ≤ M) :
    empiricalRadAbs n F x σ ≤ M := by
  classical
  unfold empiricalRadAbs
  exact Finset.sup'_le
    (s := Finset.univ)
    (f := fun h : H => |signedAverage n x (F h) σ|)
    Finset.univ_nonempty
    (by
      intro h hh
      exact signedAverage_abs_le_of_sample_bound (hn := hn) (f := F h) (x := x) (σ := σ)
        (M := M) (hPointwise h))

/-- Pointwise sample bound implies absolute Rademacher bound. -/
private lemma radAbs_le_of_sample_bound
    {H X : Type*} [Fintype H] [Nonempty H]
    {n : Nat} (hn : 0 < n)
    (F : HypothesisClass H X) (x : Sample X n)
    (M : Real)
    (hPointwise : ∀ h : H, ∀ i : Fin n, |F h (x i)| ≤ M) :
    radAbs n F x ≤ M := by
  unfold radAbs
  have hcoef_nonneg : 0 ≤ (1 / (Fintype.card (SignVector n) : Real)) := by positivity
  have hsum_le :
      ∑ σ : SignVector n, empiricalRadAbs n F x σ ≤ ∑ _σ : SignVector n, M :=
    Finset.sum_le_sum (fun σ _ =>
      empiricalRadAbs_le_of_sample_bound (hn := hn) (F := F) (x := x) (σ := σ)
        (M := M) hPointwise)
  calc
    (1 / (Fintype.card (SignVector n) : Real)) *
        ∑ σ : SignVector n, empiricalRadAbs n F x σ
      ≤ (1 / (Fintype.card (SignVector n) : Real)) *
        ∑ _σ : SignVector n, M := by
          exact mul_le_mul_of_nonneg_left hsum_le hcoef_nonneg
    _ = M := by
          simp [Finset.sum_const]

/-- One-Lipschitz-at-zero implies `|act z| ≤ |z|`. -/
private lemma act_abs_le_of_oneLipschitzAtZero
    (act : Real -> Real)
    (hLip0 : OneLipschitzAtZero act) :
    ∀ z : Real, |act z| ≤ |z| := by
  intro z
  rcases hLip0 with ⟨h0, hLip⟩
  have h := hLip z 0
  simpa [h0] using h

/--
Bridge from mathlib's standard Lipschitz assumption to the local
`OneLipschitzAtZero` interface used by the theorem chain.
-/
private lemma oneLipschitzAtZero_of_lipschitzWith_one
    (act : Real -> Real)
    (h0 : act 0 = 0)
    (hLip : LipschitzWith (1 : NNReal) act) :
    OneLipschitzAtZero act := by
  refine ⟨h0, ?_⟩
  intro a b
  have hdist : dist (act a) (act b) ≤ (1 : NNReal) * dist a b :=
    (lipschitzWith_iff_dist_le_mul.mp hLip) a b
  simpa [Real.dist_eq, NNReal.coe_one] using hdist

/-- If `|act z| ≤ |z|`, then any scale `L ≥ 1` gives `|act z| ≤ L*|z|`. -/
private lemma act_abs_le_scaled
    (act : Real -> Real)
    (hAct1 : ∀ z : Real, |act z| ≤ |z|)
    (L : Real) (hL : 1 ≤ L) :
    ∀ z : Real, |act z| ≤ L * |z| := by
  intro z
  have hz : 0 ≤ |z| := abs_nonneg z
  calc
    |act z| ≤ |z| := hAct1 z
    _ ≤ L * |z| := by nlinarith

/-- Pointwise bound for linear predictors from norm bounds on weights and samples. -/
private lemma pointwise_linear_bound_of_norm_bounds
    {H : Type*}
    {d n : Nat}
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (B2 C2 : Real) (hB2 : 0 ≤ B2)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    ∀ h : H, ∀ i : Fin n,
      |(fun h t => inner ℝ (w h) t) h (x i)| ≤ B2 * C2 / Real.sqrt (n : Real) := by
  intro h i
  have hInner : |inner ℝ (w h) (x i)| ≤ ‖w h‖ * ‖x i‖ :=
    abs_real_inner_le_norm (w h) (x i)
  have hStep1 : ‖w h‖ * ‖x i‖ ≤ B2 * ‖x i‖ := by
    exact mul_le_mul_of_nonneg_right (hW h) (norm_nonneg _)
  have hStep2 : B2 * ‖x i‖ ≤ B2 * (C2 / Real.sqrt (n : Real)) := by
    exact mul_le_mul_of_nonneg_left (hX i) hB2
  have hStep3 :
      B2 * (C2 / Real.sqrt (n : Real)) ≤ B2 * C2 / Real.sqrt (n : Real) := by
    simp [div_eq_mul_inv, mul_assoc]
  exact (hInner.trans hStep1).trans (hStep2.trans hStep3)

/-- Unified bounded linear-class data used by de-assumed Theorem 43 variants. -/
structure LinearClassData (H : Type*) (d n : Nat) where
  w : H -> EuclideanSpace Real (Fin d)
  x : Sample (EuclideanSpace Real (Fin d)) n
  B2 : Real
  C2 : Real
  hB2 : 0 ≤ B2
  hC2 : 0 ≤ C2
  hW : ∀ h : H, ‖w h‖ ≤ B2
  hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)

/-- Pointwise bound derived from packaged linear-class data. -/
private lemma pointwise_linear_bound_of_data
    {H : Type*} {d n : Nat}
    (D : LinearClassData H d n) :
    ∀ h : H, ∀ i : Fin n,
      |(fun h t => inner ℝ (D.w h) t) h (D.x i)| ≤ D.B2 * D.C2 / Real.sqrt (n : Real) :=
  pointwise_linear_bound_of_norm_bounds D.w D.x D.B2 D.C2 D.hB2 D.hW D.hX

/--
Packaged finite-class concentration premises:
for each hypothesis, a bad-event tail plus a uniform cap `δ`.
-/
structure FiniteClassConcentrationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H]
    (μ : Measure Ω) where
  bad : H -> Set Ω
  tail : H -> ENNReal
  δ : ENNReal
  hConc : ∀ h : H, μ (bad h) ≤ tail h
  hTailLe : ∀ h : H, tail h ≤ δ

/--
Sample-level concentration template for finite hypothesis classes.
This records empirical-process metadata (`nSamples`) together with
per-hypothesis concentration outputs (`tail`, `δ`).
-/
structure SampleConcentrationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] where
  μ : Measure Ω
  bad : H -> Set Ω
  nSamples : Nat
  tail : H -> ENNReal
  δ : ENNReal
  hConc : ∀ h : H, μ (bad h) ≤ tail h
  hTailLe : ∀ h : H, tail h ≤ δ

/-- Forget sample metadata and recover the generic concentration bundle. -/
def SampleConcentrationData.toFiniteClassConcentrationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H]
    (S : SampleConcentrationData (Ω := Ω) (H := H)) :
    FiniteClassConcentrationData (H := H) S.μ where
  bad := S.bad
  tail := S.tail
  δ := S.δ
  hConc := S.hConc
  hTailLe := S.hTailLe

/--
Build sample-level concentration data from a uniform finite-class tail bound
`μ (bad h) ≤ δ`.
-/
def SampleConcentrationData.ofUniformTail
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H]
    (μ : Measure Ω) (bad : H -> Set Ω) (nSamples : Nat) (δ : ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ δ) :
    SampleConcentrationData (Ω := Ω) (H := H) where
  μ := μ
  bad := bad
  nSamples := nSamples
  tail := fun _ => δ
  δ := δ
  hConc := hTail
  hTailLe := by intro h; simp

/-- Convert a real-valued measure bound to an `ENNReal` bound. -/
private lemma measure_le_of_real_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Set Ω) (r : Real)
    (hr0 : 0 ≤ r) (hr : μ.real s ≤ r) :
    μ s ≤ ENNReal.ofReal r := by
  have hne : μ s ≠ ⊤ := measure_ne_top μ s
  have htr : (μ s).toReal ≤ r := by
    simpa [Measure.real_def] using hr
  exact (ENNReal.le_ofReal_iff_toReal_le hne hr0).2 htr

/--
Build sample-level concentration data from per-hypothesis subgaussian sum tails.
The bad event for each `h` is:
`{ω | ε ≤ ∑ i ∈ Finset.range nSamples, X h i ω}`.
-/
noncomputable def SampleConcentrationData.ofSubgaussianFamily
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (nSamples : Nat)
    (X : H -> Nat -> Ω -> Real)
    (c : NNReal) (ε : Real) (hε : 0 ≤ ε)
    (hIndep : ∀ h : H, ProbabilityTheory.iIndepFun (X h) μ)
    (hSubG :
      ∀ h : H, ∀ i < nSamples, ProbabilityTheory.HasSubgaussianMGF (X h i) c μ) :
    SampleConcentrationData (Ω := Ω) (H := H) := by
  let tailReal : Real := Real.exp (-(ε ^ 2) / (2 * (nSamples : Real) * (c : Real)))
  let tailENN : ENNReal := ENNReal.ofReal tailReal
  refine
    { μ := μ
      bad := fun h => {ω | ε ≤ ∑ i ∈ Finset.range nSamples, X h i ω}
      nSamples := nSamples
      tail := fun _ => tailENN
      δ := tailENN
      hConc := ?_
      hTailLe := ?_ }
  · intro h
    have hReal :
        μ.real {ω | ε ≤ ∑ i ∈ Finset.range nSamples, X h i ω} ≤ tailReal := by
      simpa [tailReal] using
        (ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
          (h_indep := hIndep h)
          (c := c) (n := nSamples)
          (h_subG := by
            intro i hi
            exact hSubG h i hi)
          (ε := ε) hε)
    have hNonneg : 0 ≤ tailReal := by
      dsimp [tailReal]
      positivity
    exact measure_le_of_real_bound μ _ tailReal hNonneg hReal
  · intro h
    rfl

/--
Packaged bounded mean-zero sample-family assumptions used to derive
subgaussian hypotheses via Hoeffding's lemma.
-/
structure BoundedMeanZeroSampleFamilyData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H]
    (μ : Measure Ω) where
  nSamples : Nat
  X : H -> Nat -> Ω -> Real
  a : Real
  b : Real
  hIndep : ∀ h : H, ProbabilityTheory.iIndepFun (X h) μ
  hMeas : ∀ h : H, ∀ i : Nat, AEMeasurable (X h i) μ
  hMemIcc : ∀ h : H, ∀ i : Nat, ∀ᵐ ω ∂μ, X h i ω ∈ Set.Icc a b
  hMeanZero : ∀ h : H, ∀ i : Nat, ∫ ω, X h i ω ∂μ = 0

namespace BoundedMeanZeroSampleFamilyData

/-- Hoeffding-scale subgaussian parameter induced by interval bounds `[a, b]`. -/
noncomputable def subgaussianParam
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H]
    {μ : Measure Ω}
    (S : BoundedMeanZeroSampleFamilyData (H := H) μ) : NNReal :=
  ((‖S.b - S.a‖₊ / 2) ^ 2)

/--
Automatic subgaussian family generated from bundled bounded mean-zero assumptions.
-/
lemma hasSubgaussianMGF
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : BoundedMeanZeroSampleFamilyData (H := H) μ) :
    ∀ h : H, ∀ i < S.nSamples,
      ProbabilityTheory.HasSubgaussianMGF (S.X h i) S.subgaussianParam μ := by
  intro h i hi
  simpa [BoundedMeanZeroSampleFamilyData.subgaussianParam] using
    (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := S.X h i) (μ := μ) (a := S.a) (b := S.b)
      (hm := S.hMeas h i) (hb := S.hMemIcc h i) (hc := S.hMeanZero h i))

end BoundedMeanZeroSampleFamilyData

/--
Packaged standard activation assumptions:
`act 0 = 0` and 1-Lipschitz in mathlib's `LipschitzWith` sense.
-/
structure ActivationLipschitzData (act : Real -> Real) : Prop where
  hActZero : act 0 = 0
  hLip : LipschitzWith (1 : NNReal) act

/-- Build packaged activation data from explicit `hActZero/hLip` assumptions. -/
private def ActivationLipschitzData.ofZeroAndLipschitzWith
    {act : Real -> Real}
    (hActZero : act 0 = 0)
    (hLip : LipschitzWith (1 : NNReal) act) :
    ActivationLipschitzData act :=
  ⟨hActZero, hLip⟩

/-- Convert packaged standard activation assumptions to local `OneLipschitzAtZero`. -/
private lemma ActivationLipschitzData.toOneLipschitzAtZero
    {act : Real -> Real} (A : ActivationLipschitzData act) :
    OneLipschitzAtZero act :=
  oneLipschitzAtZero_of_lipschitzWith_one act A.hActZero A.hLip

/--
Theorem 43 (de-assumed version):
derive the final bound from pointwise sample control + activation growth control,
without directly assuming `hSingleUnit` / `hContractAbs`.
-/
theorem theorem43_rademacher_complexity_upper_bound_deassumed
    {H X : Type*} [Fintype H] [Nonempty H]
    (n m : Nat) (hn : 0 < n)
    (F : HypothesisClass H X) (x : Sample X n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2' : 0 ≤ B2') (hC2 : 0 ≤ C2)
    (hActGrowth :
      ∀ z : Real, |act z| ≤ (2 * B2' * Real.sqrt (m : Real)) * |z|)
    (hPointwise :
      ∀ h : H, ∀ i : Fin n, |F h (x i)| ≤ B2 * C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (F h t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real)) := by
  let L : Real := 2 * B2' * Real.sqrt (m : Real)
  let Base : Real := B2 * C2 / Real.sqrt (n : Real)
  have hL_nonneg : 0 ≤ L := by
    unfold L
    have h2B_nonneg : 0 ≤ 2 * B2' := by nlinarith
    exact mul_nonneg h2B_nonneg (Real.sqrt_nonneg (m : Real))
  have hBase_nonneg : 0 ≤ Base := by
    unfold Base
    exact div_nonneg (mul_nonneg hB2 hC2) (Real.sqrt_nonneg (n : Real))
  have hPointwiseAct :
      ∀ h : H, ∀ i : Fin n, |(fun h t => act (F h t)) h (x i)| ≤ L * Base := by
    intro h i
    have hGrowth := hActGrowth (F h (x i))
    have hBaseVal := hPointwise h i
    have hMul := mul_le_mul_of_nonneg_left hBaseVal hL_nonneg
    simpa [L, Base, abs_mul, mul_assoc, mul_left_comm, mul_comm] using hGrowth.trans hMul
  have hAbsBound :
      radAbs n (fun h t => act (F h t)) x ≤ L * Base :=
    radAbs_le_of_sample_bound (hn := hn) (F := fun h t => act (F h t)) (x := x)
      (M := L * Base) hPointwiseAct
  have hStdToAbs :
      radStd n (fun h t => act (F h t)) x ≤ radAbs n (fun h t => act (F h t)) x :=
    radStd_le_radAbs n (fun h t => act (F h t)) x
  simpa [L, Base, mul_assoc, mul_left_comm, mul_comm] using hStdToAbs.trans hAbsBound

/--
Theorem 43 (further de-assumed):
derive bounds from
1) one-Lipschitz-at-zero activation (plus scale lower bound),
2) linear predictor norm controls (`‖w_h‖` and `‖x_i‖`).
-/
theorem theorem43_rademacher_linear_from_norm_bounds
    {H : Type*} [Fintype H] [Nonempty H]
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2' : 0 ≤ B2') (hC2 : 0 ≤ C2)
    (hLip0 : OneLipschitzAtZero act)
    (hScale : 1 ≤ 2 * B2' * Real.sqrt (m : Real))
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real)) := by
  have hActBase : ∀ z : Real, |act z| ≤ |z| :=
    act_abs_le_of_oneLipschitzAtZero act hLip0
  have hActGrowth :
      ∀ z : Real, |act z| ≤ (2 * B2' * Real.sqrt (m : Real)) * |z| :=
    act_abs_le_scaled act hActBase (2 * B2' * Real.sqrt (m : Real)) hScale
  have hPointwise :
      ∀ h : H, ∀ i : Fin n,
        |(fun h t => inner ℝ (w h) t) h (x i)| ≤ B2 * C2 / Real.sqrt (n : Real) :=
    pointwise_linear_bound_of_norm_bounds w x B2 C2 hB2 hW hX
  exact theorem43_rademacher_complexity_upper_bound_deassumed
    (n := n) (m := m) (hn := hn)
    (F := fun h t => inner ℝ (w h) t) (x := x)
    (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2' hC2 hActGrowth hPointwise

/-- Natural sufficient condition for the scale lower bound. -/
private lemma scale_lower_bound_of_half_and_width
    (B2' : Real) (m : Nat)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m) :
    1 ≤ 2 * B2' * Real.sqrt (m : Real) := by
  have hB2'Nonneg : 0 ≤ B2' := by nlinarith
  have hTwo : (1 : Real) ≤ 2 * B2' := by nlinarith
  have hmR : (1 : Real) ≤ (m : Real) := by exact_mod_cast hm
  have hSqrt : (1 : Real) ≤ Real.sqrt (m : Real) := (Real.one_le_sqrt).2 hmR
  calc
    (1 : Real) = 1 * 1 := by ring
    _ ≤ (2 * B2') * Real.sqrt (m : Real) := by
      refine mul_le_mul hTwo hSqrt (by positivity) ?_
      have : 0 ≤ (2 : Real) := by positivity
      exact mul_nonneg this hB2'Nonneg

/--
Theorem 43 with natural scale assumptions:
replace explicit `hScale` by `B2' ≥ 1/2` and `m ≥ 1`.
-/
theorem theorem43_rademacher_linear_from_norm_bounds_natural_scale
    {H : Type*} [Fintype H] [Nonempty H]
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (hLip0 : OneLipschitzAtZero act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real)) := by
  have hB2' : 0 ≤ B2' := by nlinarith
  have hScale : 1 ≤ 2 * B2' * Real.sqrt (m : Real) :=
    scale_lower_bound_of_half_and_width B2' m hB2'Half hm
  exact theorem43_rademacher_linear_from_norm_bounds
    (n := n) (m := m) (d := d) (hn := hn)
    (w := w) (x := x) (act := act)
    (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2' hC2 hLip0 hScale hW hX

/--
Theorem 43 natural-scale variant with packaged standard activation assumptions.
-/
theorem theorem43_rademacher_linear_from_norm_bounds_natural_scale_activationData
    {H : Type*} [Fintype H] [Nonempty H]
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real)) := by
  exact theorem43_rademacher_linear_from_norm_bounds_natural_scale
    (n := n) (m := m) (d := d) (hn := hn)
    (w := w) (x := x) (act := act)
    (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2'Half hC2 hm AAct.toOneLipschitzAtZero hW hX

/--
Theorem 43 natural-scale variant using packaged bounded linear-class data.
This removes direct `hW/hX` arguments from the theorem boundary.
-/
theorem theorem43_rademacher_linear_from_data_natural_scale
    {H : Type*} [Fintype H] [Nonempty H]
    (n m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (hLip0 : OneLipschitzAtZero act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real)) := by
  exact theorem43_rademacher_linear_from_norm_bounds_natural_scale
    (n := n) (m := m) (d := d) (hn := hn)
    (w := D.w) (x := D.x) (act := act)
    (B2 := D.B2) (B2' := B2') (C2 := D.C2)
    D.hB2 hB2'Half D.hC2 hm hLip0 D.hW D.hX

/--
Theorem 43 natural-scale variant using mathlib's `LipschitzWith` assumption.
This avoids directly requiring the custom `OneLipschitzAtZero` predicate.
-/
theorem theorem43_rademacher_linear_from_data_natural_scale_lipschitzWith
    {H : Type*} [Fintype H] [Nonempty H]
    (n m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (hActZero : act 0 = 0)
    (hLip : LipschitzWith (1 : NNReal) act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real)) := by
  have hLip0 : OneLipschitzAtZero act :=
    oneLipschitzAtZero_of_lipschitzWith_one act hActZero hLip
  exact theorem43_rademacher_linear_from_data_natural_scale
    (n := n) (m := m) (d := d) (hn := hn)
    (D := D) (act := act) (B2' := B2')
    hB2'Half hm hLip0

/--
Theorem 43 natural-scale variant using packaged standard activation assumptions.
-/
theorem theorem43_rademacher_linear_from_data_natural_scale_activationData
    {H : Type*} [Fintype H] [Nonempty H]
    (n m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real)) := by
  exact theorem43_rademacher_linear_from_data_natural_scale
    (n := n) (m := m) (d := d) (hn := hn)
    (D := D) (act := act) (B2' := B2')
    hB2'Half hm AAct.toOneLipschitzAtZero

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

/--
Theorem 43 + PAC (de-assumed):
uses pointwise sample control and activation growth control directly,
then appends the finite-class PAC union bound.
-/
theorem theorem43_with_pac_concentration_deassumed
    {Ω H X : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (δ : ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ δ)
    (n m : Nat) (hn : 0 < n)
    (F : HypothesisClass H X) (x : Sample X n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2' : 0 ≤ B2') (hC2 : 0 ≤ C2)
    (hActGrowth :
      ∀ z : Real, |act z| ≤ (2 * B2' * Real.sqrt (m : Real)) * |z|)
    (hPointwise :
      ∀ h : H, ∀ i : Fin n, |F h (x i)| ≤ B2 * C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (F h t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  constructor
  · exact theorem43_rademacher_complexity_upper_bound_deassumed
      (n := n) (m := m) (hn := hn) (F := F) (x := x) (act := act)
      (B2 := B2) (B2' := B2') (C2 := C2)
      hB2 hB2' hC2 hActGrowth hPointwise
  · exact pac_badEvent_uniform_bound μ bad δ hTail

/--
Theorem 43 + PAC with natural scale assumptions:
replace explicit `hScale` by `B2' ≥ 1/2` and `m ≥ 1`.
-/
theorem theorem43_with_pac_concentration_natural_scale
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (δ : ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ δ)
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (hLip0 : OneLipschitzAtZero act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  constructor
  · exact theorem43_rademacher_linear_from_norm_bounds_natural_scale
      (n := n) (m := m) (d := d) (hn := hn)
      (w := w) (x := x) (act := act)
      (B2 := B2) (B2' := B2') (C2 := C2)
      hB2 hB2'Half hC2 hm hLip0 hW hX
  · exact pac_badEvent_uniform_bound μ bad δ hTail

/--
Theorem 43 + PAC with natural scale assumptions and packaged standard activation assumptions.
-/
theorem theorem43_with_pac_concentration_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (δ : ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ δ)
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  exact theorem43_with_pac_concentration_natural_scale
    (μ := μ) (bad := bad) (δ := δ) hTail
    (n := n) (m := m) (d := d) (hn := hn)
    (w := w) (x := x)
    (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2'Half hC2 hm AAct.toOneLipschitzAtZero hW hX

/--
Theorem 43 + PAC from concentration premises (natural scale version):
replace direct `hTail` with a two-step concentration assumption
`μ(bad h) ≤ tail h ≤ δ`.
-/
theorem theorem43_with_pac_from_concentration_bundle_natural_scale
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (C : FiniteClassConcentrationData (H := H) μ)
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (hLip0 : OneLipschitzAtZero act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, C.bad h) ≤ (Fintype.card H : ENNReal) * C.δ := by
  constructor
  · exact theorem43_rademacher_linear_from_norm_bounds_natural_scale
      (n := n) (m := m) (d := d) (hn := hn)
      (w := w) (x := x) (act := act)
      (B2 := B2) (B2' := B2') (C2 := C2)
      hB2 hB2'Half hC2 hm hLip0 hW hX
  · calc
      μ (⋃ h : H, C.bad h) ≤ ∑ h : H, C.tail h :=
        pac_badEvent_from_concentration μ C.bad C.tail C.hConc
      _ ≤ ∑ h : H, C.δ :=
        Finset.sum_le_sum (fun h _ => C.hTailLe h)
      _ = (Fintype.card H : ENNReal) * C.δ := by
        simp

/--
Theorem 43 + PAC from concentration (bundle form) with packaged standard activation assumptions.
-/
theorem theorem43_with_pac_from_concentration_bundle_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (C : FiniteClassConcentrationData (H := H) μ)
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, C.bad h) ≤ (Fintype.card H : ENNReal) * C.δ := by
  exact theorem43_with_pac_from_concentration_bundle_natural_scale
    (μ := μ) (C := C) (n := n) (m := m) (d := d) (hn := hn)
    (w := w) (x := x)
    (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2'Half hC2 hm AAct.toOneLipschitzAtZero hW hX

/--
Theorem 43 + PAC from concentration premises (natural scale version):
wrapper form with explicit `bad/tail/δ` arguments.
-/
theorem theorem43_with_pac_from_concentration_natural_scale
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (tail : H -> ENNReal) (δ : ENNReal)
    (hConc : ∀ h : H, μ (bad h) ≤ tail h)
    (hTailLe : ∀ h : H, tail h ≤ δ)
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (hLip0 : OneLipschitzAtZero act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  let C : FiniteClassConcentrationData (H := H) μ :=
    { bad := bad
      tail := tail
      δ := δ
      hConc := hConc
      hTailLe := hTailLe }
  simpa [C] using theorem43_with_pac_from_concentration_bundle_natural_scale
    (μ := μ) (C := C) (n := n) (m := m) (d := d) (hn := hn)
    (w := w) (x := x) (act := act)
    (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2'Half hC2 hm hLip0 hW hX

/--
Theorem 43 + PAC from concentration (explicit wrapper),
with packaged standard activation assumptions.
-/
theorem theorem43_with_pac_from_concentration_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (tail : H -> ENNReal) (δ : ENNReal)
    (hConc : ∀ h : H, μ (bad h) ≤ tail h)
    (hTailLe : ∀ h : H, tail h ≤ δ)
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  exact theorem43_with_pac_from_concentration_natural_scale
    (μ := μ) (bad := bad) (tail := tail) (δ := δ)
    hConc hTailLe
    (n := n) (m := m) (d := d) (hn := hn)
    (w := w) (x := x)
    (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2'Half hC2 hm AAct.toOneLipschitzAtZero hW hX

/--
Theorem 43 + PAC from sample-level concentration data (non-data endpoint).
-/
theorem theorem43_with_pac_from_sample_concentration_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (S : SampleConcentrationData (Ω := Ω) (H := H))
    (m d : Nat) (hn : 0 < S.nSamples)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) S.nSamples)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin S.nSamples, ‖x i‖ ≤ C2 / Real.sqrt (S.nSamples : Real)) :
    radStd S.nSamples (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (S.nSamples : Real))
    ∧ S.μ (⋃ h : H, S.bad h) ≤ (Fintype.card H : ENNReal) * S.δ := by
  exact theorem43_with_pac_from_concentration_bundle_natural_scale_activationData
    (μ := S.μ) (C := S.toFiniteClassConcentrationData)
    (n := S.nSamples) (m := m) (d := d) (hn := hn)
    (w := w) (x := x)
    (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2'Half hC2 hm AAct hW hX

/--
Theorem 43 + PAC from a uniform tail bound `μ (bad h) ≤ δ`
using the sample-level concentration template (non-data endpoint).
-/
theorem theorem43_with_pac_from_uniform_tail_sample_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω)
    (n : Nat) (δ : ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ δ)
    (m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  simpa [SampleConcentrationData.ofUniformTail] using
    theorem43_with_pac_from_sample_concentration_natural_scale_activationData
      (S := SampleConcentrationData.ofUniformTail μ bad n δ hTail)
      (m := m) (d := d) (hn := hn)
      (w := w) (x := x)
      (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
      hB2 hB2'Half hC2 hm AAct hW hX

/--
Theorem 43 + PAC from subgaussian family tails
using `SampleConcentrationData.ofSubgaussianFamily` (non-data endpoint).
-/
theorem theorem43_with_pac_from_subgaussian_sample_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (n : Nat)
    (X : H -> Nat -> Ω -> Real)
    (c : NNReal) (ε : Real) (hε : 0 ≤ ε)
    (hIndep : ∀ h : H, ProbabilityTheory.iIndepFun (X h) μ)
    (hSubG : ∀ h : H, ∀ i < n, ProbabilityTheory.HasSubgaussianMGF (X h i) c μ)
    (m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, {ω | ε ≤ ∑ i ∈ Finset.range n, X h i ω}) ≤
      (Fintype.card H : ENNReal) *
        ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * (n : Real) * (c : Real)))) := by
  simpa [SampleConcentrationData.ofSubgaussianFamily] using
    theorem43_with_pac_from_sample_concentration_natural_scale_activationData
      (S := SampleConcentrationData.ofSubgaussianFamily μ n X c ε hε hIndep hSubG)
      (m := m) (d := d) (hn := hn)
      (w := w) (x := x)
      (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
      hB2 hB2'Half hC2 hm AAct hW hX

/--
Theorem 43 + PAC from subgaussian family tails
using `SampleConcentrationData.ofSubgaussianFamily` (data endpoint).
-/
theorem theorem43_with_pac_from_subgaussian_sample_data_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (n : Nat)
    (X : H -> Nat -> Ω -> Real)
    (c : NNReal) (ε : Real) (hε : 0 ≤ ε)
    (hIndep : ∀ h : H, ProbabilityTheory.iIndepFun (X h) μ)
    (hSubG : ∀ h : H, ∀ i < n, ProbabilityTheory.HasSubgaussianMGF (X h i) c μ)
    (m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, {ω | ε ≤ ∑ i ∈ Finset.range n, X h i ω}) ≤
      (Fintype.card H : ENNReal) *
        ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * (n : Real) * (c : Real)))) := by
    have hMain :
      radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
        (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real))
      ∧ μ (⋃ h : H, (SampleConcentrationData.ofSubgaussianFamily μ n X c ε hε hIndep hSubG).bad h) ≤
        (Fintype.card H : ENNReal) *
          (SampleConcentrationData.ofSubgaussianFamily μ n X c ε hε hIndep hSubG).δ := by
      let S := SampleConcentrationData.ofSubgaussianFamily μ n X c ε hε hIndep hSubG
      exact theorem43_with_pac_from_concentration_bundle_natural_scale_activationData
        (μ := μ)
        (C := S.toFiniteClassConcentrationData)
        (n := n) (m := m) (d := d) (hn := hn)
        (w := D.w) (x := D.x)
        (act := act) (B2 := D.B2) (B2' := B2') (C2 := D.C2)
        D.hB2 hB2'Half D.hC2 hm AAct D.hW D.hX
    simpa [SampleConcentrationData.ofSubgaussianFamily] using
      hMain

/--
Theorem 43 + PAC from bounded, mean-zero samples (non-data endpoint).
Uses mathlib Hoeffding lemma to derive `HasSubgaussianMGF` assumptions.
-/
theorem theorem43_with_pac_from_bounded_zeroMean_sample_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat)
    (X : H -> Nat -> Ω -> Real)
    (a b ε : Real) (hε : 0 ≤ ε)
    (hIndep : ∀ h : H, ProbabilityTheory.iIndepFun (X h) μ)
    (hMeas : ∀ h : H, ∀ i : Nat, AEMeasurable (X h i) μ)
    (hMemIcc : ∀ h : H, ∀ i : Nat, ∀ᵐ ω ∂μ, X h i ω ∈ Set.Icc a b)
    (hMeanZero : ∀ h : H, ∀ i : Nat, ∫ ω, X h i ω ∂μ = 0)
    (m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, {ω | ε ≤ ∑ i ∈ Finset.range n, X h i ω}) ≤
      (Fintype.card H : ENNReal) *
        ENNReal.ofReal
          (Real.exp (-(ε ^ 2) / (2 * (n : Real) * (((‖b - a‖₊ / 2) ^ 2 : NNReal) : Real)))) := by
  let cBound : NNReal := ((‖b - a‖₊ / 2) ^ 2)
  have hSubG : ∀ h : H, ∀ i < n, ProbabilityTheory.HasSubgaussianMGF (X h i) cBound μ := by
    intro h i hi
    simpa [cBound] using
      (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (X := X h i) (μ := μ) (a := a) (b := b)
        (hm := hMeas h i) (hb := hMemIcc h i) (hc := hMeanZero h i))
  simpa [cBound] using
    theorem43_with_pac_from_subgaussian_sample_natural_scale_activationData
      (μ := μ) (n := n)
      (X := X) (c := cBound) (ε := ε) hε
      hIndep hSubG
      (m := m) (d := d) (hn := hn)
      (w := w) (x := x)
      (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
      hB2 hB2'Half hC2 hm AAct hW hX

/--
Theorem 43 + PAC from bounded, mean-zero samples (data endpoint).
Uses mathlib Hoeffding lemma to derive `HasSubgaussianMGF` assumptions.
-/
theorem theorem43_with_pac_from_bounded_zeroMean_sample_data_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat)
    (X : H -> Nat -> Ω -> Real)
    (a b ε : Real) (hε : 0 ≤ ε)
    (hIndep : ∀ h : H, ProbabilityTheory.iIndepFun (X h) μ)
    (hMeas : ∀ h : H, ∀ i : Nat, AEMeasurable (X h i) μ)
    (hMemIcc : ∀ h : H, ∀ i : Nat, ∀ᵐ ω ∂μ, X h i ω ∈ Set.Icc a b)
    (hMeanZero : ∀ h : H, ∀ i : Nat, ∫ ω, X h i ω ∂μ = 0)
    (m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, {ω | ε ≤ ∑ i ∈ Finset.range n, X h i ω}) ≤
      (Fintype.card H : ENNReal) *
        ENNReal.ofReal
          (Real.exp (-(ε ^ 2) / (2 * (n : Real) * (((‖b - a‖₊ / 2) ^ 2 : NNReal) : Real)))) := by
  let cBound : NNReal := ((‖b - a‖₊ / 2) ^ 2)
  have hSubG : ∀ h : H, ∀ i < n, ProbabilityTheory.HasSubgaussianMGF (X h i) cBound μ := by
    intro h i hi
    simpa [cBound] using
      (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (X := X h i) (μ := μ) (a := a) (b := b)
        (hm := hMeas h i) (hb := hMemIcc h i) (hc := hMeanZero h i))
  simpa [cBound] using
    theorem43_with_pac_from_subgaussian_sample_data_natural_scale_activationData
      (μ := μ) (n := n)
      (X := X) (c := cBound) (ε := ε) hε
      hIndep hSubG
      (m := m) (d := d) (hn := hn)
      (D := D)
      (act := act) (B2' := B2')
      hB2'Half hm AAct

/--
Bundle endpoint for theorem43 + PAC under bounded, mean-zero sample assumptions
(non-data linear-class form).
-/
theorem theorem43_with_pac_from_bounded_family_bundle_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : BoundedMeanZeroSampleFamilyData (H := H) μ)
    (ε : Real) (hε : 0 ≤ ε)
    (m d : Nat) (hn : 0 < S.nSamples)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) S.nSamples)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin S.nSamples, ‖x i‖ ≤ C2 / Real.sqrt (S.nSamples : Real)) :
    radStd S.nSamples (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (S.nSamples : Real))
    ∧ μ (⋃ h : H, {ω | ε ≤ ∑ i ∈ Finset.range S.nSamples, S.X h i ω}) ≤
      (Fintype.card H : ENNReal) *
        ENNReal.ofReal
          (Real.exp
            (-(ε ^ 2) /
              (2 * (S.nSamples : Real) *
                ((BoundedMeanZeroSampleFamilyData.subgaussianParam S : NNReal) : Real)))) := by
  simpa [BoundedMeanZeroSampleFamilyData.subgaussianParam] using
    theorem43_with_pac_from_subgaussian_sample_natural_scale_activationData
      (μ := μ) (n := S.nSamples)
      (X := S.X) (c := S.subgaussianParam) (ε := ε) hε
      S.hIndep S.hasSubgaussianMGF
      (m := m) (d := d) (hn := hn)
      (w := w) (x := x)
      (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
      hB2 hB2'Half hC2 hm AAct hW hX

/--
Bundle endpoint for theorem43 + PAC under bounded, mean-zero sample assumptions
(packaged linear-class data form).
-/
theorem theorem43_with_pac_from_bounded_family_data_bundle_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : BoundedMeanZeroSampleFamilyData (H := H) μ)
    (ε : Real) (hε : 0 ≤ ε)
    (m d : Nat) (hn : 0 < S.nSamples)
    (D : LinearClassData H d S.nSamples)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act) :
    radStd S.nSamples (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (S.nSamples : Real))
    ∧ μ (⋃ h : H, {ω | ε ≤ ∑ i ∈ Finset.range S.nSamples, S.X h i ω}) ≤
      (Fintype.card H : ENNReal) *
        ENNReal.ofReal
          (Real.exp
            (-(ε ^ 2) /
              (2 * (S.nSamples : Real) *
                ((BoundedMeanZeroSampleFamilyData.subgaussianParam S : NNReal) : Real)))) := by
  simpa [BoundedMeanZeroSampleFamilyData.subgaussianParam] using
    theorem43_with_pac_from_subgaussian_sample_data_natural_scale_activationData
      (μ := μ) (n := S.nSamples)
      (X := S.X) (c := S.subgaussianParam) (ε := ε) hε
      S.hIndep S.hasSubgaussianMGF
      (m := m) (d := d) (hn := hn)
      (D := D)
      (act := act) (B2' := B2')
      hB2'Half hm AAct

/--
Theorem 43 + PAC concentration from packaged bounded linear-class data.
This removes direct `hW/hX` arguments from theorem inputs.
-/
theorem theorem43_with_pac_from_concentration_data_bundle_natural_scale
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (C : FiniteClassConcentrationData (H := H) μ)
    (n m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (hLip0 : OneLipschitzAtZero act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, C.bad h) ≤ (Fintype.card H : ENNReal) * C.δ := by
  constructor
  · exact theorem43_rademacher_linear_from_data_natural_scale
      (n := n) (m := m) (d := d) (hn := hn)
      (D := D) (act := act) (B2' := B2')
      hB2'Half hm hLip0
  · calc
      μ (⋃ h : H, C.bad h) ≤ ∑ h : H, C.tail h :=
        pac_badEvent_from_concentration μ C.bad C.tail C.hConc
      _ ≤ ∑ h : H, C.δ :=
        Finset.sum_le_sum (fun h _ => C.hTailLe h)
      _ = (Fintype.card H : ENNReal) * C.δ := by simp

/--
Theorem 43 + PAC (bundle form) using mathlib `LipschitzWith`.
-/
theorem theorem43_with_pac_from_concentration_data_bundle_natural_scale_lipschitzWith
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (C : FiniteClassConcentrationData (H := H) μ)
    (n m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (hActZero : act 0 = 0)
    (hLip : LipschitzWith (1 : NNReal) act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, C.bad h) ≤ (Fintype.card H : ENNReal) * C.δ := by
  have hLip0 : OneLipschitzAtZero act :=
    oneLipschitzAtZero_of_lipschitzWith_one act hActZero hLip
  exact theorem43_with_pac_from_concentration_data_bundle_natural_scale
    (μ := μ) (C := C) (n := n) (m := m) (d := d) (hn := hn)
    (D := D) (act := act) (B2' := B2')
    hB2'Half hm hLip0

/--
Theorem 43 + PAC (bundle form) using packaged standard activation assumptions.
-/
theorem theorem43_with_pac_from_concentration_data_bundle_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (C : FiniteClassConcentrationData (H := H) μ)
    (n m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, C.bad h) ≤ (Fintype.card H : ENNReal) * C.δ := by
  exact theorem43_with_pac_from_concentration_data_bundle_natural_scale
    (μ := μ) (C := C) (n := n) (m := m) (d := d) (hn := hn)
    (D := D) (act := act) (B2' := B2')
    hB2'Half hm AAct.toOneLipschitzAtZero

/--
Theorem 43 + PAC from concentration premises (natural scale version),
with mathlib `LipschitzWith` assumptions in the explicit-arguments wrapper.
-/
theorem theorem43_with_pac_from_concentration_natural_scale_lipschitzWith
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (tail : H -> ENNReal) (δ : ENNReal)
    (hConc : ∀ h : H, μ (bad h) ≤ tail h)
    (hTailLe : ∀ h : H, tail h ≤ δ)
    (n m d : Nat) (hn : 0 < n)
    (w : H -> EuclideanSpace Real (Fin d))
    (x : Sample (EuclideanSpace Real (Fin d)) n)
    (act : Real -> Real) (B2 B2' C2 : Real)
    (hB2 : 0 ≤ B2) (hB2'Half : (1 / 2 : Real) ≤ B2') (hC2 : 0 ≤ C2)
    (hm : 1 ≤ m)
    (hActZero : act 0 = 0)
    (hLip : LipschitzWith (1 : NNReal) act)
    (hW : ∀ h : H, ‖w h‖ ≤ B2)
    (hX : ∀ i : Fin n, ‖x i‖ ≤ C2 / Real.sqrt (n : Real)) :
    radStd n (fun h t => act (inner ℝ (w h) t)) x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (B2 * C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  exact theorem43_with_pac_from_concentration_natural_scale_activationData
    (μ := μ) (bad := bad) (tail := tail) (δ := δ)
    hConc hTailLe
    (n := n) (m := m) (d := d) (hn := hn)
    (w := w) (x := x)
    (act := act) (B2 := B2) (B2' := B2') (C2 := C2)
    hB2 hB2'Half hC2 hm (ActivationLipschitzData.ofZeroAndLipschitzWith hActZero hLip) hW hX

/--
Theorem 43 + PAC concentration from packaged bounded linear-class data.
Wrapper form with explicit `bad/tail/δ` arguments.
-/
theorem theorem43_with_pac_from_concentration_data_natural_scale
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (tail : H -> ENNReal) (δ : ENNReal)
    (hConc : ∀ h : H, μ (bad h) ≤ tail h)
    (hTailLe : ∀ h : H, tail h ≤ δ)
    (n m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (hLip0 : OneLipschitzAtZero act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  let C : FiniteClassConcentrationData (H := H) μ :=
    { bad := bad
      tail := tail
      δ := δ
      hConc := hConc
      hTailLe := hTailLe }
  simpa [C] using theorem43_with_pac_from_concentration_data_bundle_natural_scale
    (μ := μ) (C := C) (n := n) (m := m) (d := d) (hn := hn)
    (D := D) (act := act) (B2' := B2')
    hB2'Half hm hLip0

/--
Theorem 43 + PAC concentration (data wrapper form) with mathlib `LipschitzWith`.
-/
theorem theorem43_with_pac_from_concentration_data_natural_scale_lipschitzWith
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (tail : H -> ENNReal) (δ : ENNReal)
    (hConc : ∀ h : H, μ (bad h) ≤ tail h)
    (hTailLe : ∀ h : H, tail h ≤ δ)
    (n m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (hActZero : act 0 = 0)
    (hLip : LipschitzWith (1 : NNReal) act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  have hLip0 : OneLipschitzAtZero act :=
    oneLipschitzAtZero_of_lipschitzWith_one act hActZero hLip
  exact theorem43_with_pac_from_concentration_data_natural_scale
    (μ := μ) (bad := bad) (tail := tail) (δ := δ)
    hConc hTailLe
    (n := n) (m := m) (d := d) (hn := hn)
    (D := D) (act := act) (B2' := B2')
    hB2'Half hm hLip0

/--
Theorem 43 + PAC concentration (data wrapper form) with packaged standard activation assumptions.
-/
theorem theorem43_with_pac_from_concentration_data_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω) (tail : H -> ENNReal) (δ : ENNReal)
    (hConc : ∀ h : H, μ (bad h) ≤ tail h)
    (hTailLe : ∀ h : H, tail h ≤ δ)
    (n m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  exact theorem43_with_pac_from_concentration_data_natural_scale_lipschitzWith
    (μ := μ) (bad := bad) (tail := tail) (δ := δ)
    hConc hTailLe
    (n := n) (m := m) (d := d) (hn := hn)
    (D := D) (act := act) (B2' := B2')
    hB2'Half hm AAct.hActZero AAct.hLip

/--
Theorem 43 + PAC from sample-level concentration data (data endpoint).
-/
theorem theorem43_with_pac_from_sample_concentration_data_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (S : SampleConcentrationData (Ω := Ω) (H := H))
    (m d : Nat) (hn : 0 < S.nSamples)
    (D : LinearClassData H d S.nSamples)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act) :
    radStd S.nSamples (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (S.nSamples : Real))
    ∧ S.μ (⋃ h : H, S.bad h) ≤ (Fintype.card H : ENNReal) * S.δ := by
  exact theorem43_with_pac_from_concentration_data_bundle_natural_scale_activationData
    (μ := S.μ) (C := S.toFiniteClassConcentrationData)
    (n := S.nSamples) (m := m) (d := d) (hn := hn)
    (D := D) (act := act) (B2' := B2')
    hB2'Half hm AAct

/--
Theorem 43 + PAC from a uniform tail bound `μ (bad h) ≤ δ`
using the sample-level concentration template (data endpoint).
-/
theorem theorem43_with_pac_from_uniform_tail_sample_data_natural_scale_activationData
    {Ω H : Type*} [MeasurableSpace Ω] [Fintype H] [Nonempty H]
    (μ : Measure Ω) (bad : H -> Set Ω)
    (n : Nat) (δ : ENNReal)
    (hTail : ∀ h : H, μ (bad h) ≤ δ)
    (m d : Nat) (hn : 0 < n)
    (D : LinearClassData H d n)
    (act : Real -> Real) (B2' : Real)
    (hB2'Half : (1 / 2 : Real) ≤ B2')
    (hm : 1 ≤ m)
    (AAct : ActivationLipschitzData act) :
    radStd n (fun h t => act (inner ℝ (D.w h) t)) D.x ≤
      (2 * B2' * Real.sqrt (m : Real)) * (D.B2 * D.C2 / Real.sqrt (n : Real))
    ∧ μ (⋃ h : H, bad h) ≤ (Fintype.card H : ENNReal) * δ := by
  simpa [SampleConcentrationData.ofUniformTail] using
    theorem43_with_pac_from_sample_concentration_data_natural_scale_activationData
      (S := SampleConcentrationData.ofUniformTail μ bad n δ hTail)
      (m := m) (d := d) (hn := hn)
      (D := D) (act := act) (B2' := B2')
      hB2'Half hm AAct

end Paper.BlindTests
