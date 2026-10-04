import Mathlib
import Submission.Work.Diff.GE.kato_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the Gram–Schmidt step `katoU` and of its Gram function `katoGram`

`katoU g V W i = V i - ∑_{j < i} g.inner (V i) (W j) · W j` is an explicit (finite) algebraic
combination of the fields `V i` and `W j` (`j < i`) with coefficients the metric pairings
`g.inner (V i) (W j)`.  Hence, whenever `V i` is a smooth field and every `W j` with `j < i` is
smooth, both the field `katoU g V W i` and the scalar function
`katoGram g V W i = g.inner (katoU g V W i) (katoU g V W i)` are smooth.

The only non-formal input is that the metric pairing of two smooth fields is smooth, which is
Mathlib's `ContMDiff.inner_bundle` after registering the explicit metric `g` as the Riemannian
structure of the tangent bundle (`⟨g.toRiemannianMetric⟩`); with this instance the fibre inner
product is *definitionally* `g.inner`.  We record this step as `katoMetricPairingSmooth`; the rest
is the library calculus of smooth sections (`ContMDiff.smul_section`, `ContMDiff.sum_section`,
`ContMDiff.sub_section`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.GE

/-- **The metric pairing of two smooth tangent fields is smooth.**  For a smooth Riemannian
metric `g` and smooth fields `X`, `Y`, the function `y ↦ g.inner y (X y) (Y y)` is smooth.

This is the global form of `Work.Diff.GE.Pieces.pairing`: `CMDiff` is by definition the pointwise
property, so it suffices to establish smoothness at each point. -/
theorem katoMetricPairingSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) :
    CMDiff ∞ (fun y : M => g.inner y (X y) (Y y)) := by
  -- `CMDiff ∞ F` is `∀ y, CMDiffAt ∞ F y`; work pointwise.
  intro x
  -- Register `g` as the Riemannian structure of the tangent bundle: this provides both the fibre
  -- inner product space structure and the `IsContMDiffRiemannianBundle` instance required by
  -- `ContMDiffAt.inner_bundle`, and makes the fibre inner product definitionally `g.inner`.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact ContMDiffAt.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id)
    (v := X) (w := Y) (hX x) (hY x)

theorem kato_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (V W : katoIdx E → Π y : M, TangentSpace I y) (i : katoIdx E)
    (hV : CMDiff ∞ (T% (V i)))
    (hW : ∀ j, j.val < i.val → CMDiff ∞ (T% (W j))) :
    CMDiff ∞ (T% (katoU g V W i)) ∧ CMDiff ∞ (katoGram g V W i) := by
  -- The `j`-th summand of `katoU g V W i`, as a section.
  let t : katoIdx E → Π y : M, TangentSpace I y :=
    fun j y => g.inner y (V i y) (W j y) • W j y
  -- Smoothness of the pre-normalisation field.
  have hU : CMDiff ∞ (T% (katoU g V W i)) := by
    -- Each summand is the product of a smooth coefficient with the smooth field `W j`.
    have hterm : ∀ j ∈ katoPre (E := E) i, CMDiff ∞ (T% (t j)) := by
      intro j hj
      rw [katoPre_mem] at hj
      exact (katoMetricPairingSmooth g hV (hW j hj)).smul_section (hW j hj)
    -- The finite sum of the summands is smooth.
    have hsum : CMDiff ∞ (T% (fun x : M => ∑ j ∈ katoPre (E := E) i, t j x)) :=
      ContMDiff.sum_section (s := katoPre (E := E) i) hterm
    -- Subtract the sum from `V i`.
    have hV' : CMDiff ∞ (T% (V i - fun x : M => ∑ j ∈ katoPre (E := E) i, t j x)) :=
      hV.sub_section hsum
    -- `katoU g V W i` is that difference, by definition.
    convert hV' using 1
    funext y
    rfl
  -- `katoGram g V W i = g.inner (katoU g V W i) (katoU g V W i)` is a metric pairing.
  refine ⟨hU, ?_⟩
  exact katoMetricPairingSmooth g hU hU

end Work.Diff.GE
