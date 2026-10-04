/-
# Layer C2: the within-`J` metric compatibility along a curve

The sealed library's `Submission.Variation.hasDerivAt_inner_sections` gives the product rule along a
curve for the metric pairing of two globally smooth sections, with a *two-sided* hypothesis on the
curve.  The DeTurck pull-back computation only has a **within-`J`** differentiability of the curve
(`hvel`), so we record here the within-`J` form.

The proof is the within-`J` chain rule `Work.Diff.STE.C2.hasDerivWithinAt_comp_curve` combined with
the pointwise metric compatibility `IsMetricCompatible`.
-/

import Mathlib
import Submission.Variation
import Submission.Work.Diff.STE.C2.hasDerivWithinAt_comp_curve

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.C2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- **Metric compatibility along a curve, within-`J` form.**  For globally smooth sections `Y`, `Z`
and a curve `γ` whose within-`J` velocity at `t` is `v`, the function `s ↦ ⟪Y (γ s), Z (γ s)⟫` has
within-`J` derivative `⟪∇_v Y, Z⟫ + ⟪Y, ∇_v Z⟫` at `t`. -/
theorem hasDerivWithinAt_inner_sections
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {Y Z : Π x : M, TangentSpace I x}
    (hY : ContMDiff I I.tangent ∞ (fun y : M ↦ (⟨y, Y y⟩ : TangentBundle I M)))
    (hZ : ContMDiff I I.tangent ∞ (fun y : M ↦ (⟨y, Z y⟩ : TangentBundle I M)))
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} {v : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    HasDerivWithinAt (fun s : ℝ ↦ inner ℝ (Y (γ s)) (Z (γ s)))
      (inner ℝ (cov Y (γ t) v) (Z (γ t)) + inner ℝ (Y (γ t)) (cov Z (γ t) v)) J t := by
  have hinner : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y : M ↦ inner ℝ (Y y) (Z y)) (γ t) :=
    Submission.Variation.mdifferentiableAt_inner_sections hY hZ (γ t)
  have h := Work.Diff.STE.C2.hasDerivWithinAt_comp_curve (I := I) (M := M) (F := ℝ)
    (ψ := fun y : M ↦ inner ℝ (Y y) (Z y)) hγ hinner
  rwa [hmet Y Z hY hZ (γ t) v] at h

end Work.Diff.STE.C2
