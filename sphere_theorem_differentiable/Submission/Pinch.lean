import Submission.CurvatureVec
import Submission.ChartConnection
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pinching bound on the curvature in coordinates

`QuarterPinched cov` says that every sectional curvature lies in `(1, 4]`.  Here we record the
consequence used in Bonnet–Myers and in Klingenberg's estimate: for an **orthonormal pair**
`a, b` of coordinate vectors (orthonormal for the chart metric `chartGram x₀ p`),

`1 ≤ ⟪σ_a, R(σ_a, σ_b)σ_b⟫`   (`σ_a = frameVector x₀ p a`),

i.e. the sectional curvature of the plane spanned by `a` and `b` is at least `1`.  The proof
extends `σ_a` and `σ_b` to globally smooth sections (the values at `p` are what matters), applies
`quarterPinched_curvForm_unit`, and translates back with `curvFormVec_eq` / `inner_curvVec_self`.
-/

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Curvature
open Submission.CurvatureVec
open Commons.Geometry.Manifold.VectorField
open Commons.Geometry.Manifold.Tangent

set_option linter.unusedSectionVars false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.Pinch

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **The pinching bound in coordinates** (strict form).  If `σ_a = frameVector x₀ p a` and
`σ_b = frameVector x₀ p b` are orthonormal at `p`, then the sectional curvature of the plane they
span is strictly bigger than `1`, i.e. `⟪σ_a, R(σ_a,σ_b)σ_b⟫ > 1`. -/
theorem one_lt_inner_curvVec
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) {x₀ p : M} {a b : E}
    (ha : inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p a) = 1)
    (hb : inner ℝ (frameVector (I := I) x₀ p b) (frameVector (I := I) x₀ p b) = 1)
    (hab : inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b) = 0) :
    (1 : ℝ) < inner ℝ (frameVector (I := I) x₀ p a)
      (curvVec cov p (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b)
        (frameVector (I := I) x₀ p b)) := by
  obtain ⟨X, hX, hXp⟩ :=
    exists_contMDiff_section_apply_eq (I := I) (M := M) (frameVector (I := I) x₀ p a)
  obtain ⟨Y, hY, hYp⟩ :=
    exists_contMDiff_section_apply_eq (I := I) (M := M) (frameVector (I := I) x₀ p b)
  have h1 : ‖X p‖ = 1 := by
    have hsq : ‖X p‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hXp]
      exact ha
    nlinarith [norm_nonneg (X p)]
  have h2 : ‖Y p‖ = 1 := by
    have hsq : ‖Y p‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hYp]
      exact hb
    nlinarith [norm_nonneg (Y p)]
  have h3 : inner ℝ (X p) (Y p) = 0 := by
    rw [hXp, hYp]
    exact hab
  have hpin := (quarterPinched_curvForm_unit cov hcov hmet hpinch hX hY h1 h2 h3).1
  rw [← curvFormVec_eq cov hcov hX hY hXp hYp] at hpin
  rw [← inner_curvVec_self cov hcov p (frameVector (I := I) x₀ p a)
    (frameVector (I := I) x₀ p b)] at hpin
  rw [real_inner_comm] at hpin
  linarith

/-- **The pinching bound in coordinates** (non-strict form), a corollary of the strict one. -/
theorem one_le_inner_curvVec
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) {x₀ p : M} {a b : E}
    (ha : inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p a) = 1)
    (hb : inner ℝ (frameVector (I := I) x₀ p b) (frameVector (I := I) x₀ p b) = 1)
    (hab : inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b) = 0) :
    (1 : ℝ) ≤ inner ℝ (frameVector (I := I) x₀ p a)
      (curvVec cov p (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b)
        (frameVector (I := I) x₀ p b)) :=
  (one_lt_inner_curvVec (cov := cov) hcov hmet hpinch ha hb hab).le

/-- The pinching bound with the hypotheses and conclusion phrased through the chart metric. -/
theorem one_le_chartGram_curvVec
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) {x₀ p : M} {a b : E}
    (ha : chartGram (I := I) x₀ p a a = 1) (hb : chartGram (I := I) x₀ p b b = 1)
    (hab : chartGram (I := I) x₀ p a b = 0) :
    (1 : ℝ) ≤ inner ℝ (frameVector (I := I) x₀ p a)
      (curvVec cov p (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b)
        (frameVector (I := I) x₀ p b)) :=
  one_le_inner_curvVec (cov := cov) hcov hmet hpinch ha hb hab

end

end Submission.Pinch
