/-
# Library shim for the `d = 2` branch of the differentiable sphere theorem.

Collects the seeded (sorry-free) library modules that the dimension-2 smooth-Reeb development
uses, so that delegated lemmas can simply `import Submission.Work.Diff.Dim2.Lib`.
-/
import Mathlib
import Submission.Diff.ODE
import Submission.Geodesic
import Submission.ChartBounds
import Submission.GSField
import Submission.GSGlobal
import Submission.GSGlobal2
import Submission.GSNoCrit
import Submission.GSChartBall
import Submission.GSDisk
import Submission.GSStep1
import Submission.Klingenberg
import Submission.GlobalBM
import Submission.HopfRinow
import Submission.EDist
import Submission.InjBall
import Submission.InjRadius
import Submission.LocalInj
import Submission.GExpSmooth
import Submission.MetricScale
import Submission.Roadmap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic

namespace Work.Diff.Dim2

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The chart coordinate of `x` centred at `x₀`.**  This is a chart coordinate map near `x₀`
with `chartCoord x₀ x₀ = 0`, used to build the "polar" structure at the poles. -/
noncomputable def chartCoord (x₀ x : M) : E :=
  extChartAt I x₀ x - extChartAt I x₀ x₀

@[simp] lemma chartCoord_self (x₀ : M) : chartCoord (I := I) x₀ x₀ = 0 := by
  simp [chartCoord]

/-- **The chart-radial vector field**: the section of the tangent bundle whose chart coordinates
(in the chart at `x₀`) are the coordinates of the point itself.  Its flow lines are the "rays"
through `x₀` in the chart, and the flow is `φ ↦ e^t φ` in those coordinates. -/
noncomputable def chartRadial (x₀ : M) : (x : M) → TangentSpace I x :=
  fun x => frameVector (I := I) x₀ x (chartCoord (I := I) x₀ x)

/-- **The chart-ball (cap) of radius `r` around `x₀`**, a subset of the chart source at `x₀`. -/
def cap (x₀ : M) (r : ℝ) : Set M :=
  {x : M | x ∈ (chartAt H x₀).source ∧ ‖chartCoord (I := I) x₀ x‖ ≤ r}

lemma mem_cap_iff {x₀ x : M} {r : ℝ} :
    x ∈ cap (I := I) (H := H) x₀ r ↔ x ∈ (chartAt H x₀).source ∧
      ‖chartCoord (I := I) x₀ x‖ ≤ r := Iff.rfl

/-- **The quarter turn** `J (x, y) = (-y, x)` of the plane `ℝ² = EuclideanSpace ℝ (Fin 2)`.
It is the multiplication by `i` under the identification `(x,y) ↦ x + i y`, and it is the
orientation form used in the statement "a circle map is orientation preserving": the quantity
`⟪J (γ θ), γ' θ⟫` is the angular velocity of a curve `γ`. -/
noncomputable def rot90 (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) (𝕜 := ℝ)).symm ![-(v 1), v 0]

lemma rot90_apply_zero (v : EuclideanSpace ℝ (Fin 2)) : rot90 v 0 = -v 1 := by
  simp [rot90, EuclideanSpace.equiv]

lemma rot90_apply_one (v : EuclideanSpace ℝ (Fin 2)) : rot90 v 1 = v 0 := by
  simp [rot90, EuclideanSpace.equiv]

/-- **The point of the unit circle with angle `t`**, in coordinates. -/
noncomputable def circPt (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) (𝕜 := ℝ)).symm ![Real.cos t, Real.sin t]

lemma circPt_zero (t : ℝ) : circPt t 0 = Real.cos t := by
  simp [circPt, EuclideanSpace.equiv]

lemma circPt_one (t : ℝ) : circPt t 1 = Real.sin t := by
  simp [circPt, EuclideanSpace.equiv]

/-- The inner product of `x` and `y` in `ℝ²`, in coordinates. -/
lemma inner_fin_two (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma inner_rot90_rot90 (u v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (rot90 u) (rot90 v) = inner ℝ u v := by
  rw [inner_fin_two, inner_fin_two, rot90_apply_zero, rot90_apply_one,
    rot90_apply_zero, rot90_apply_one]
  ring

lemma norm_rot90 (v : EuclideanSpace ℝ (Fin 2)) : ‖rot90 v‖ = ‖v‖ := by
  have h : inner ℝ (rot90 v) (rot90 v) = inner ℝ v v := inner_rot90_rot90 v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg v, norm_nonneg (rot90 v)]

lemma norm_circPt (t : ℝ) : ‖circPt t‖ = 1 := by
  have h : inner ℝ (circPt t) (circPt t) = 1 := by
    rw [inner_fin_two, circPt_zero, circPt_one]
    nlinarith [Real.cos_sq_add_sin_sq t]
  have h3 := real_inner_self_eq_norm_sq (circPt t)
  nlinarith [h, h3, norm_nonneg (circPt t)]

end

end Work.Diff.Dim2
