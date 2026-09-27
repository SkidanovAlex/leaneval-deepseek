import Submission.UnifDeps
import Submission.Balayage
import Submission.TwoConstants
import Submission.GreenFunction
import Submission.HarmonicX

/-!
# The Green function of a Riemann surface, via the hitting probability

For a point `z₀` of a Riemann surface `X` and a radius `ρ₂ > 0`, the *normalised hitting probability*
is `greenPsi z₀ ρ₂ ρ = log (ρ₂/ρ) · h_ρ`, and the Green function is expected to be its supremum over
`ρ ∈ (0, ρ₂)`, equivalently the limit along the sequence `greenApprox z₀ ρ₂ n = log (n+1) ·
h_{ρ₂/(n+1)}` of *Green approximations*.  This module records the definitions together with the
elementary properties that are available unconditionally:

* non-negativity of the approximations;
* harmonicity of each approximation away from the closed chart disc of its own radius;
* the two-constants *lower* bound: on the chart ball, `log (ρ₂ / ‖c x - c z₀‖) ≤ greenPsi z₀ ρ₂ ρ x`.

The two remaining steps (see `Submission/ROADMAP.md`, SESSION 13) are (i) monotonicity in `ρ`
(equivalently in `n`), which is what turns the limit into a Harnack limit, and (ii) the dichotomy
finite (hyperbolic) / identically `+∞` (parabolic).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section Green

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The normalised hitting probability -/

/-- The normalised hitting probability `log (ρ₂/ρ) · h_ρ`. -/
def greenPsi (z₀ : X) (ρ₂ ρ : ℝ) : X → ℝ :=
  fun x => Real.log (ρ₂ / ρ) *
    hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x

theorem greenPsi_apply (z₀ : X) (ρ₂ ρ : ℝ) (x : X) :
    greenPsi z₀ ρ₂ ρ x = Real.log (ρ₂ / ρ) *
      hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x :=
  rfl

/-! ## The Green approximations -/

/-- The `n`-th approximation of the Green function with pole `z₀`. -/
def greenApprox (z₀ : X) (ρ₂ : ℝ) (n : ℕ) : X → ℝ :=
  greenPsi z₀ ρ₂ (ρ₂ / ((n : ℝ) + 1))

/-- Unfolding of `greenApprox` in terms of the hitting probability. -/
theorem greenApprox_apply (z₀ : X) {ρ₂ : ℝ} (hρ₂ : 0 < ρ₂) (n : ℕ) (x : X) :
    greenApprox z₀ ρ₂ n x =
      Real.log ((n : ℝ) + 1) *
        hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) (ρ₂ / ((n : ℝ) + 1)) x := by
  rw [greenApprox, greenPsi_apply]
  have hdiv : ρ₂ / (ρ₂ / ((n : ℝ) + 1)) = (n : ℝ) + 1 := by
    field_simp
  rw [hdiv]

theorem greenApprox_nonneg (z₀ : X) {ρ₂ : ℝ} (hρ₂ : 0 < ρ₂) (n : ℕ) (x : X) :
    0 ≤ greenApprox z₀ ρ₂ n x := by
  rw [greenApprox_apply z₀ hρ₂]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) (ρ₂ / ((n : ℝ) + 1)) x :=
    hittingProbability_nonneg (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) (ρ₂ / ((n : ℝ) + 1)) x
  exact mul_nonneg h1 h2

/-- Each Green approximation is harmonic off the closed chart disc of its own radius. -/
theorem greenApprox_harmonic (z₀ : X) {ρ₂ : ℝ} (hρ₂ : 0 < ρ₂) (n : ℕ)
    (hsub : Metric.closedBall (chartAt ℂ z₀ z₀) (ρ₂ / ((n : ℝ) + 1)) ⊆ (chartAt ℂ z₀).target) :
    HarmonicOnX (greenApprox z₀ ρ₂ n)
      ((chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) (ρ₂ / ((n : ℝ) + 1)))ᶜ) := by
  rw [greenApprox]
  exact (harmonicOnX_hittingProbability (ρ := ρ₂ / ((n : ℝ) + 1)) (by positivity) hsub).const_smul _

/-- **The normalised hitting probability dominates the Green kernel** on the chart ball: this is the
two-constants estimate, in the normalisation used for the Green function. -/
theorem greenPsi_lower_bound {z₀ : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hρρ₂ : ρ < ρ₂)
    (hsub : Metric.closedBall (chartAt ℂ z₀ z₀) ρ₂ ⊆ (chartAt ℂ z₀).target)
    {x : X} (hx : x ∈ chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂)
    (hx' : x ∉ chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ) :
    Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) ≤ greenPsi z₀ ρ₂ ρ x := by
  have hlog_nonneg : 0 ≤ -Real.log ρ := by
    rw [neg_nonneg, ← Real.log_one]
    exact Real.log_le_log hρ hρ₁
  have hmain := hittingProbability_ge_log_ratio (z₀ := z₀) hρ hρρ₂ hsub x hx hx'
  have hden : 0 < Real.log (ρ₂ / ρ) := Real.log_pos (by rw [one_lt_div hρ]; exact hρρ₂)
  rw [greenPsi_apply]
  -- `log(ρ₂/ρ) · (log(ρ₂/ρ))⁻¹ = 1`
  have hrewrite : Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) ≤
      Real.log (ρ₂ / ρ) * hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x := by
    have h := mul_le_mul_of_nonneg_left hmain hden.le
    have hsimp : Real.log (ρ₂ / ρ) *
        (Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) / Real.log (ρ₂ / ρ)) =
        Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) := by
      field_simp
    rwa [hsimp] at h
  exact hrewrite

end Green

end Submission
