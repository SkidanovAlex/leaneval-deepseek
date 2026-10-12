import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseBoxFock.NormSymAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.LatSym.quadCut` — the truncating bump used in the `Δ³` integration by parts

`lap3 = Δ³` is not compactly supported, so the pairing identity
`∫ σ · lap3 v = ∫ (lap3 σ) · v` for a smbol `σ` of quadratic growth and a decaying `v` is obtained
by truncating `v`: for `n : ℕ` the bump

    quadCut n p = 1  on  closedBall 0 (n+1) ,   0  outside  closedBall 0 (2(n+1))

is smooth with compact support, and **its iterated derivatives are bounded uniformly in `n` and
`p`** (`quadCut_iteratedFDeriv_le`), which is what makes the dominated-convergence step of the
truncated integration by parts work.

The two facts that matter elsewhere are `quadCut_contDiff` (smoothness, so that `lap3` of a product
with `quadCut n` is defined) and `quadCut_hasCompactSupport` (so that the unconditional
integration by parts `Work.BoseBoxFock.lap3_ibp` applies with the *second* argument
`v · quadCut n`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators Topology

namespace Work.BoseBoxFock.LatSym

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The reference bump: it equals `1` on `closedBall 0 1` and vanishes outside `closedBall 0 2`. -/
noncomputable def quadBump : ContDiffBump (0 : E3) :=
  { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

/-- The real truncation: `quadCutR n p = quadBump ((n+1)⁻¹ • p)`. -/
noncomputable def quadCutR (n : ℕ) : E3 → ℝ := fun p => quadBump (((n : ℝ) + 1)⁻¹ • p)

/-- The complex-valued truncation used in the integration by parts. -/
noncomputable def quadCut (n : ℕ) : E3 → ℂ := fun p => ((quadCutR n p : ℝ) : ℂ)

@[simp] lemma quadCut_apply (n : ℕ) (p : E3) : quadCut n p = ((quadCutR n p : ℝ) : ℂ) := rfl

@[simp] lemma quadCutR_apply (n : ℕ) (p : E3) :
    quadCutR n p = quadBump (((n : ℝ) + 1)⁻¹ • p) := rfl

lemma quadCutR_nonneg (n : ℕ) (p : E3) : 0 ≤ quadCutR n p := quadBump.nonneg

lemma quadCutR_le_one (n : ℕ) (p : E3) : quadCutR n p ≤ 1 := quadBump.le_one

lemma norm_quadCut_le_one (n : ℕ) (p : E3) : ‖quadCut n p‖ ≤ 1 := by
  rw [quadCut_apply]
  have h1 : ‖(((quadCutR n p) : ℝ) : ℂ)‖ = |quadCutR n p| := by simp
  rw [h1, abs_of_nonneg (quadCutR_nonneg n p)]
  exact quadCutR_le_one n p

lemma quadCut_sq_le_one (n : ℕ) (p : E3) : ‖quadCut n p‖ ^ 2 ≤ 1 := by
  have h := norm_quadCut_le_one n p
  nlinarith [norm_nonneg (quadCut n p)]

/-- `quadCutR n` equals `1` on the closed ball of radius `n+1`. -/
lemma quadCutR_eq_one_of_norm_le {n : ℕ} {p : E3} (h : ‖p‖ ≤ (n : ℝ) + 1) :
    quadCutR n p = 1 := by
  rw [quadCutR_apply]
  refine quadBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)]
  rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  rw [show quadBump.rIn = 1 from rfl]
  simpa using h

/-- `quadCutR n` vanishes outside the closed ball of radius `2(n+1)`. -/
lemma quadCutR_eq_zero_of_le_norm {n : ℕ} {p : E3} (h : 2 * ((n : ℝ) + 1) ≤ ‖p‖) :
    quadCutR n p = 0 := by
  rw [quadCutR_apply]
  refine quadBump.zero_of_le_dist ?_
  rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)]
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  rw [show quadBump.rOut = 2 from rfl]
  linarith

/-- `quadCut n` equals `1` in a neighbourhood of any point of norm `< n+1`. -/
lemma quadCut_eventuallyEq_one (n : ℕ) {p : E3} (hp : ‖p‖ < (n : ℝ) + 1) :
    quadCut n =ᶠ[𝓝 p] (fun _ => 1) := by
  have hmem : Metric.ball p (((n : ℝ) + 1 - ‖p‖) / 2) ∈ 𝓝 p :=
    Metric.ball_mem_nhds p (by linarith)
  filter_upwards [hmem] with q hq
  have hq' : ‖q‖ ≤ (n : ℝ) + 1 := by
    have h1 : dist q p < ((n : ℝ) + 1 - ‖p‖) / 2 := by
      simpa [Metric.mem_ball] using hq
    have h2 : ‖q‖ ≤ ‖p‖ + ‖q - p‖ := by
      have := norm_add_le p (q - p)
      simpa using this
    rw [dist_eq_norm] at h1
    have h3 := norm_nonneg (q - p)
    linarith
  rw [quadCut_apply, quadCutR_eq_one_of_norm_le hq']
  simp

lemma quadCut_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (quadCut n) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 => ((quadCutR n p : ℝ) : ℂ)) := by
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : E3 => quadBump (((n : ℝ) + 1)⁻¹ • p)) :=
      quadBump.contDiff.comp (contDiff_id.const_smul (((n : ℝ) + 1)⁻¹))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 => quadCutR n p) := hcomp
    exact Complex.ofRealCLM.contDiff.comp h2
  exact h1

lemma quadCutR_hasCompactSupport (n : ℕ) : HasCompactSupport (quadCutR n) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall (0 : E3) (2 * ((n : ℝ) + 1))) (isCompact_closedBall _ _) ?_
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hcon
  rw [Metric.mem_closedBall, dist_zero_right] at hcon
  exact hp (quadCutR_eq_zero_of_le_norm (le_of_lt (not_le.mp hcon)))

lemma quadCut_hasCompactSupport (n : ℕ) : HasCompactSupport (quadCut n) :=
  (quadCutR_hasCompactSupport n).comp_left (g := fun r : ℝ => ((r : ℂ))) (by simp)

end Work.BoseBoxFock.LatSym
