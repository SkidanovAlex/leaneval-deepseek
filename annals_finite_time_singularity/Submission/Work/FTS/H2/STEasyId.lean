import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.H2.STEasyDefs
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 8000000





/-! ## Nonnegativity and the AM-GM read-off -/

theorem w_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem Whz_nonneg_prv {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Whz z θ := by
  rw [Whz_eq]
  exact div_nonneg (w_nonneg hz) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)

private theorem Wm_nonneg_prv (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wm α z θ := by
  rw [Wm_eq, Work.Spaces.Wt, Work.Spaces.wTheta]
  exact mul_nonneg (w_nonneg hz) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)

theorem rpow_eta_le_gam {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hS1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam]
    have := Work.Spaces.eta_lt_one
    linarith
  rcases eq_or_lt_of_le hS with h0 | h0
  · rw [← h0,
      Real.zero_rpow (show (-Work.Spaces.eta) ≠ 0 by linarith [Work.Spaces.eta_pos]),
      Real.zero_rpow (show (-(Work.Spaces.gam α)) ≠ 0 by
        have := Work.Spaces.gam_pos hα; linarith)]
  · rw [show -Work.Spaces.eta = -(Work.Spaces.gam α) + (Work.Spaces.gam α - Work.Spaces.eta)
        by ring, Real.rpow_add h0]
    have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta) ≤ 1 :=
      Real.rpow_le_one hS hS1 (by linarith)
    have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hS _
    calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta)
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by ring



theorem choose_le_six (m b : ℕ) (hm : m ≤ 4) (hb : b ≤ m) : (m.choose b : ℝ) ≤ 6 := by
  have h : m.choose b ≤ 6 := by interval_cases m <;> interval_cases b <;> decide
  exact_mod_cast h

end Work.FTS.H2
