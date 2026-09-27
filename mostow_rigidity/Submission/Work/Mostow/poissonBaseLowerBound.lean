import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.BaryBase

/-!
# Lower bound for the Poisson kernel base

For `x` in the ball of radius `R ≥ 0` and `ξ` on the unit sphere one has
`(1 + 2R)⁻¹ ≤ tpart x - ⟪x, ξ⟫`.  This is the elementary estimate that makes the
Poisson kernel `(tpart x - ⟪x,ξ⟫)^{-(n-1)}` uniformly bounded on bounded sets from above.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem poissonBaseLowerBound {n : ℕ} {R : ℝ} (hR : 0 ≤ R) {ξ : Submission.Mostow.E n}
    (hξ : ξ ∈ Submission.Mostow.Sph n) {x : Submission.Mostow.E n} (hx : ‖x‖ ≤ R) :
    (1 + 2 * R)⁻¹ ≤ Submission.Mostow.tpart x - inner ℝ x ξ := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have hinner : inner ℝ x ξ ≤ ‖x‖ := by
    have h := real_inner_le_norm x ξ
    rwa [hξn, mul_one] at h
  -- `tpart x - ‖x‖ = (tpart x + ‖x‖)⁻¹`
  have hkey : tpart x - ‖x‖ = (tpart x + ‖x‖)⁻¹ := by
    rw [inv_eq_one_div, eq_div_iff (ne_of_gt (tpart_add_norm_pos x)), mul_comm]
    exact tpart_add_norm_mul_tpart_sub_norm x
  -- the elementary bound `tpart x ≤ 1 + R`
  have hx2 : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x, hx]
  have hsqrt : tpart x ≤ 1 + R := by
    rw [tpart, show (1 : ℝ) + ‖x‖ ^ 2 = 1 + ‖x‖ ^ 2 from rfl]
    calc √(1 + ‖x‖ ^ 2) ≤ √((1 + R) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hx2, hR])
      _ = 1 + R := Real.sqrt_sq (by linarith)
  have hsum : tpart x + ‖x‖ ≤ 1 + 2 * R := by linarith
  have hstep : (1 + 2 * R)⁻¹ ≤ (tpart x + ‖x‖)⁻¹ := by
    rw [inv_le_inv₀ (by linarith) (tpart_add_norm_pos x)]
    exact hsum
  calc (1 + 2 * R)⁻¹ ≤ (tpart x + ‖x‖)⁻¹ := hstep
    _ = tpart x - ‖x‖ := hkey.symm
    _ ≤ tpart x - inner ℝ x ξ := by linarith

end Work.Mostow
