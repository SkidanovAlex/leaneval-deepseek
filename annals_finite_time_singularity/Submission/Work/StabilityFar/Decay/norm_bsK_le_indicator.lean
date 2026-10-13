import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.StabilityFar.Defs
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

/-- Pointwise bound on the Biot–Savart integrand: if `‖ω‖ ≤ C` and `ω` is supported in
`closedBall 0 R`, then the integrand `bsK ω x y` is bounded by the `closedBall 0 R`-indicator
of `C * ‖x - y‖⁻²`. -/
theorem norm_bsK_le_indicator {ω : Work.StabilityFar.R3 → Work.StabilityFar.R3} {R C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ y, ‖ω y‖ ≤ C)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) (x y : Work.StabilityFar.R3) :
    ‖Work.LWP.BiotSavart.bsK ω x y‖ ≤
      (Metric.closedBall (0 : Work.StabilityFar.R3) R).indicator
        (fun y => C * ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by
  by_cases h0 : ω y = 0
  · rw [Work.LWP.BiotSavart.bsK_eq_zero h0, norm_zero]
    exact Set.indicator_nonneg (fun z _ => mul_nonneg hC (inv_nonneg.mpr (by positivity))) y
  · have hyR : y ∈ Metric.closedBall (0 : Work.StabilityFar.R3) R := hsupp y h0
    rw [Set.indicator_of_mem hyR]
    have h1 := Work.LWP.BiotSavart.norm_bsK_le ω x y
    have hkey : (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖ = (‖x - y‖ ^ (2 : ℕ))⁻¹ := by
      rcases eq_or_ne ‖x - y‖ 0 with h | h
      · rw [h]; simp
      · have h3 : (‖x - y‖) ^ (3 : ℕ) = ‖x - y‖ ^ (2 : ℕ) * ‖x - y‖ := by ring
        rw [h3, mul_inv, mul_assoc, inv_mul_cancel₀ h, mul_one]
    calc ‖Work.LWP.BiotSavart.bsK ω x y‖
        ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖ω y‖ * ‖x - y‖ := h1
      _ ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * C * ‖x - y‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left (hb y) (inv_nonneg.mpr (by positivity))
      _ = C * (‖x - y‖ ^ (2 : ℕ))⁻¹ := by
            rw [show (‖x - y‖ ^ (3 : ℕ))⁻¹ * C * ‖x - y‖
                  = C * ((‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖) by ring, hkey]

end Work.StabilityFar.Decay
