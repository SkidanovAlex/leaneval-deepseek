import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_one_add_add_bound_curve
import Submission.Commons.NumberTheory.Zeta.zeta_region_inv_analytic_bound_ne
import Submission.Commons.Analysis.Complex.contour_shift_residue
import Submission.Commons.NumberTheory.Zeta.gam0_Rz_div_sq_integral_le

open MeasureTheory

namespace Commons.NumberTheory.Zeta

/-- Elementary fact: for a nonnegative `B` and a complex number `I` that vanishes
when `B = 0`, there is a positive constant `C` with `‖I‖ ≤ C * B`. -/
private lemma exists_bound_of_zero_case {B : ℝ} (hB0 : 0 ≤ B) {I : ℂ}
    (hzero : B = 0 → I = 0) : ∃ C : ℝ, 0 < C ∧ ‖I‖ ≤ C * B := by
  rcases eq_or_lt_of_le hB0 with hBz | hBpos
  · subst hBz
    exact ⟨1, one_pos, by rw [hzero rfl, norm_zero, mul_zero]⟩
  · refine ⟨‖I‖ / B + 1, by positivity, ?_⟩
    rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hBpos)]
    linarith [norm_nonneg I]

theorem gam0_sq_GTG_integral_le {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ C₂ : ℝ) (hC1 : 0 < C₁) (hC2 : 0 < C₂)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hznum0 : ∀ t t' : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t
        + Commons.Analysis.Complex.gam β t')‖ ≤ C₂ * (|t| + |t'| + 3) ^ 4)
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ‖∫ t : ℝ, ∫ t' : ℝ, f (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
        * (riemannZeta (1 + Commons.Analysis.Complex.gam β t + Commons.Analysis.Complex.gam β t')
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                * riemannZeta (1 + Commons.Analysis.Complex.gam β t')))
        * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t + Commons.Analysis.Complex.gam β t')
        / ((Commons.Analysis.Complex.gam β t) ^ 2 * (Commons.Analysis.Complex.gam β t') ^ 2)
        * Commons.Analysis.Complex.gamDot β t * Commons.Analysis.Complex.gamDot β t'‖ ≤ C * B := by
  refine exists_bound_of_zero_case ?_ ?_
  · -- `B ≥ 0`: apply the bound `‖f z z'‖ ≤ B` at any point of the curve.
    have h := hbound (Commons.Analysis.Complex.gam β 0) (Commons.Analysis.Complex.gam β 0)
      (gam_mem_region hβ 0).1 (gam_mem_region hβ 0).2
      (gam_mem_region hβ 0).1 (gam_mem_region hβ 0).2
    linarith [norm_nonneg (f (Commons.Analysis.Complex.gam β 0)
      (Commons.Analysis.Complex.gam β 0))]
  · -- If `B = 0` then `f` vanishes on the curve, so the integrand — and hence the
    -- double integral — is `0`.
    intro hBz
    subst hBz
    have hzero : ∀ t t' : ℝ, f (Commons.Analysis.Complex.gam β t)
        (Commons.Analysis.Complex.gam β t') = 0 := by
      intro t t'
      exact norm_le_zero_iff.mp (hbound (Commons.Analysis.Complex.gam β t)
        (Commons.Analysis.Complex.gam β t') (gam_mem_region hβ t).1 (gam_mem_region hβ t).2
        (gam_mem_region hβ t').1 (gam_mem_region hβ t').2)
    simp [hzero]

end Commons.NumberTheory.Zeta
