import Mathlib
import Submission.Work.WilE10.Psi

namespace Work.WilE10.Basic

theorem pos_iff_exists_mul_sq_eq_one {g : ℝ} : 0 < g ↔ ∃ v : ℝ, g * v ^ 2 = 1 := by
  constructor
  · intro hg
    refine ⟨Real.sqrt g⁻¹, ?_⟩
    rw [Real.sq_sqrt (inv_nonneg.mpr hg.le), mul_inv_cancel₀ (ne_of_gt hg)]
  · rintro ⟨v, hv⟩
    have h1 : (0 : ℝ) < g * v ^ 2 := by rw [hv]; norm_num
    have h2 : g * v ^ 2 = v ^ 2 * g := mul_comm _ _
    exact pos_of_mul_pos_right (h2 ▸ h1) (sq_nonneg v)

end Work.WilE10.Basic
