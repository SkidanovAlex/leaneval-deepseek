import Mathlib

namespace Work.LinnikAreas.Density4

/-- `L³ e^{-uL} ≤ 6/u³` for `0 < u`, `0 ≤ L` (from `e^{uL} ≥ (uL)³/6`). -/
theorem cube_mul_exp_neg_le {u L : ℝ} (hu : 0 < u) (hL : 0 ≤ L) :
    L^3 * Real.exp (-(u*L)) ≤ 6/u^3 := by
  have hu3 : (0:ℝ) < u^3 := pow_pos hu 3
  rw [le_div_iff₀ hu3]
  have hx : 0 ≤ u * L := mul_nonneg hu.le hL
  have h3 : (u*L)^3 / 6 ≤ Real.exp (u*L) := by
    have h := Real.pow_div_factorial_le_exp (u*L) hx 3
    norm_num at h
    exact h
  have hE : 0 ≤ Real.exp (-(u*L)) := (Real.exp_pos _).le
  have h4 : (u*L)^3 / 6 * Real.exp (-(u*L)) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right h3 hE
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  have h5 : (u*L)^3 * Real.exp (-(u*L)) ≤ 6 := by
    nlinarith [h4]
  calc (L^3 * Real.exp (-(u*L))) * u^3
      = (u*L)^3 * Real.exp (-(u*L)) := by ring
    _ ≤ 6 := h5

end Work.LinnikAreas.Density4
