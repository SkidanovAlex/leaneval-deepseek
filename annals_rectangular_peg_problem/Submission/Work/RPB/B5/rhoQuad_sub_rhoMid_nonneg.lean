import Mathlib
import Submission.Work.RPB.B5.RhoPerDefs

namespace Work.RPB.B5

/-- `rhoQuad` rewritten under the substitution `t = x + √2`: `rhoQuad x = π²/8 · t²`. -/
theorem rhoQuad_eq_pi8 (x : ℝ) :
    rhoQuad x = Real.pi ^ 2 / 8 * (x + Real.sqrt 2) ^ 2 := by
  unfold rhoQuad
  have h1 : 1 + x / Real.sqrt 2 = (x + Real.sqrt 2) / Real.sqrt 2 := by
    field_simp
    ring
  rw [h1, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- `rhoMid` rewritten under the substitution `t = x + √2`: `rhoMid x = π²/32 · (1 + t)`. -/
theorem rhoMid_eq_pi32 (x : ℝ) :
    rhoMid x = Real.pi ^ 2 / 32 * (1 + (x + Real.sqrt 2)) := by
  unfold rhoMid
  ring

/-- Key numerical step: if `4 u₂² ≥ 1 + u₂`, `u₂ > 0` and `u₂ < t`, then `4 t² - t - 1 ≥ 0`.
Indeed `4 u₂² ≥ 1 + u₂` with `u₂ > 0` forces `u₂ > 1/2` (otherwise `4 u₂² ≤ 1 < 1 + u₂`),
so `4(t + u₂) - 1 > 0`; and `t > u₂` gives the factorization
`4 t² - t - 1 = (4 u₂² - u₂ - 1) + (t - u₂)(4(t + u₂) - 1)`. -/
theorem quad_sub_nonneg {u₂ t : ℝ} (hu : 4 * u₂ ^ 2 ≥ 1 + u₂) (hu0 : 0 < u₂)
    (hx : u₂ < t) : 0 ≤ 4 * t ^ 2 - t - 1 := by
  have h2 : 1 / 2 < u₂ := by nlinarith [sq_nonneg u₂]
  have hfac : 4 * t ^ 2 - t - 1 = (4 * u₂ ^ 2 - u₂ - 1) + (t - u₂) * (4 * (t + u₂) - 1) := by
    ring
  nlinarith [hfac, hu, hx, h2]

theorem rhoQuad_sub_rhoMid_nonneg {u₂ x : ℝ} (hu : 4 * u₂ ^ 2 ≥ 1 + u₂) (hu0 : 0 < u₂)
    (hx : u₂ < x + Real.sqrt 2) : 0 ≤ rhoQuad x - rhoMid x := by
  have hkey : 0 ≤ 4 * (x + Real.sqrt 2) ^ 2 - (x + Real.sqrt 2) - 1 :=
    quad_sub_nonneg hu hu0 hx
  have hpi : (0 : ℝ) < Real.pi ^ 2 / 32 := by positivity
  rw [rhoQuad_eq_pi8, rhoMid_eq_pi32]
  nlinarith [hkey, hpi]

end Work.RPB.B5
