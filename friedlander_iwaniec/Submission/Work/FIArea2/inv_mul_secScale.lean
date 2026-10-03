import Mathlib
import Submission.Work.FIArea2.CCountPoissonDefs

namespace Work.FIArea2

/-- `gnorm` is multiplicative (`z ↦ |z|²` is the norm of the Gaussian ring). -/
lemma gnorm_mul_aux (z1 z2 : GaussianInt) :
    Work.FIPlan.gnorm (z1 * z2) = Work.FIPlan.gnorm z1 * Work.FIPlan.gnorm z2 := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- The elementary real identity behind `inv_mul_secScale`:
`(1/d)·(√(d/√g₂)·√(d/√g₁)) = (g₁g₂)^{-1/4}` for positive `d,g₁,g₂`. -/
lemma inv_mul_secScale_aux (d g1 g2 : ℝ) (hd : 0 < d) (hg1 : 0 < g1) (hg2 : 0 < g2) :
    (1 / d) * (Real.sqrt (d / Real.sqrt g2) * Real.sqrt (d / Real.sqrt g1))
      = (g1 * g2) ^ (-(1 : ℝ) / 4) := by
  have hg1nn : 0 ≤ g1 := le_of_lt hg1
  have hg2nn : 0 ≤ g2 := le_of_lt hg2
  have hs2 : Real.sqrt (d / Real.sqrt g2) = d ^ (1 / 2 : ℝ) / g2 ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show Real.sqrt g2 = g2 ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow g2]
    rw [Real.div_rpow (le_of_lt hd) (Real.rpow_nonneg hg2nn _)]
    have hmul : (g2 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = g2 ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_mul hg2nn (1 / 2 : ℝ) (1 / 2 : ℝ)]; norm_num
    rw [hmul]
  have hs1 : Real.sqrt (d / Real.sqrt g1) = d ^ (1 / 2 : ℝ) / g1 ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show Real.sqrt g1 = g1 ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow g1]
    rw [Real.div_rpow (le_of_lt hd) (Real.rpow_nonneg hg1nn _)]
    have hmul : (g1 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = g1 ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_mul hg1nn (1 / 2 : ℝ) (1 / 2 : ℝ)]; norm_num
    rw [hmul]
  rw [hs2, hs1]
  rw [show d ^ (1 / 2 : ℝ) / g2 ^ (1 / 4 : ℝ) * (d ^ (1 / 2 : ℝ) / g1 ^ (1 / 4 : ℝ))
        = (d ^ (1 / 2 : ℝ) * d ^ (1 / 2 : ℝ)) / (g2 ^ (1 / 4 : ℝ) * g1 ^ (1 / 4 : ℝ))
        by ring]
  rw [← Real.rpow_add hd (1 / 2 : ℝ) (1 / 2 : ℝ),
    show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]
  rw [mul_comm (g2 ^ (1 / 4 : ℝ)) (g1 ^ (1 / 4 : ℝ)), ← Real.mul_rpow hg1nn hg2nn]
  have hG : 0 < g1 * g2 := mul_pos hg1 hg2
  rw [show (-(1 : ℝ)) / 4 = -(1 / 4 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hG)]
  have hX : (g1 * g2) ^ (1 / 4 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hG _)
  field_simp

theorem inv_mul_secScale (z1 z2 : GaussianInt) (hm : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    (1 / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
        * (Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2)
      = (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ^ (-(1 : ℝ) / 4) := by
  have hd : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hm
  have hz1 : z1 ≠ 0 := fun h =>
    hm (by simp [Work.FIPlan.absDelta, Work.FIPlan.Delta, h])
  have hz2 : z2 ≠ 0 := fun h =>
    hm (by simp [Work.FIPlan.absDelta, Work.FIPlan.Delta, h])
  have hg1 : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_of_ne_zero hz1
  have hg2 : (0 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_of_ne_zero hz2
  have hG : ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
      = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    rw [gnorm_mul_aux, Nat.cast_mul]
  rw [hG, secScale₁, secScale₂]
  exact inv_mul_secScale_aux _ _ _ hd hg1 hg2

end Work.FIArea2
