import Mathlib
import Submission.Work.Resample.auDefs

namespace Work.Resample

/-- In the non-guard branch the fixed-point exponent `auZ` (encoded by `Z`) exceeds the guard
`(p+10)·2^{auPrec p}`, which by the approximation hypothesis forces the true exponent `u` to be
`≥ p+9`.  Since `exp` beats `2^x`, this gives the required decay `exp(-u) ≤ 4/2^p`. -/
theorem notGuardBound (p : ℕ) (hp : 100 ≤ p) (Z : ℤ) (u : ℝ) (hZ0 : 0 ≤ Z) (hu0 : 0 ≤ u)
    (hZu : |(Z : ℝ) - (2 : ℝ) ^ Work.Resample.auPrec p * u| ≤ 1 + u / 3)
    (hguard : ((p : ℝ) + 10) * (2 : ℝ) ^ Work.Resample.auPrec p < (Z : ℝ)) :
    Real.exp (-u) ≤ 4 / (2 : ℝ) ^ p := by
  set A : ℝ := (2:ℝ)^(Work.Resample.auPrec p) with hA
  have hApos : (0:ℝ) < A := by rw [hA]; positivity
  -- `(p:ℝ)+10 ≤ A`
  have hnat : p + 10 ≤ 2 ^ (Work.Resample.auPrec p) := by
    have h1 : p + 9 < 2 ^ (p+9) := Nat.lt_two_pow_self
    have h2 : 2 ^ (p+9) ≤ 2 ^ (Work.Resample.auPrec p) := by
      apply Nat.pow_le_pow_right (by norm_num)
      simp only [Work.Resample.auPrec]; omega
    omega
  have hcast : ((p+10 : ℕ) : ℝ) ≤ A := by
    rw [hA]
    have := hnat
    exact_mod_cast this
  have hAB : ((p:ℝ) + 10) ≤ A := by
    have hcp : (p:ℝ) + 10 = ((p+10:ℕ):ℝ) := by push_cast; ring
    linarith [hcast, hcp]
  have h3A : ((p:ℝ) + 12) ≤ 3 * A := by
    have hp0 : (0:ℝ) ≤ p := by positivity
    linarith [hAB, hp0]
  -- from the approximation and the guard: `u * (3A + 1) > 3(p+10)A - 3`
  have hstep1 : 3 * (((p:ℝ)+10) * A) - 3 < u * (3 * A + 1) := by
    have hzu_lower : (Z:ℝ) - A*u ≤ 1 + u/3 := (abs_le.mp hZu).2
    have h1 : 3 * ((Z:ℝ) - A*u) ≤ 3 * (1 + u/3) := by linarith
    have h2 : 3 * (((p:ℝ)+10) * A) < 3 * (Z:ℝ) := by linarith [hguard]
    linarith [h1, h2]
  have hstep2 : ((p:ℝ)+9) * (3 * A + 1) ≤ 3 * (((p:ℝ)+10) * A) - 3 := by
    linarith [h3A]
  have hpos : (0:ℝ) ≤ 3 * A + 1 := by linarith [hApos]
  have hu : (p:ℝ) + 9 < u := by
    have hlt : ((p:ℝ)+9) * (3 * A + 1) < u * (3 * A + 1) := lt_of_le_of_lt hstep2 hstep1
    exact lt_of_mul_lt_mul_right hlt hpos
  have hu' : (((p+9:ℕ):ℝ)) < u := by
    have hcp : ((p+9:ℕ):ℝ) = (p:ℝ)+9 := by push_cast; ring
    linarith [hu, hcp]
  have hexp_le : Real.exp (-u) ≤ Real.exp (-(((p+9:ℕ):ℝ))) := Real.exp_le_exp.mpr (by linarith [hu'])
  -- `exp(-(p+9)) ≤ 4/2^p`
  have hfinal : Real.exp (-(((p+9:ℕ):ℝ))) ≤ 4 / (2:ℝ)^p := by
    rw [Real.exp_neg]
    have hexpn : Real.exp (((p+9:ℕ):ℝ)) = Real.exp 1 ^ (p+9) := by
      have := Real.exp_nat_mul 1 (p+9)
      rw [mul_one] at this
      exact this
    have hge : (2:ℝ)^(p+9) ≤ Real.exp 1 ^ (p+9) :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_two) (p+9)
    have hle1 : (Real.exp (((p+9:ℕ):ℝ)))⁻¹ ≤ ((2:ℝ)^(p+9))⁻¹ := by
      rw [hexpn, ← one_div, ← one_div]
      apply one_div_le_one_div_of_le (by positivity)
      exact hge
    have hle2 : ((2:ℝ)^(p+9))⁻¹ ≤ 4 / (2:ℝ)^p := by
      rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (2:ℝ)^p ≤ (2:ℝ)^(p+11) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (2:ℝ)^(p+11) = 4 * (2:ℝ)^(p+9) := by
        rw [show p+11 = 2 + (p+9) by omega, pow_add]; norm_num
      linarith [h1, h2]
    linarith [hle1, hle2]
  linarith [hexp_le, hfinal]

end Work.Resample
