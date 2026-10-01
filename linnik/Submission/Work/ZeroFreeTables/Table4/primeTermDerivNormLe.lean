import Mathlib
import Submission.Work.ZeroFreeTables.Table4.eulerDerivs

/-!
# ZeroFreeTables/Table4/primeTermDerivNormLe

`‖d/dz (log p / (p^z - 1))‖ ≤ 4 (log p)^2 / p` for a prime `p` and `Re z ≥ 1` — the
pointwise bound on the first `z`-derivative of an Euler factor behind HB Table 4.
-/

namespace Work.ZeroFreeTables.Table4

theorem primeTermDerivNormLe (p : ℕ) (hp : p.Prime) (z : ℂ) (hz : 1 ≤ z.re) :
    ‖deriv (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)) z‖
      ≤ 4 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hpt : (p : ℝ) ≤ (p : ℝ) ^ z.re := by
    have h1 : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ z.re :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hz
    rwa [Real.rpow_one] at h1
  have ht2 : (2 : ℝ) ≤ (p : ℝ) ^ z.re := le_trans hp2 hpt
  have hne : (p : ℂ) ^ z - 1 ≠ 0 := by
    intro h
    have h1 : ‖(p : ℂ) ^ z‖ = 1 := by rw [sub_eq_zero.mp h]; simp
    rw [cpow_norm_eq' p hp.pos z] at h1
    linarith
  -- the norm of the explicit derivative
  have hnorm : ‖eulerD1' p z‖
      = (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ z.re / ‖(p : ℂ) ^ z - 1‖ ^ 2 := by
    simp only [eulerD1', norm_neg, norm_div, norm_mul, norm_pow, pow_two]
    rw [cpow_norm_eq' p hp.pos z, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  -- the denominator of the cofactor is at least `t - 1`
  have hden : (p : ℝ) ^ z.re - 1 ≤ ‖(p : ℂ) ^ z - 1‖ := by
    have h := norm_sub_norm_le ((p : ℂ) ^ z) 1
    rw [norm_one, cpow_norm_eq' p hp.pos z] at h
    linarith
  -- `t / (t-1)^2 ≤ 4/p`
  have hkey : (p : ℝ) ^ z.re / ((p : ℝ) ^ z.re - 1) ^ 2 ≤ 4 / (p : ℝ) := by
    have hdenpos : 0 < ((p : ℝ) ^ z.re - 1) ^ 2 := by nlinarith
    rw [le_div_iff₀ hppos, div_mul_eq_mul_div, div_le_iff₀ hdenpos]
    have h1 : (p : ℝ) ^ z.re * (p : ℝ) ≤ (p : ℝ) ^ z.re * (p : ℝ) ^ z.re :=
      mul_le_mul_of_nonneg_left hpt (by linarith)
    have h2 : (p : ℝ) ^ z.re / 2 ≤ (p : ℝ) ^ z.re - 1 := by linarith
    have h3 : ((p : ℝ) ^ z.re / 2) ^ 2 ≤ ((p : ℝ) ^ z.re - 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (p : ℝ) ^ z.re / 2) h2 2
    nlinarith [h1, h3]
  rw [(term_hasDerivAt' p hp z hne).deriv, hnorm]
  calc (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ z.re / ‖(p : ℂ) ^ z - 1‖ ^ 2
      ≤ (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ z.re / ((p : ℝ) ^ z.re - 1) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity)
        · nlinarith
        · exact pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ (p : ℝ) ^ z.re - 1) hden 2
    _ = (Real.log (p : ℝ)) ^ 2 * ((p : ℝ) ^ z.re / ((p : ℝ) ^ z.re - 1) ^ 2) := by ring
    _ ≤ (Real.log (p : ℝ)) ^ 2 * (4 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 4 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by ring

end Work.ZeroFreeTables.Table4
