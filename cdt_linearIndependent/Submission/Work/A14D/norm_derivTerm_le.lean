import Mathlib

namespace Work.A14D

/-- Termwise bound for the derivative series: if the coefficients `a n` grow at most like
`C * R^n * (n+1)^k` then the `n`-th term of the derivative series, evaluated at a point of
norm at most `ρ`, is bounded by `C * R * 2^k * ((n+1)^(k+1) * (R*ρ)^n)`. -/
theorem norm_derivTerm_le (a : ℕ → ℂ) {C R ρ : ℝ} {k : ℕ} (hC : 0 ≤ C) (hR : 0 < R)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * R ^ n * ((n : ℝ) + 1) ^ k) (hρ : 0 ≤ ρ)
    (n : ℕ) {y : ℂ} (hy : ‖y‖ ≤ ρ) :
    ‖((n : ℂ) + 1) * a (n + 1) * y ^ n‖
      ≤ C * R * 2 ^ k * (((n : ℝ) + 1) ^ (k + 1) * (R * ρ) ^ n) := by
  have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_natCast]; push_cast; ring
  have ha' : ‖a (n + 1)‖ ≤ C * R ^ (n + 1) * ((n : ℝ) + 2) ^ k := by
    have h := ha (n + 1)
    have h2 : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
    rwa [h2] at h
  have hy' : ‖y‖ ^ n ≤ ρ ^ n := pow_le_pow_left₀ (norm_nonneg y) hy n
  -- the arithmetic heart: `(n+1) * (n+2)^k ≤ 2^k * (n+1)^(k+1)`
  have hkey : ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ k ≤ 2 ^ k * ((n : ℝ) + 1) ^ (k + 1) := by
    have hx1 : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
    have hle : ((n : ℝ) + 2) ^ k ≤ (2 * ((n : ℝ) + 1)) ^ k :=
      pow_le_pow_left₀ (by positivity) hx1 k
    rw [mul_pow] at hle
    calc ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ k
        ≤ ((n : ℝ) + 1) * (2 ^ k * ((n : ℝ) + 1) ^ k) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2 ^ k * ((n : ℝ) + 1) ^ (k + 1) := by rw [pow_succ]; ring
  have hnum : ((n : ℝ) + 1) * (C * R ^ (n + 1) * ((n : ℝ) + 2) ^ k) * ρ ^ n
      ≤ C * R * 2 ^ k * (((n : ℝ) + 1) ^ (k + 1) * (R * ρ) ^ n) := by
    have hCnR : 0 ≤ C * R * R ^ n * ρ ^ n :=
      mul_nonneg (mul_nonneg (mul_nonneg hC hR.le) (pow_nonneg hR.le n)) (pow_nonneg hρ n)
    calc ((n : ℝ) + 1) * (C * R ^ (n + 1) * ((n : ℝ) + 2) ^ k) * ρ ^ n
        = (C * R * R ^ n * ρ ^ n) * (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ k) := by
            rw [pow_succ]; ring
      _ ≤ (C * R * R ^ n * ρ ^ n) * (2 ^ k * ((n : ℝ) + 1) ^ (k + 1)) :=
            mul_le_mul_of_nonneg_left hkey hCnR
      _ = C * R * 2 ^ k * (((n : ℝ) + 1) ^ (k + 1) * (R * ρ) ^ n) := by
            rw [mul_pow]; ring
  calc ‖((n : ℂ) + 1) * a (n + 1) * y ^ n‖
      = ((n : ℝ) + 1) * ‖a (n + 1)‖ * ‖y‖ ^ n := by
        rw [norm_mul, norm_mul, norm_pow, hnorm]
    _ ≤ ((n : ℝ) + 1) * (C * R ^ (n + 1) * ((n : ℝ) + 2) ^ k) * ρ ^ n := by
        have hB : 0 ≤ C * R ^ (n + 1) * ((n : ℝ) + 2) ^ k :=
          mul_nonneg (mul_nonneg hC (pow_nonneg hR.le (n + 1))) (pow_nonneg (by positivity) k)
        have hstep : ((n : ℝ) + 1) * ‖a (n + 1)‖
            ≤ ((n : ℝ) + 1) * (C * R ^ (n + 1) * ((n : ℝ) + 2) ^ k) :=
          mul_le_mul_of_nonneg_left ha' (by positivity)
        exact mul_le_mul hstep hy' (pow_nonneg (norm_nonneg y) n) (mul_nonneg (by positivity) hB)
    _ ≤ C * R * 2 ^ k * (((n : ℝ) + 1) ^ (k + 1) * (R * ρ) ^ n) := hnum

end Work.A14D
