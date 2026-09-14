import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Exponential

namespace Commons.Analysis.Calculus

/-- For `b > 0`, `n : ℕ` and `t > 0`, `t ^ n * exp (-b * t)` is bounded above by
`n ! * (2 / b) ^ n`. This follows from `exp x ≥ x ^ n / n !` applied at `x = b * t / 2`. -/
private lemma exp_neg_mul_pow_le (b : ℝ) (hb : 0 < b) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ n * Real.exp (-b * t) ≤ (n.factorial : ℝ) * (2 / b) ^ n := by
  have hx : 0 ≤ b * t / 2 := by positivity
  have hfac : (b * t / 2) ^ n / (n.factorial : ℝ) ≤ Real.exp (b * t / 2) :=
    Real.pow_div_factorial_le_exp (b * t / 2) hx n
  have hfacpos : 0 < (b * t / 2) ^ n / (n.factorial : ℝ) := by positivity
  have hinv : (Real.exp (b * t / 2))⁻¹ ≤ ((b * t / 2) ^ n / (n.factorial : ℝ))⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) hfacpos).mpr hfac
  have step1 : t ^ n * Real.exp (-b * t / 2) ≤
      t ^ n * ((b * t / 2) ^ n / (n.factorial : ℝ))⁻¹ := by
    rw [show -b * t / 2 = -(b * t / 2) by ring, Real.exp_neg]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have heq : t ^ n * ((b * t / 2) ^ n / (n.factorial : ℝ))⁻¹ =
      (n.factorial : ℝ) * (2 / b) ^ n := by
    have hmain : (2 / b) ^ n = t ^ n / (b * t / 2) ^ n := by
      rw [← div_pow]
      congr 1
      field_simp
    rw [inv_div, ← mul_div_assoc, hmain]
    ring_nf
  have step2 : t ^ n * Real.exp (-b * t) ≤ t ^ n * Real.exp (-b * t / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [ht.le]
  calc t ^ n * Real.exp (-b * t) ≤ t ^ n * Real.exp (-b * t / 2) := step2
    _ ≤ t ^ n * ((b * t / 2) ^ n / (n.factorial : ℝ))⁻¹ := step1
    _ = (n.factorial : ℝ) * (2 / b) ^ n := heq

theorem pow_mul_exp_neg_sq_bounded (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, (1 + u ^ 2) ^ n * Real.exp (-a * u ^ 2) ≤ C := by
  refine ⟨(2 : ℝ) ^ n + (n.factorial : ℝ) * (4 / a) ^ n, ?_, ?_⟩
  · have h2 : 0 < (n.factorial : ℝ) * (4 / a) ^ n :=
      mul_pos (by positivity) (pow_pos (by positivity) n)
    have h1 : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    linarith
  · intro u
    rcases lt_or_ge (u ^ 2) 1 with h | h
    · have h1 : (1 + u ^ 2) ^ n ≤ (2 : ℝ) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
      have h2 : Real.exp (-a * u ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg u]
      calc (1 + u ^ 2) ^ n * Real.exp (-a * u ^ 2) ≤ (2 : ℝ) ^ n * 1 := by
            exact mul_le_mul h1 h2 (Real.exp_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ n := by ring
        _ ≤ (2 : ℝ) ^ n + (n.factorial : ℝ) * (4 / a) ^ n := by
            have : 0 ≤ (n.factorial : ℝ) * (4 / a) ^ n :=
              mul_nonneg (by positivity) (pow_nonneg (by positivity) n)
            linarith
    · have h1 : (1 + u ^ 2) ^ n ≤ (2 * u ^ 2) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [h]
      have ht : 0 < u ^ 2 := by linarith
      have key : (u ^ 2) ^ n * Real.exp (-a * u ^ 2) ≤
          (n.factorial : ℝ) * (2 / a) ^ n := exp_neg_mul_pow_le a ha n ht
      have hmul : (2 * u ^ 2) ^ n = (2 : ℝ) ^ n * (u ^ 2) ^ n := mul_pow 2 (u ^ 2) n
      calc (1 + u ^ 2) ^ n * Real.exp (-a * u ^ 2)
          ≤ (2 * u ^ 2) ^ n * Real.exp (-a * u ^ 2) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
        _ = (2 : ℝ) ^ n * ((u ^ 2) ^ n * Real.exp (-a * u ^ 2)) := by
            rw [hmul]; ring
        _ ≤ (2 : ℝ) ^ n * ((n.factorial : ℝ) * (2 / a) ^ n) :=
            mul_le_mul_of_nonneg_left key (by positivity)
        _ = (n.factorial : ℝ) * (4 / a) ^ n := by
            have hconv : (2 : ℝ) ^ n * (2 / a) ^ n = (4 / a) ^ n := by
              rw [← mul_pow]; congr 1; ring
            rw [← hconv]; ring
        _ ≤ (2 : ℝ) ^ n + (n.factorial : ℝ) * (4 / a) ^ n := by
            have : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
            linarith

end Commons.Analysis.Calculus