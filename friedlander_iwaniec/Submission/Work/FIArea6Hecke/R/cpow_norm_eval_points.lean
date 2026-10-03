import Mathlib

namespace Work.FIArea6Hecke.R

lemma cpow_norm_eval_points {c : ℂ} {p : ℕ} (hp : 2 ≤ p) (hc : ‖c‖ = 1 ∨ c = 0) :
    (∀ s : ℂ, s.re = -2 → (‖c * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 ∨ 4 ≤ ‖c * (p : ℂ) ^ (-s)‖))
      ∧ (∀ s : ℂ, s.re = 3 → ‖c * (p : ℂ) ^ (-s)‖ ≤ 1 / 2) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  -- The norm of `c * p^(-s)` is `‖c‖ * p^(-s.re)`.
  have key : ∀ s : ℂ, ‖c * (p : ℂ) ^ (-s)‖ = ‖c‖ * (p : ℝ) ^ (-s.re) := by
    intro s
    rw [norm_mul, ← Complex.ofReal_natCast p,
      Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)]
    rw [Complex.neg_re]
  constructor
  · intro s hs
    rw [key s, hs]
    rw [show (-(-2) : ℝ) = (2 : ℝ) by norm_num]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rcases hc with h | h
    · right
      rw [h, one_mul]
      nlinarith [hp2, sq_nonneg ((p : ℝ) - 2)]
    · left
      rw [h, norm_zero, zero_mul]
      norm_num
  · intro s hs
    rw [key s, hs]
    have hpow : (p : ℝ) ^ (-(3 : ℝ)) = ((p : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hp0),
        show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hpow]
    have hp3 : (8 : ℝ) ≤ (p : ℝ) ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp2 3
      norm_num at h
      exact h
    rcases hc with h | h
    · rw [h, one_mul]
      calc ((p : ℝ) ^ 3)⁻¹ ≤ (8 : ℝ)⁻¹ :=
            inv_anti₀ (by norm_num) hp3
        _ ≤ 1 / 2 := by norm_num
    · rw [h, norm_zero, zero_mul]
      norm_num

end Work.FIArea6Hecke.R
