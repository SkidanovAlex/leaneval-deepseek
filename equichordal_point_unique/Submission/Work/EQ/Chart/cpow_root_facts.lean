import Mathlib

namespace Work.EQ.Chart

/-- **The `d`-th root of `ρᵈ ζ`, and its powers.**

For `ρ > 0`, `d > 0` and `0 < ‖ζ‖ < 1`, the complex power
`t := (ρᵈ ζ) ^ (d⁻¹ : ℂ)` satisfies `t ^ d = ρᵈ ζ`, `0 < ‖t‖ < ρ`, and, for every `k` divisible by
`d`, `t ^ k = ρᵏ ζ ^ (k / d)`.

Route: `Complex.cpow_nat_inv_pow` gives `t ^ d = ρᵈ ζ`; taking norms, `‖t‖ ^ d = ρᵈ ‖ζ‖`, whence
`0 < ‖t‖ < ρ` since `‖ζ‖ < 1`; and `t ^ k = (t ^ d) ^ (k / d)` (`pow_mul`, `Nat.mul_div_cancel'`)
`= (ρᵈ) ^ (k / d) ζ ^ (k / d) = ρᵏ ζ ^ (k / d)` (`mul_pow`, `← pow_mul`). -/
theorem cpow_root_facts {ρ : ℝ} (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) {ζ : ℂ}
    (hζ0 : 0 < ‖ζ‖) (hζ1 : ‖ζ‖ < 1) {k : ℕ} (hdvd : d ∣ k) :
    0 < ‖((ρ : ℂ) ^ d * ζ) ^ ((d : ℂ)⁻¹)‖ ∧
      ‖((ρ : ℂ) ^ d * ζ) ^ ((d : ℂ)⁻¹)‖ < ρ ∧
      (((ρ : ℂ) ^ d * ζ) ^ ((d : ℂ)⁻¹)) ^ d = (ρ : ℂ) ^ d * ζ ∧
      (((ρ : ℂ) ^ d * ζ) ^ ((d : ℂ)⁻¹)) ^ k = (ρ : ℂ) ^ k * ζ ^ (k / d) := by
  set t : ℂ := ((ρ : ℂ) ^ d * ζ) ^ ((d : ℂ)⁻¹) with ht
  -- `t ^ d = ρᵈ ζ`
  have htd : t ^ d = (ρ : ℂ) ^ d * ζ := by
    rw [ht]; exact Complex.cpow_nat_inv_pow _ hd.ne'
  -- norm of `ρᵈ` as a complex number
  have hρdnorm : ‖(ρ : ℂ) ^ d‖ = ρ ^ d := by
    rw [Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  -- `‖t‖ ^ d = ρᵈ ‖ζ‖`
  have hn : ‖t‖ ^ d = ρ ^ d * ‖ζ‖ := by
    rw [← Complex.norm_pow, htd, norm_mul, hρdnorm]
  have hpos : 0 < ‖t‖ ^ d := by rw [hn]; positivity
  have hlt : ‖t‖ ^ d < ρ ^ d := by
    rw [hn]
    exact lt_of_lt_of_eq (mul_lt_mul_of_pos_left hζ1 (pow_pos hρ d)) (mul_one _)
  -- `0 < ‖t‖`
  have hnorm0 : 0 < ‖t‖ := by
    rcases eq_or_lt_of_le (norm_nonneg t) with h | h
    · exfalso
      rw [← h, zero_pow hd.ne'] at hpos
      exact lt_irrefl 0 hpos
    · exact h
  -- `‖t‖ < ρ`
  have hnorm_lt : ‖t‖ < ρ :=
    (pow_lt_pow_iff_left₀ (norm_nonneg t) (le_of_lt hρ) hd.ne').mp hlt
  -- the powers `t ^ k`
  have hpow : t ^ k = (ρ : ℂ) ^ k * ζ ^ (k / d) := by
    have hdm : d * (k / d) = k := Nat.mul_div_cancel' hdvd
    have h1 : t ^ k = (t ^ d) ^ (k / d) := by
      conv_lhs => rw [← hdm]
      rw [pow_mul]
    have h2 : ((ρ : ℂ) ^ d * ζ) ^ (k / d) = (ρ : ℂ) ^ k * ζ ^ (k / d) := by
      rw [mul_pow, ← pow_mul, hdm]
    rw [h1, htd, h2]
  exact ⟨hnorm0, hnorm_lt, htd, hpow⟩

end Work.EQ.Chart
