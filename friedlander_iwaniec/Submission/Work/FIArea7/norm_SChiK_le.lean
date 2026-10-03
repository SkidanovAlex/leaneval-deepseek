import Mathlib
import Submission.Work.FIArea7.Prop172

namespace Work.FIArea7

/-- The point `a / ‖a‖` (with `0 / 0 = 0`) lies in the closed unit disc, and every integer power
of it has norm at most `1`. This is the elementary fact behind `‖ψ(z)‖ ≤ 1` for the
Grossencharacter `ψ(z) = χ(z)(z/|z|)^k` of (17.17). -/
lemma norm_div_norm_zpow_le_one (a : ℂ) (k : ℤ) : ‖(a / ((‖a‖ : ℝ) : ℂ)) ^ k‖ ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_div, norm_zpow, norm_zero]
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · rw [zero_zpow k hk]; norm_num
  · have hnz : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hnorm : ‖a / ((‖a‖ : ℝ) : ℂ)‖ = 1 := by
      rw [norm_div]
      have h2 : ‖((‖a‖ : ℝ) : ℂ)‖ = ‖a‖ := by simp
      rw [h2]
      exact div_self hnz
    rw [norm_zpow, hnorm, one_zpow]

/-- **The Grossencharacter has modulus at most one**: `‖ψ(z)‖ ≤ 1` for `ψ = χ·(z/|z|)^k`
(17.17), for any character `χ` with `‖χ‖ ≤ 1`. This is the elementary size bound used in the
proof of Proposition 17.2. -/
lemma norm_grossenChar_le_one (chi : GaussianInt → ℂ) (k : ℤ) (hchi : ∀ z, ‖chi z‖ ≤ 1)
    (z : GaussianInt) : ‖grossenChar chi k z‖ ≤ 1 := by
  rw [grossenChar, norm_mul]
  have h2 := norm_div_norm_zpow_le_one z.toComplex k
  calc ‖chi z‖ * ‖(z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ)) ^ k‖ ≤ 1 * 1 :=
        mul_le_mul (hchi z) h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **(17.12)/(17.14), elementary size bound**: the twisted character sum
`S^k_χ(β') = Σ_z β'_z χ(z)(z/|z|)^k` is bounded by the sum of the moduli of the twisted
coefficients `β'_z`, i.e. `|S^k_χ(β')| ≤ Σ_{|z| ≤ √R} |β'_z|`. -/
theorem norm_SChiK_le (Rz : ℤ) (β : GaussianInt → ℂ) (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z, ‖chi z‖ ≤ 1) :
    ‖SChiK Rz β chi k‖ ≤ ∑ z ∈ Work.FIPlan.gBox Rz, ‖betaPrime β z‖ := by
  rw [SChiK]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro z _
  rw [norm_mul]
  calc ‖betaPrime β z‖ * ‖grossenChar chi k z‖ ≤ ‖betaPrime β z‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_grossenChar_le_one chi k hchi z) (norm_nonneg _)
    _ = ‖betaPrime β z‖ := mul_one _

end Work.FIArea7
