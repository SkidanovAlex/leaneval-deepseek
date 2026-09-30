import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Blaschke-factor algebra: for `0 < R`, `0 < η`, a finite set `Z` of integers with
`|l| + η < R` for `l ∈ Z`, and `z ∈ ℂ` with `‖z‖ ≤ R` and `z ∉ Z`, all denominators `R² - l z` are
nonzero, the product `∏_{l∈Z} β(z;l)^{T+1}` of Blaschke factors `β(z;l) = R(z-l)/(R²-lz)` is
nonzero, and `∏_{l∈Z}(z-l)^{T+1} = (∏_{l∈Z}((R²-lz)/R)^{T+1}) · ∏_{l∈Z}β(z;l)^{T+1}`.

(Per factor: `β(z;l)·((R²-lz)/R) = z-l`; multiply over `l ∈ Z` with `Finset.prod_mul_distrib`.
For the denominator: `|l| < R` from `hZ` and `hη`, so `|l·z| ≤ |l|·‖z‖ < R²`.) -/
theorem bfac_prod_algebra (R η : ℝ) (hR : 0 < R) (hη : 0 < η) (Z : Finset ℤ)
    (hZ : ∀ l ∈ Z, ((|l| : ℤ) : ℝ) + η < R) (Tp : ℕ) (z : ℂ) (hz : ‖z‖ ≤ R)
    (hzZ : ∀ l ∈ Z, z ≠ (l : ℂ)) :
    (∀ l ∈ Z, (R : ℂ) ^ 2 - (l : ℂ) * z ≠ 0) ∧
      (∏ l ∈ Z, Work.BW.bfac R l z ^ (Tp + 1)) ≠ 0 ∧
      ∏ l ∈ Z, (z - (l : ℂ)) ^ (Tp + 1) =
        (∏ l ∈ Z, (((R : ℂ) ^ 2 - (l : ℂ) * z) / (R : ℂ)) ^ (Tp + 1)) *
          ∏ l ∈ Z, Work.BW.bfac R l z ^ (Tp + 1) := by
  -- `|l| < R` for `l ∈ Z`, from `|l| + η < R` and `η > 0`.
  have habs_lt : ∀ l ∈ Z, ((|l| : ℤ) : ℝ) < R := by
    intro l hl
    have := hZ l hl
    linarith
  -- The denominators `R² - l z` never vanish: `‖l z‖ = |l| · ‖z‖ < R · R = R²`.
  have hden : ∀ l ∈ Z, (R : ℂ) ^ 2 - (l : ℂ) * z ≠ 0 := by
    intro l hl
    have hlR : ((|l| : ℤ) : ℝ) < R := habs_lt l hl
    intro h
    have h2 : (R : ℂ) ^ 2 = (l : ℂ) * z := sub_eq_zero.mp h
    have hnorm : ‖(R : ℂ) ^ 2‖ = ‖(l : ℂ) * z‖ := by rw [h2]
    have hRnorm : ‖(R : ℂ)‖ = R := by simp [abs_of_pos hR]
    have hlnorm : ‖(l : ℂ)‖ = ((|l| : ℤ) : ℝ) := by
      rw [Complex.norm_intCast, Int.cast_abs]
    rw [norm_pow, norm_mul, hRnorm, hlnorm] at hnorm
    have hlt2 : ((|l| : ℤ) : ℝ) * ‖z‖ < R * R := by
      rcases eq_or_lt_of_le (norm_nonneg z) with h0 | hpos
      · rw [← h0, mul_zero]; positivity
      · calc ((|l| : ℤ) : ℝ) * ‖z‖ < R * ‖z‖ := mul_lt_mul_of_pos_right hlR hpos
          _ ≤ R * R := mul_le_mul_of_nonneg_left hz hR.le
    nlinarith [hnorm, hlt2]
  -- Each Blaschke factor is nonzero.
  have hbfac : ∀ l ∈ Z, Work.BW.bfac R l z ≠ 0 := by
    intro l hl
    rw [Work.BW.bfac]
    exact div_ne_zero
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (sub_ne_zero.mpr (hzZ l hl)))
      (hden l hl)
  -- The per-factor identity `((R²-l z)/R) · β(z;l) = z - l`.
  have hper : ∀ l ∈ Z,
      (((R : ℂ) ^ 2 - (l : ℂ) * z) / (R : ℂ)) * Work.BW.bfac R l z = z - (l : ℂ) := by
    intro l hl
    have hd := hden l hl
    have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    rw [Work.BW.bfac]
    field_simp [hRne]
  refine ⟨hden, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro l hl
    exact pow_ne_zero _ (hbfac l hl)
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro l hl
    rw [← mul_pow, hper l hl]

end Work.BW
