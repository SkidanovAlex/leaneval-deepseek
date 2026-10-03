import Mathlib

namespace Work.KMTAreas.A7rand

/-- If `η''` vanishes on the inner disc `|y| < 1/2` and on the outer region `|y| ≥ 1`, then it
vanishes at every point whose absolute value does not lie in the annulus `[1/2, 1)`. -/
private lemma iteratedDeriv_two_eq_zero_of_not_mem_annulus (η : ℝ → ℂ)
    (hηin : ∀ y : ℝ, |y| < 1 / 2 → iteratedDeriv 2 η y = 0)
    (hηout : ∀ y : ℝ, 1 ≤ |y| → iteratedDeriv 2 η y = 0)
    {y : ℝ} (hy : ¬ ((1 : ℝ) / 2 ≤ |y| ∧ |y| < 1)) : iteratedDeriv 2 η y = 0 := by
  by_cases h : |y| < 1 / 2
  · exact hηin y h
  · exact hηout y (not_lt.mp fun h1 => hy ⟨not_lt.mp h, h1⟩)

/-- Both `η''`-terms in the "good" range of the dyadic scale `s` vanish: if the scale strictly
increases then `good` forces one of the two arguments to lie outside the annulus `[1/2, 1)` where
`η''` can be non-zero; if it does not increase the two terms are literally equal. -/
theorem good_deriv2_zero (η : ℝ → ℂ)
    (hηin : ∀ y : ℝ, |y| < 1 / 2 → iteratedDeriv 2 η y = 0)
    (hηout : ∀ y : ℝ, 1 ≤ |y| → iteratedDeriv 2 η y = 0)
    (s : ℕ → ℕ) (hs : Monotone s) (m : ℕ) (ξ : ℝ)
    (hgood : ¬ (s (m + 1) > s m ∧ (2 : ℝ) ^ (s m) * |ξ| ≤ 1 ∧
      (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ|)) :
    (2 : ℝ) ^ (2 * s m) * iteratedDeriv 2 η ((2 : ℝ) ^ (s m) * ξ)
      - (2 : ℝ) ^ (2 * s (m + 1)) * iteratedDeriv 2 η ((2 : ℝ) ^ (s (m + 1)) * ξ) = 0 := by
  have hmono : s m ≤ s (m + 1) := hs (Nat.le_succ m)
  have hpow : (2 : ℝ) ^ (s m) ≤ (2 : ℝ) ^ (s (m + 1)) :=
    pow_le_pow_right₀ (by norm_num) hmono
  have hle : (2 : ℝ) ^ (s m) * |ξ| ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ| :=
    mul_le_mul_of_nonneg_right hpow (abs_nonneg ξ)
  have hy1 : |(2 : ℝ) ^ (s m) * ξ| = (2 : ℝ) ^ (s m) * |ξ| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have hy2 : |(2 : ℝ) ^ (s (m + 1)) * ξ| = (2 : ℝ) ^ (s (m + 1)) * |ξ| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
  by_cases hgt : s (m + 1) > s m
  · -- strictly increasing scale: both arguments escape the annulus
    have hnot : ¬ ((2 : ℝ) ^ (s m) * |ξ| ≤ 1 ∧
        (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ|) := fun hc => hgood ⟨hgt, hc⟩
    have hz1 : iteratedDeriv 2 η ((2 : ℝ) ^ (s m) * ξ) = 0 := by
      by_cases hA : (2 : ℝ) ^ (s m) * |ξ| ≤ 1
      · -- then `2 ^ s (m+1) * |ξ| < 1 / 2`, so both arguments are in the inner disc
        have hB : ¬ ((1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ|) := fun hB => hnot ⟨hA, hB⟩
        refine iteratedDeriv_two_eq_zero_of_not_mem_annulus η hηin hηout ?_
        rintro ⟨h1, _⟩
        rw [hy1] at h1
        linarith [lt_of_not_ge hB]
      · exact hηout _ (by rw [hy1]; exact le_of_lt (not_le.mp hA))
    have hz2 : iteratedDeriv 2 η ((2 : ℝ) ^ (s (m + 1)) * ξ) = 0 := by
      by_cases hA : (2 : ℝ) ^ (s m) * |ξ| ≤ 1
      · have hB : ¬ ((1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ|) := fun hB => hnot ⟨hA, hB⟩
        exact hηin _ (by rw [hy2]; exact lt_of_not_ge hB)
      · exact hηout _ (by rw [hy2]; exact le_of_lt (lt_of_lt_of_le (not_le.mp hA) hle))
    rw [hz1, hz2]
    ring
  · -- the scale does not increase, so the two terms coincide
    have heq : s (m + 1) = s m := le_antisymm (not_lt.mp hgt) hmono
    rw [heq]
    ring

end Work.KMTAreas.A7rand
