import Mathlib

namespace Work.LinnikBurgess

/-- If two naturals `y₁ y₂` are both `< p ^ M` and their integer difference is a
multiple of `p ^ M`, then they are equal. -/
theorem eq_of_dvd_sub_of_lt {p M y₁ y₂ : ℕ} (h₁ : y₁ < p ^ M) (h₂ : y₂ < p ^ M)
    (hdvd : (p ^ M : ℤ) ∣ ((y₁ : ℤ) - (y₂ : ℤ))) : y₁ = y₂ := by
  -- Pass to the absolute value: `p ^ M` divides the natural number `|y₁ - y₂|`.
  have hdvd' : p ^ M ∣ ((y₁ : ℤ) - (y₂ : ℤ)).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [Int.natAbs_natCast] using this
  -- And that absolute value is strictly smaller than `p ^ M`.
  have hlt : ((y₁ : ℤ) - (y₂ : ℤ)).natAbs < p ^ M := by
    rcases le_total y₁ y₂ with h | h
    · have hc : (y₁ : ℤ) - (y₂ : ℤ) = -(((y₂ - y₁ : ℕ)) : ℤ) := by omega
      rw [hc, Int.natAbs_neg, Int.natAbs_natCast]
      exact lt_of_le_of_lt (Nat.sub_le _ _) h₂
    · have hc : (y₁ : ℤ) - (y₂ : ℤ) = (((y₁ - y₂ : ℕ)) : ℤ) := by omega
      rw [hc, Int.natAbs_natCast]
      exact lt_of_le_of_lt (Nat.sub_le _ _) h₁
  have hzero : ((y₁ : ℤ) - (y₂ : ℤ)).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' hlt
  have hz : (y₁ : ℤ) - (y₂ : ℤ) = 0 := Int.natAbs_eq_zero.mp hzero
  have heq : (y₁ : ℤ) = (y₂ : ℤ) := by omega
  exact Int.ofNat_inj.mp heq

end Work.LinnikBurgess
