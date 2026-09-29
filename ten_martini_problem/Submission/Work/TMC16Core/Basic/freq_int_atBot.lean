import Mathlib

namespace Work.TMC16Core.Basic

theorem freq_int_atBot (P : ℤ → Prop) :
    (∃ᶠ k : ℤ in Filter.atBot, P k) ↔ ∃ᶠ n : ℕ in Filter.atTop, P (-(n : ℤ)) := by
  rw [Filter.frequently_atBot, Filter.frequently_atTop]
  constructor
  · intro h m
    obtain ⟨b, hb, hPb⟩ := h (-(m : ℤ))
    have hb0 : b ≤ 0 := by omega
    refine ⟨(-b).toNat, ?_, ?_⟩
    · rw [Int.le_toNat (by omega : (0 : ℤ) ≤ -b)]
      omega
    · rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -b), neg_neg]
      exact hPb
  · intro h a
    by_cases ha : a ≤ 0
    · obtain ⟨n, hn, hPn⟩ := h ((-a).toNat)
      refine ⟨-(n : ℤ), ?_, hPn⟩
      have h1 : (((-a).toNat : ℕ) : ℤ) = -a := Int.toNat_of_nonneg (by omega)
      have h2 : (((-a).toNat : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      omega
    · obtain ⟨n, hn, hPn⟩ := h 0
      exact ⟨-(n : ℤ), by omega, hPn⟩

end Work.TMC16Core.Basic
