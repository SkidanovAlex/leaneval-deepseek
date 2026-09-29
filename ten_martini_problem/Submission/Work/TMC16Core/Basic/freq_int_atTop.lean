import Mathlib

namespace Work.TMC16Core.Basic

/-- `atTop` on `ℤ` and on `ℕ` (transported along the coercion `ℕ → ℤ`) have the same
frequently-occurring sets: the natural numbers are cofinal in the integers. -/
theorem freq_int_atTop (P : ℤ → Prop) :
    (∃ᶠ k : ℤ in Filter.atTop, P k) ↔ ∃ᶠ n : ℕ in Filter.atTop, P (n : ℤ) := by
  rw [Filter.frequently_atTop, Filter.frequently_atTop]
  constructor
  · intro h N
    obtain ⟨k, hkN, hPk⟩ := h (N : ℤ)
    have hk0 : 0 ≤ k := le_trans (Int.natCast_nonneg N) hkN
    exact ⟨k.toNat, by omega, by rw [Int.toNat_of_nonneg hk0]; exact hPk⟩
  · intro h M
    obtain ⟨n, hnM, hPn⟩ := h M.toNat
    exact ⟨(n : ℤ), by omega, hPn⟩

end Work.TMC16Core.Basic
