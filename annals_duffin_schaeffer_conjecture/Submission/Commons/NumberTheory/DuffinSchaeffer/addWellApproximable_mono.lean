import Mathlib.NumberTheory.WellApproximable

namespace Commons.NumberTheory.DuffinSchaeffer

open Set

/-- `addWellApproximable` is monotone in the sequence of error bounds. -/
theorem addWellApproximable_mono (δ₁ δ₂ : ℕ → ℝ) (h : ∀ n, δ₁ n ≤ δ₂ n) :
    addWellApproximable UnitAddCircle δ₁ ⊆ addWellApproximable UnitAddCircle δ₂ := by
  intro x hx
  rw [UnitAddCircle.mem_addWellApproximable_iff] at hx ⊢
  exact hx.mono (by
    intro n hn
    rcases hn with ⟨m, hmn, hgcd, hnorm⟩
    exact ⟨m, hmn, hgcd, lt_of_lt_of_le hnorm (h n)⟩)

end Commons.NumberTheory.DuffinSchaeffer
