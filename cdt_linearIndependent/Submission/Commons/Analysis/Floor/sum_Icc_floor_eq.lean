import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.Analysis.Floor

theorem sum_Icc_floor_eq (c : ℕ → ℝ) {B : ℝ} (hB : 0 < B) {A : ℝ} (hA : 0 ≤ A) {H : ℕ}
    (hH : ⌊A⌋₊ ≤ H) :
    (∑ h ∈ Finset.Icc 1 ⌊A⌋₊, c h)
      = ∑ h ∈ Finset.Icc 1 H, c h * (if ((h : ℕ) : ℝ) ≤ A then 1 else 0) := by
  have hfilter : (Finset.Icc 1 H).filter (fun h => ((h : ℕ) : ℝ) ≤ A)
      = Finset.Icc 1 ⌊A⌋₊ := by
    apply Finset.ext
    intro h
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, hA'⟩
      exact ⟨h1, Nat.le_floor hA'⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2 hH⟩, le_trans (by exact_mod_cast h2) (Nat.floor_le hA)⟩
  rw [← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro h _
  by_cases hc : ((h : ℕ) : ℝ) ≤ A <;> simp [hc]

end Commons.Analysis.Floor