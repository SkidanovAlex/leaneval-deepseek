import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star

namespace Commons.Measure.Real

/-- If a point `x` lies in the closed interval `[a, a + L·h]`, then it lies in one of the `L` consecutive
closed subintervals `[a + k·h, a + (k+1)·h]`, `k < L`. -/
theorem exists_cell_Icc {a h x : ℝ} (L : ℕ) (hL : 0 < L)
    (hx : x ∈ Set.Icc a (a + (L : ℝ) * h)) :
    ∃ k : ℕ, k < L ∧ x ∈ Set.Icc (a + (k : ℝ) * h) (a + ((k + 1 : ℕ) : ℝ) * h) := by
  have aux : ∀ L : ℕ, 0 < L → ∀ a h x : ℝ,
      x ∈ Set.Icc a (a + (L : ℝ) * h) →
      ∃ k : ℕ, k < L ∧ x ∈ Set.Icc (a + (k : ℝ) * h) (a + ((k + 1 : ℕ) : ℝ) * h) := by
    intro L
    induction L with
    | zero => intro hL; exact absurd hL (Nat.lt_irrefl 0)
    | succ L ih =>
      intro _hL a h x hx
      rcases hx with ⟨hax, hxle⟩
      rcases Nat.eq_zero_or_pos L with hL0 | hLpos
      · subst hL0
        exact ⟨0, by norm_num, by simpa using hax, by simpa using hxle⟩
      · by_cases hcase : x ≤ a + (L : ℝ) * h
        · obtain ⟨k, hkL, hk⟩ := ih hLpos a h x ⟨hax, hcase⟩
          exact ⟨k, Nat.lt_succ_of_lt hkL, hk⟩
        · exact ⟨L, Nat.lt_succ_self L, le_of_lt (not_le.mp hcase), hxle⟩
  exact aux L hL a h x hx

end Commons.Measure.Real