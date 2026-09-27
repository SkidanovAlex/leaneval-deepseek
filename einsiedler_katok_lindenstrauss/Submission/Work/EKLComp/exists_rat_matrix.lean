import Mathlib

namespace Work.EKLComp

lemma exists_rat_matrix (M : Matrix (Fin 3) (Fin 3) ℝ) (t : Fin 3 → ℝ) (hMzero : ∀ i j, t i ≠ t j → M i j = 0) {δ : ℝ} (hδ : 0 < δ) : ∃ Rq : Matrix (Fin 3) (Fin 3) ℚ, (∀ i j, |(Rq i j : ℝ) - M i j| < δ) ∧ (∀ i j, t i ≠ t j → Rq i j = 0) := by
  classical
  have hper : ∀ i j, ∃ r : ℚ, |(r : ℝ) - M i j| < δ ∧ (t i ≠ t j → r = 0) := by
    intro i j
    by_cases h : t i = t j
    · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show M i j - δ < M i j + δ by linarith)
      exact ⟨r, by rw [abs_lt]; constructor <;> linarith, fun hne => absurd h hne⟩
    · refine ⟨0, ?_, fun _ => rfl⟩
      rw [hMzero i j h, Rat.cast_zero, sub_zero, abs_zero]
      exact hδ
  choose q hq using hper
  exact ⟨q, fun i j => (hq i j).1, fun i j h => (hq i j).2 h⟩

end Work.EKLComp
