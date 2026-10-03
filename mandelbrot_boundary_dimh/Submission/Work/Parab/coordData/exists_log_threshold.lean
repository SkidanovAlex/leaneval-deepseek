import Mathlib
import Submission.Work.Parab.coordData.log_le_frac

namespace Work.Parab.coordData

/-- A quantity that grows at most logarithmically in `t` is eventually dominated by `t`:
for any real constants `A B c₁ c₂` the expression `c₁ + c₂ * (A * (1 + log (2 + t)) + B)`
is strictly below `t` for all sufficiently large `t`. -/
theorem exists_log_threshold (A B c₁ c₂ : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      c₁ + c₂ * (A * (1 + Real.log (2 + t)) + B) < t := by
  obtain ⟨M, hM1, hM⟩ := log_le_frac (c₂ * A)
  refine ⟨max M (max 1 (4 / 3 * (c₁ + c₂ * B) + 1)), ?_, fun t ht => ?_⟩
  · exact le_trans (le_max_left 1 (4 / 3 * (c₁ + c₂ * B) + 1))
      (le_max_right M (max 1 (4 / 3 * (c₁ + c₂ * B) + 1)))
  · have htM : M ≤ t := le_trans (le_max_left _ _) ht
    have htK : 4 / 3 * (c₁ + c₂ * B) + 1 ≤ t :=
      le_trans (le_max_right 1 (4 / 3 * (c₁ + c₂ * B) + 1))
        (le_trans (le_max_right M (max 1 (4 / 3 * (c₁ + c₂ * B) + 1))) ht)
    have h1 : c₂ * A * (1 + Real.log (2 + t)) ≤ t / 4 := hM t htM
    have h2 : c₁ + c₂ * B < 3 / 4 * t := by linarith
    have heq : c₁ + c₂ * (A * (1 + Real.log (2 + t)) + B)
        = c₂ * A * (1 + Real.log (2 + t)) + (c₁ + c₂ * B) := by ring
    rw [heq]; linarith

end Work.Parab.coordData
