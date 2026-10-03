import Mathlib

namespace Work.FITop4.Red5

lemma wsr_shellW_le {mm ai u x θ pi : ℝ} (hpi : 0 ≤ pi) (hmm : 0 ≤ mm) (hai : 0 < ai)
    (hθ : 0 < θ) (hu : u ≤ (1 + θ) * ai) :
    (if x < mm * u then (1:ℝ) else 0) * (if mm * ai < x then (1:ℝ) else 0) * pi
      ≤ (if x < mm * u ∧ mm * u ≤ x * (1 + θ) then (1:ℝ) else 0) * pi := by
  -- Key: whenever both left indicator conditions hold, the right window condition
  -- `mm * u ≤ x * (1 + θ)` holds as well.
  have key : x < mm * u → mm * ai < x → mm * u ≤ x * (1 + θ) := by
    intro h1 h2
    nlinarith [mul_le_mul_of_nonneg_left hu hmm,
      mul_lt_mul_of_pos_left h2 (by linarith : (0:ℝ) < 1 + θ)]
  by_cases h1 : x < mm * u
  · by_cases h2 : mm * ai < x
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, key h1 h2⟩]
      linarith
    · rw [if_pos h1, if_neg h2]
      by_cases hA : x < mm * u ∧ mm * u ≤ x * (1 + θ)
      · rw [if_pos hA]; nlinarith [hpi]
      · rw [if_neg hA]; simp
  · have hA : ¬ (x < mm * u ∧ mm * u ≤ x * (1 + θ)) := fun h => h1 h.1
    rw [if_neg h1, if_neg hA]
    simp

end Work.FITop4.Red5
