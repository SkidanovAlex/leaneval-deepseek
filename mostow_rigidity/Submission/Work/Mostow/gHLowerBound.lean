import Mathlib
import Submission.Work.Mostow.localIsomDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- `gH u` is bounded below by `‖v‖ ^ 2 / (1 + ‖u‖ ^ 2)` (Cauchy–Schwarz), and `gH` is
positive definite in its second argument. -/
theorem gHLowerBound {n : ℕ} (u v : E n) :
    ‖v‖ ^ 2 / (1 + ‖u‖ ^ 2) ≤ gH u v ∧ (gH u v = 0 ↔ v = 0) := by
  have hden : (0 : ℝ) < 1 + ‖u‖ ^ 2 := by positivity
  have hcs : (inner ℝ u v) ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    have h := real_inner_mul_inner_self_le u v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    simpa [sq] using h
  constructor
  · rw [gH]
    have key : (inner ℝ u v) ^ 2 / (1 + ‖u‖ ^ 2) + ‖v‖ ^ 2 / (1 + ‖u‖ ^ 2) ≤ ‖v‖ ^ 2 := by
      rw [← add_div, div_le_iff₀ hden]
      nlinarith [hcs]
    linarith
  · constructor
    · intro h
      have hA : ‖v‖ ^ 2 = (inner ℝ u v) ^ 2 / (1 + ‖u‖ ^ 2) := by
        rw [gH] at h
        linarith
      have hle : ‖v‖ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 / (1 + ‖u‖ ^ 2) := by
        calc ‖v‖ ^ 2 = (inner ℝ u v) ^ 2 / (1 + ‖u‖ ^ 2) := hA
          _ ≤ (‖u‖ ^ 2 * ‖v‖ ^ 2) / (1 + ‖u‖ ^ 2) :=
              div_le_div_of_nonneg_right hcs (le_of_lt hden)
      have hle' : ‖v‖ ^ 2 * (1 + ‖u‖ ^ 2) ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 :=
        (le_div_iff₀ hden).mp hle
      have hA0 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [hle']
      have hv2 : ‖v‖ ^ 2 = 0 := le_antisymm hA0 (by positivity)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hv2)
    · intro h
      subst h
      simp [gH]

end Work.Mostow
