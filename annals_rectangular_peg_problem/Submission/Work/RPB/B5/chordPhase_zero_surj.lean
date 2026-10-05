import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.chordPhase_zero_eq

namespace Work.RPB.B5

/-- At `τ = 0` the curve is the unit circle, so the phase `t ↦ a 0 t r` is the affine map
`t ↦ t + π/2 + 2πk` (`Work.RPB.B5.chordPhase_zero_eq`); in particular it is onto `ℝ` for every
admissible chord radius `r ∈ (0, π/2]`. -/
theorem chordPhase_zero_surj (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) :
    ∀ r : ℝ, 0 < r → r ≤ Real.pi / 2 → ∀ v : ℝ, ∃ t : ℝ, a 0 t r = v := by
  obtain ⟨k, hk⟩ := chordPhase_zero_eq CI a ha
  intro r hr0 hr2 v
  refine ⟨v - Real.pi / 2 - 2 * Real.pi * (k : ℝ), ?_⟩
  have hrIcc : r ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt hr0, by linarith [hr2, Real.pi_pos]⟩
  rw [hk _ r hrIcc]
  ring

end Work.RPB.B5
