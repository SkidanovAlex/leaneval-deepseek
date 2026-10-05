import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.V

namespace Work.RPB.B5

/-- The level identity of the chord annulus: `K₀ + 1 = r² ‖halfChord‖²`, i.e. the chord `(z,w)` with
`z = c τ (t+r)`, `w = c τ (t-r)` has `K₀ = ‖z-w‖²/4 - 1 = r² ‖(z-w)/(2r)‖² - 1`. -/
theorem K0_chordSurf_level (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ) (τ t r : ℝ) :
    Work.RPV.K0 (Work.RPB.chordSurf c a τ t r) + 1
      = r ^ 2 * ‖Work.RPB.halfChord c τ t r‖ ^ 2 := by
  rw [Work.RPB.chordSurf, Work.RPV.K0_chordPS]
  have hsq : ‖Work.RPB.halfChord c τ t r‖ ^ 2
      = ‖c τ (t + r) - c τ (t - r)‖ ^ 2 / (4 * r ^ 2) := by
    rw [Complex.sq_norm, Work.RPB.halfChord]
    rw [show (2 : ℂ) * ↑r = ((2 * r : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.normSq_div, Complex.normSq_ofReal, Complex.sq_norm]
    rw [show (2 * r) * (2 * r) = 4 * r ^ 2 by ring_nf]
  have hnum : ‖c τ (t + r) - c τ (t - r)‖ ^ 2 / 4 - 1 + 1
      = ‖c τ (t + r) - c τ (t - r)‖ ^ 2 / 4 := by ring
  rw [hnum, hsq]
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    simp
  · field_simp

end Work.RPB.B5
