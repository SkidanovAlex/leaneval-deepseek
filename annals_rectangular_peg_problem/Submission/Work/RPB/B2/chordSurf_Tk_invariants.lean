import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.V

namespace Work.RPB.B2

open RectangularPegProblem
open Complex Real

/-- `Tk k` acting on the chord chart is the shift of the phase by `2πk`: the chord point
`chordPS z w a` taken after the `2πk`-shift of the angle is the chord point with phase
`a + 2πk` (the reduced coordinate `e^{-ia}(z+w)/√2` and `p₂` are unchanged). -/
theorem Tk_chordPS (k : ℤ) (z w : ℂ) (a : ℝ) :
    Work.RPV.Tk k (Work.RPV.chordPS z w a) =
      Work.RPV.chordPS z w (a + 2 * π * (k : ℝ)) := by
  have he : Complex.exp (-(((a + 2 * π * (k : ℝ)) : ℝ) : ℂ) * I) = Complex.exp (-(a : ℂ) * I) := by
    rw [show -(((a + 2 * π * (k : ℝ)) : ℝ) : ℂ) * I
        = -(a : ℂ) * I + ((-k : ℤ) : ℂ) * (2 * ↑π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [Work.RPV.Tk, Work.RPV.chordPS, he]

theorem chordSurf_Tk_invariants (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
      ∀ r' ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ t' (k : ℤ),
        Work.RPB.chordSurf CI.c a τ t' r' = Work.RPV.Tk k (Work.RPB.chordSurf CI.c a τ t r) →
          a τ t' r' = a τ t r + 2 * Real.pi * (k : ℝ) ∧
          CI.c τ (t' + r') + CI.c τ (t' - r') = CI.c τ (t + r) + CI.c τ (t - r) ∧
          ‖CI.c τ (t' + r') - CI.c τ (t' - r')‖ = ‖CI.c τ (t + r) - CI.c τ (t - r)‖ := by
  intro τ _ t r _ r' _ t' k h
  -- Unfold the chord annulus in the hypothesis and push `Tk` onto the phase.
  simp only [Work.RPB.chordSurf] at h
  rw [Tk_chordPS] at h
  -- The chord chart is determined by (phase, midpoint, length).
  exact (Work.RPV.chordPS_eq_iff
    (z := CI.c τ (t' + r')) (w := CI.c τ (t' - r')) (a := a τ t' r')
    (z' := CI.c τ (t + r)) (w' := CI.c τ (t - r))
    (a' := a τ t r + 2 * π * (k : ℝ))).mp h

end Work.RPB.B2
