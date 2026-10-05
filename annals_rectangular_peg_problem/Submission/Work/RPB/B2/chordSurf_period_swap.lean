import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.V

open Complex

namespace Work.RPB.B2

/-- Shifting the phase `a` of the chord chart by `2π` is exactly the shift `Tk 1` of the angle
`q₂` in `PS`: the reduced coordinate `e^{-ia}(z+w)/√2` is unchanged because `e^{-2πi} = 1`. -/
theorem Tk_one_chordPS (z w : ℂ) (a : ℝ) :
    Work.RPV.Tk 1 (Work.RPV.chordPS z w a) = Work.RPV.chordPS z w (a + 2 * Real.pi) := by
  have hexp : Complex.exp (-((a + 2 * Real.pi : ℝ) : ℂ) * I) = Complex.exp (-(a : ℂ) * I) := by
    rw [show -((a + 2 * Real.pi : ℝ) : ℂ) * I = -(a : ℂ) * I + (-(2 * Real.pi * I)) by
      push_cast; ring]
    rw [Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
  ext <;> simp only [Work.RPV.Tk, Work.RPV.chordPS, hexp, Int.cast_one, mul_one]

-- Hint for the prover: `chordSurf c a τ t r = chordPS (c τ (t+r)) (c τ (t-r)) (a τ t r)`.  The
-- periodicity uses `IsChordPhase.per` (which holds for `0 < r < π`) together with `CurveIsotopy.per`
-- and the fact that shifting the phase by `2π` is exactly `Tk 1`
-- (`Tk 1 (chordPS z w a) = chordPS z w (a + 2π)`); the swap uses `IsChordPhase.swap` together with
-- `Work.RPV.chordPS_swap` (`chordPS w z (a+π) = tau π (chordPS z w a)`), noting `π - r ∈ (0,π)`.
theorem chordSurf_period_swap (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) :
    (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
        Work.RPB.chordSurf CI.c a τ (t + 2 * Real.pi) r
          = Work.RPV.Tk 1 (Work.RPB.chordSurf CI.c a τ t r)) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
        Work.RPB.chordSurf CI.c a τ (t + Real.pi) (Real.pi - r)
          = Work.RPV.tau Real.pi (Work.RPB.chordSurf CI.c a τ t r)) := by
  obtain ⟨-, -, hper, hswap⟩ := ha
  constructor
  · -- periodicity: `t ↦ t + 2π` moves both chord endpoints back by `CurveIsotopy.per` and the
    -- phase by `IsChordPhase.per`; what is left is exactly `Tk 1` on the chord chart.
    intro τ hτ t r hr
    have h1 : CI.c τ (t + 2 * Real.pi + r) = CI.c τ (t + r) := by
      rw [show t + 2 * Real.pi + r = (t + r) + 2 * Real.pi by ring, CI.per]
    have h2 : CI.c τ (t + 2 * Real.pi - r) = CI.c τ (t - r) := by
      rw [show t + 2 * Real.pi - r = (t - r) + 2 * Real.pi by ring, CI.per]
    rw [Work.RPB.chordSurf, h1, h2, hper τ hτ t r hr]
    exact (Tk_one_chordPS _ _ _).symm
  · -- the swap: `(t, r) ↦ (t + π, π - r)` exchanges the endpoints of the chord and adds `π` to
    -- the phase, which is exactly `τ_π` (`Work.RPV.chordPS_swap`).
    intro τ hτ t r hr
    have h1 : CI.c τ (t + Real.pi + (Real.pi - r)) = CI.c τ (t - r) := by
      rw [show t + Real.pi + (Real.pi - r) = (t - r) + 2 * Real.pi by ring, CI.per]
    have h2 : CI.c τ (t + Real.pi - (Real.pi - r)) = CI.c τ (t + r) := by
      rw [show t + Real.pi - (Real.pi - r) = t + r by ring]
    rw [Work.RPB.chordSurf, h1, h2, hswap τ hτ t r hr]
    exact Work.RPV.chordPS_swap (CI.c τ (t + r)) (CI.c τ (t - r)) (a τ t r)

end Work.RPB.B2
