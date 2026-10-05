import Mathlib
import Submission.Work.RPB.B2.PhaseDefs

open Complex Real

namespace Work.RPB.B2

/-- The chord vector of the unit circle.  If the time-`0` curve is `t ↦ exp (t * I)`, then the
chord `c 0 (t+r) - c 0 (t-r)` equals `2 sin r` times the unit complex number `exp ((t + π/2) * I)`:
the chord of a circle is a rotated/scaled version of the normal direction at its midpoint. -/
theorem chordVec_circle (c : ℝ → ℝ → ℂ) (h0 : ∀ t, c 0 t = Complex.exp (t * Complex.I))
    (t r : ℝ) :
    Work.RPB.chordVec c 0 t r = (2 * Real.sin r : ℂ) * Complex.exp ((t + π / 2) * Complex.I) := by
  rw [Work.RPB.chordVec, h0 (t + r), h0 (t - r)]
  -- `exp (a + b) - exp (a - b) = exp a * (exp b - exp (-b))`
  have key : ∀ a b : ℂ, Complex.exp (a + b) - Complex.exp (a - b)
      = Complex.exp a * (Complex.exp b - Complex.exp (-b)) := by
    intro a b
    rw [Complex.exp_add, show a - b = a + (-b) by ring, Complex.exp_add, Complex.exp_neg]
    ring
  -- the elementary chord identity on the unit circle: `exp (r I) - exp (-(r I)) = 2 sin r * I`
  have htri : Complex.exp (↑r * Complex.I) - Complex.exp (-(↑r * Complex.I))
      = (2 * Real.sin r : ℂ) * Complex.I := by
    have h1 : Complex.exp (↑r * Complex.I)
        = (Real.cos r : ℂ) + (Real.sin r : ℂ) * Complex.I := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have h2 : Complex.exp (-(↑r * Complex.I))
        = (Real.cos r : ℂ) - (Real.sin r : ℂ) * Complex.I := by
      rw [show -(↑r * Complex.I) = (↑(-r) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      rw [Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [h1, h2]; ring
  rw [show ((t + r : ℝ) : ℂ) * Complex.I = ↑t * Complex.I + ↑r * Complex.I by push_cast; ring]
  rw [show ((t - r : ℝ) : ℂ) * Complex.I = ↑t * Complex.I - ↑r * Complex.I by push_cast; ring]
  rw [show (↑t + ↑Real.pi / 2) * Complex.I = ↑t * Complex.I + ↑Real.pi / 2 * Complex.I by ring]
  rw [key (↑t * Complex.I) (↑r * Complex.I)]
  rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  rw [show Complex.exp (↑t * Complex.I)
          * (Complex.exp (↑r * Complex.I) - Complex.exp (-(↑r * Complex.I)))
        = Complex.exp (↑t * Complex.I) * ((2 * Real.sin r : ℂ) * Complex.I) from by rw [htri]]
  ring

end Work.RPB.B2
