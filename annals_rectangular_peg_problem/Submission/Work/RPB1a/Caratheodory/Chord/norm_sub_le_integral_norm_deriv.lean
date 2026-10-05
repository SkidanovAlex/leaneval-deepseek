import Mathlib

open MeasureTheory
open scoped Interval

namespace Work.RPB1a.Caratheodory.Chord

theorem norm_sub_le_integral_norm_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g g' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : IntervalIntegrable g' MeasureTheory.volume a b) :
    ‖g b - g a‖ ≤ ∫ x in Set.uIoc a b, ‖g' x‖ := by
  -- The set integral over `uIoc a b` agrees with the oriented interval integral `a..b`.
  have h1 : (∫ x in Set.uIoc a b, ‖g' x‖) = ∫ x in a..b, ‖g' x‖ := by
    rw [Set.uIoc_of_le hab, ← intervalIntegral.integral_of_le hab]
  -- Fundamental theorem of calculus: `g b - g a` is the interval integral of `g'`.
  rw [h1, ← intervalIntegral.integral_eq_sub_of_hasDerivAt hg hg']
  -- Norm of an integral is bounded by the integral of the norm.
  exact intervalIntegral.norm_integral_le_integral_norm hab

end Work.RPB1a.Caratheodory.Chord
