import Mathlib

namespace Work.RPB.B5

/-- For `t ∈ (0, π²/4]` the "good branch" identity holds: `sin (√t)` is nonnegative, so that
`√(sin²(√t)) = sin (√t)`, and applying `arcsin` and squaring recovers `t`. -/
theorem sqrt_sin_sq_arcsin_sq {t : ℝ} (h0 : 0 < t) (h1 : t ≤ Real.pi ^ 2 / 4) :
    Real.sqrt ((Real.sin (Real.sqrt t)) ^ 2) = Real.sin (Real.sqrt t) ∧
    (Real.arcsin (Real.sqrt ((Real.sin (Real.sqrt t)) ^ 2))) ^ 2 = t := by
  have ht0 : 0 ≤ t := le_of_lt h0
  have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsle : Real.sqrt t ≤ Real.pi / 2 := by
    rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    rw [show (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 by ring]
    exact h1
  have hsin_nonneg : 0 ≤ Real.sin (Real.sqrt t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith [Real.pi_pos, hsle])
  have hsqrt : Real.sqrt ((Real.sin (Real.sqrt t)) ^ 2) = Real.sin (Real.sqrt t) := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsin_nonneg]
  have harc : Real.arcsin (Real.sqrt ((Real.sin (Real.sqrt t)) ^ 2)) = Real.sqrt t := by
    rw [hsqrt]
    exact Real.arcsin_sin (by linarith [Real.pi_pos, hs0]) hsle
  exact ⟨hsqrt, by rw [harc, Real.sq_sqrt ht0]⟩

end Work.RPB.B5
