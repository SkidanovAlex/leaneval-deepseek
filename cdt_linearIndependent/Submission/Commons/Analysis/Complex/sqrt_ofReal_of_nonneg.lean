import Mathlib.Analysis.RCLike.Sqrt

namespace Commons.Analysis.Complex

/-- The complex square root of a nonnegative real number agrees with its real
square root, embedded into the complex numbers. -/
lemma sqrt_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
  rw [Complex.sqrt_of_nonneg (a := (x : ℂ)) (by simpa [RCLike.ofReal_le_ofReal] using hx)]
  simp

end Commons.Analysis.Complex