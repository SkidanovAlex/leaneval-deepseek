import Mathlib

namespace Work.CKFinal.Socket

/-- The Euclidean squared distance in terms of the hyperbolic distance:
`|z - w|² = 2 · Im z · Im w · (cosh (dist z w) - 1)`. -/
theorem sq_sum_cosh (z w : UpperHalfPlane) :
    (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = 2 * z.im * w.im * (Real.cosh (dist z w) - 1) := by
  rw [UpperHalfPlane.cosh_dist']
  field_simp
  ring

end Work.CKFinal.Socket
