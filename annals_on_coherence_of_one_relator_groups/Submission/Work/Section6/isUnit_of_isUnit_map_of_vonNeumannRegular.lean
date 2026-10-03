import Mathlib
import Submission.Work.ORHughesFree.StarRegular

namespace Work.Section6

/-- In a von Neumann regular ring, an element whose image under an injective ring homomorphism
is a unit is itself a unit.

The point is that `f x` being a unit forces `x` to be a non-zero-divisor: if `x * r = 0` then
`f x * f r = 0`, whence `f r = 0` and `r = 0` by injectivity (and symmetrically on the other
side). A non-zero-divisor in a von Neumann regular ring is a unit: from a weak inverse `y` with
`x * y * x = x` one gets `x * (y * x - 1) = 0` and `(x * y - 1) * x = 0`, so `y * x = 1` and
`x * y = 1`. -/
theorem isUnit_of_isUnit_map_of_vonNeumannRegular {R S : Type} [Ring R] [Ring S]
    [Work.ORHughesFree.VonNeumannRegularRing R] (f : R →+* S) (hf : Function.Injective f) {x : R}
    (h : IsUnit (f x)) : IsUnit x := by
  -- `x` is not a left zero divisor.
  have hleft : ∀ r : R, x * r = 0 → r = 0 := by
    intro r hr
    have h1 : f x * f r = 0 := by rw [← map_mul, hr, map_zero]
    have h2 : f r = 0 := h.mul_left_cancel (by rw [h1, mul_zero])
    exact hf (by rw [h2, map_zero])
  -- `x` is not a right zero divisor.
  have hright : ∀ r : R, r * x = 0 → r = 0 := by
    intro r hr
    have h1 : f r * f x = 0 := by rw [← map_mul, hr, map_zero]
    have h2 : f r = 0 := h.mul_right_cancel (by rw [h1, zero_mul])
    exact hf (by rw [h2, map_zero])
  -- take a weak inverse of `x`
  obtain ⟨y, hy⟩ := Work.ORHughesFree.VonNeumannRegularRing.exists_mul_inverse (R := R) x
  have hyx : y * x = 1 := by
    have hzero : x * (y * x - 1) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, hy, sub_self]
    exact sub_eq_zero.mp (hleft _ hzero)
  have hxy : x * y = 1 := by
    have hzero : (x * y - 1) * x = 0 := by
      rw [sub_mul, one_mul, hy, sub_self]
    exact sub_eq_zero.mp (hright _ hzero)
  exact isUnit_iff_exists.mpr ⟨y, hxy, hyx⟩

end Work.Section6
