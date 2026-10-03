import Mathlib
import Submission.Work.ORHughesFree.StarRegular

namespace Work.ORHughesFree.StarRegular

/-- If `y` and `z` are both relative (Moore--Penrose) inverses of `x`, then `y = z`.
The proof works in any ∗-ring: the two Moore--Penrose products `x * y`, `x * z` (and likewise
`y * x`, `z * x`) are forced equal because each is an idempotent `e` with `e = f * e` and, by
self-adjointness, `e = e * f`. -/
theorem isRelativeInverse_unique {U : Type*} [Ring U] [StarRing U] {x y z : U}
    (hy : IsRelativeInverse x y) (hz : IsRelativeInverse x z) : y = z := by
  -- `x * y = (x * z) * (x * y)`, obtained by rewriting the middle `x` as `x * z * x`.
  have hFE : x * y = (x * z) * (x * y) := by
    calc x * y = (x * z * x) * y := by rw [hz.left]
      _ = (x * z) * (x * y) := by rw [mul_assoc]
  -- Applying `star` (using self-adjointness of `x * y`, `x * z`) yields the mirror identity.
  have hEF : x * y = (x * y) * (x * z) := by
    calc x * y = star (x * y) := hy.star_left.symm
      _ = star ((x * z) * (x * y)) := congrArg star hFE
      _ = star (x * y) * star (x * z) := star_mul _ _
      _ = (x * y) * (x * z) := by rw [hy.star_left, hz.star_left]
  -- The same manipulation with the roles of `y` and `z` interchanged.
  have hFE' : x * z = (x * y) * (x * z) := by
    calc x * z = (x * y * x) * z := by rw [hy.left]
      _ = (x * y) * (x * z) := by rw [mul_assoc]
  have hxy : x * y = x * z := hEF.trans hFE'.symm
  -- Analogously for the left Moore--Penrose products `y * x` and `z * x`.
  have hyx : y * x = (y * x) * (z * x) := by
    calc y * x = y * ((x * z) * x) := by rw [hz.left]
      _ = (y * (x * z)) * x := (mul_assoc y (x * z) x).symm
      _ = ((y * x) * z) * x := by rw [← mul_assoc y x z]
      _ = (y * x) * (z * x) := mul_assoc (y * x) z x
  have hyx' : y * x = (z * x) * (y * x) := by
    calc y * x = star (y * x) := hy.star_right.symm
      _ = star ((y * x) * (z * x)) := congrArg star hyx
      _ = star (z * x) * star (y * x) := star_mul _ _
      _ = (z * x) * (y * x) := by rw [hy.star_right, hz.star_right]
  have hzx : z * x = (z * x) * (y * x) := by
    calc z * x = z * ((x * y) * x) := by rw [hy.left]
      _ = (z * (x * y)) * x := (mul_assoc z (x * y) x).symm
      _ = ((z * x) * y) * x := by rw [← mul_assoc z x y]
      _ = (z * x) * (y * x) := mul_assoc (z * x) y x
  have hyx_eq : y * x = z * x := hyx'.trans hzx.symm
  -- Finally `y = y * x * y = z * x * y = z * (x * y) = z * (x * z) = z * x * z = z`.
  calc y = y * x * y := hy.right.symm
    _ = (y * x) * y := rfl
    _ = (z * x) * y := by rw [hyx_eq]
    _ = z * (x * y) := mul_assoc z x y
    _ = z * (x * z) := by rw [hxy]
    _ = z * x * z := (mul_assoc z x z).symm
    _ = z := hz.right

end Work.ORHughesFree.StarRegular
