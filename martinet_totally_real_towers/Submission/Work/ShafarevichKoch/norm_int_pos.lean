import Mathlib
import Submission.Work.ShafarevichKoch.GenusConj
import Submission.Work.ClassFieldTower.int_coords_and_norm

namespace Work.ShafarevichKoch

/-- `Kc = ℚ(√-30030)` is imaginary quadratic, so the norm of a nonzero element of `𝓞 Kc` is
positive: `0 < Algebra.norm ℤ z` for `z ≠ 0`.  Hints: `Work.ClassFieldTower.int_coords_and_norm`
gives `z = x + y·scR` with `x y : ℤ` and `Algebra.norm ℤ z = x² + 30030 y²`; if `(x,y) ≠ (0,0)`
then `x² + 30030 y² > 0` (`positivity`/`nlinarith`), and `(x,y) = (0,0)` gives `z = 0`, excluded
by `hz`. -/
theorem norm_int_pos (z : NumberField.RingOfIntegers Work.ClassFieldTower.Kc)
    (hz : z ≠ 0) : 0 < Algebra.norm ℤ z := by
  obtain ⟨x, y, hxy, hnorm⟩ := Work.ClassFieldTower.int_coords_and_norm z
  rw [hnorm]
  have hd : (0 : ℤ) < (Work.ClassFieldTower.dWit : ℤ) := by
    norm_num [Work.ClassFieldTower.dWit]
  rcases eq_or_ne x 0 with hx | hx
  · -- `x = 0`: then `y ≠ 0`, so `y² > 0` and `30030·y² > 0`
    rcases eq_or_ne y 0 with hy | hy
    · -- `x = y = 0` would give `z = 0`
      exfalso
      have hzK : (z : Work.ClassFieldTower.Kc) = 0 := by
        rw [hxy, hx, hy]
        push_cast
        simp
      exact hz (Subtype.ext hzK)
    · have hy2 : (0 : ℤ) < y ^ 2 := sq_pos_of_ne_zero hy
      nlinarith [sq_nonneg x, hd, hy2]
  · -- `x ≠ 0`: then `x² > 0` and the rest is nonnegative
    have hx2 : (0 : ℤ) < x ^ 2 := sq_pos_of_ne_zero hx
    nlinarith [sq_nonneg y, hd]

end Work.ShafarevichKoch
