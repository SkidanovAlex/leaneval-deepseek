import Mathlib
import Submission.Work.PSU3.FMap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.FMap

/-- `f` is an involution on `(SZ E)ˣ`: writing `f(x,y) = (x/y, 1/y)` one has
`f(f(x,y)) = ((x/y)/(1/y), 1/(1/y)) = (x, y)`. -/
theorem fMap_invol {E : Type*} [Field E] [FrobeniusInvolution E] (p : SZ E) (hp : p ≠ 1)
    (hq : SZ.fMap p hp ≠ 1) : SZ.fMap (SZ.fMap p hp) hq = p := by
  -- `p ≠ 1` makes the second coordinate of `p` nonzero.
  have hy : p.y ≠ 0 := fun h => hq (SZ.eq_one_of_y_eq_zero (by simp [SZ.fMap_y, h]))
  ext
  · simp only [SZ.fMap_x, SZ.fMap_y]
    field_simp
  · simp only [SZ.fMap_y, inv_inv]

end Work.PSU3.FMap
