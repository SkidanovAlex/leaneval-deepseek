import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `bndOfU` is a right inverse of the perimeter parameter `uPerim`: the point of `∂Sq` with
perimeter parameter `v = Int.fract t` is sent back to `v` by `uPerim`.

Writing `v = Int.fract t ∈ [0,1)`, `bndOfU t` runs through the four edges of the square as `v`
crosses `0, 1/4, 1/2, 3/4`, and on each edge `uPerim` is the inverse of the corresponding affine
traversal:

* `v < 1/4`: `bndOfU t = (1, 1-8v)` lies on the right edge `q 0 = 1`, so
  `uPerim = (1 - (1-8v))/8 = v`;
* `1/4 ≤ v < 1/2`: `bndOfU t = (3-8v, -1)`.  If `3-8v = 1` (i.e. `v = 1/4`) this is the corner
  `(1,-1)` and `uPerim = (1-(-1))/8 = 1/4 = v`; otherwise `q 0 ≠ 1` and `q 1 = -1` give
  `uPerim = (3-(3-8v))/8 = v`;
* `1/2 ≤ v < 3/4`: `bndOfU t = (-1, 8v-5)`.  If `8v-5 = -1` (i.e. `v = 1/2`) this is the corner
  `(-1,-1)` and `uPerim = (3-(-1))/8 = 1/2 = v`; otherwise `q 0 = -1`, `q 1 ≠ -1` give
  `uPerim = (5+(8v-5))/8 = v`;
* `3/4 ≤ v < 1`: `bndOfU t = (8v-7, 1)`.  If `8v-7 = -1` (i.e. `v = 3/4`) this is the corner
  `(-1,1)` and `uPerim = (5+1)/8 = 3/4 = v`; otherwise `q 0 ∈ (-1,1)`, `q 1 = 1` give
  `uPerim = (7+(8v-7))/8 = v`.

The proof simply unfolds both definitions and lets the case distinctions of the two `if`-chains
meet; every resulting goal is a linear identity in `v` (discharged by `linarith`), except for the
four `if`-branches that the first coordinate already contradicts, which are closed by the
inconsistency of their own hypotheses. -/
theorem uPerim_bndOfU (t : ℝ) : uPerim (bndOfU t) = Int.fract t := by
  have hv0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have hv1 : Int.fract t < 1 := Int.fract_lt_one t
  simp only [bndOfU, uPerim]
  split_ifs
  all_goals (simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at *)
  all_goals (first | linarith | (exfalso; simp_all only [not_true_eq_false]))

end Work.Cusp
