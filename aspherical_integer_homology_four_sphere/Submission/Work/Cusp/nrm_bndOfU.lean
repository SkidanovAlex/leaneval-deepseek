import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The point `bndOfU t` of the boundary circle `∂Sq` has sup norm `1`.

`bndOfU t` depends only on `v = Int.fract t ∈ [0,1)`, and traverses the four edges of the square in
the four sub-intervals of `[0,1)`: in each case one coordinate is `±1` and the other one has absolute
value `≤ 1`.  Concretely, with `v = Int.fract t`:

* `v < 1/4`: `bndOfU t = (1, 1-8v)` and `|1-8v| ≤ 1` since `0 ≤ 8v < 2`;
* `1/4 ≤ v < 1/2`: `bndOfU t = (3-8v, -1)` and `|3-8v| ≤ 1` since `2 ≤ 8v < 4`;
* `1/2 ≤ v < 3/4`: `bndOfU t = (-1, 8v-5)` and `|8v-5| ≤ 1` since `4 ≤ 8v < 6`;
* `3/4 ≤ v < 1`: `bndOfU t = (8v-7, 1)` and `|8v-7| ≤ 1` since `6 ≤ 8v < 8`.

In every case `nrm (bndOfU t) = max |p 0| |p 1| = 1`. -/
theorem nrm_bndOfU (t : ℝ) : nrm (bndOfU t) = 1 := by
  have hv0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have hv1 : Int.fract t < 1 := Int.fract_lt_one t
  simp only [bndOfU, nrm]
  split_ifs with h1 h2 h3
  all_goals (simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, abs_one, abs_neg, max_eq_left_iff, max_eq_right_iff]; rw [abs_le]; constructor <;> linarith)

end Work.Cusp
