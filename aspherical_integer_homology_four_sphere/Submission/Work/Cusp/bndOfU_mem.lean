import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `bndOfU t` lies in the square `Sq = [-1,1]²`: the point of `∂Sq` with perimeter parameter
`frac t` has both coordinates in `[-1,1]`. -/
theorem bndOfU_mem (t : ℝ) : bndOfU t ∈ Sq := by
  have hv0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have hv1 : Int.fract t < 1 := Int.fract_lt_one t
  change |(bndOfU t) 0| ≤ 1 ∧ |(bndOfU t) 1| ≤ 1
  simp only [bndOfU]
  split_ifs with h1 h2 h3
  · constructor <;>
      simp only [abs_le', Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      constructor <;> linarith
  · constructor <;>
      simp only [abs_le', Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      constructor <;> linarith
  · constructor <;>
      simp only [abs_le', Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      constructor <;> linarith
  · constructor <;>
      simp only [abs_le', Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      constructor <;> linarith

end Work.Cusp
