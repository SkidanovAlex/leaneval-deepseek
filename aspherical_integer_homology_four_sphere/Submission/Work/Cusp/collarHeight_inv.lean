import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

theorem collarHeight_inv (t b s : ℝ) (hb : 0 < b) (hb' : b ≠ sJ) (h : s = collarHeight t b) :
    t = 1 + (Real.log s - Real.log b) / (2 * (Real.log b - Real.log sJ)) := by
  have hsJ : 0 < sJ := Real.exp_pos _
  have hd : Real.log b - Real.log sJ ≠ 0 := by
    intro hd0
    have hbd : Real.log b = Real.log sJ := sub_eq_zero.mp hd0
    exact hb' (Real.log_injOn_pos hb hsJ hbd)
  have hlog : Real.log s = (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ := by
    rw [h, collarHeight, Real.log_exp]
  have key : Real.log s - Real.log b = 2 * (t - 1) * (Real.log b - Real.log sJ) := by
    rw [hlog]; ring
  have h2d : 2 * (Real.log b - Real.log sJ) ≠ 0 := mul_ne_zero (by norm_num) hd
  rw [key, show 2 * (t - 1) * (Real.log b - Real.log sJ)
        = (t - 1) * (2 * (Real.log b - Real.log sJ)) by ring,
      mul_div_cancel_right₀ _ h2d]
  ring

end Work.Cusp
