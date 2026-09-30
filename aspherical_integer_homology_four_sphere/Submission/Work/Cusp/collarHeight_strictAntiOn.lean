import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- Helper: the exponent of `collarHeight` is strictly antitone on `ℝ` when `log b < log sJ`. -/
theorem collarHeight_exponent_strictAnti (b : ℝ) (hb : Real.log b < Real.log sJ) :
    StrictAnti fun t : ℝ => (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ := by
  intro t1 t2 ht
  have : (2 * t2 - 1) * Real.log b + (2 - 2 * t2) * Real.log sJ
      < (2 * t1 - 1) * Real.log b + (2 - 2 * t1) * Real.log sJ := by
    nlinarith [ht, hb]
  exact this

theorem collarHeight_strictAntiOn (b : ℝ) (hb : 0 < b) (hb' : b < sJ) :
    StrictAntiOn (fun t => collarHeight t b) Set.univ := by
  have hsJpos : 0 < sJ := Real.exp_pos (1 / 2)
  have hlog : Real.log b < Real.log sJ := Real.log_lt_log hb hb'
  have hanti := collarHeight_exponent_strictAnti b hlog
  intro t1 _ t2 _ ht
  simp only [collarHeight]
  exact Real.exp_lt_exp.mpr (hanti ht)

end Work.Cusp
