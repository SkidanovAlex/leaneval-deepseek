import Mathlib
import Submission.Work.ELNest.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

/-- The level `Qlev L n = L ^ (1/1024^n)` is `> 1` for `L > 1`, and the levels strictly
decrease: `Qlev L (n+1) < Qlev L n`. -/
theorem Qlev_facts {L : ℝ} (hL : 1 < L) (n : ℕ) :
    1 < Work.ELNest.Qlev L n ∧ Work.ELNest.Qlev L (n + 1) < Work.ELNest.Qlev L n := by
  have h1024 : (1 : ℝ) < 1024 := by norm_num
  have hpos : (0 : ℝ) < (1024 : ℝ) ^ n := pow_pos (by norm_num) n
  have hlt : (1024 : ℝ) ^ n < (1024 : ℝ) ^ (n + 1) :=
    pow_lt_pow_right₀ h1024 (Nat.lt_succ_self n)
  constructor
  · exact Real.one_lt_rpow hL (by positivity)
  · rw [Work.ELNest.Qlev, Work.ELNest.Qlev, Real.rpow_lt_rpow_left_iff hL]
    exact one_div_lt_one_div_of_lt hpos hlt

end Work.ELNest
