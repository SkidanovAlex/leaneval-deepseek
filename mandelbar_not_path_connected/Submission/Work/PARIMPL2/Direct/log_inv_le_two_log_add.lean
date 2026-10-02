import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- For `lam > 0` and `R ≥ 1` the quantity `log (1/lam)` is controlled by
`2 log R` plus the first-order term `1/(lam R^2)`. -/
theorem log_inv_le_two_log_add (lam R : ℝ) (hlam : 0 < lam) (hR : 1 ≤ R) (hlamR : lam * R ^ 2 ≤ 1) :
    Real.log (1 / lam) ≤ 2 * Real.log R + 1 / (lam * R ^ 2) := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hR2pos : 0 < R ^ 2 := pow_pos hRpos 2
  have hprod : 0 < lam * R ^ 2 := mul_pos hlam hR2pos
  have htpos : 0 < 1 / (lam * R ^ 2) := div_pos one_pos hprod
  have hkey : 1 / lam = R ^ 2 * (1 / (lam * R ^ 2)) := by
    field_simp
  rw [hkey, Real.log_mul (ne_of_gt hR2pos) (ne_of_gt htpos), Real.log_pow]
  have hlog : Real.log (1 / (lam * R ^ 2)) ≤ 1 / (lam * R ^ 2) := by
    have := Real.log_le_sub_one_of_pos htpos
    linarith
  push_cast
  linarith

end Work.PARIMPL2.Direct
