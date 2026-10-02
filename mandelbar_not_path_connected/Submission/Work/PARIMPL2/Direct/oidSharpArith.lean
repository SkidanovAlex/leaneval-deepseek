import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Sharp arithmetic estimate used in the implosion endgame.

Reducing the difference of the two logarithms to a single constant,
`3 * log (2π/(lam*R)) - 3 * log (24/(5*(lam*R))) = 3 * log (5π/12)`,
and bounding `log (5π/12) ≥ 1 - 12/(5π) ≥ 1/5` (from `π > 3`), while
`4/R ≤ 4/128 = 1/32`, gives the claim with room to spare. -/
theorem oidSharpArith (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1) :
    4 / R + 3 * Real.log (24 / (5 * (lam * R))) ≤ 3 * Real.log (2 * Real.pi / (lam * R)) := by
  have _hlamR : lam * R ^ 2 ≤ 1 := hlamR
  have hRpos : 0 < R := by linarith
  have hx : 0 < lam * R := mul_pos hlam hRpos
  have hA : 0 < 24 / (5 * (lam * R)) := by positivity
  have hB : 0 < 5 * Real.pi / 12 := by positivity
  -- pull the two logarithm arguments into a common factor
  have hkey : 2 * Real.pi / (lam * R) = (5 * Real.pi / 12) * (24 / (5 * (lam * R))) := by
    field_simp
    ring
  rw [hkey, Real.log_mul (ne_of_gt hB) (ne_of_gt hA)]
  -- it remains to compare `4/R` with `3 * log (5π/12)`
  have h1 : 4 / R ≤ (1 : ℝ) / 32 := by
    rw [div_le_iff₀ hRpos]
    linarith
  have hy : 0 < 12 / (5 * Real.pi) := by positivity
  have hylog : Real.log (12 / (5 * Real.pi)) ≤ 12 / (5 * Real.pi) - 1 :=
    Real.log_le_sub_one_of_pos hy
  have hlog : Real.log (5 * Real.pi / 12) = - Real.log (12 / (5 * Real.pi)) := by
    rw [← inv_div 12 (5 * Real.pi), Real.log_inv]
  have hy_lt : 12 / (5 * Real.pi) < 4 / 5 := by
    have hp : (15 : ℝ) < 5 * Real.pi := by linarith [Real.pi_gt_three]
    have : (12 : ℝ) / (5 * Real.pi) < 12 / 15 :=
      div_lt_div_of_pos_left (by norm_num) (by norm_num) hp
    linarith
  have hlog5 : (1 : ℝ) / 5 ≤ Real.log (5 * Real.pi / 12) := by
    rw [hlog]
    linarith
  have h2 : (1 : ℝ) / 32 ≤ 3 * Real.log (5 * Real.pi / 12) := by linarith
  linarith

end Work.PARIMPL2.Direct
