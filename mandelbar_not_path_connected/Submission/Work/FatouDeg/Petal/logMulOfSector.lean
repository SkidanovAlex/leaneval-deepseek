import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

theorem logMulOfSector {z w : ℂ} (hz : 0 < z.re) (hw : ‖w‖ ≤ 1 / 2) :
    Complex.log (z * (1 - w)) = Complex.log z + Complex.log (1 - w) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  have h1w_re : 0 < (1 - w).re := by
    have hw_re : w.re ≤ ‖w‖ := Complex.re_le_norm w
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have h1w0 : (1 - w) ≠ 0 := by
    intro h; rw [h] at h1w_re; simp at h1w_re
  refine Complex.log_mul hz0 h1w0 ?_
  have hza : |z.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hwa : |(1 - w).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h1w_re)
  rw [Set.mem_Ioc]
  constructor
  · rw [abs_lt] at hza hwa; linarith [hza.1, hwa.1]
  · rw [abs_lt] at hza hwa; linarith [hza.2, hwa.2]

end Work.FatouDeg.Petal
