import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- For a function on a finite-measure space, the `L²` seminorm is controlled by the essential
supremum times the square root of the total measure. -/
theorem eLpNorm_two_le_ofReal_sqrt_mul_eLpNorm_top {f : ℂ → ℂ} {ν : MeasureTheory.Measure ℂ} (hν : ν Set.univ < ⊤) (hf : MeasureTheory.AEStronglyMeasurable f ν) : MeasureTheory.eLpNorm f 2 ν ≤ ENNReal.ofReal (Real.sqrt ((ν Set.univ).toReal)) * MeasureTheory.eLpNorm f ⊤ ν := by
  have hν_ne_top : ν Set.univ ≠ ⊤ := ne_of_lt hν
  have hpow : (ν Set.univ) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt ((ν Set.univ).toReal)) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hν_ne_top]
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num)]
  calc MeasureTheory.eLpNorm f 2 ν
      ≤ MeasureTheory.eLpNorm f ⊤ ν * (ν Set.univ) ^ ((1 : ℝ) / 2) := by
        refine (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := ⊤) le_top hf).trans_eq ?_
        norm_num
    _ = ENNReal.ofReal (Real.sqrt ((ν Set.univ).toReal)) * MeasureTheory.eLpNorm f ⊤ ν := by
        rw [hpow, mul_comm]

end Work.MRMT.Found
