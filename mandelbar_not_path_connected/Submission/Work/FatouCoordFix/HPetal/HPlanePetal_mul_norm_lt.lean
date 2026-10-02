import Mathlib
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoordFix.HPetal

/-- `u ∈ HPlanePetal M` means `M < Re (-1 / u)`.  Since `Re W ≤ ‖W‖`, this gives
`M < 1 / ‖u‖`, and multiplying by `‖u‖ > 0` yields `M * ‖u‖ < 1`. -/
theorem HPlanePetal_mul_norm_lt {M : ℝ} {u : ℂ} (hu : u ∈ Work.FatouCoordFix.HPlanePetal M) : M * ‖u‖ < 1 := by
  obtain ⟨hu0, huM⟩ := hu
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hlt : M < 1 / ‖u‖ := by
    have h : (-1 / u).re ≤ ‖(-1 / u : ℂ)‖ := Complex.re_le_norm _
    have h2 : ‖(-1 / u : ℂ)‖ = 1 / ‖u‖ := by simp
    linarith
  have h3 := mul_lt_mul_of_pos_right hlt hpos
  have h4 : (1 / ‖u‖) * ‖u‖ = (1 : ℝ) := by field_simp
  linarith [h3, h4]

end Work.FatouCoordFix.HPetal
