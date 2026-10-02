import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- The glued map differs from the model `T_c` by `ε * χ z * q z`; hence, with `0 ≤ ε`,
`0 ≤ χ ≤ B`, its distance to `T_c` is at most `ε * ‖q z‖ * B`. -/
theorem norm_glueMap_sub_le (c : ℂ) (q : ℂ → ℂ) {ε : ℝ} (hε : 0 ≤ ε) {χ : ℂ → ℝ}
    {B : ℝ} (hχ0 : ∀ z : ℂ, 0 ≤ χ z) (hχ1 : ∀ z : ℂ, χ z ≤ B) :
    ∀ z : ℂ, ‖Work.FBif.glueMap c q ε χ z - LeanEval.ComplexAnalysis.Tantibar c z‖ ≤
      ε * ‖q z‖ * B := by
  intro z
  have hεn : ‖((ε : ℝ) : ℂ)‖ = ε := by simp [abs_of_nonneg hε]
  have hχn : ‖((χ z : ℝ) : ℂ)‖ = χ z := by simp [abs_of_nonneg (hχ0 z)]
  rw [glueMap_apply, add_sub_cancel_left, norm_mul, norm_mul, hεn, hχn]
  calc ε * χ z * ‖q z‖ ≤ ε * B * ‖q z‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hχ1 z) hε) (norm_nonneg _)
    _ = ε * ‖q z‖ * B := by ring

end Work.FBif
