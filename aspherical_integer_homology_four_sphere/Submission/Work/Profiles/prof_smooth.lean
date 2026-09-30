import Mathlib
import Submission.Work.Profiles.Basic
import Submission.Work.Profiles.Eta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Profiles

open scoped ContDiff Convolution
open MeasureTheory

/-- The smoothing `prof F η x = ∫ t, F (x - t) η t` of a continuous function `F` against a
smooth compactly supported bump `η` is again `C^∞`: it is the convolution
`η ⋆[lsmul ℝ ℝ, volume] F`, and a convolution is `C^n` as soon as one factor is `C^n` with
compact support and the other is locally integrable. -/
theorem prof_smooth {F η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hF : Continuous F) : ContDiff ℝ ∞ (prof F η) := by
  have h := HasCompactSupport.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := volume) (n := ⊤) hηc hη hF.locallyIntegrable
  convert h using 1
  ext x
  simp [prof, convolution, smul_eq_mul, mul_comm]

end Work.Profiles
