import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Complex Function

set_option linter.unusedVariables false

namespace Work.MRMT.Found

/-- The `dz`-moments of a compactly supported `C¹` function: the integral of an affine
function of `u` and `star u` against `dz η` is determined by the three moments
`∫ dz η`, `∫ u * dz η`, `∫ star u * dz η`.  With the normalisation `∫ dz η = 0`,
`∫ u * dz η = -1`, `∫ star u * dz η = 0`, the pair `(a, b)` contributes `-a`. -/
theorem integral_affine_mul_dz {η : ℂ → ℂ} (hη : ContDiff ℝ 1 η) (hηs : HasCompactSupport η)
    (hηI : MeasureTheory.Integrable (fun u => Work.MRMT.dz η u))
    (hηu : MeasureTheory.Integrable (fun u => u * Work.MRMT.dz η u))
    (hηc : MeasureTheory.Integrable (fun u => (starRingEnd ℂ) u * Work.MRMT.dz η u))
    (hd0 : ∫ u, Work.MRMT.dz η u = 0)
    (hm1 : ∫ u, u * Work.MRMT.dz η u = -1)
    (hm2 : ∫ u, (starRingEnd ℂ) u * Work.MRMT.dz η u = 0)
    (c a b : ℂ) (e : ℂ → ℂ) (he : Continuous e)
    (heI : MeasureTheory.Integrable (fun u => e u * Work.MRMT.dz η u)) :
    ∫ u, (c + (a * u + b * (starRingEnd ℂ) u) + e u) * Work.MRMT.dz η u
      = -a + ∫ u, e u * Work.MRMT.dz η u := by
  have hA : MeasureTheory.Integrable (fun u => c * Work.MRMT.dz η u) := hηI.const_mul c
  have hB1 : MeasureTheory.Integrable (fun u => a * (u * Work.MRMT.dz η u)) := hηu.const_mul a
  have hB2 : MeasureTheory.Integrable (fun u => b * ((starRingEnd ℂ) u * Work.MRMT.dz η u)) :=
    hηc.const_mul b
  have hB12 : MeasureTheory.Integrable (fun u => a * (u * Work.MRMT.dz η u)
      + b * ((starRingEnd ℂ) u * Work.MRMT.dz η u)) :=
    (hB1.add hB2).congr (by filter_upwards with u; rfl)
  have hAB : MeasureTheory.Integrable (fun u => c * Work.MRMT.dz η u +
      (a * (u * Work.MRMT.dz η u) + b * ((starRingEnd ℂ) u * Work.MRMT.dz η u))) :=
    (hA.add hB12).congr (by filter_upwards with u; rfl)
  have hfun : (fun u => (c + (a * u + b * (starRingEnd ℂ) u) + e u) * Work.MRMT.dz η u)
      = fun u => c * Work.MRMT.dz η u +
          (a * (u * Work.MRMT.dz η u) + b * ((starRingEnd ℂ) u * Work.MRMT.dz η u))
          + e u * Work.MRMT.dz η u := by
    funext u; ring
  rw [hfun]
  rw [integral_add hAB heI, integral_add hA hB12, integral_add hB1 hB2,
      integral_const_mul c, integral_const_mul a, integral_const_mul b,
      hd0, hm1, hm2]
  ring

end Work.MRMT.Found
