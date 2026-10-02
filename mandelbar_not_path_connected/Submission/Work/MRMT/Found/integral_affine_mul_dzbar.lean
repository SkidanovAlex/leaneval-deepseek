import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- Linearity of the Bochner integral against `∂̄η`: for a smooth compactly supported `η` whose
`∂̄`-moments are normalised (`∫ ∂̄η = 0`, `∫ u ∂̄η = 0`, `∫ ū ∂̄η = -1`), the integral of an affine
combination `c + a u + b ū` against `∂̄η` is `-b`, and an arbitrary additional (integrable) term
`e` passes through additively. -/
theorem integral_affine_mul_dzbar {η : ℂ → ℂ} (hη : ContDiff ℝ 1 η) (hηs : HasCompactSupport η)
    (hηI : MeasureTheory.Integrable (fun u => Work.MRMT.dzbar η u))
    (hηu : MeasureTheory.Integrable (fun u => u * Work.MRMT.dzbar η u))
    (hηc : MeasureTheory.Integrable (fun u => (starRingEnd ℂ) u * Work.MRMT.dzbar η u))
    (hd0 : ∫ u, Work.MRMT.dzbar η u = 0)
    (hm1 : ∫ u, u * Work.MRMT.dzbar η u = 0)
    (hm2 : ∫ u, (starRingEnd ℂ) u * Work.MRMT.dzbar η u = -1)
    (c a b : ℂ) (e : ℂ → ℂ) (he : Continuous e)
    (heI : MeasureTheory.Integrable (fun u => e u * Work.MRMT.dzbar η u)) :
    ∫ u, (c + (a * u + b * (starRingEnd ℂ) u) + e u) * Work.MRMT.dzbar η u
      = -b + ∫ u, e u * Work.MRMT.dzbar η u := by
  -- Integrability of the four pieces of the expanded integrand.
  have h1 : MeasureTheory.Integrable (fun u => c * Work.MRMT.dzbar η u) := hηI.const_mul c
  have h2 : MeasureTheory.Integrable (fun u => a * (u * Work.MRMT.dzbar η u)) := hηu.const_mul a
  have h3 : MeasureTheory.Integrable (fun u => b * ((starRingEnd ℂ) u * Work.MRMT.dzbar η u)) :=
    hηc.const_mul b
  have h4 : MeasureTheory.Integrable (fun u => e u * Work.MRMT.dzbar η u) := heI
  -- Expand the integrand pointwise.
  have hcongr : (fun u => (c + (a * u + b * (starRingEnd ℂ) u) + e u) * Work.MRMT.dzbar η u)
      = fun u => c * Work.MRMT.dzbar η u + a * (u * Work.MRMT.dzbar η u)
          + b * ((starRingEnd ℂ) u * Work.MRMT.dzbar η u) + e u * Work.MRMT.dzbar η u := by
    funext u; ring
  rw [hcongr]
  -- Split the integral additively.
  rw [MeasureTheory.integral_add (f := fun u => c * Work.MRMT.dzbar η u + a * (u * Work.MRMT.dzbar η u)
        + b * ((starRingEnd ℂ) u * Work.MRMT.dzbar η u)) (g := fun u => e u * Work.MRMT.dzbar η u)
        ((h1.add h2).add h3) h4]
  rw [MeasureTheory.integral_add (f := fun u => c * Work.MRMT.dzbar η u + a * (u * Work.MRMT.dzbar η u))
        (g := fun u => b * ((starRingEnd ℂ) u * Work.MRMT.dzbar η u)) (h1.add h2) h3]
  rw [MeasureTheory.integral_add (f := fun u => c * Work.MRMT.dzbar η u)
        (g := fun u => a * (u * Work.MRMT.dzbar η u)) h1 h2]
  -- Pull out the constants and use the moment normalisations.
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hd0, hm1, hm2]
  ring

end Work.MRMT.Found
