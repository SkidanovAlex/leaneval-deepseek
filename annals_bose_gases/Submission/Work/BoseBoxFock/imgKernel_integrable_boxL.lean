import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.uncurry_pairImg_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgKernel_integrable_boxL`

Joint integrability of the periodised lattice-images pair kernel
`imgKernel ℓ W a b = χ_ℓ(a)·(Σ'_{m≠0} W(a - b + ℓ•m))·χ_ℓ(b)` (for `W` an `L¹` one-body kernel
supported in `‖u‖ < R`, `R ≤ ℓ/2`) **with respect to the product of the two restricted
box-measures** `volume.restrict (boxL ℓ)`.

This is the box-restricted form of the second conjunct of the already-proved
`Work.BoseBoxFock.uncurry_pairImg_integrable` (which gives integrability w.r.t. the unrestricted
product measure `volume.prod volume`).  The passage to the product of the two restrictions is
monotonicity of the integral: for nonnegative integrands, `∫⁻ g ∂(μ.restrict s) ≤ ∫⁻ g ∂μ`, and
`Measure.prod` is monotone in its two arguments (`Measure.prod_mono`), so
`(volume.restrict s).prod (volume.restrict s) ≤ volume.prod volume`; then
`Integrable.mono_measure` transfers integrability from the larger measure to the smaller.

The hypotheses `hR : 0 ≤ R` and `hRℓ : R ≤ ℓ/2` are not needed by this route (they are part of the
caller's ambient setting); the support hypothesis `hWs` is exactly what
`uncurry_pairImg_integrable` consumes.
-/

namespace Work.BoseBoxFock

theorem imgKernel_integrable_boxL {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hR : 0 ≤ R) (hRℓ : R ≤ ℓ / 2)
    (hWs : ∀ u : EuclideanSpace ℝ (Fin 3), R ≤ ‖u‖ → W u = 0) :
    MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBoxFock.imgKernel ℓ W q.1 q.2)
      ((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))) := by
  -- `uncurry_pairImg_integrable` gives integrability w.r.t. the unrestricted product measure;
  -- the product of the two restrictions is a sub-measure of it.
  refine (uncurry_pairImg_integrable hℓ hWi hWs).2.mono_measure ?_
  exact MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self
    MeasureTheory.Measure.restrict_le_self

end Work.BoseBoxFock
