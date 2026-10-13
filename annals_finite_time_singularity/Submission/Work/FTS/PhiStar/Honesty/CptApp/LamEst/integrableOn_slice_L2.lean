import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.LamEst

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- The single `D_z`-summand of the `ℋ^k`-integrand is integrable in `z` once the angular
slice integral is taken:  for `F` smooth on the open quadrant and `F ∈ ℋ^k`,
`z ↦ ∫_θ (D_z^i F · w / sin(2θ)^{η/2})²` is integrable on `Iz`, for every `i ≤ k`.

The proof is a pure domination argument, exactly as in
`Work.FTS.EllipticEst.integrableOn_zSummand` and `Work.Blocks.slice_integrable_of_bound`:

* pointwise, `(D_z^iF · w/sin^{η/2})² ≤ HkIntegrand α k F` (`Work.Spaces.sq_le_HkIntegrand_z`),
  so for each `z ∈ Iz` the slice integral is bounded by `∫_θ HkIntegrand α k F z θ`;
* the majorant `z ↦ ∫_θ HkIntegrand α k F z θ` is integrable on `Iz` by `HkMem α k F`;
* the marginal `z ↦ ∫_θ (D_z^iF · w/sin^{η/2})²` is a.e. strongly measurable because the
  uncurried integrand is continuous on the open quadrant, hence a.e. strongly measurable for
  the product of the restricted measures (`Work.Spaces.aesm_of_continuousOn_Qd`), and
  `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` integrates out `θ`. -/
theorem integrableOn_slice_L2 {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    {i : ℕ} (hi : i ≤ k) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))^2)
      Work.Spaces.Iz := by
  -- a.e. strong measurability of the marginal, from continuity of the integrand on `Q0`
  have hX : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i F p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ ((hsm.continuousOn_summand i).pow 2)
  have hInner : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hX.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa using h
  refine MeasureTheory.Integrable.mono' hF.2 hInner ?_
  -- the pointwise domination, for a.e. `z` (namely for `z ∈ Iz`)
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) (fun z hz => ?_)
  have hle : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hF.1 z hz)
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.sq_le_HkIntegrand_z α k F z θ i hi)
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
  exact hle

end Work.FTS.PhiStar.Honesty.CptApp.LamEst
