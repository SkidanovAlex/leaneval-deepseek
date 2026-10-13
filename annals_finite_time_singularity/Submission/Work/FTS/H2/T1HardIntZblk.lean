import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-- Integrability on `Iθ` of the two `θ`-integrands of the `D_z`-slot `D_θ(D_z^4 g)·D_z^4 g·sin(2θ)^{-η}`
weighted by an arbitrary smooth `f`: at a fixed `z > 0`, both
`θ ↦ f(z,θ)·D_θ(D_z^4g)(z,θ)·D_z^4g(z,θ)·sin(2θ)^{-η}` and `θ ↦ (D_z^4g(z,θ))²·sin(2θ)^{-η}` are
integrable on `Iθ = [0,π/2]`.
Route: `f·D_θv·v·sin(2θ)^{-η} = sin(2θ)^{1-η}·(f·(∂_θv)·v)` with `1 - η > 0`, so it is
continuous on the compact `Iθ` (`Work.Coercivity.slice_pth_continuousOn`,
`Work.Coercivity.slice_continuousOn`, `Real.continuous_rpow_const`), hence integrable
(`ContinuousOn.integrableOn_compact`); and `v²·sin(2θ)^{-η}` is the product of the integrable
`sin(2θ)^{-η}` (`Work.Coercivity.integrableOn_sin_two_eta_neg`, or `Work.Spaces.sin_two_rpow`
with `-1 < -η ≤ 0`) with the continuous `v²` (`MeasureTheory.IntegrableOn.mul_continuousOn`,
`isCompact_Icc`). -/
theorem T1HardIntZblk (f g : ℝ → ℝ → ℝ) (hsmf : Work.Spaces.SmoothNbhd f)
    (hsmg : Work.Spaces.SmoothNbhd g) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => f z θ * Work.Spaces.Dth (Work.Spaces.DzIter 4 g) z θ
        * Work.Spaces.DzIter 4 g z θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 4 g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ := by
  -- `v = D_z^4 g` is again smooth on a neighbourhood of the closed quadrant.
  have hv : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter 4 g) :=
    Work.Spaces.SmoothNbhd.DzIter hsmg 4
  -- The weight `sin(2θ)^{-η}` is integrable on `Iθ` since `-1 < -η ≤ 0`.
  have hw := Work.Coercivity.integrableOn_sin_two_eta_neg
  constructor
  · -- First integrand: `f · D_θ v · v · sin(2θ)^{-η}`.
    -- The angular slice of `D_θ v = sin(2θ)·∂_θ v` is continuous on `Iθ`.
    have hDth : ContinuousOn (fun θ => Work.Spaces.Dth (Work.Spaces.DzIter 4 g) z θ)
        Work.Spaces.Iθ := by
      show ContinuousOn (fun θ => Real.sin (2 * θ)
        * Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ) Work.Spaces.Iθ
      exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (Work.Coercivity.slice_pth_continuousOn (Work.Spaces.DzIter 4 g) hv hz)
    -- Hence so is the whole `θ`-dependent factor `f · D_θ v · v`.
    have hcont : ContinuousOn (fun θ => f z θ * Work.Spaces.Dth (Work.Spaces.DzIter 4 g) z θ
        * Work.Spaces.DzIter 4 g z θ) Work.Spaces.Iθ :=
      ((Work.Coercivity.slice_continuousOn f hsmf hz).mul hDth).mul
        (Work.Coercivity.slice_continuousOn (Work.Spaces.DzIter 4 g) hv hz)
    -- Integrable weight times continuous factor on the compact `Iθ`.
    have h := hw.mul_continuousOn hcont isCompact_Icc
    exact h.congr_fun (fun θ _ => by ring) measurableSet_Icc
  · -- Second integrand: `v² · sin(2θ)^{-η}`, with `v²` continuous on the compact `Iθ`.
    have hcont : ContinuousOn (fun θ => (Work.Spaces.DzIter 4 g z θ) ^ 2) Work.Spaces.Iθ :=
      (Work.Coercivity.slice_continuousOn (Work.Spaces.DzIter 4 g) hv hz).pow 2
    have h := hw.mul_continuousOn hcont isCompact_Icc
    exact h.congr_fun (fun θ _ => by ring) measurableSet_Icc

end Work.FTS.H2
