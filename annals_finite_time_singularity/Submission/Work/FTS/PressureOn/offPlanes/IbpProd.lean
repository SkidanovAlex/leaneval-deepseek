import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.PressureOn.offPlanes.Ibp1D

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integration by parts with one exceptional hyperplane, in product form

`Work.FTS.PressureOn.offPlanes.ibp_off_plane_prod`: the `(E × ℝ)`-version of
`ibp_except_zero`, obtained by Fubini (`MeasureTheory.integral_prod`) and the fibrewise
one-dimensional statement.  The exceptional set is the hyperplane `{t = 0}`.
-/

open MeasureTheory Filter Topology

namespace Work.FTS.PressureOn.offPlanes

theorem ibp_off_plane_prod {E : Type*} [MeasurableSpace E] [MeasureSpace E]
    {μ : Measure E} [SFinite μ]
    {G Gp Ψ Ψp : E × ℝ → ℝ}
    (hΨGp : Integrable (fun p => Ψ p * Gp p) (μ.prod volume))
    (hΨpG : Integrable (fun p => Ψp p * G p) (μ.prod volume))
    (hGc : ∀ᵐ y ∂μ, Continuous (fun t => G (y, t)))
    (hΨc : ∀ᵐ y ∂μ, Continuous (fun t => Ψ (y, t)))
    (hΨd : ∀ᵐ y ∂μ, ∀ t, HasDerivAt (fun s => Ψ (y, s)) (Ψp (y, t)) t)
    (hGd : ∀ᵐ y ∂μ, ∀ t, t ≠ 0 → HasDerivAt (fun s => G (y, s)) (Gp (y, t)) t)
    (hbot : ∀ᵐ y ∂μ, Tendsto (fun t => Ψ (y, t) * G (y, t)) atBot (𝓝 0))
    (htop : ∀ᵐ y ∂μ, Tendsto (fun t => Ψ (y, t) * G (y, t)) atTop (𝓝 0)) :
    ∫ p, Ψ p * Gp p ∂(μ.prod volume) = -∫ p, Ψp p * G p ∂(μ.prod volume) := by
  have h1 : ∫ p, Ψ p * Gp p ∂(μ.prod volume)
      = ∫ y, (∫ t, Ψ (y, t) * Gp (y, t)) ∂μ := integral_prod _ hΨGp
  have h2 : ∫ p, Ψp p * G p ∂(μ.prod volume)
      = ∫ y, (∫ t, Ψp (y, t) * G (y, t)) ∂μ := integral_prod _ hΨpG
  rw [h1, h2, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hΨGp.prod_right_ae, hΨpG.prod_right_ae, hGc, hΨc, hΨd, hGd, hbot, htop]
    with y h1y h2y hcy hcy' hdy hdy' hby hty
  exact ibp_except_zero hdy hdy' hcy hcy' h1y h2y hby hty

end Work.FTS.PressureOn.offPlanes
