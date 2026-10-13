import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.InterpBrickAux

/-- **The `ℋ⁰`-density of a function of `SmoothOpen` is the unweighted density.**
For `θ ∈ Iθ = [0,π/2]` the `k = 0` integrand reduces to
`(F z θ)² · w(z)² · sin(2θ)^{-η}`: the plain `D_z^0 = id` term is the only one occurring
(no mixed derivative appears at level `0`), and the `θ`-weight square
`(sin(2θ)^{η/2})² = sin(2θ)^{η}` is converted using `sin(2θ) ≥ 0`. -/
private theorem hkDensity_pointwise (α : ℝ) (F : ℝ → ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) ?_
    have := Real.pi_pos
    linarith [hθ.2]
  -- `(sin(2θ)^{η/2})² = sin(2θ)^{η}`
  have hpow : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    congr 1
    ring
  -- `sin(2θ)^{-η} = (sin(2θ)^{η})⁻¹`
  have hneg : Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
      = (Real.sin (2 * θ) ^ Work.Spaces.eta)⁻¹ :=
    Real.rpow_neg hs Work.Spaces.eta
  simp only [Work.Spaces.HkIntegrand]
  norm_num [Finset.sum_range_one]
  rw [mul_pow, div_pow, hpow, div_eq_mul_inv, hneg]
  ring

theorem hkDensity_prod_integrable {α : ℝ} {F : ℝ → ℝ → ℝ} (hF : Work.Spaces.HkMem α 0 F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- The `ℋ⁰`-integrand is integrable on the product: nonnegative, continuous on the open
  -- quadrant (so a.e. strongly measurable), with integrable slices and integrable iterated
  -- integral by `HkMem α 0 F`.  This is `integrable_prod_of_iterated`.
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 0 F z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 0 F z θ
  have hAE : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α 0 F z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hsm.continuousOn_HkIntegrand α 0)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 0 F z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hF.1 z hz
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α 0 F z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hF.2
  obtain ⟨hint, -⟩ := Work.Spaces.integrable_prod_of_iterated hnn hAE hslice houter
  -- On `Iz ×ˢ Iθ` the two densities agree pointwise.
  refine hint.congr ?_
  rw [MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) fun p hp => ?_
  exact hkDensity_pointwise α F hp.2 p.1

end Work.FTS.EllipticEst.Cores.InterpBrickAux
