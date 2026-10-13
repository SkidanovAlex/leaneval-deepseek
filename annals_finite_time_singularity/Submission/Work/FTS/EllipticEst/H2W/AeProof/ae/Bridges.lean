import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Bridges between the Bochner norm `HkSq` and its `∫⁻`-form

`HkSq α 0 g` is the iterated *Bochner* integral of `(g·w/σ^{1/2})²`.  Under the honesty
hypothesis `HkMem α 0 g` this is the honest value, and the identity

`ENNReal.ofReal (HkSq α 0 g) = ∫⁻_z ofReal (w z²) · (∫⁻_θ ofReal (g² σ))`

holds.  This is the form in which the `σ`-Poincaré upgrade (`AeSigmaUpgradeU_all`) and the
cut-off energy inequality are stated, so it is the bridge that lets the final arithmetic be done
in `ENNReal` and converted to the Bochner statement only at the very end.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

set_option autoImplicit false

/-- `σ θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.Spaces.Iθ] at hθ
  refine Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) ?_) _
  linarith [hθ.2, Real.pi_pos]

/-- **`HkSq α 0 g` as an `∫⁻`-integral**, for an honest `g`. -/
theorem ofReal_HkSq_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 0 g) :
    ENNReal.ofReal (Work.Spaces.HkSq α 0 g)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  have hHk : Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ := rfl
  rw [hHk]
  -- ## the outer bridge
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) :=
    Filter.Eventually.of_forall (fun z =>
      MeasureTheory.integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ))
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2 hnn]
  -- ## the inner bridge, a.e. in `z`
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
  have hslice : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 g z θ) Work.Spaces.Iθ := hmem.1 z hz
  have hnnθ : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 0 g z θ) :=
    Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hslice hnnθ]
  -- the constant `ofReal (w z²)` is pulled out of the inner `∫⁻`
  rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)) _
    ENNReal.ofReal_ne_top]
  -- the two inner integrands agree a.e. on `Iθ`
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hsEta : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Iθ hθ
  have hsq : 0 ≤ (g z θ) ^ 2 := sq_nonneg _
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq_Iθ α g hθ,
    show (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from by ring,
    ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z)), ENNReal.ofReal_mul hsq]

end Work.FTS.EllipticEst.H2W.AeProof.ae
