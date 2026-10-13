import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_integrable
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_integral_le
import Submission.Work.FTS.PhiStar.Honesty.aesm_uncurry_abs_pzF
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Real Topology

/-- The `t`-marginal of `|∂_zF|` is integrable on any interval of radii `[y,x]` with `y > 0`,
and the two iterated integrals agree: Tonelli/Fubini for the nonnegative measurable function
`(t,θ) ↦ |∂_zF t θ|`, whose angular slices are `L¹` by `slice_abs_integrable` and whose
`t`-marginals are dominated by `(∫_θ HkIntegrand α 1 F t θ)/y² + π/4` by
`slice_abs_integral_le`. -/
theorem integral_swap_pz_abs {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => ∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|))
        = ∫ t in Set.uIoc y x, (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|) := by
  rw [Set.uIoc_of_le hyx]
  -- the reference measure on the radial interval, and the fact that it lies in `Iz`
  have hsub : Set.Ioc y x ⊆ Work.Spaces.Iz := fun t ht =>
    le_of_lt (lt_trans hy ht.1)
  -- the marginal `t ↦ ∫_θ HkIntegrand α 1 F t θ` is `L¹` on the radial interval
  have hHIint : MeasureTheory.Integrable
      (fun t : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ)
      (MeasureTheory.volume.restrict (Set.Ioc y x)) :=
    hF.2.mono_set hsub
  -- the dominating function `W` is `L¹` on the radial interval
  have hWint : MeasureTheory.Integrable
      (fun t : ℝ => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) / y ^ 2
        + Real.pi / 4)
      (MeasureTheory.volume.restrict (Set.Ioc y x)) := by
    have h1 : MeasureTheory.Integrable
        (fun t : ℝ => (1 / y ^ 2) * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 1 F t θ))
        (MeasureTheory.volume.restrict (Set.Ioc y x)) := hHIint.const_mul _
    have h2 : MeasureTheory.Integrable (fun _ : ℝ => Real.pi / 4)
        (MeasureTheory.volume.restrict (Set.Ioc y x)) := MeasureTheory.integrable_const _
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun t => ?_)
    show (1 / y ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ)
        + Real.pi / 4
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) / y ^ 2 + Real.pi / 4
    ring
  -- joint a.e. strong measurability of `(t,θ) ↦ |∂_zF t θ|` on the product
  have hjointIcc : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun t θ : ℝ => |Work.Spaces.pz F t θ|))
      ((MeasureTheory.volume.restrict (Set.Icc y x)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aesm_uncurry_abs_pzF hsm hy
  have hmono : (MeasureTheory.volume.restrict (Set.Ioc y x)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict (Set.Icc y x)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl) le_rfl
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun t θ : ℝ => |Work.Spaces.pz F t θ|))
      ((MeasureTheory.volume.restrict (Set.Ioc y x)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hjointIcc.mono_measure hmono
  -- a.e. (in `t`) integrability of the angular slices
  have hslice : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc y x)),
      MeasureTheory.Integrable (fun θ : ℝ => |Work.Spaces.pz F t θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact (slice_abs_integrable hsm hF (lt_trans hy ht.1)).2
  -- integrability of the `t`-marginal
  have houter : MeasureTheory.Integrable
      (fun t : ℝ => ∫ θ, |Work.Spaces.pz F t θ|
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioc y x)) := by
    have haesm := hjoint.integral_prod_right'
    refine MeasureTheory.Integrable.mono' hWint haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => abs_nonneg _)]
    exact (slice_abs_integral_le hsm hF hy ht.1.le).2
  -- Tonelli/Fubini
  obtain ⟨hprod, hprod_eq⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict (Set.Ioc y x))
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun t θ : ℝ => |Work.Spaces.pz F t θ|) (fun t θ => abs_nonneg _) hjoint hslice houter
  refine ⟨?_, ?_⟩
  · exact hprod.integral_prod_right
  · have hsymm := MeasureTheory.integral_prod_symm
      (Function.uncurry (fun t θ : ℝ => |Work.Spaces.pz F t θ|)) hprod
    exact hsymm.symm.trans hprod_eq

end Work.FTS.PhiStar.Honesty
