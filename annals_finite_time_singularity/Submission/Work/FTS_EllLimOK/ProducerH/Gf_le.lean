import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS_EllLimOK.ProducerH.psiP_div_cos_defs
import Submission.Work.FTS_EllLimOK.ProducerH.Gf_le_defs
import Submission.Work.FTS_EllLimOK.ProducerH.GfKer_zslice
import Submission.Work.FTS_EllLimOK.ProducerH.GfKer_touter_le
import Submission.Work.FTS_EllLimOK.ProducerH.GfKer_aesm_slices
import Submission.Work.FTS.H2.HkSqSwap

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

/-- **Global bound for the radial density `Gf`.**  For `0 < α ≤ 1` (so `β = 3/α - 1 ≥ 2 > 0`) and
`U ∈ ℋ⁰`, the radial density
`Gf α U z = w(z)² ∫₀¹ v^β M₁(zv) dv` (with `M₁ = mom U`,
`M₁(z) = ∫_θ U(z,θ)² sin(2θ)^{-η}`) is integrable on `(0,∞)`, and

  `∫_{(0,∞)} Gf α U z dz ≤ (1/β) · HkSq α 0 U`.

Route (one interval substitution plus one Tonelli on a *product*; `M₁` never has to be composed
with `t ↦ zt`):

1. `∫₀¹ v^β M₁(zv) dv = z^{-(β+1)} ∫₀^z t^β M₁(t) dt` for `z > 0`
   (`Work.FTS_EllLimOK.ProducerH.mom_subst`, from
   `Work.FTS.PhiStar.RadialWAux.integral_zero_one_rpow`).
2. On `t > 0`, `M₁(t) = A(t)/w(t)²` where `A = mass α U z = ∫_θ HkIntegrand α 0 U z θ`
   (`mass_eq_w2_mom`), so `t^β M₁(t) = t^{β+4} A(t) / (1+t)^4` (as `w(t)² = (1+t)^4/t^4`,
   `w_sq_mul_z4`); the inner integral `∫₀^z …` is `∫_{t∈(0,∞)} … · 1_{t<z} dt` (interval integral
   `0..z` = set integral over `Ioc 0 z` = set integral over `(0,∞)` of the indicator).
3. Tonelli on `(0,∞) × (0,∞)`: `∫_z w(z)²z^{-(β+1)}∫_t t^{β+4}A(t)/(1+t)^4 1_{t<z} dt dz =
   ∫_t t^{β+4}A(t)/(1+t)^4 [∫_{z>t} w(z)²z^{-(β+1)} dz] dt`;
   use `Work.FTS.H2.swap_iterated_integral_of_nonneg` with the *`t`-variable as the outer one*
   (so that the integrability of the `z`-outer partially integrated function, i.e. of `Gf`, is a
   *conclusion*, not a hypothesis).  The joint a.e. strong measurability is assembled from
   `mass_aesm`/`AEStronglyMeasurable.comp_fst` (the `t`-factor), the continuous `z`-factor
   (`AEStronglyMeasurable.comp_snd`) and the Borel set `{(t,z) : t < z}`; the `z`-slice is
   integrable because `∫_{z>t} w(z)²z^{-(β+1)} dz ≤ w(t)² ∫_{z>t} z^{-(β+1)} dz = w(t)² t^{-β}/β`
   (using `(1+z)^4/z^4 ≤ (1+t)^4/t^4` for `z ≥ t` and `β > 0`), and the `t`-outer function is
   integrable because `t^{β+4}/(1+t)^4 · w(t)² t^{-β}/β = 1/β`, so it is dominated by `A(t)/β`,
   which is integrable by `hU` (`mass_integrableOn`).
4. `∫_{(0,∞)} A = HkSq α 0 U` (`mass_Ioi_eq_HkSq`). -/
theorem Gf_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {U : ℝ → ℝ → ℝ}
    (hU : Work.Spaces.HkMem α 0 U) :
    MeasureTheory.IntegrableOn (Work.FTS_EllLimOK.ProducerH.Gf α U) (Set.Ioi 0) ∧
      ∫ z in Set.Ioi (0 : ℝ), Work.FTS_EllLimOK.ProducerH.Gf α U z
        ≤ (1 / Work.FTS_EllLimOK.ProducerH.beta α) * Work.Spaces.HkSq α 0 U := by
  -- The Tonelli kernel and its three defining facts.
  have hnn : ∀ t z : ℝ, 0 ≤ GfKer α U t z := fun t z => GfKer_nonneg α U t z
  have haesm : AEStronglyMeasurable (Function.uncurry (GfKer α U))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
    (GfKer_aesm_slices hα hα1 hU).1
  have hsliceAll : ∀ t ∈ Set.Ioi (0 : ℝ),
      Integrable (fun z => GfKer α U t z) (volume.restrict (Set.Ioi 0)) :=
    (GfKer_aesm_slices hα hα1 hU).2
  have hslice : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      Integrable (fun z => GfKer α U t z) (volume.restrict (Set.Ioi 0)) :=
    ae_restrict_of_forall_mem measurableSet_Ioi hsliceAll
  have htz : ∀ t ∈ Set.Ioi (0 : ℝ),
      ∫ z in Set.Ioi 0, GfKer α U t z ≤ mass α U t / beta α :=
    fun t ht => GfKer_touter_le hα hα1 ht
  -- Integrability of the `t`-outer function, by domination by `A(t)/β`.
  have haesmOut : AEStronglyMeasurable
      (fun t => ∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
      (volume.restrict (Set.Ioi 0)) := by
    have h := haesm.integral_prod_right'
    simpa only [Function.uncurry] using h
  have hIntMass : Integrable (fun t => mass α U t / beta α)
      (volume.restrict (Set.Ioi 0)) :=
    (mass_integrableOn α U hU).div_const _
  have hbnd : (fun t => ∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
      ≤ᵐ[volume.restrict (Set.Ioi 0)] (fun t => mass α U t / beta α) :=
    ae_restrict_of_forall_mem measurableSet_Ioi htz
  have hnorm : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      ‖∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0))‖ ≤ mass α U t / beta α := by
    filter_upwards [hbnd] with t ht
    have hpos : 0 ≤ ∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)) :=
      integral_nonneg (fun z => GfKer_nonneg α U t z)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    exact ht
  have houter : Integrable (fun t => ∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
      (volume.restrict (Set.Ioi 0)) := hIntMass.mono' haesmOut hnorm
  -- Tonelli, with the `t`-variable outermost.
  obtain ⟨hswap, hIntZ, _⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := volume.restrict (Set.Ioi 0)) (ν := volume.restrict (Set.Ioi 0))
      (g := GfKer α U) hnn haesm hslice houter
  -- The `z`-slices of the kernel integrate back to `Gf`.
  have hzid : (fun z => ∫ t, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
      =ᵐ[volume.restrict (Set.Ioi 0)] Gf α U :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => GfKer_zslice (α := α) (U := U) hz)
  refine ⟨hIntZ.congr hzid, ?_⟩
  have hzid_int : ∫ z, Gf α U z ∂(volume.restrict (Set.Ioi 0))
      = ∫ z, (∫ t, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
          ∂(volume.restrict (Set.Ioi 0)) := (integral_congr_ae hzid).symm
  rw [hzid_int]
  calc ∫ z, (∫ t, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
        ∂(volume.restrict (Set.Ioi 0))
      = ∫ t, (∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
          ∂(volume.restrict (Set.Ioi 0)) := hswap
    _ ≤ ∫ t, mass α U t / beta α ∂(volume.restrict (Set.Ioi 0)) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun t =>
            integral_nonneg (fun z => GfKer_nonneg α U t z))) hIntMass hbnd
    _ = (∫ t, mass α U t ∂(volume.restrict (Set.Ioi 0))) / beta α := integral_div _ _
    _ = (1 / beta α) * Work.Spaces.HkSq α 0 U := by
        rw [mass_Ioi_eq_HkSq α U, div_eq_mul_inv, one_div]
        exact mul_comm _ _

end Work.FTS_EllLimOK.ProducerH
