import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.psiP_div_cos_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Auxiliary facts for the small-`z` kernel bound -/

/-- `β + 4 = 3/α + 3 > 0` whenever `0 < α`. -/
theorem beta_add_four_pos {α : ℝ} (hα : 0 < α) : (0 : ℝ) < beta α + 4 := by
  have h : (0 : ℝ) < 3 / α := div_pos (by norm_num) hα
  rw [beta]
  linarith

/-- **Pointwise domination on the small-`z` range.**  For `0 < α` and `0 < t ≤ z`,
`t^β M₁(t) ≤ z^{β+4} A(t)`, where `M₁ = mom U` and `A = mass α U`.

Indeed `M₁(t) = A(t)/w(t)² ≤ t⁴A(t)` (`mom_le_mass_mul_z4`), so
`t^β M₁(t) ≤ t^{β+4}A(t)`, and `t^{β+4} ≤ z^{β+4}` since `β + 4 = 3/α + 3 > 0`. -/
theorem rpow_beta_mul_mom_le {α : ℝ} (hα : 0 < α) (U : ℝ → ℝ → ℝ) {z t : ℝ}
    (ht : 0 < t) (htz : t ≤ z) :
    t ^ (beta α) * mom U t ≤ z ^ (beta α + 4) * mass α U t := by
  have hβ4 : (0 : ℝ) < beta α + 4 := beta_add_four_pos hα
  have hβt : 0 ≤ t ^ (beta α) := Real.rpow_nonneg (le_of_lt ht) _
  have hmom : mom U t ≤ t ^ 4 * mass α U t := mom_le_mass_mul_z4 α U ht
  have hmassnn : 0 ≤ mass α U t := mass_nonneg α U t
  have hkey : t ^ (beta α) * (t ^ 4 * mass α U t) = t ^ (beta α + 4) * mass α U t := by
    rw [← Real.rpow_natCast t 4, ← mul_assoc, ← Real.rpow_add ht]
    norm_num
  have h3 : t ^ (beta α + 4) ≤ z ^ (beta α + 4) :=
    Real.rpow_le_rpow (le_of_lt ht) htz (le_of_lt hβ4)
  calc t ^ (beta α) * mom U t
      ≤ t ^ (beta α) * (t ^ 4 * mass α U t) := mul_le_mul_of_nonneg_left hmom hβt
    _ = t ^ (beta α + 4) * mass α U t := hkey
    _ ≤ z ^ (beta α + 4) * mass α U t := mul_le_mul_of_nonneg_right h3 hmassnn

/-- **The inner integral bound.**  For `0 < α`, `U ∈ ℋ⁰` and `0 < z`,
`∫₀^z t^β M₁(t) dt ≤ z^{β+4} · HkSq α 0 U`.

The integrand is dominated on `(0,z]` by `z^{β+4}A(t)` (previous lemma), and
`∫_{(0,z)} A ≤ ∫_{(0,∞)} A = HkSq α 0 U` by monotonicity of the integral in the domain
(`setIntegral_mono_set`) and `mass_Ioi_eq_HkSq`. -/
theorem integral_rpow_mom_le {α : ℝ} (hα : 0 < α) {U : ℝ → ℝ → ℝ}
    (hU : Work.Spaces.HkMem α 0 U) {z : ℝ} (h1 : 0 < z) :
    (∫ t in (0 : ℝ)..z, t ^ (beta α) * mom U t)
      ≤ z ^ (beta α + 4) * Work.Spaces.HkSq α 0 U := by
  have hle : (0 : ℝ) ≤ z := le_of_lt h1
  have hmassIoc : IntegrableOn (mass α U) (Set.Ioc (0 : ℝ) z) :=
    (mass_integrableOn α U hU).mono_set Set.Ioc_subset_Ioi_self
  have hgint : Integrable (fun t => z ^ (beta α + 4) * mass α U t)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    hmassIoc.const_mul _
  have hfnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) z)]
      (fun t => t ^ (beta α) * mom U t) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht.1) _) (mom_nonneg U t)
  have hleae : (fun t => t ^ (beta α) * mom U t) ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) z)]
      (fun t => z ^ (beta α + 4) * mass α U t) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
      rpow_beta_mul_mom_le hα U ht.1 ht.2
  have hmono := MeasureTheory.integral_mono_of_nonneg hfnn hgint hleae
  have hmono_set :
      (∫ t in Set.Ioc (0 : ℝ) z, mass α U t) ≤ ∫ t in Set.Ioi (0 : ℝ), mass α U t :=
    MeasureTheory.setIntegral_mono_set (mass_integrableOn α U hU)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => mass_nonneg α U t)
      (Filter.Eventually.of_forall fun t ht => ht.1)
  have hzpow : 0 ≤ z ^ (beta α + 4) := Real.rpow_nonneg hle _
  calc (∫ t in (0 : ℝ)..z, t ^ (beta α) * mom U t)
      = ∫ t in Set.Ioc (0 : ℝ) z, t ^ (beta α) * mom U t :=
        intervalIntegral.integral_of_le hle
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) z, z ^ (beta α + 4) * mass α U t := hmono
    _ = z ^ (beta α + 4) * ∫ t in Set.Ioc (0 : ℝ) z, mass α U t :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ z ^ (beta α + 4) * ∫ t in Set.Ioi (0 : ℝ), mass α U t :=
        mul_le_mul_of_nonneg_left hmono_set hzpow
    _ = z ^ (beta α + 4) * Work.Spaces.HkSq α 0 U := by rw [mass_Ioi_eq_HkSq]

/-! ## The target -/

/-- **Small-`z` bound for the kernel integral.**  For `0 < α`, `U ∈ ℋ⁰` and `0 < z`:
`∫₀¹ v^β M₁(zv) dv ≤ z³ · HkSq α 0 U` (`β = 3/α - 1`, `M₁ = mom U`).

Route: `mom_subst` turns the left side into `z^{-(β+1)}∫₀^z t^β M₁(t) dt`; the pointwise
`M₁(t) = A(t)/w(t)² ≤ t⁴A(t)` for `t > 0` (`mom_le_mass_mul_z4` in pointwise form,
`mass_eq_w2_mom`, where `A = mass α U`) gives `t^β M₁(t) ≤ t^{β+4}A(t) ≤ z^{β+4}A(t)` for
`0 < t ≤ z` (as `β + 4 = 3/α + 3 > 0`), so the inner integral is
`≤ z^{β+4}∫_{(0,z)} A ≤ z^{β+4} HkSq α 0 U` (`setIntegral_mono_set` against
`mass_Ioi_eq_HkSq`, `mass_integrableOn`), and `z^{-(β+1)}·z^{β+4} = z³`. -/
theorem kernel_le_small {α : ℝ} (hα : 0 < α) {U : ℝ → ℝ → ℝ}
    (hU : Work.Spaces.HkMem α 0 U) {z : ℝ} (h1 : 0 < z) :
    (∫ v in (0 : ℝ)..1, v ^ (Work.FTS_EllLimOK.ProducerH.beta α)
        * Work.FTS_EllLimOK.ProducerH.mom U (z * v))
      ≤ z ^ 3 * Work.Spaces.HkSq α 0 U := by
  have hpow : 0 < z ^ (-(beta α + 1)) := Real.rpow_pos_of_pos h1 _
  rw [mom_subst α U h1]
  calc z ^ (-(beta α + 1)) * (∫ t in (0 : ℝ)..z, t ^ (beta α) * mom U t)
      ≤ z ^ (-(beta α + 1)) * (z ^ (beta α + 4) * Work.Spaces.HkSq α 0 U) :=
        mul_le_mul_of_nonneg_left (integral_rpow_mom_le hα hU h1) (le_of_lt hpow)
    _ = z ^ 3 * Work.Spaces.HkSq α 0 U := by
        rw [← mul_assoc, ← Real.rpow_add h1]
        norm_num

end Work.FTS_EllLimOK.ProducerH
