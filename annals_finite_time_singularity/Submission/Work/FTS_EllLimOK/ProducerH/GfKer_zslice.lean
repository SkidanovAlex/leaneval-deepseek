import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.Gf_le_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `z`-slice of the Tonelli kernel of `Gf`

The joint kernel of the Tonelli step computing `Gf α U z = w(z)² ∫₀¹ v^β M₁(zv) dv` is

  `GfKer α U t z = 1_{t<z} · ζ(z) · φ(t)`   (`ζ = GfZeta`, `φ = GfPhi`).

Here we prove the identity that identifies the `z`-slice of that kernel with `Gf`:

  `∫_{(0,∞)} GfKer α U t z dt = Gf α U z`   for `z > 0`,

with **no** regularity hypothesis on `U` (both the substitution `t = zv`, `mom_subst`, and the
indicator/pull-out steps are exact identities of Bochner integrals).  The pointwise input is

  `GfPhi α U t = t^β M₁(t)`   for `t > 0`   (`GfPhi_eq_rpow_mom`),

which combines `GfPhi_eq_of_pos`, `mass_eq_w2_mom` and `w_sq_mul_z4`.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

/-- On `t > 0` the `t`-factor of the Tonelli kernel is exactly `t^β M₁(t)`. -/
theorem GfPhi_eq_rpow_mom (α : ℝ) (U : ℝ → ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    GfPhi α U t = t ^ beta α * mom U t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hw2 : (Work.Spaces.w t) ^ 2 = (1 + t) ^ 4 / t ^ 4 := by
    rw [eq_div_iff (pow_ne_zero 4 ht0), w_sq_mul_z4 ht0]
  rw [GfPhi_eq_of_pos α U ht, mass_eq_w2_mom, hw2, Real.rpow_add ht]
  field_simp
  rw [Real.rpow_ofNat]

/-- The `0..z` form of the inner integral of `Gf`, obtained from the substitution `t = zv`. -/
theorem integral_zero_z_eq (α : ℝ) (U : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ t in (0 : ℝ)..z, t ^ beta α * mom U t
      = z ^ (beta α + 1) * ∫ v in (0 : ℝ)..1, v ^ beta α * mom U (z * v) := by
  have hp : z ^ (beta α + 1) * z ^ (-(beta α + 1)) = 1 := by
    rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
  rw [mom_subst α U hz, ← mul_assoc, hp, one_mul]

/-- The `z`-slice of the Tonelli kernel integrates to `Gf`. -/
theorem GfKer_zslice {α : ℝ} {U : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    ∫ t, GfKer α U t z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) = Gf α U z := by
  have hker : (fun t => GfKer α U t z)
      = (Set.Iio z).indicator (fun t => GfZeta α z * GfPhi α U t) := by
    funext t
    simp only [GfKer, Set.indicator_apply, Set.mem_Iio]
    by_cases h : t < z <;> simp only [h, ite_true, ite_false, one_mul, zero_mul]
  have hset : Set.Ioi (0 : ℝ) ∩ Set.Iio z = Set.Ioo 0 z := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]
  have hred : ∫ t, GfKer α U t z ∂(MeasureTheory.volume.restrict (Set.Ioi 0))
      = GfZeta α z * ∫ t in (0 : ℝ)..z, t ^ beta α * mom U t := by
    rw [hker, MeasureTheory.setIntegral_indicator measurableSet_Iio, hset]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun t ht => GfPhi_eq_rpow_mom α U ht.1)]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (le_of_lt hz)]
  rw [hred, integral_zero_z_eq α U hz, Gf, GfZeta, abs_of_pos hz]
  have hp : z ^ (-(beta α + 1)) * z ^ (beta α + 1) = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  rw [show (Work.Spaces.w z ^ 2 * z ^ (-(beta α + 1)))
          * (z ^ (beta α + 1) * ∫ v in (0 : ℝ)..1, v ^ beta α * mom U (z * v))
        = Work.Spaces.w z ^ 2 * (z ^ (-(beta α + 1)) * z ^ (beta α + 1))
            * ∫ v in (0 : ℝ)..1, v ^ beta α * mom U (z * v) from by ring,
      hp, mul_one]

end Work.FTS_EllLimOK.ProducerH
