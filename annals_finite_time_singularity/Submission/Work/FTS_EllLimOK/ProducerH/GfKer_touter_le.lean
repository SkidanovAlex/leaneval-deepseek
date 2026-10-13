import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS_EllLimOK.ProducerH.Gf_le_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `t`-outer slice of the Tonelli kernel

This module proves the `t`-outer bound for the joint Tonelli kernel
`GfKer α U t z = 1_{t<z} · ζ(z) · φ(t)` of `Gf_le_defs`:

  `∫_{z>0} GfKer α U t z dz ≤ A(t)/β`,  `A = mass α U`,  `β = beta α = 3/α - 1`,
  (`0 < α ≤ 1`, `t > 0`).

This is the first of the two estimates that make the Tonelli step in `Gf_le` work (the
other is the identification `z ↦ ∫_t GfKer α U t z = Gf α U z`).

Mathematically: `φ(t) = t^{β+4} A(t)/(1+t)^4` and `ζ(z) = w(z)² z^{-(β+1)}`, with
`w(z)² z⁴ = (1+z)⁴`; for `z ≥ t > 0` the weight monotonicity `w(z)² ≤ w(t)²`
(`z ↦ (1+1/z)²` is decreasing) bounds the `z`-integral by
`ζ(t)`-normalised: `∫_{z>t} ζ ≤ w(t)² ∫_{z>t} z^{-(β+1)} = w(t)² t^{-β}/β`, and
`(t^{β+4}/(1+t)^4)·(w(t)² t^{-β}) = 1`, so the product collapses to `A(t)/β`.

The statement is unconditional in `U` (no `ℋ⁰` hypothesis is needed for this half; only
nonnegativity of `mass` enters).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS_EllLimOK.ProducerH

/-- **The `t`-outer bound for the Tonelli kernel.**  For `0 < α ≤ 1` and `t > 0`,

  `∫_{z>0} GfKer α U t z dz ≤ mass α U t / beta α`.

Route: `GfKer` vanishes for `z ≤ t`, so the integral over `(0,∞)` is an integral over
`(t,∞)`; there `w(z)² ≤ w(t)²` and `ζ(z) ≤ w(t)² z^{-(β+1)}`, whose integral is
`w(t)² t^{-β}/β` (`integral_Ioi_rpow_of_lt`); the `t`-factor `φ(t) = t^{β+4}A(t)/(1+t)^4`
times `w(t)² = (1+t)^4/t^4` and `t^{-β}` is exactly `1/β` times `A(t)`. -/
theorem GfKer_touter_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {U : ℝ → ℝ → ℝ}
    {t : ℝ} (ht : 0 < t) :
    ∫ z, GfKer α U t z ∂(MeasureTheory.volume.restrict (Set.Ioi 0))
      ≤ mass α U t / beta α := by
  have hβ : 0 < beta α := beta_pos hα hα1
  have hlt : -(beta α + 1) < -1 := by linarith
  -- `w(t)² = (1+t)⁴/t⁴`
  have hw2 : (Work.Spaces.w t) ^ 2 = (1 + t) ^ 4 / t ^ 4 := by
    rw [eq_div_iff (pow_ne_zero 4 (ne_of_gt ht))]
    exact w_sq_mul_z4 (ne_of_gt ht)
  -- the pointwise bound for the `z`-factor on `z > t`
  have hGZle : ∀ z ∈ Set.Ioi t,
      GfZeta α z ≤ (Work.Spaces.w t) ^ 2 * z ^ (-(beta α + 1)) := by
    intro z hz
    have hzt : 0 < z := lt_trans ht hz
    have hwt : Work.Spaces.w t = (1 + 1 / t) ^ 2 := by
      rw [Work.Spaces.w, ← div_pow]; congr 1; field_simp; ring
    have hwz : Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
      rw [Work.Spaces.w, ← div_pow]; congr 1; field_simp; ring
    have h1 : (1 : ℝ) + 1 / z ≤ 1 + 1 / t := by
      have := one_div_le_one_div_of_le ht (le_of_lt hz)
      linarith
    have h2 : (0 : ℝ) ≤ 1 + 1 / z := by
      have : 0 < 1 / z := by positivity
      linarith
    have hwle' : Work.Spaces.w z ≤ Work.Spaces.w t := by
      rw [hwz, hwt]
      exact pow_le_pow_left₀ h2 h1 2
    have hwle : (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.w t) ^ 2 :=
      pow_le_pow_left₀ (by rw [hwz]; positivity) hwle' 2
    simp only [GfZeta, abs_of_pos hzt]
    exact mul_le_mul_of_nonneg_right hwle (Real.rpow_nonneg (le_of_lt hzt) _)
  -- integrability of the dominating function on `(t,∞)`
  have hBint : IntegrableOn (fun z : ℝ => (Work.Spaces.w t) ^ 2 * z ^ (-(beta α + 1)))
      (Set.Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt hlt ht).const_mul _
  -- continuity of the `z`-factor on `(t,∞)`
  have hcont : ContinuousOn (fun z : ℝ => GfZeta α z) (Set.Ioi t) := by
    have h1 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi t) := by
      have hb : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi t) :=
        ContinuousOn.div (((continuous_const.add continuous_id).pow 2).continuousOn)
          ((continuous_id.pow 2).continuousOn)
          (fun z hz => pow_ne_zero 2 (ne_of_gt (lt_trans ht hz)))
      have h2 : ContinuousOn ((fun z : ℝ => (1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi t) := hb.pow 2
      convert h2 using 1
      funext z
      simp only [Work.Spaces.w, Pi.pow_apply]
    have h2 : ContinuousOn (fun z : ℝ => |z| ^ (-(beta α + 1))) (Set.Ioi t) := by
      intro z hz
      exact ((Real.continuousAt_rpow_const _ _
        (Or.inl (abs_ne_zero.mpr (ne_of_gt (lt_trans ht hz))))).comp
        continuous_abs.continuousAt).continuousWithinAt
    convert h1.mul h2 using 1
    funext z
    simp only [GfZeta, Pi.mul_apply]
  have hGZint : IntegrableOn (fun z : ℝ => GfZeta α z) (Set.Ioi t) := by
    refine Integrable.mono' hBint (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_of_nonneg (GfZeta_nonneg α z)]
    exact hGZle z hz
  have hmono : ∫ z in Set.Ioi t, GfZeta α z ≤
      ∫ z in Set.Ioi t, (Work.Spaces.w t) ^ 2 * z ^ (-(beta α + 1)) :=
    setIntegral_mono_on hGZint hBint measurableSet_Ioi hGZle
  -- the value of the dominating integral
  have hval : ∫ z in Set.Ioi t, (Work.Spaces.w t) ^ 2 * z ^ (-(beta α + 1))
      = (Work.Spaces.w t) ^ 2 * t ^ (-(beta α)) / beta α := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt ht]
    rw [show -(beta α + 1) + 1 = -(beta α) from by ring, neg_div_neg_eq, mul_div_assoc]
  -- `GfKer` vanishes for `z ≤ t`
  have hvan : ∫ z in Set.Ioi (0 : ℝ), GfKer α U t z = ∫ z in Set.Ioi t, GfKer α U t z := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi ht.le) ?_
    intro z hz
    have hzt : ¬ t < z := fun h => hz.2 h
    simp [GfKer, hzt]
  -- on `(t,∞)` the kernel is the `t`-factor times the `z`-factor
  have hcongr : ∫ z in Set.Ioi t, GfKer α U t z
      = ∫ z in Set.Ioi t, GfPhi α U t * GfZeta α z := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    rw [GfKer, ite_eq_left (show t < z from hz)]; ring
  have harith : GfPhi α U t * ((Work.Spaces.w t) ^ 2 * t ^ (-(beta α)) / beta α)
      = mass α U t / beta α := by
    rw [GfPhi_eq_of_pos α U ht, hw2]
    have hpow : t ^ (beta α + 4) * t ^ (-(beta α)) = t ^ 4 := by
      rw [← Real.rpow_add ht]; norm_num
    field_simp
    have heq : t ^ (beta α + 4) * mass α U t * t ^ (-(beta α))
        = mass α U t * (t ^ (beta α + 4) * t ^ (-(beta α))) := by ring
    rw [heq, hpow]
  calc ∫ z, GfKer α U t z ∂(MeasureTheory.volume.restrict (Set.Ioi 0))
      = ∫ z in Set.Ioi (0 : ℝ), GfKer α U t z := rfl
    _ = ∫ z in Set.Ioi t, GfKer α U t z := hvan
    _ = ∫ z in Set.Ioi t, GfPhi α U t * GfZeta α z := hcongr
    _ = GfPhi α U t * ∫ z in Set.Ioi t, GfZeta α z := integral_const_mul _ _
    _ ≤ GfPhi α U t * ((Work.Spaces.w t) ^ 2 * t ^ (-(beta α)) / beta α) := by
        apply mul_le_mul_of_nonneg_left _ (GfPhi_nonneg α U t)
        calc ∫ z in Set.Ioi t, GfZeta α z
            ≤ ∫ z in Set.Ioi t, (Work.Spaces.w t) ^ 2 * z ^ (-(beta α + 1)) := hmono
          _ = (Work.Spaces.w t) ^ 2 * t ^ (-(beta α)) / beta α := hval
    _ = mass α U t / beta α := harith

end Work.FTS_EllLimOK.ProducerH
