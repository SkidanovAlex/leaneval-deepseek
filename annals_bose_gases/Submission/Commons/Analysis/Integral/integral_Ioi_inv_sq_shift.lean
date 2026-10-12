import Mathlib.MeasureTheory.Integral.IntegralEqImproper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Integral

open MeasureTheory Filter Set
open scoped Topology

/-- `d/dx (-(x - c)⁻¹) = (x - c)⁻¹ * (x - c)⁻¹` for `x ≠ c`. -/
private lemma hasDerivAt_neg_inv_sub {c x : ℝ} (hx : x ≠ c) :
    HasDerivAt (fun y : ℝ => -(y - c)⁻¹) ((x - c)⁻¹ * (x - c)⁻¹) x := by
  have hne : x - c ≠ 0 := sub_ne_zero.mpr hx
  have h1 : HasDerivAt (fun y : ℝ => y - c) 1 x := (hasDerivAt_id x).sub_const c
  have h := (h1.inv hne).neg
  refine h.congr_deriv ?_
  rw [neg_div, neg_neg, one_div, ← inv_pow]
  ring

/-- For `c < T`, the improper integral `∫_{t>T} (t-c)^{-2} dt` equals `(T-c)^{-1}`.
Computed with the antiderivative `t ↦ -(t-c)^{-1}`, which is increasing on `(c,∞)` with
limit `0` at `+∞`. -/
theorem integral_Ioi_inv_sq_shift {c T : ℝ} (hcT : c < T) :
    (∫ t in Set.Ioi T, (t - c)⁻¹ * (t - c)⁻¹) = (T - c)⁻¹ := by
  have hderiv : ∀ x ∈ Set.Ici T,
      HasDerivAt (fun y : ℝ => -(y - c)⁻¹) ((x - c)⁻¹ * (x - c)⁻¹) x := by
    intro x hx
    exact hasDerivAt_neg_inv_sub (ne_of_gt (lt_of_lt_of_le hcT hx))
  have hnonneg : ∀ x ∈ Set.Ioi T, 0 ≤ (x - c)⁻¹ * (x - c)⁻¹ := by
    intro x hx
    have hxc : 0 < x - c := sub_pos.mpr (lt_of_lt_of_le hcT (le_of_lt hx))
    exact mul_nonneg (inv_nonneg.mpr hxc.le) (inv_nonneg.mpr hxc.le)
  have hlim : Tendsto (fun y : ℝ => -(y - c)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun y : ℝ => y - c) atTop atTop := by
      simpa [sub_eq_add_neg] using
        Filter.tendsto_atTop_add_const_right atTop (-c)
          (Filter.tendsto_id : Tendsto (fun y : ℝ => y) atTop atTop)
    have h2 : Tendsto (fun y : ℝ => (y - c)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h
    simpa using h2.neg
  have hInt := integral_Ioi_of_hasDerivAt_of_nonneg' (a := T) (l := 0)
    (g := fun y : ℝ => -(y - c)⁻¹) (g' := fun y : ℝ => (y - c)⁻¹ * (y - c)⁻¹)
    hderiv hnonneg hlim
  rw [hInt]
  ring

end Commons.Analysis.Integral
