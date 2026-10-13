import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

/-- The "head" piece of the radial Green function source integral: for a source `c` supported in
`[a,b] ⊂ (0,∞)` with `|c| ≤ M`, the truncated integral `∫_0^z c(t) t^e dt` is bounded by
`M · (min z b)^(e+1)/(e+1)` for every exponent `e > -1` (so that `t ↦ t^e` is integrable at `0`).

The point is that the integration range that actually matters is `[0, min z b]`: `min z b` is the
right endpoint of the support cut off by `z`, and on the rest of `[0,z]` the integrand vanishes. -/
theorem head_supp {c : ℝ → ℝ} {a b M e z : ℝ} (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M)
    (he : -1 < e) (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) (hb : ∀ t : ℝ, |c t| ≤ M)
    (hz : 0 < z) :
    |∫ t in (0 : ℝ)..z, c t * t ^ e| ≤ M * (min z b) ^ (e + 1) / (e + 1) := by
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hmpos : 0 < min z b := lt_min hz hbpos
  have hmz : min z b ≤ z := min_le_left _ _
  have hnne : e + 1 ≠ 0 := by linarith
  have hnonneg : 0 ≤ M * (min z b) ^ (e + 1) / (e + 1) :=
    div_nonneg (mul_nonneg hM (Real.rpow_nonneg hmpos.le _)) (by linarith : (0 : ℝ) ≤ e + 1)
  -- The integrand vanishes on `[0,z] \ [0, min z b]`, so the integral only sees `[0, min z b]`.
  have hshift : ∫ t in (0 : ℝ)..z, c t * t ^ e
      = ∫ t in Set.Ioc (0 : ℝ) (min z b), c t * t ^ e := by
    rw [intervalIntegral.integral_of_le hz.le]
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      (Set.Ioc_subset_Ioc le_rfl hmz) ?_
    intro x hx
    rw [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Ioc] at hx
    obtain ⟨⟨hx0, hxz⟩, hx2⟩ := hx
    have hxgt : min z b < x := lt_of_not_ge fun h => hx2 ⟨hx0, h⟩
    have hxb : b < x := by
      rcases le_total b z with hbz | hzb
      · rwa [min_eq_right hbz] at hxgt
      · rw [min_eq_left hzb] at hxgt
        exact absurd hxgt (not_lt.mpr hxz)
    have hmem : x ∉ Set.Icc a b := fun h => absurd h.2 (not_le.mpr hxb)
    rw [hsupp x hmem, zero_mul]
  rw [hshift]
  -- Bound the absolute value by the (unrestricted) integral of the modulus.
  have hstep : |∫ t in Set.Ioc (0 : ℝ) (min z b), c t * t ^ e|
      ≤ ∫ t in (0 : ℝ)..(min z b), |c t * t ^ e| := by
    rw [intervalIntegral.integral_of_le hmpos.le]
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (f := fun t : ℝ => c t * t ^ e)
  refine hstep.trans ?_
  -- Compare with `∫_0^{min z b} M t^e`; this needs the (non-measurable) modulus to be integrable,
  -- otherwise both sides are `0` by `integral_undef`.
  rcases em (MeasureTheory.Integrable (fun t : ℝ => |c t * t ^ e|)
    (volume.restrict (Set.Ioc (0 : ℝ) (min z b)))) with hint | hint
  · have hII : IntervalIntegrable (fun t : ℝ => |c t * t ^ e|) volume 0 (min z b) := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hmpos.le]
      exact hint
    have hgII : IntervalIntegrable (fun t : ℝ => M * t ^ e) volume 0 (min z b) :=
      (intervalIntegral.intervalIntegrable_rpow' he).const_mul M
    refine (intervalIntegral.integral_mono_on hmpos.le hII hgII ?_).trans_eq ?_
    · intro x hx
      have hex : 0 ≤ x ^ e := Real.rpow_nonneg hx.1 e
      rw [abs_mul, abs_of_nonneg hex]
      exact mul_le_mul_of_nonneg_right (hb x) hex
    · rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl he), Real.zero_rpow hnne,
        sub_zero]
      ring
  · rw [intervalIntegral.integral_of_le hmpos.le, MeasureTheory.integral_undef hint]
    exact hnonneg

end Work.FTS.PhiStar.Honesty.RadGreenSupp
