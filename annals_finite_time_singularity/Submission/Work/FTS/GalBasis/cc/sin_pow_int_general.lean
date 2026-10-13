import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc

open MeasureTheory intervalIntegral

/-- For `r > -1` and `0 ≤ θ' ≤ π/4`, the function `θ ↦ sin(2θ)^r` is dominated by
`max 1 (2^r) · θ^r` on `(0, θ']`, and `∫_0^{θ'} θ^r = θ'^{r+1}/(r+1)`.

The pointwise bound is the whole content: for `r ≥ 0` it follows from `sin(2θ) ≤ 2θ`, and for
`r < 0` (where `t ↦ t^r` is *decreasing*) it follows from Jordan's inequality
`sin(2θ) ≥ (4/π)θ` together with `(4/π)^r = (π/4)^{-r} ≤ 1`. -/
private theorem sin_two_rpow_integral_le {r θ' : ℝ} (hr : -1 < r) (h0 : 0 ≤ θ')
    (hπ : θ' ≤ Real.pi / 4) :
    ∫ θ in (0 : ℝ)..θ', (Real.sin (2 * θ)) ^ r
      ≤ max 1 (2 ^ r) * θ' ^ (r + 1) / (r + 1) := by
  have hpt : ∀ x ∈ Set.Ioc (0 : ℝ) θ', (Real.sin (2 * x)) ^ r ≤ max 1 (2 ^ r) * x ^ r := by
    intro x hx
    have hxpos : 0 < x := hx.1
    have h2xpos : 0 < 2 * x := by linarith
    have h2xle : 2 * x ≤ Real.pi / 2 := by linarith [hx.2, hπ, Real.pi_pos]
    have hsinpos : 0 < Real.sin (2 * x) :=
      Real.sin_pos_of_pos_of_lt_pi h2xpos (by linarith [Real.pi_pos, h2xle])
    have hxr : 0 ≤ x ^ r := Real.rpow_nonneg (le_of_lt hxpos) r
    rcases le_or_gt 0 r with hr0 | hr0
    · -- `r ≥ 0`: `sin(2x) ≤ 2x`
      have hsle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (le_of_lt h2xpos)
      have hstep : (Real.sin (2 * x)) ^ r ≤ (2 * x) ^ r :=
        Real.rpow_le_rpow (le_of_lt hsinpos) hsle hr0
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hxpos)] at hstep
      exact hstep.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hxr)
    · -- `r < 0`: Jordan's inequality
      have hjord : (4 / Real.pi) * x ≤ Real.sin (2 * x) := by
        have h := Real.mul_le_sin (x := 2 * x) (le_of_lt h2xpos) h2xle
        have he : 2 / Real.pi * (2 * x) = (4 / Real.pi) * x := by ring
        rwa [he] at h
      have hbase : 0 < (4 / Real.pi) * x := by positivity
      have hstep : (Real.sin (2 * x)) ^ r ≤ ((4 / Real.pi) * x) ^ r :=
        Real.rpow_le_rpow_of_nonpos hbase hjord (le_of_lt hr0)
      have hsplit : ((4 / Real.pi) * x) ^ r = (4 / Real.pi) ^ r * x ^ r :=
        Real.mul_rpow (by positivity) (le_of_lt hxpos)
      have hcoef : (4 / Real.pi) ^ r ≤ 1 := by
        have hp4 : (0 : ℝ) < Real.pi / 4 := by positivity
        have hle1 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
        have h' : (4 / Real.pi) = (Real.pi / 4)⁻¹ := by rw [inv_div]
        rw [h', Real.inv_rpow (le_of_lt hp4), ← Real.rpow_neg (le_of_lt hp4)]
        exact Real.rpow_le_one (le_of_lt hp4) hle1 (neg_nonneg.mpr (le_of_lt hr0))
      calc (Real.sin (2 * x)) ^ r ≤ ((4 / Real.pi) * x) ^ r := hstep
        _ = (4 / Real.pi) ^ r * x ^ r := hsplit
        _ ≤ 1 * x ^ r := mul_le_mul_of_nonneg_right hcoef hxr
        _ = x ^ r := one_mul _
        _ ≤ max 1 (2 ^ r) * x ^ r := by
            simpa using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (2 ^ r)) hxr
  have hgint : IntervalIntegrable (fun x : ℝ => max 1 (2 ^ r) * x ^ r) volume 0 θ' :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := θ') hr).const_mul _
  have hmeas : Measurable (fun x : ℝ => x ^ r) :=
    measurable_of_continuousOn_compl_singleton 0
      (ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl hx))
  have hfint : IntervalIntegrable (fun x : ℝ => (Real.sin (2 * x)) ^ r) volume 0 θ' := by
    refine hgint.mono_fun' ?_ ?_
    · exact (hmeas.comp (Real.measurable_sin.comp
        (measurable_const.mul measurable_id))).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
      have hx' : x ∈ Set.Ioc (0 : ℝ) θ' := by rwa [Set.uIoc_of_le h0] at hx
      have h2xle : 2 * x ≤ Real.pi := by
        have := hx'.2
        linarith [hπ, Real.pi_pos]
      have hfnn : 0 ≤ (Real.sin (2 * x)) ^ r :=
        Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx'.1]) h2xle) r
      rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
      exact hpt x hx'
  have hval : ∫ x in (0 : ℝ)..θ', max 1 (2 ^ r) * x ^ r
      = max 1 (2 ^ r) * θ' ^ (r + 1) / (r + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr),
      Real.zero_rpow (by linarith : r + 1 ≠ 0)]
    ring
  calc ∫ θ in (0 : ℝ)..θ', (Real.sin (2 * θ)) ^ r
      ≤ ∫ θ in (0 : ℝ)..θ', max 1 (2 ^ r) * θ ^ r :=
        intervalIntegral.integral_mono_on_of_le_Ioo h0 hfint hgint
          (fun x hx => hpt x ⟨hx.1, le_of_lt hx.2⟩)
    _ = max 1 (2 ^ r) * θ' ^ (r + 1) / (r + 1) := hval

theorem sin_pow_int_general {γ θ' : ℝ} (h1 : 1 < γ) (h0 : 0 ≤ θ') (hπ : θ' ≤ Real.pi / 4) :
    ∫ θ in (0 : ℝ)..θ', (Real.sin (2 * θ)) ^ (γ - 2)
      ≤ max 1 (2 ^ (γ - 2)) * θ' ^ (γ - 1) / (γ - 1) := by
  have hr : -1 < γ - 2 := by linarith
  have he : γ - 2 + 1 = γ - 1 := by ring
  have h := sin_two_rpow_integral_le (r := γ - 2) hr h0 hπ
  rw [he] at h
  exact h

end Work.FTS.GalBasis.cc
