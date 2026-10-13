import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllipticEst.H2W

/-- **Growth of the left half of the `L₀`-kernel.**

For `θ ∈ (0, π/4]`,

`∫_θ^{π/4} ds / (cos s · sin²(2s)) ≤ (π²/8) / θ`.

Route: on `[θ, π/4]` one has `s ∈ (0, π/4]`, hence `cos s ≥ cos (π/4) = √2/2` and
`sin s > 0`.  Writing `sin(2s) = 2 sin s cos s`,

`cos s · sin²(2s) = 4 sin²s cos³s ≥ 4 (√2/2)³ sin²s = √2 · sin²s ≥ sin²s`,

so the integrand is dominated by `1/sin²s`.  Then `∫_θ^{π/4} ds/sin²s = cot θ - 1 ≤ cot θ ≤ 1/θ`
(the last step being `θ < tan θ` for `θ ∈ (0, π/2)`), and `1 ≤ π²/8`. -/
theorem lzeroGrowthKernelLeft {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (Real.pi / 4)) :
    ∫ s in θ..(Real.pi / 4), 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      ≤ (Real.pi ^ 2 / 8) / θ := by
  obtain ⟨hθ0, hθ4⟩ := hθ
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have huIcc : Set.uIcc θ (Real.pi / 4) = Set.Icc θ (Real.pi / 4) := Set.uIcc_of_le hθ4
  -- The pointwise domination of the integrand by `1/sin²s` on the closed interval.
  have hpt : ∀ s ∈ Set.Icc θ (Real.pi / 4),
      1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) ≤ 1 / (Real.sin s) ^ 2 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hθ0 hs.1
    have hs4 : s ≤ Real.pi / 4 := hs.2
    have hsin_pos : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith)
    have hcos_half : Real.sqrt 2 / 2 ≤ Real.cos s := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ s from hs0.le)
        (show Real.pi / 4 ≤ Real.pi by linarith) hs4
      rwa [Real.cos_pi_div_four] at h
    have hcos_pos : 0 < Real.cos s :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.sqrt 2 / 2) hcos_half
    have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.one_le_sqrt]; norm_num
    have hcube : (Real.sqrt 2 / 2) ^ 3 ≤ (Real.cos s) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hcos_half 3
    have hsqrt_eq : 4 * (Real.sqrt 2 / 2) ^ 3 = Real.sqrt 2 := by
      have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      rw [show (Real.sqrt 2 / 2) ^ 3 = (Real.sqrt 2) ^ 3 / 8 by ring]
      rw [show (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 by ring, h2]
      ring
    have hfour : (1 : ℝ) ≤ 4 * (Real.cos s) ^ 3 := by linarith
    have hprod : (Real.sin s) ^ 2 ≤ Real.cos s * (Real.sin (2 * s)) ^ 2 := by
      rw [Real.sin_two_mul]
      have h2 : (0 : ℝ) ≤ (Real.sin s) ^ 2 := sq_nonneg _
      have h3 := mul_le_mul_of_nonneg_right hfour h2
      nlinarith [h3]
    have hsin_sq_pos : 0 < (Real.sin s) ^ 2 := pow_pos hsin_pos 2
    exact one_div_le_one_div_of_le hsin_sq_pos hprod
  -- Non-vanishing of the denominators on the interval (used for continuity).
  have hsin2_ne : ∀ s ∈ Set.uIcc θ (Real.pi / 4), Real.sin (2 * s) ≠ 0 := by
    intro s hs
    rw [huIcc] at hs
    have hs0 : 0 < s := lt_of_lt_of_le hθ0 hs.1
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hs.2]))
  have hcos_ne : ∀ s ∈ Set.uIcc θ (Real.pi / 4), Real.cos s ≠ 0 := by
    intro s hs
    rw [huIcc] at hs
    have hs0 : 0 < s := lt_of_lt_of_le hθ0 hs.1
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith [hs.2]⟩)
  have hsin_ne : ∀ s ∈ Set.uIcc θ (Real.pi / 4), Real.sin s ≠ 0 := by
    intro s hs
    rw [huIcc] at hs
    have hs0 : 0 < s := lt_of_lt_of_le hθ0 hs.1
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith [hs.2]))
  have hsin2c : Continuous (fun s : ℝ => Real.sin (2 * s)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hcont1 : ContinuousOn (fun s : ℝ => 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      (Set.uIcc θ (Real.pi / 4)) :=
    continuousOn_const.div ((Real.continuous_cos.continuousOn).mul ((hsin2c.continuousOn).pow 2))
      (fun s hs => mul_ne_zero (hcos_ne s hs) (pow_ne_zero 2 (hsin2_ne s hs)))
  have hcont2 : ContinuousOn (fun s : ℝ => 1 / (Real.sin s) ^ 2) (Set.uIcc θ (Real.pi / 4)) :=
    continuousOn_const.div ((Real.continuous_sin.continuousOn).pow 2)
      (fun s hs => pow_ne_zero 2 (hsin_ne s hs))
  have hfi : IntervalIntegrable (fun s : ℝ => 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      volume θ (Real.pi / 4) := hcont1.intervalIntegrable
  have hgi : IntervalIntegrable (fun s : ℝ => 1 / (Real.sin s) ^ 2) volume θ (Real.pi / 4) :=
    hcont2.intervalIntegrable
  have hmono : ∫ s in θ..(Real.pi / 4), 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      ≤ ∫ s in θ..(Real.pi / 4), 1 / (Real.sin s) ^ 2 :=
    intervalIntegral.integral_mono_on hθ4 hfi hgi hpt
  -- The explicit value of the comparison integral: `∫ ds/sin²s = cot θ - cot(π/4)`.
  have hderiv : ∀ x ∈ Set.uIcc θ (Real.pi / 4),
      HasDerivAt Real.cot (-(1 / (Real.sin x) ^ 2)) x := by
    intro x hx
    rw [huIcc] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hθ0 hx.1
    have hsinx : Real.sin x ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [hx.2]))
    have hfun : Real.cot = fun y => Real.cos y / Real.sin y := funext Real.cot_eq_cos_div_sin
    rw [hfun]
    have h := (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hsinx
    refine h.congr_deriv ?_
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hint' : IntervalIntegrable (fun x : ℝ => -(1 / (Real.sin x) ^ 2)) volume θ (Real.pi / 4) :=
    hcont2.neg.intervalIntegrable
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint'
  have hI : ∫ x in θ..(Real.pi / 4), 1 / (Real.sin x) ^ 2
      = Real.cot θ - Real.cot (Real.pi / 4) := by
    have hneg := intervalIntegral.integral_neg (μ := volume) (a := θ) (b := Real.pi / 4)
      (f := fun x : ℝ => 1 / (Real.sin x) ^ 2)
    rw [hneg] at hsub
    linarith
  have hcot_pi4 : Real.cot (Real.pi / 4) = 1 := by
    rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    exact div_self (by positivity)
  -- `cot θ ≤ 1/θ` from `θ < tan θ`.
  have hcot_le : Real.cot θ ≤ 1 / θ := by
    have htan := Real.lt_tan hθ0 (by linarith)
    rw [Real.tan_eq_sin_div_cos] at htan
    have hcos_pos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)
    rw [lt_div_iff₀ hcos_pos] at htan
    rw [Real.cot_eq_cos_div_sin, div_le_div_iff₀ hsin_pos hθ0]
    linarith
  have hpi_sq : (1 : ℝ) ≤ Real.pi ^ 2 / 8 := by nlinarith [Real.pi_gt_three]
  calc ∫ s in θ..(Real.pi / 4), 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      ≤ ∫ s in θ..(Real.pi / 4), 1 / (Real.sin s) ^ 2 := hmono
    _ = Real.cot θ - Real.cot (Real.pi / 4) := hI
    _ = Real.cot θ - 1 := by rw [hcot_pi4]
    _ ≤ 1 / θ := by linarith [hcot_le]
    _ ≤ (Real.pi ^ 2 / 8) / θ := div_le_div_of_nonneg_right hpi_sq hθ0.le

end Work.FTS.EllipticEst.H2W
