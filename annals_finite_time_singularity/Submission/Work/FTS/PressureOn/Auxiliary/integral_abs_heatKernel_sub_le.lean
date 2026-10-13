import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.ihak_GaussFacts
import Submission.Work.FTS.PressureOn.Auxiliary.ihak_r_exp_gauss_le
import Submission.Work.FTS.PressureOn.Auxiliary.ihak_hasDerivAt_heatKernel_sub_smul
import Submission.Work.FTS.PressureOn.Auxiliary.ihak_interval_shift_mean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L¹` modulus of continuity of the heat kernel on `ℝ³`

`‖γ_t(· - h) - γ_t(·)‖_{L¹(ℝ³)} ≤ 4 ‖h‖ / √t`, where `γ_t` is the heat kernel
`γ_t z = (4πt)^{-3/2} exp (-‖z‖²/(4t))`.

## Proof

Write `c = (4πt)^{-3/2}`, so that `γ_t z = c · exp (-‖z‖²/(4t))` and `γ_t` is smooth with
`∇γ_t z = -γ_t z · z/(2t)`; hence the directional derivative of `s ↦ γ_t (z - s • h)` is
`γ_t (z - s • h) · ⟪z - s • h, h⟫ / (2t)`, whose absolute value is at most
`(‖h‖/(2t)) · ‖z - s • h‖ · γ_t (z - s • h) =: φ (z, s) ≥ 0`.

By the fundamental theorem of calculus and the triangle inequality for the integral,

  `|γ_t (z - h) - γ_t z| ≤ ∫_0^1 φ (z, s) ds   (z ∈ ℝ³)`,

and integrating over `z` against the Lebesgue measure reduces (by the shear-averaging identity
`ihak_interval_shift_mean`, i.e. Fubini plus translation invariance) to

  `∫_z |γ_t (z - h) - γ_t z| ≤ (‖h‖/(2t)) ∫_w ‖w‖ γ_t w dw`.

The last integral is bounded with the elementary Gaussian pointwise inequality
`r exp(-r²/(4t)) ≤ 2√t exp(-r²/(8t))` (`ihak_r_exp_gauss_le`), which gives

  `∫_w ‖w‖ γ_t w dw ≤ c · 2√t · ∫_w exp(-(‖w‖²/(8t))) dw = c · 2√t · (8πt)^{3/2} = 4√2 √t`,

and `(‖h‖/(2t)) · 4√2 √t = 2√2 ‖h‖/√t ≤ 4 ‖h‖/√t`. -/

open MeasureTheory
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

theorem integral_abs_heatKernel_sub_le (h : Work.FTS.PressureOn.R3) (t : ℝ) (ht : 0 < t) :
    ∫ z : Work.FTS.PressureOn.R3,
        |Work.FTS.PressureOn.Auxiliary.heatKernel t (z - h) - Work.FTS.PressureOn.Auxiliary.heatKernel t z|
      ≤ 4 * ‖h‖ / Real.sqrt t := by
  -- ## Constants
  set c : ℝ := (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) with hc_def
  have hcpos : 0 < c := by
    rw [hc_def]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hγnn : ∀ w : R3, 0 ≤ heatKernel t w := fun w => heatKernel_nonneg ht.le w
  -- ## Differentiability of `γ_t` in the space variable
  have hγcont : Continuous (fun w : R3 => heatKernel t w) := by
    unfold heatKernel
    fun_prop
  have hcurve : ∀ z : R3, Continuous (fun s : ℝ => z - s • h) := fun z =>
    continuous_const.sub (continuous_id.smul continuous_const)
  have hcont_deriv : ∀ z : R3, Continuous (fun s : ℝ =>
      heatKernel t (z - s • h) * (inner ℝ (z - s • h) h) / (2 * t)) := fun z =>
    (((hγcont.comp (hcurve z)).mul ((hcurve z).inner continuous_const))).div_const _
  have hderiv : ∀ (z : R3) (s : ℝ), HasDerivAt (fun r : ℝ => heatKernel t (z - r • h))
      (heatKernel t (z - s • h) * (inner ℝ (z - s • h) h) / (2 * t)) s :=
    fun z s => ihak_hasDerivAt_heatKernel_sub_smul t ht z h s
  -- ## The pointwise fundamental-theorem-of-calculus bound
  have hFTC : ∀ z : R3,
      (∫ s in (0 : ℝ)..1, heatKernel t (z - s • h) * (inner ℝ (z - s • h) h) / (2 * t))
        = heatKernel t (z - h) - heatKernel t z := by
    intro z
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun r : ℝ => heatKernel t (z - r • h))
      (f' := fun s : ℝ => heatKernel t (z - s • h) * (inner ℝ (z - s • h) h) / (2 * t))
      (fun s _ => hderiv z s) ((hcont_deriv z).intervalIntegrable 0 1)
    simpa using h
  have hφ : ∀ z : R3, |heatKernel t (z - h) - heatKernel t z|
      ≤ ∫ s in (0 : ℝ)..1, ‖h‖ / (2 * t) * (‖z - s • h‖ * heatKernel t (z - s • h)) := by
    intro z
    rw [← hFTC z]
    refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      ((hcont_deriv z).abs.intervalIntegrable 0 1) ?_ (fun s _ => ?_)
    · exact ((continuous_const.mul ((continuous_norm.comp (hcurve z)).mul
        (hγcont.comp (hcurve z)))).intervalIntegrable 0 1)
    · have hw : 0 ≤ heatKernel t (z - s • h) := hγnn _
      have h2t : 0 < 2 * t := by positivity
      calc |heatKernel t (z - s • h) * inner ℝ (z - s • h) h / (2 * t)|
          = heatKernel t (z - s • h) * |inner ℝ (z - s • h) h| / (2 * t) := by
            rw [abs_div, abs_mul, abs_of_nonneg hw, abs_of_pos h2t]
        _ ≤ heatKernel t (z - s • h) * (‖z - s • h‖ * ‖h‖) / (2 * t) := by
            gcongr
            exact abs_real_inner_le_norm _ _
        _ = ‖h‖ / (2 * t) * (‖z - s • h‖ * heatKernel t (z - s • h)) := by ring
  have hφ' : ∀ z : R3, |heatKernel t (z - h) - heatKernel t z|
      ≤ ‖h‖ / (2 * t) * (∫ s in (0 : ℝ)..1, ‖z - s • h‖ * heatKernel t (z - s • h)) := by
    intro z
    simpa only [intervalIntegral.integral_const_mul] using hφ z
  -- ## The shear-averaging identity for `w ↦ ‖w‖ γ_t w`
  have hg0cont : Continuous (fun w : R3 => ‖w‖ * heatKernel t w) :=
    continuous_norm.mul hγcont
  have hg0bound : ∀ w : R3, |‖w‖ * heatKernel t w|
      ≤ (c * (2 * Real.sqrt t)) * Real.exp (-((1 / (8 * t)) * ‖w‖ ^ 2)) := by
    intro w
    have hw : 0 ≤ ‖w‖ := norm_nonneg w
    have hgnn : 0 ≤ heatKernel t w := hγnn w
    have h1 := ihak_r_exp_gauss_le t ‖w‖ ht hw
    have h2 : |‖w‖ * heatKernel t w|
        = c * (‖w‖ * Real.exp (-(‖w‖ ^ 2 / (4 * t)))) := by
      rw [abs_of_nonneg (mul_nonneg hw hgnn), hc_def]
      unfold heatKernel
      ring
    rw [h2]
    calc c * (‖w‖ * Real.exp (-(‖w‖ ^ 2 / (4 * t))))
        ≤ c * (2 * Real.sqrt t * Real.exp (-(‖w‖ ^ 2 / (8 * t)))) :=
          mul_le_mul_of_nonneg_left h1 hcpos.le
      _ = (c * (2 * Real.sqrt t)) * Real.exp (-((1 / (8 * t)) * ‖w‖ ^ 2)) := by
          rw [show -(‖w‖ ^ 2 / (8 * t)) = -((1 / (8 * t)) * ‖w‖ ^ 2) by ring]
          ring
  have hgaussint : Integrable
      (fun w : R3 => (c * (2 * Real.sqrt t)) * Real.exp (-((1 / (8 * t)) * ‖w‖ ^ 2))) volume :=
    (ihak_integrable_rexp_normSq (1 / (8 * t)) (by positivity)).const_mul _
  have hg0int : Integrable (fun w : R3 => ‖w‖ * heatKernel t w) volume := by
    refine hgaussint.mono' hg0cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    exact hg0bound w
  obtain ⟨hIntAvg, hAvgVal⟩ := ihak_interval_shift_mean hg0cont (c * (2 * Real.sqrt t))
    (1 / (8 * t)) (by positivity) (by positivity) hg0bound h
  -- ## Monotonicity of the outer integral
  have hInt2 : Integrable (fun z : R3 =>
      ‖h‖ / (2 * t) * (∫ s in (0 : ℝ)..1, ‖z - s • h‖ * heatKernel t (z - s • h))) volume :=
    hIntAvg.const_mul _
  have step1 : ∫ z : R3, |heatKernel t (z - h) - heatKernel t z|
      ≤ ‖h‖ / (2 * t) * ∫ z : R3,
          (∫ s in (0 : ℝ)..1, ‖z - s • h‖ * heatKernel t (z - s • h)) := by
    have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _) hInt2
      (Filter.Eventually.of_forall fun z => hφ' z)
    rwa [MeasureTheory.integral_const_mul] at h
  -- ## Evaluation of the averaged integral and of the Gaussian integral
  have step2 : ‖h‖ / (2 * t) * (∫ z : R3,
        (∫ s in (0 : ℝ)..1, ‖z - s • h‖ * heatKernel t (z - s • h)))
      ≤ ‖h‖ / (2 * t) * (∫ z : R3, ‖z‖ * heatKernel t z) :=
    mul_le_mul_of_nonneg_left (le_of_eq hAvgVal) (by positivity)
  have hg0le : ∀ w : R3, ‖w‖ * heatKernel t w
      ≤ (c * (2 * Real.sqrt t)) * Real.exp (-((1 / (8 * t)) * ‖w‖ ^ 2)) := fun w =>
    le_of_abs_le (hg0bound w)
  have step3 : ∫ z : R3, ‖z‖ * heatKernel t z
      ≤ (c * (2 * Real.sqrt t)) * (Real.pi / (1 / (8 * t))) ^ ((3 : ℝ) / 2) := by
    have hEq : ∫ z : R3, (c * (2 * Real.sqrt t)) * Real.exp (-((1 / (8 * t)) * ‖z‖ ^ 2))
        = (c * (2 * Real.sqrt t)) * (Real.pi / (1 / (8 * t))) ^ ((3 : ℝ) / 2) := by
      rw [MeasureTheory.integral_const_mul,
        ihak_integral_rexp_normSq (1 / (8 * t)) (by positivity)]
    rw [← hEq]
    exact integral_mono hg0int hgaussint (fun w => hg0le w)
  -- ## The final arithmetic
  have hfinal : ‖h‖ / (2 * t) * ((c * (2 * Real.sqrt t)) * (Real.pi / (1 / (8 * t))) ^
        ((3 : ℝ) / 2)) ≤ 4 * ‖h‖ / Real.sqrt t := by
    have hA : (0 : ℝ) < 4 * Real.pi * t := by positivity
    have hpidiv : Real.pi / (1 / (8 * t)) = 8 * Real.pi * t := by
      rw [div_eq_mul_inv, inv_div]
      ring
    rw [hpidiv]
    have hA32 : (4 * Real.pi * t) ^ ((3 : ℝ) / 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hA _)
    have hcube : c * (8 * Real.pi * t) ^ ((3 : ℝ) / 2) = 2 * Real.sqrt 2 := by
      have h1 : c * (8 * Real.pi * t) ^ ((3 : ℝ) / 2)
          = ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹
            * (2 ^ ((3 : ℝ) / 2) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2)) := by
        rw [hc_def, show (8 : ℝ) * Real.pi * t = 2 * (4 * Real.pi * t) by ring,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hA.le, Real.rpow_neg hA.le]
      have h2 : (2 : ℝ) ^ ((3 : ℝ) / 2) = 2 * Real.sqrt 2 := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, ← Real.sqrt_eq_rpow]
      calc c * (8 * Real.pi * t) ^ ((3 : ℝ) / 2)
          = ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹
            * (2 ^ ((3 : ℝ) / 2) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2)) := h1
        _ = 2 ^ ((3 : ℝ) / 2) := by
            rw [mul_comm (((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹)
              (2 ^ ((3 : ℝ) / 2) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2)), mul_assoc,
              mul_inv_cancel₀ hA32, mul_one]
        _ = 2 * Real.sqrt 2 := h2
    have hcombine : ‖h‖ / (2 * t) * (2 * Real.sqrt t) = ‖h‖ / Real.sqrt t := by
      have h1 : ‖h‖ / (2 * t) * (2 * Real.sqrt t) = ‖h‖ * Real.sqrt t / t := by ring
      rw [h1, div_eq_div_iff (ne_of_gt ht) (ne_of_gt hsqrtpos), mul_assoc, hsq]
    have h22 : 2 * Real.sqrt 2 ≤ 4 := by
      have h2 : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      linarith
    calc ‖h‖ / (2 * t) * ((c * (2 * Real.sqrt t)) * (8 * Real.pi * t) ^ ((3 : ℝ) / 2))
        = (‖h‖ / (2 * t) * (2 * Real.sqrt t)) * (c * (8 * Real.pi * t) ^ ((3 : ℝ) / 2)) := by
          ring
      _ = (‖h‖ / Real.sqrt t) * (2 * Real.sqrt 2) := by rw [hcombine, hcube]
      _ = (2 * Real.sqrt 2) * (‖h‖ / Real.sqrt t) := by ring
      _ ≤ 4 * (‖h‖ / Real.sqrt t) :=
          mul_le_mul_of_nonneg_right h22 (by positivity)
      _ = 4 * ‖h‖ / Real.sqrt t := by ring
  exact step1.trans (step2.trans ((mul_le_mul_of_nonneg_left step3 (by positivity)).trans hfinal))

end

end Work.FTS.PressureOn.Auxiliary
