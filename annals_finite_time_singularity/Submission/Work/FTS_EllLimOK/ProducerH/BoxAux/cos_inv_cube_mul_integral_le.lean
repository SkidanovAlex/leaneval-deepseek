import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

/-- Antiderivative computation: `∫_a^b sin t · cos²t dt = cos³a/3 - cos³b/3`. -/
theorem integral_sin_mul_cos_sq (a b : ℝ) (hab : a ≤ b) :
    ∫ t in a..b, Real.sin t * (Real.cos t) ^ 2
      = (Real.cos a) ^ 3 / 3 - (Real.cos b) ^ 3 / 3 := by
  have hcd : Continuous (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2) :=
    Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun s : ℝ => -((Real.cos s) ^ 3) / 3) (Real.sin x * (Real.cos x) ^ 2) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => (Real.cos s) ^ 3)
        (3 * (Real.cos x) ^ 2 * (-Real.sin x)) x := (Real.hasDerivAt_cos x).pow 3
    have h2 : HasDerivAt (fun s : ℝ => -((Real.cos s) ^ 3) / 3)
        (-(3 * (Real.cos x) ^ 2 * (-Real.sin x)) / 3) x := h1.neg.div_const 3
    convert h2 using 1
    ring
  have hint' : IntervalIntegrable (fun x : ℝ => Real.sin x * (Real.cos x) ^ 2)
      MeasureTheory.volume a b := hcd.intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint']
  ring

theorem cos_inv_cube_mul_integral_le {β θ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hθ : θ ∈ Set.Icc (Real.pi / 4) (Real.pi / 2)) :
    (Real.cos θ)⁻¹ ^ 3
        * ∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (Real.pi / 2 - t) ^ β
      ≤ 32 * (Real.pi / 2 - θ) ^ β := by
  have hle : θ ≤ Real.pi / 2 := hθ.2
  have hθpos : 0 ≤ θ := le_trans (by positivity) hθ.1
  have hcd : Continuous (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2) :=
    Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  have hcont_pow : ContinuousOn (fun t : ℝ => (Real.pi / 2 - t) ^ β)
      (Set.uIcc θ (Real.pi / 2)) :=
    (continuous_const.sub continuous_id).continuousOn.rpow_const (fun _ _ => Or.inr hβ.le)
  have hint_f : IntervalIntegrable
      (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 * (Real.pi / 2 - t) ^ β)
      MeasureTheory.volume θ (Real.pi / 2) :=
    ((hcd.continuousOn).mul hcont_pow).intervalIntegrable
  have hint_g : IntervalIntegrable
      (fun t : ℝ => (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2))
      MeasureTheory.volume θ (Real.pi / 2) :=
    (hcd.continuousOn.const_mul _).intervalIntegrable
  have hXnn : 0 ≤ (Real.pi / 2 - θ) ^ β := Real.rpow_nonneg (by linarith) β
  -- pointwise comparison of the integrands: `(π/2-t)^β ≤ (π/2-θ)^β` on `[θ, π/2]`
  have hpt : ∀ t ∈ Set.Icc θ (Real.pi / 2),
      Real.sin t * (Real.cos t) ^ 2 * (Real.pi / 2 - t) ^ β
        ≤ (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hθpos ht.1
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [ht.2, Real.pi_pos])
    have hb : 0 ≤ Real.sin t * (Real.cos t) ^ 2 := mul_nonneg hsin (sq_nonneg _)
    have hr : (Real.pi / 2 - t) ^ β ≤ (Real.pi / 2 - θ) ^ β :=
      Real.rpow_le_rpow (by linarith [ht.2]) (by linarith [ht.1]) hβ.le
    calc Real.sin t * (Real.cos t) ^ 2 * (Real.pi / 2 - t) ^ β
        ≤ (Real.sin t * (Real.cos t) ^ 2) * (Real.pi / 2 - θ) ^ β :=
          mul_le_mul_of_nonneg_left hr hb
      _ = (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) := by ring
  have hmono := intervalIntegral.integral_mono_on hle hint_f hint_g hpt
  have hint_val : ∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2
      = (Real.cos θ) ^ 3 / 3 := by
    rw [integral_sin_mul_cos_sq θ (Real.pi / 2) hle, Real.cos_pi_div_two]
    ring
  have hI : ∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (Real.pi / 2 - t) ^ β
      ≤ (Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 / 3) := by
    rw [intervalIntegral.integral_const_mul, hint_val] at hmono
    exact hmono
  have hcosnn : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hle⟩
  have hcoef_nn : 0 ≤ (Real.cos θ)⁻¹ ^ 3 := pow_nonneg (inv_nonneg.mpr hcosnn) 3
  have hmain : (Real.cos θ)⁻¹ ^ 3 * ((Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 / 3))
      ≤ 32 * (Real.pi / 2 - θ) ^ β := by
    by_cases ha : Real.cos θ = 0
    · have h1 : (Real.cos θ)⁻¹ ^ 3 = 0 := by rw [ha, inv_zero]; norm_num
      rw [h1, zero_mul]
      exact mul_nonneg (by norm_num) hXnn
    · have h3 : (Real.cos θ)⁻¹ ^ 3 * ((Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 / 3))
          = (Real.pi / 2 - θ) ^ β / 3 := by
        rw [inv_pow]
        field_simp
      rw [h3]
      linarith [hXnn]
  exact (mul_le_mul_of_nonneg_left hI hcoef_nn).trans hmain

end Work.FTS_EllLimOK.ProducerH.BoxAux
