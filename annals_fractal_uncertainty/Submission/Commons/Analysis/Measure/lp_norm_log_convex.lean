import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Commons.Analysis.Measure

open scoped BigOperators ENNReal

open MeasureTheory in
/-- Auxiliary Hölder type interpolation inequality for the `ℝ≥0∞`-valued integral of
`‖f‖ₑ ^ t`: if `1/q = (1-θ)/p + θ/r` then
`(∫⁻ ‖f‖ₑ^q)^(1/q) ≤ (∫⁻ ‖f‖ₑ^p)^((1-θ)/p) * (∫⁻ ‖f‖ₑ^r)^(θ/r)`. -/
theorem lintegral_enorm_rpow_interpolate {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p q r θ : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hqr : 1 / q = (1 - θ) / p + θ / r)
    {f : α → ℂ} (hf : AEMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ ^ q ∂μ) ^ (1 / q)
      ≤ (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ ((1 - θ) / p)
        * (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ^ (θ / r) := by
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hE0 : 0 ≤ (1 - θ) * q / p := div_nonneg (mul_nonneg h1θ hq.le) hp.le
  have hA0 : 0 ≤ θ * q / r := div_nonneg (mul_nonneg hθ0 hq.le) hr.le
  have hab : (1 - θ) * q / p + θ * q / r = 1 := by
    have h : (1 - θ) * q / p + θ * q / r = q * ((1 - θ) / p + θ / r) := by
      field_simp
    rw [h, ← hqr, mul_one_div, div_self hq.ne']
  have hHolder :
      ∫⁻ x, (‖f x‖ₑ ^ p) ^ ((1 - θ) * q / p) * (‖f x‖ₑ ^ r) ^ (θ * q / r) ∂μ
        ≤ (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ ((1 - θ) * q / p)
          * (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ^ (θ * q / r) :=
    ENNReal.lintegral_mul_norm_pow_le (μ := μ)
      (f := fun x => ‖f x‖ₑ ^ p) (g := fun x => ‖f x‖ₑ ^ r)
      (hf.enorm.pow_const p) (hf.enorm.pow_const r) hE0 hA0 hab
  have hL : ∫⁻ x, (‖f x‖ₑ ^ p) ^ ((1 - θ) * q / p) * (‖f x‖ₑ ^ r) ^ (θ * q / r) ∂μ
      = ∫⁻ x, ‖f x‖ₑ ^ q ∂μ := by
    refine lintegral_congr fun x => ?_
    have hpa : p * ((1 - θ) * q / p) = (1 - θ) * q := by field_simp
    have hrb : r * (θ * q / r) = θ * q := by field_simp
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg (p * ((1 - θ) * q / p)) (r * (θ * q / r))
        (by rw [hpa]; exact mul_nonneg h1θ hq.le)
        (by rw [hrb]; exact mul_nonneg hθ0 hq.le)]
    rw [hpa, hrb]
    congr 1
    ring
  rw [hL] at hHolder
  have hstep : (∫⁻ x, ‖f x‖ₑ ^ q ∂μ) ^ (1 / q)
      ≤ ((∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ ((1 - θ) * q / p)
          * (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ^ (θ * q / r)) ^ (1 / q) :=
    ENNReal.rpow_le_rpow hHolder (one_div_pos.mpr hq).le
  refine hstep.trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hq).le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  have h1 : (1 - θ) * q / p * (1 / q) = (1 - θ) / p := by field_simp
  have h2 : θ * q / r * (1 / q) = θ / r := by field_simp
  rw [h1, h2]

open MeasureTheory in
/-- Auxiliary: for integrable `‖f‖^t` (with `t > 0`) the `ℝ≥0∞`-valued integral of the
`enorm` is the `ofReal` of the real valued integral. -/
theorem lintegral_enorm_rpow_eq_ofReal {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {t : ℝ} (ht : 0 < t) {f : α → ℂ} (hint : Integrable (fun x => ‖f x‖ ^ t) μ) :
    ∫⁻ x, ‖f x‖ₑ ^ t ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ t ∂μ) := by
  have hfun : (fun x => ‖f x‖ₑ ^ t) = fun x => ENNReal.ofReal (‖f x‖ ^ t) := by
    funext x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ht.le]
  rw [hfun]
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) t)).symm

open scoped BigOperators

open MeasureTheory in
/-- Lyapunov's inequality: log-convexity of the `L^p` norm,
`‖f‖_q ≤ ‖f‖_p^{1-θ} · ‖f‖_r^θ` when `1/q = (1-θ)/p + θ/r` and `0 < p ≤ q ≤ r`. -/
theorem lp_norm_log_convex {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p q r θ : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hqr : 1 / q = (1 - θ) / p + θ / r)
    {f : α → ℂ} (hf : AEMeasurable f μ)
    (hintp : Integrable (fun x => ‖f x‖ ^ p) μ)
    (hintq : Integrable (fun x => ‖f x‖ ^ q) μ)
    (hintr : Integrable (fun x => ‖f x‖ ^ r) μ) :
    (∫ x, ‖f x‖ ^ q ∂μ) ^ (1 / q)
      ≤ (∫ x, ‖f x‖ ^ p ∂μ) ^ ((1 - θ) / p) * (∫ x, ‖f x‖ ^ r ∂μ) ^ (θ / r) := by
  have hENN := lintegral_enorm_rpow_interpolate μ hp hq hr hθ0 hθ1 hqr hf
  have hP := lintegral_enorm_rpow_eq_ofReal μ hp hintp
  have hQ := lintegral_enorm_rpow_eq_ofReal μ hq hintq
  have hR := lintegral_enorm_rpow_eq_ofReal μ hr hintr
  rw [hP, hQ, hR] at hENN
  have hBP : (0 : ℝ) ≤ ∫ x, ‖f x‖ ^ p ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) p)
  have hBQ : (0 : ℝ) ≤ ∫ x, ‖f x‖ ^ q ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) q)
  have hBR : (0 : ℝ) ≤ ∫ x, ‖f x‖ ^ r ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) r)
  have htop : (ENNReal.ofReal (∫ x, ‖f x‖ ^ p ∂μ)) ^ ((1 - θ) / p)
      * (ENNReal.ofReal (∫ x, ‖f x‖ ^ r ∂μ)) ^ (θ / r) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (div_nonneg (sub_nonneg.mpr hθ1) hp.le)
        ENNReal.ofReal_lt_top.ne
    · exact ENNReal.rpow_ne_top_of_nonneg (div_nonneg hθ0 hr.le) ENNReal.ofReal_lt_top.ne
  have htoReal := ENNReal.toReal_mono htop hENN
  have hLHS : ((ENNReal.ofReal (∫ x, ‖f x‖ ^ q ∂μ)) ^ (1 / q)).toReal
      = (∫ x, ‖f x‖ ^ q ∂μ) ^ (1 / q) := by
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hBQ]
  have hRHS : ((ENNReal.ofReal (∫ x, ‖f x‖ ^ p ∂μ)) ^ ((1 - θ) / p)
        * (ENNReal.ofReal (∫ x, ‖f x‖ ^ r ∂μ)) ^ (θ / r)).toReal
      = (∫ x, ‖f x‖ ^ p ∂μ) ^ ((1 - θ) / p) * (∫ x, ‖f x‖ ^ r ∂μ) ^ (θ / r) := by
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hBP, ENNReal.toReal_ofReal hBR]
  rw [hLHS, hRHS] at htoReal
  exact htoReal

end Commons.Analysis.Measure