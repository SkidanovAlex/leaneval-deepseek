import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory
open scoped ENNReal

namespace Commons.Measure.Integral

/-- Weighted Hölder inequality for real exponents.  For `p ≥ 1` and nonnegative functions
`a`, `w` on a measure space, with `a^p · w` and `w` integrable,

    ∫ a·w ≤ (∫ a^p·w)^(1/p) · (∫ w)^(1 - 1/p) .

The proof factorises `a·w = (a^p·w)^(1/p) · w^(1-1/p)` pointwise and applies Hölder's
inequality with conjugate exponents `p` and `p/(p-1)` in `ℝ≥0∞`, then transfers the
result back to the Bochner integral. -/
theorem integral_mul_le_rpow_mul_integral_rpow {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p : ℝ} (hp : 1 ≤ p) {a w : α → ℝ}
    (ha : ∀ y, 0 ≤ a y) (hw : ∀ y, 0 ≤ w y)
    (hapw : Integrable (fun y => a y ^ p * w y) μ)
    (hwint : Integrable w μ) :
    ∫ y, a y * w y ∂μ ≤
      (∫ y, a y ^ p * w y ∂μ) ^ (1 / p) * (∫ y, w y ∂μ) ^ (1 - 1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1p : 0 ≤ (1 : ℝ) / p := by positivity
  have hq : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one hp0]; exact hp
  have hpq : 1 / p + (1 - 1 / p) = 1 := by ring
  have hA0 : 0 ≤ ∫ y, a y ^ p * w y ∂μ :=
    integral_nonneg fun y => mul_nonneg (Real.rpow_nonneg (ha y) p) (hw y)
  have hW0 : 0 ≤ ∫ y, w y ∂μ := integral_nonneg hw
  -- a.e. measurability of the two `ℝ≥0∞`-valued functions
  have hU : AEMeasurable (fun y => ENNReal.ofReal (a y ^ p * w y)) μ :=
    hapw.aemeasurable.ennreal_ofReal
  have hV : AEMeasurable (fun y => ENNReal.ofReal (w y)) μ :=
    hwint.aemeasurable.ennreal_ofReal
  -- pointwise factorisation
  have hpt : ∀ y, ENNReal.ofReal (a y * w y)
      = (ENNReal.ofReal (a y ^ p * w y)) ^ (1 / p) * (ENNReal.ofReal (w y)) ^ (1 - 1 / p) := by
    intro y
    have hAy : 0 ≤ a y := ha y
    have hWy : 0 ≤ w y := hw y
    have hAp : 0 ≤ a y ^ p := Real.rpow_nonneg hAy p
    have hApW : 0 ≤ a y ^ p * w y := mul_nonneg hAp hWy
    have e1 : (a y ^ p * w y) ^ (1 / p) = (a y ^ p) ^ (1 / p) * w y ^ (1 / p) :=
      Real.mul_rpow hAp hWy
    have e2 : (a y ^ p) ^ (1 / p) = a y := by
      rw [← Real.rpow_mul hAy p (1 / p), mul_one_div, div_self hpne, Real.rpow_one]
    have e3 : w y ^ (1 / p) * w y ^ (1 - 1 / p) = w y := by
      rw [← Real.rpow_add_of_nonneg hWy h1p hq,
        show 1 / p + (1 - 1 / p) = (1 : ℝ) by ring, Real.rpow_one]
    have hfac : a y * w y = (a y ^ p * w y) ^ (1 / p) * w y ^ (1 - 1 / p) := by
      rw [e1, e2, mul_assoc, e3]
    rw [hfac, ENNReal.ofReal_mul (Real.rpow_nonneg hApW (1 / p)),
      ← ENNReal.ofReal_rpow_of_nonneg hApW h1p,
      ← ENNReal.ofReal_rpow_of_nonneg hWy hq]
  -- the `ℝ≥0∞` Hölder bound
  have hlin : ∫⁻ y, ENNReal.ofReal (a y * w y) ∂μ ≤
      (∫⁻ y, ENNReal.ofReal (a y ^ p * w y) ∂μ) ^ (1 / p) *
        (∫⁻ y, ENNReal.ofReal (w y) ∂μ) ^ (1 - 1 / p) := by
    calc ∫⁻ y, ENNReal.ofReal (a y * w y) ∂μ
        = ∫⁻ y, (ENNReal.ofReal (a y ^ p * w y)) ^ (1 / p) *
            (ENNReal.ofReal (w y)) ^ (1 - 1 / p) ∂μ :=
          lintegral_congr hpt
      _ ≤ (∫⁻ y, ENNReal.ofReal (a y ^ p * w y) ∂μ) ^ (1 / p) *
            (∫⁻ y, ENNReal.ofReal (w y) ∂μ) ^ (1 - 1 / p) :=
          ENNReal.lintegral_mul_norm_pow_le hU hV h1p hq hpq
  have hUA : ∫⁻ y, ENNReal.ofReal (a y ^ p * w y) ∂μ = ENNReal.ofReal (∫ y, a y ^ p * w y ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hapw
      (ae_of_all μ fun y => mul_nonneg (Real.rpow_nonneg (ha y) p) (hw y))).symm
  have hVW : ∫⁻ y, ENNReal.ofReal (w y) ∂μ = ENNReal.ofReal (∫ y, w y ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hwint (ae_of_all μ hw)).symm
  have hen : ∫⁻ y, ENNReal.ofReal (a y * w y) ∂μ ≤
      ENNReal.ofReal ((∫ y, a y ^ p * w y ∂μ) ^ (1 / p) *
        (∫ y, w y ∂μ) ^ (1 - 1 / p)) := by
    rw [hUA, hVW] at hlin
    rw [ENNReal.ofReal_rpow_of_nonneg hA0 h1p,
      ENNReal.ofReal_rpow_of_nonneg hW0 hq,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hA0 (1 / p))] at hlin
    exact hlin
  have hstep : ENNReal.ofReal (∫ y, a y * w y ∂μ) ≤ ∫⁻ y, ENNReal.ofReal (a y * w y) ∂μ := by
    by_cases hm : AEStronglyMeasurable (fun y => a y * w y) μ
    · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all μ fun y => mul_nonneg (ha y) (hw y)) hm]
      exact ENNReal.ofReal_toReal_le
    · rw [integral_non_aestronglyMeasurable hm, ENNReal.ofReal_zero]
      exact bot_le
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hA0 (1 / p))
      (Real.rpow_nonneg hW0 (1 - 1 / p)))).mp (hstep.trans hen)

/-- Norm bound for a function satisfying the convolution identity `g x = ∫ y, g (x-y) ψ y`. -/
theorem norm_le_integral_norm_mul {k : ℕ} {g : EuclideanSpace ℝ (Fin k) → ℂ}
    {ψ : EuclideanSpace ℝ (Fin k) → ℝ} (hψnn : ∀ y, 0 ≤ ψ y)
    (hconv : ∀ x, g x = ∫ y, g (x - y) * ((ψ y : ℝ) : ℂ))
    (x : EuclideanSpace ℝ (Fin k)) :
    ‖g x‖ ≤ ∫ y, ‖g (x - y)‖ * ψ y := by
  calc ‖g x‖ = ‖∫ y, g (x - y) * ((ψ y : ℝ) : ℂ)‖ := by rw [hconv x]
    _ ≤ ∫ y, ‖g (x - y) * ((ψ y : ℝ) : ℂ)‖ :=
        norm_integral_le_integral_norm (fun y => g (x - y) * ((ψ y : ℝ) : ℂ))
    _ = ∫ y, ‖g (x - y)‖ * ψ y := by
        apply integral_congr_ae
        filter_upwards with y
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hψnn y)]

/-- Convolution `L^p` bound: if `g = g ⋆ ψ` with `ψ ≥ 0` integrable and
`‖g(x-·)‖^p ψ` integrable, then
`‖g x‖^p ≤ (∫ ψ)^(p-1) · ∫ ‖g (x-·)‖^p ψ` for every `p ≥ 1`. -/
theorem abs_rpow_le_convolution_abs {k : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {g : EuclideanSpace ℝ (Fin k) → ℂ} {ψ : EuclideanSpace ℝ (Fin k) → ℝ}
    (hψnn : ∀ y, 0 ≤ ψ y) (hψ : MeasureTheory.Integrable ψ)
    (hconv : ∀ x, g x = ∫ y, g (x - y) * ((ψ y : ℝ) : ℂ))
    (x : EuclideanSpace ℝ (Fin k))
    (hint : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖g (x - y)‖ ^ p * ψ y)) :
    ‖g x‖ ^ p ≤ (∫ y, ψ y) ^ (p - 1) * ∫ y, ‖g (x - y)‖ ^ p * ψ y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpnn : 0 ≤ p := le_of_lt hp0
  have hA0 : 0 ≤ ∫ y, ‖g (x - y)‖ ^ p * ψ y :=
    integral_nonneg fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) p) (hψnn y)
  have hW0 : 0 ≤ ∫ y, ψ y := integral_nonneg hψnn
  -- Step 1: bring the norm inside the convolution integral.
  have h1 : ‖g x‖ ≤ ∫ y, ‖g (x - y)‖ * ψ y :=
    norm_le_integral_norm_mul hψnn hconv x
  -- Step 2: raise to the `p`-th power.
  have h2 : ‖g x‖ ^ p ≤ (∫ y, ‖g (x - y)‖ * ψ y) ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) h1 hpnn
  -- Step 3: weighted Hölder.
  have h3 : (∫ y, ‖g (x - y)‖ * ψ y) ≤
      (∫ y, ‖g (x - y)‖ ^ p * ψ y) ^ (1 / p) * (∫ y, ψ y) ^ (1 - 1 / p) :=
    integral_mul_le_rpow_mul_integral_rpow (μ := volume) (p := p)
      (a := fun y => ‖g (x - y)‖) (w := ψ) hp (fun y => norm_nonneg _) hψnn hint hψ
  -- Step 4: collect the exponents, using `(1/p)·p = 1` and `(1 - 1/p)·p = p - 1`.
  have h4 : (∫ y, ‖g (x - y)‖ * ψ y) ^ p ≤
      (∫ y, ‖g (x - y)‖ ^ p * ψ y) * (∫ y, ψ y) ^ (p - 1) := by
    have hnd : 0 ≤ ∫ y, ‖g (x - y)‖ * ψ y :=
      integral_nonneg fun y => mul_nonneg (norm_nonneg _) (hψnn y)
    calc (∫ y, ‖g (x - y)‖ * ψ y) ^ p
        ≤ ((∫ y, ‖g (x - y)‖ ^ p * ψ y) ^ (1 / p) *
            (∫ y, ψ y) ^ (1 - 1 / p)) ^ p :=
          Real.rpow_le_rpow hnd h3 hpnn
      _ = (∫ y, ‖g (x - y)‖ ^ p * ψ y) * (∫ y, ψ y) ^ (p - 1) := by
          rw [Real.mul_rpow (Real.rpow_nonneg hA0 (1 / p))
                (Real.rpow_nonneg hW0 (1 - 1 / p)),
            ← Real.rpow_mul hA0 (1 / p) p, ← Real.rpow_mul hW0 (1 - 1 / p) p,
            show (1 / p) * p = 1 by
              rw [mul_comm, mul_one_div, div_self (ne_of_gt hp0)],
            show (1 - 1 / p) * p = p - 1 by
              rw [sub_mul, one_mul, mul_comm (1 / p) p, mul_one_div, div_self (ne_of_gt hp0)],
            Real.rpow_one]
  calc ‖g x‖ ^ p ≤ (∫ y, ‖g (x - y)‖ * ψ y) ^ p := h2
    _ ≤ (∫ y, ‖g (x - y)‖ ^ p * ψ y) * (∫ y, ψ y) ^ (p - 1) := h4
    _ = (∫ y, ψ y) ^ (p - 1) * ∫ y, ‖g (x - y)‖ ^ p * ψ y := by ring

end Commons.Measure.Integral