import Mathlib
import Submission.Work.Analysis.Interpolation.Basic
import Submission.Port.Aesm

/-!
# The analytic family at a purely imaginary parameter: the `Lᵖ`-norm of the endpoint

For the Riesz--Thorin / Stein interpolation argument of Krause--Mirek--Tao, *Pointwise ergodic
theorems for non-conventional bilinear polynomial averages*, Annals 195 (2022), one evaluates the
analytic family

`analyticFamily f t₀ t₁ z = fun x ↦ ‖f x‖ ^ ((1 - z) t₀ + z t₁) • f x / ‖f x‖`

of a function `f` at the *left* endpoint `z = iy` of the interpolation strip (`z.re = 0`), where
the exponent family takes the value `t₀ = p / p₀`.

This file records the resulting identity: if `z.re = 0`, then the exponent family at
`t₀ = p/p₀`, `t₁ = p/p₁` has real part `p / p₀ > 0`, so pointwise
`‖analyticFamily f t₀ t₁ z x‖ₑ = ‖f x‖ₑ ^ (p / p₀)`, and hence

`eLpNorm (analyticFamily f t₀ t₁ z) (ofReal p₀) μ = (eLpNorm f (ofReal p) μ) ^ (p / p₀)`.

Both extended seminorms are expanded with `eLpNorm_eq_lintegral_rpow_enorm_toReal` and the
integral of the family is related to that of `f` by
`Work.Analysis.Interpolation.lintegral_enorm_analyticFamily_rpow`; the remaining exponent
arithmetic is `(1/p) * (p/p₀) = 1/p₀` via `ENNReal.rpow_mul`.
-/

-- The hypothesis `hp₁` is part of the (fixed) statement but is not needed when `z.re = 0`,
-- since the exponent `t₁ = p/p₁` is multiplied by `z.re = 0`.
set_option linter.unusedVariables false

namespace Work.Analysis.Interpolation

open MeasureTheory
open scoped ENNReal NNReal

/-- **The analytic family at a purely imaginary parameter.**  If `z.re = 0` then the parameter `z`
lies on the line of the left endpoint of the strip, so the analytic family with exponents
`t₀ = p / p₀`, `t₁ = p / p₁` has pointwise extended norm `‖f x‖ₑ ^ (p / p₀)`; consequently its
`ℒ^{p₀}`-seminorm is the `(p / p₀)`-th power of the `ℒ^p`-seminorm of `f`. -/
lemma eLpNorm_analyticFamily_re_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} {p₀ p₁ p : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp : 0 < p) {z : ℂ} (hz : z.re = 0) (hF : AEStronglyMeasurable (Work.Analysis.Interpolation.analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z) μ := by pw_aesm) (hf : AEStronglyMeasurable f μ := by pw_aesm) : eLpNorm (Work.Analysis.Interpolation.analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z) (ENNReal.ofReal p₀) μ = (eLpNorm f (ENNReal.ofReal p) μ) ^ (p / p₀) := by
  have hp₀ne : p₀ ≠ 0 := ne_of_gt hp₀
  have hpne : p ≠ 0 := ne_of_gt hp
  -- the real part of the exponent family at `z` is `p / p₀`, since `z.re = 0`
  have hr : 0 < p / p₀ := by positivity
  have hre : (expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z).re = p / p₀ := by
    rw [expFamily_ofReal_re, hz, zero_mul, sub_zero, one_mul, add_zero]
  -- exponent arithmetic
  have hmul : p₀ * (p / p₀) = p := by field_simp
  have hexp : (1 / p) * (p / p₀) = 1 / p₀ := by field_simp
  -- expand both extended seminorms into explicit integrals
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hF) (p := ENNReal.ofReal p₀)
      (f := Work.Analysis.Interpolation.analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
      (ENNReal.ofReal_ne_zero_iff.mpr hp₀) ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf) (p := ENNReal.ofReal p) (f := f)
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp₀.le, ENNReal.toReal_ofReal hp.le,
    -- pointwise norm of the family, and the resulting integral
    lintegral_enorm_analyticFamily_rpow (μ := μ) hr hre, hmul,
    -- `(A ^ (1/p)) ^ (p/p₀) = A ^ ((1/p) * (p/p₀)) = A ^ (1/p₀)`
    ← ENNReal.rpow_mul, hexp]

end Work.Analysis.Interpolation
