import Mathlib
import Submission.Work.Analysis.Interpolation.Basic
import Submission.Port.Aesm

namespace Work.Analysis.Interpolation

open MeasureTheory
open scoped ENNReal NNReal

/-- On the line `re z = 1` the analytic family sits at the exponent `p / p₁`, so that both
the pointwise extended norm and the `ℒᵖ` integral of the family are those of `f` at the
exponent `p`: the `L^{p₁}` seminorm of the family is the `(p/p₁)`-th power of the `L^p`
seminorm of `f`. -/
lemma eLpNorm_analyticFamily_re_one {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} {p₀ p₁ p : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp : 0 < p) {z : ℂ} (hz : z.re = 1) (hF : AEStronglyMeasurable (Work.Analysis.Interpolation.analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z) μ := by pw_aesm) (hf : AEStronglyMeasurable f μ := by pw_aesm) : eLpNorm (Work.Analysis.Interpolation.analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z) (ENNReal.ofReal p₁) μ = (eLpNorm f (ENNReal.ofReal p) μ) ^ (p / p₁) := by
  have hr : 0 < p / p₁ := by positivity
  have hre : (Work.Analysis.Interpolation.expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z).re
      = p / p₁ := by
    rw [Work.Analysis.Interpolation.expFamily_ofReal_re, hz]; ring
  have hpq : p₁ * (p / p₁) = p := by field_simp
  have hkey : ∫⁻ x, ‖Work.Analysis.Interpolation.analyticFamily f ((p / p₀ : ℝ) : ℂ)
      ((p / p₁ : ℝ) : ℂ) z x‖ₑ ^ p₁ ∂μ = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    rw [Work.Analysis.Interpolation.lintegral_enorm_analyticFamily_rpow μ hr hre, hpq]
  have hinv : (1 / p) * (p / p₁) = 1 / p₁ := by field_simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hF)
      (ENNReal.ofReal_ne_zero_iff.mpr hp₁) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp₁.le, hkey,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf)
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le,
      ← ENNReal.rpow_mul, hinv]

end Work.Analysis.Interpolation
