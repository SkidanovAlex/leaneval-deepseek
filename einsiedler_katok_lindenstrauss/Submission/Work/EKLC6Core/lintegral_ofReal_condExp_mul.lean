import Mathlib
import Submission.Work.EKLC6Core.C6Aux

namespace Work.EKLC6Core

open MeasureTheory Filter
open scoped ENNReal MeasureTheory

/-- **Pull-out / adjoint property for a pair of functions with equal integrals on all
`m`-measurable sets.**

Let `m ≤ mX` be σ-algebras on `X`, let `μ` be a measure on `X`, and let `Y, h : X → ℝ≥0∞`
with `Y` `m`-measurable, `h` a.e.-measurable with respect to `μ`, and such that
`∫⁻ x in s, Y x ∂μ = ∫⁻ x in s, h x ∂μ` for every `m`-measurable set `s`.
Then for every `m`-measurable `g : X → ℝ≥0∞`,

`∫⁻ x, g x * Y x ∂μ = ∫⁻ x, g x * h x ∂μ`.

The proof passes to the measures `ν_Y = (μ.trim hm).withDensity Y` and
`ν_h = (μ.withDensity h).trim hm` (as measures on `m`), which agree on every `m`-measurable
set by the hypothesis, and compares the integrals of the `m`-measurable function `g`. -/
theorem lintegral_mul_eq_of_forall_setLIntegral_eq {X : Type*} {m : MeasurableSpace X}
    [mX : MeasurableSpace X] (hm : m ≤ mX) (μ : Measure X)
    {Y h : X → ENNReal} (hY : Measurable[m] Y) (hh : AEMeasurable h μ)
    (hset : ∀ s, MeasurableSet[m] s → ∫⁻ x in s, Y x ∂μ = ∫⁻ x in s, h x ∂μ)
    {g : X → ENNReal} (hg : Measurable[m] g) :
    ∫⁻ x, g x * Y x ∂μ = ∫⁻ x, g x * h x ∂μ := by
  have hgm : Measurable g := hg.mono hm le_rfl
  have hgY : Measurable[m] (fun x => g x * Y x) := hg.mul hY
  have key : (μ.trim hm).withDensity Y = (μ.withDensity h).trim hm := by
    refine @Measure.ext X m _ _ (fun s hs => ?_)
    rw [withDensity_apply Y hs, setLIntegral_trim hm hY hs, hset s hs,
        trim_measurableSet_eq hm hs, withDensity_apply h (hm s hs)]
  calc ∫⁻ x, g x * Y x ∂μ
      = ∫⁻ x, g x * Y x ∂(μ.trim hm) := (lintegral_trim hm hgY).symm
    _ = ∫⁻ x, Y x * g x ∂(μ.trim hm) := lintegral_congr (fun x => mul_comm _ _)
    _ = ∫⁻ x, g x ∂((μ.trim hm).withDensity Y) :=
        (lintegral_withDensity_eq_lintegral_mul (μ.trim hm) hY hg).symm
    _ = ∫⁻ x, g x ∂((μ.withDensity h).trim hm) := by rw [key]
    _ = ∫⁻ x, g x ∂(μ.withDensity h) := lintegral_trim hm hg
    _ = ∫⁻ x, h x * g x ∂μ :=
        lintegral_withDensity_eq_lintegral_mul₀ hh hgm.aemeasurable
    _ = ∫⁻ x, g x * h x ∂μ := lintegral_congr (fun x => mul_comm _ _)

/-- The adjoint ("pull-out") property of the conditional expectation, in the `ℝ≥0∞`-valued
setting: for `f` integrable and nonnegative a.e. and `g` nonnegative, `m`-measurable,

`∫⁻ x, g x * ENNReal.ofReal (condExp m μ f x) ∂μ = ∫⁻ x, g x * ENNReal.ofReal (f x) ∂μ`. -/
theorem lintegral_ofReal_condExp_mul {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (hm : m ≤ mX) (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Integrable f μ)
    (hf0 : 0 ≤ᵐ[μ] f) {g : X → ENNReal} (hg : Measurable[m] g) :
    ∫⁻ x, g x * ENNReal.ofReal (condExp m μ f x) ∂μ =
      ∫⁻ x, g x * ENNReal.ofReal (f x) ∂μ := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  refine lintegral_mul_eq_of_forall_setLIntegral_eq hm μ ?_ ?_ ?_ hg
  · exact ENNReal.measurable_ofReal.comp stronglyMeasurable_condExp.measurable
  · exact ENNReal.measurable_ofReal.comp_aemeasurable hf.aestronglyMeasurable.aemeasurable
  · intro s hs
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_condExp.integrableOn
          (ae_restrict_of_ae (condExp_nonneg hf0)),
        setIntegral_condExp hm hf hs,
        ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_restrict_of_ae hf0)]

end Work.EKLC6Core
