import Mathlib
import Submission.Work.Analysis.Interpolation.Basic

/-!
# The analytic family of a simple function is a finite sum of level-set indicators

For a simple function `f : SimpleFunc α ℂ` and the affine exponent family
`expFamily t₀ t₁ z = (1 - z) * t₀ + z * t₁`, the analytic family
`analyticFamily f t₀ t₁ z = fun x ↦ phasePow (f x) (expFamily t₀ t₁ z)` is
equal to the finite sum, over the (finitely many) values `c` of `f`, of
`phasePow c (expFamily t₀ t₁ z)` times the indicator of the level set
`f ⁻¹' {c}`.

This is the representation of the analytic family as a finite linear
combination of level-set indicators with entire coefficients which makes the
Hadamard three-lines argument run for arbitrary (merely) bilinear forms: the
indicators do not depend on `z`, and the `z`-dependence sits in the entire
coefficients `phasePow c (expFamily t₀ t₁ z)`.
-/

namespace Work.Analysis.Interpolation

open MeasureTheory
open scoped ENNReal NNReal

lemma analyticFamily_eq_sum {α : Type*} [MeasurableSpace α] (f : SimpleFunc α ℂ) (t₀ t₁ : ℂ) (z : ℂ) : Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) t₀ t₁ z = ∑ c ∈ f.range, Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily t₀ t₁ z) • Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)) := by
  funext x
  -- the value `f x` is one of the (finitely many) values of `f`
  have hmem : (f : α → ℂ) x ∈ f.range := SimpleFunc.mem_range_self f x
  -- every summand other than the one indexed by `f x` vanishes at `x`
  have h₀ : ∀ b ∈ f.range, b ≠ (f : α → ℂ) x →
      (Work.Analysis.Interpolation.phasePow b (Work.Analysis.Interpolation.expFamily t₀ t₁ z) •
        Set.indicator ((f : α → ℂ) ⁻¹' {b}) (fun _ => (1 : ℂ))) x = 0 := by
    intro b _ hne
    rw [Pi.smul_apply, Set.indicator_of_notMem, smul_zero]
    intro hx
    exact hne (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx)).symm
  trans Work.Analysis.Interpolation.phasePow ((f : α → ℂ) x) (Work.Analysis.Interpolation.expFamily t₀ t₁ z)
  · rfl
  · rw [Finset.sum_apply, Finset.sum_eq_single_of_mem ((f : α → ℂ) x) hmem h₀]
    simp

/-- The analytic family of a simple function is a.e.-measurable. -/
lemma aemeasurable_analyticFamily {β : Type*} [MeasurableSpace β] {ν : Measure β}
    (g : SimpleFunc β ℂ) (t₀ t₁ z : ℂ) :
    AEMeasurable (analyticFamily (g : β → ℂ) t₀ t₁ z) ν := by
  rw [analyticFamily_eq_sum]
  refine Finset.aemeasurable_sum _ fun c _ => ?_
  have hrew : phasePow c (expFamily t₀ t₁ z) • Set.indicator (g ⁻¹' {c}) (fun _ => (1 : ℂ))
      = Set.indicator (g ⁻¹' {c}) (fun _ => phasePow c (expFamily t₀ t₁ z)) := by
    ext y
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hy : y ∈ g ⁻¹' {c}
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [hrew]
  exact (measurable_const.indicator (measurableSet_preimage (SimpleFunc.measurable g)
    (measurableSet_singleton c))).aemeasurable

end Work.Analysis.Interpolation
