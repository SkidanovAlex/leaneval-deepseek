import Mathlib
import Submission.Work.Analysis.Interpolation.Basic

/-!
# Differentiability of a bilinear form evaluated on analytic families

If a bilinear form `Λ : (α → ℂ) → (β → ℂ) → ℂ`, evaluated on the analytic families
attached to two simple functions, admits the level-set decomposition

`Λ (analyticFamily f t₀ t₁ z) (analyticFamily g u₀ u₁ z)
  = ∑_{c ∈ f.range} ∑_{d ∈ g.range} (phasePow c (expFamily t₀ t₁ z) * phasePow d (expFamily u₀ u₁ z))
      * Λ (𝟙_{f ⁻¹' {c}}) (𝟙_{g ⁻¹' {d}})`

(for all `z : ℂ`), then `z ↦ Λ (analyticFamily f t₀ t₁ z) (analyticFamily g u₀ u₁ z)`
is entire: the ranges of the simple functions `f` and `g` are finite, and each summand is
the product of the entire functions `phasePow c (expFamily t₀ t₁ z)` and
`phasePow d (expFamily u₀ u₁ z)` (`differentiable_phasePow_expFamily`) with a
`z`-independent constant.  This is the differentiability input for the Hadamard
three-lines argument for arbitrary (merely) bilinear forms.

## Main results

* `Work.Analysis.Interpolation.differentiable_sum_sum`: a finite double sum of
  differentiable functions of `z` is differentiable;
* `Work.Analysis.Interpolation.differentiable_of_decomposition`: the target lemma.
-/

namespace Work.Analysis.Interpolation

open MeasureTheory
open scoped ENNReal NNReal

/-! ## A finite double sum of differentiable functions -/

/-- A finite double sum of differentiable functions of `z` is differentiable.  The sum
is over two `Finset`s, and each summand may depend on both indices and on `z`. -/
lemma differentiable_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : ι → κ → ℂ → ℂ) (h : ∀ c ∈ s, ∀ d ∈ t, Differentiable ℂ (fun z => A c d z)) :
    Differentiable ℂ (fun z => ∑ c ∈ s, ∑ d ∈ t, A c d z) := by
  have h1 : (fun z => ∑ c ∈ s, ∑ d ∈ t, A c d z) = ∑ c ∈ s, (fun z => ∑ d ∈ t, A c d z) := by
    funext z; simp
  rw [h1]
  refine Differentiable.sum fun c hc => ?_
  have h2 : (fun z => ∑ d ∈ t, A c d z) = ∑ d ∈ t, (fun z => A c d z) := by
    funext z; simp
  rw [h2]
  exact Differentiable.sum fun d hd => h c hc d hd

/-! ## The target lemma -/

/-- If the bilinear form `Λ` evaluated on the analytic families of two simple functions
decomposes as a finite sum over level sets with coefficients
`phasePow c (expFamily t₀ t₁ z) * phasePow d (expFamily u₀ u₁ z)` times
`z`-independent constants, then `z ↦ Λ (analyticFamily f t₀ t₁ z)
(analyticFamily g u₀ u₁ z)` is entire. -/
lemma differentiable_of_decomposition {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (Λ : (α → ℂ) → (β → ℂ) → ℂ) (f : SimpleFunc α ℂ) (g : SimpleFunc β ℂ) (t₀ t₁ u₀ u₁ : ℂ) (hΛ : ∀ z : ℂ, Λ (Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) t₀ t₁ z) (Work.Analysis.Interpolation.analyticFamily (g : β → ℂ) u₀ u₁ z) = ∑ c ∈ f.range, ∑ d ∈ g.range, (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily t₀ t₁ z) * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily u₀ u₁ z)) * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ))))) : Differentiable ℂ fun z : ℂ => Λ (Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) t₀ t₁ z) (Work.Analysis.Interpolation.analyticFamily (g : β → ℂ) u₀ u₁ z) := by
  -- rewrite the function of `z` as the finite double sum provided by `hΛ`
  have hF : (fun z : ℂ => Λ (Work.Analysis.Interpolation.analyticFamily (f : α → ℂ) t₀ t₁ z) (Work.Analysis.Interpolation.analyticFamily (g : β → ℂ) u₀ u₁ z))
      = fun z : ℂ => ∑ c ∈ f.range, ∑ d ∈ g.range, (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily t₀ t₁ z) * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily u₀ u₁ z)) * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))) := by
    funext z
    exact hΛ z
  rw [hF]
  -- the double sum is differentiable, term by term
  refine differentiable_sum_sum f.range g.range (fun c d z => (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily t₀ t₁ z) * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily u₀ u₁ z)) * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ))))) ?_
  intro c _ d _
  exact ((differentiable_phasePow_expFamily c t₀ t₁).mul
    (differentiable_phasePow_expFamily d u₀ u₁)).mul (differentiable_const _)

end Work.Analysis.Interpolation
