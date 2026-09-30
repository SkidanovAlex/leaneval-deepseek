import Mathlib
import Submission.Work.BMF.halasz_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Measurability of the Dirichlet series `Kser` along a vertical line

`Work.BMF.Kser f s = ∑' n, (f n * log n) * n^{-s}` is the Dirichlet series with coefficients
`f n * log n`.  Since `n^{-(a + iτ)} = n^{-a} · n^{-iτ}` and `n^{-iτ}` is the continuous (hence
Borel measurable) function `τ ↦ exp(-i τ log n)`, every summand is measurable in `τ`.  Mathlib's
`Measurable.tsum` then gives measurability of the (unconditionally summed, and continued by `0`
where the series fails to converge) total sum.

The hypothesis `1 < a` is not needed for this measurability statement.
-/

set_option linter.unusedVariables false

namespace Work.BMF.casdiv

open MeasureTheory

/-- The `n`-th summand `τ ↦ (f n * log n) * n^{-(a + i τ)}` of `Kser f` restricted to the vertical
line `s = a + i τ` is Borel measurable in `τ`. -/
lemma measurable_Kser_term (f : ℕ → ℂ) (a : ℝ) (n : ℕ) :
    Measurable (fun τ : ℝ =>
      (f n * (Real.log n : ℂ)) * (n : ℂ) ^ (-((a : ℂ) + (τ : ℂ) * Complex.I))) := by
  fun_prop

theorem Kser_line_aemeasurable (f : ℕ → ℂ) (a : ℝ) (ha : 1 < a) :
    AEMeasurable (fun τ : ℝ => Work.BMF.Kser f ((a : ℂ) + (τ : ℂ) * Complex.I)) volume := by
  unfold Work.BMF.Kser
  exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) (E := ℂ)
      (f := fun n (τ : ℝ) =>
        (f n * (Real.log n : ℂ)) * (n : ℂ) ^ (-((a : ℂ) + (τ : ℂ) * Complex.I)))
      (fun n => measurable_Kser_term f a n)).aemeasurable

end Work.BMF.casdiv
