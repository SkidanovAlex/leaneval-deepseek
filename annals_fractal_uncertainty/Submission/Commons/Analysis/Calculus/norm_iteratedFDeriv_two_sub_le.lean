import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.CompletePartialOrder

set_option linter.unusedVariables false

namespace Commons.Analysis.Calculus

/-- **The second iterated derivative of a `C³` function with bounded third derivative is
Lipschitz.**  If `‖D³f‖ ≤ λ` everywhere then `x ↦ D²f x` is `λ`-Lipschitz. -/
theorem norm_iteratedFDeriv_two_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {lam : ℝ}
    (hf : ContDiff ℝ 3 f) (h3 : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ lam) (x y : E) :
    ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ lam * ‖y - x‖ := by
  -- `lam` is nonnegative because the third derivative is bounded by it at `0`.
  have hlam : 0 ≤ lam := le_trans (norm_nonneg _) (h3 0)
  -- `iteratedFDeriv ℝ 2 f` is differentiable, being a lower iterated derivative of a `C³` map.
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ 2 f) :=
    hf.differentiable_iteratedFDeriv (m := 2) (by norm_num)
  -- Its derivative is (up to the currying isometry) the third iterated derivative.
  have hbound : ∀ z, ‖fderiv ℝ (iteratedFDeriv ℝ 2 f) z‖ ≤ lam := by
    intro z
    rw [norm_fderiv_iteratedFDeriv]
    exact h3 z
  -- Mean value inequality applied to `iteratedFDeriv ℝ 2 f` on the convex set `univ`.
  have hmain := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := iteratedFDeriv ℝ 2 f) (C := lam) (s := Set.univ)
    (fun z _ => hdiff z) (fun z _ => hbound z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa using hmain

end Commons.Analysis.Calculus
