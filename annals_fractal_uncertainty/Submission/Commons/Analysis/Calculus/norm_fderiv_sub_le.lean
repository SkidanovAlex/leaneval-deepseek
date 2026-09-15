import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.CompletePartialOrder

set_option linter.unusedVariables false

namespace Commons.Analysis.Calculus

/-- **The derivative of a `C²` function with bounded second derivative is Lipschitz.**  If
`‖D²f‖ ≤ λ` everywhere then `y ↦ fderiv ℝ f y` is `λ`-Lipschitz. -/
theorem norm_fderiv_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {lam : ℝ} (hlam : 0 ≤ lam)
    (hf : ContDiff ℝ 2 f) (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ lam) (x y : E) :
    ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ lam * ‖y - x‖ := by
  -- `fderiv ℝ f` is `C¹`, hence differentiable.
  have hdiff : Differentiable ℝ (fderiv ℝ f) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
  -- Its derivative is `fderiv ℝ (fderiv ℝ f)`, whose norm is that of `iteratedFDeriv ℝ 2 f`.
  have hbound : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ lam := by
    intro z
    have hz : ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 2 f z‖ := by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ f) (x := z)]
      rw [norm_iteratedFDeriv_fderiv]
    rw [hz]
    exact h2 z
  -- Mean value inequality applied to `fderiv ℝ f` on the convex set `univ`.
  have hmain := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := fderiv ℝ f) (C := lam) (s := Set.univ)
    (fun z _ => hdiff z) (fun z _ => hbound z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa using hmain

end Commons.Analysis.Calculus