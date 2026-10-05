import Mathlib

namespace Work.RPCore.Flow

theorem fderiv_eq_of_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : E → V) (hf : Differentiable ℝ f)
    {c : E} (h : ∀ x, f (x + c) = f x) (x : E) : fderiv ℝ f (x + c) = fderiv ℝ f x := by
  -- Translation `T y = y + c` is differentiable with derivative the identity.
  have hTdiff : DifferentiableAt ℝ (fun y : E => y + c) x :=
    (hasFDerivAt_id x).add_const c |>.differentiableAt
  have hT : fderiv ℝ (fun y : E => y + c) x = ContinuousLinearMap.id ℝ E :=
    ((hasFDerivAt_id x).add_const c).fderiv
  -- Chain rule for `f ∘ T`.
  have hcomp := fderiv_comp (𝕜 := ℝ) (f := fun y : E => y + c) (x := x) (g := f)
    hf.differentiableAt hTdiff
  calc fderiv ℝ f (x + c)
      = (fderiv ℝ f (x + c)) ∘SL (ContinuousLinearMap.id ℝ E) := by
          rw [ContinuousLinearMap.comp_id]
    _ = (fderiv ℝ f ((fun y : E => y + c) x)) ∘SL (fderiv ℝ (fun y : E => y + c) x) := by
          rw [hT]
    _ = fderiv ℝ (f ∘ (fun y : E => y + c)) x := hcomp.symm
    _ = fderiv ℝ f x := by rw [show f ∘ (fun y : E => y + c) = f from funext h]

end Work.RPCore.Flow
