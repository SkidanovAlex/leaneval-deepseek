import Mathlib
import Submission.Work.EvenBound.Imports

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.EvenBound.FarthestPoint

/-- **Derivative of the norm along a differentiable curve to a real inner product space.**

If `γ` is differentiable at `t` with derivative `X` and `γ t ≠ 0`, then `s ↦ ‖γ s‖` is
differentiable at `t` with derivative `⟪γ t, X⟫ / ‖γ t‖`.

Proof: `HasDerivAt.norm_sq` gives the derivative `2 * ⟪γ t, X⟫` of `s ↦ ‖γ s‖ ^ 2`, and the chain
rule with `Real.hasDerivAt_sqrt` at the positive number `‖γ t‖ ^ 2` (together with
`Real.sqrt_sq`) gives the result. -/
lemma hasDerivAt_norm_comp {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {γ : ℝ → F} {X : F} {t : ℝ} (hγ : HasDerivAt γ X t) (h : γ t ≠ 0) :
    HasDerivAt (fun s : ℝ => ‖γ s‖) (inner ℝ (γ t) X / ‖γ t‖) t := by
  -- `‖γ t‖ > 0`, hence also `‖γ t‖ ^ 2 ≠ 0` so that `Real.sqrt` is differentiable there.
  have hpos : (0:ℝ) < ‖γ t‖ := norm_pos_iff.2 h
  -- Chain rule: `s ↦ ‖γ s‖ ^ 2` has derivative `2 * ⟪γ t, X⟫`,
  -- and `Real.sqrt` is differentiable away from `0`.
  have hs : HasDerivAt (fun s : ℝ => Real.sqrt (‖γ s‖ ^ 2))
      ((2 * inner ℝ (γ t) X) / (2 * Real.sqrt (‖γ t‖ ^ 2))) t :=
    hγ.norm_sq.sqrt (pow_ne_zero 2 hpos.ne')
  -- Rewrite `Real.sqrt (‖γ s‖ ^ 2) = ‖γ s‖` (pointwise, then as a function equality).
  have hfun : (fun s : ℝ => Real.sqrt (‖γ s‖ ^ 2)) = fun s : ℝ => ‖γ s‖ :=
    funext fun s => Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hs
  -- It remains to simplify the derivative: `√(‖γ t‖ ^ 2) = ‖γ t‖` and `2 * ⟪·⟫ / (2 * ‖γ t‖)
  -- = ⟪·⟫ / ‖γ t‖` since `‖γ t‖ ≠ 0`.
  refine hs.congr_deriv ?_
  rw [Real.sqrt_sq (norm_nonneg (γ t))]
  field_simp

end Work.EvenBound.FarthestPoint
