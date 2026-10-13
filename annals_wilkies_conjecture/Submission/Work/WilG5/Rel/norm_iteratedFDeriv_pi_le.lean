import Mathlib
import Submission.Work.WilG5.Defs

namespace Work.WilG5.Rel

/-- The `m`-th iterated derivative of a map into a finite product `Fin n → ℝ` is bounded in
operator norm by the supremum of the operator norms of the iterated derivatives of its
coordinate functions.

Indeed, writing `Φ = iteratedFDeriv ℝ m f x`, the `i`-th coordinate of `Φ` is obtained by
post-composing with the projection `ContinuousLinearMap.proj i`, and
`ContinuousLinearMap.iteratedFDeriv_comp_left` identifies this with the iterated derivative of
`t ↦ f t i`.  A continuous multilinear map into a product is bounded by the supremum of its
coordinate norms, so `‖Φ‖ ≤ max_i ‖proj i ∘ Φ‖`. -/
theorem norm_iteratedFDeriv_pi_le {m μ n : ℕ} (f : (Fin μ → ℝ) → (Fin n → ℝ)) (x : Fin μ → ℝ)
    (hf : ContDiffAt ℝ m f x)
    (h : ∀ i : Fin n, ‖iteratedFDeriv ℝ m (fun t : Fin μ → ℝ => f t i) x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ m f x‖ ≤ 1 := by
  -- `hcoord i` bounds the `i`-th coordinate of the iterated derivative of `f`.
  have hcoord : ∀ i : Fin n,
      ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m f x)‖ ≤ 1 := by
    intro i
    -- Post-composition with the `i`-th projection is the iterated derivative of the `i`-th
    -- coordinate function.
    rw [← ContinuousLinearMap.iteratedFDeriv_comp_left
      (g := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) hf (le_rfl)]
    have hfun : (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) ∘ f)
        = (fun t : Fin μ → ℝ => f t i) := by
      funext t
      rw [Function.comp_apply, ContinuousLinearMap.proj_apply]
    rw [hfun]
    exact h i
  -- Bound the operator norm of `Φ` itself.
  refine ContinuousMultilinearMap.opNorm_le_bound (by norm_num) fun v => ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  calc ‖(iteratedFDeriv ℝ m f x v) i‖
      = ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m f x) v‖ := by
        rw [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
            ContinuousLinearMap.proj_apply]
    _ ≤ ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m f x)‖ * ∏ j, ‖v j‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ 1 * ∏ j, ‖v j‖ :=
        mul_le_mul_of_nonneg_right (hcoord i) (Finset.prod_nonneg fun j _ => norm_nonneg _)
    _ = ∏ j, ‖v j‖ := one_mul _

end Work.WilG5.Rel
