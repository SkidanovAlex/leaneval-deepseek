import Mathlib
import Submission.Work.Diff.EXT.MixedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bounding the jet of a directional derivative

For a smooth `ψ : E → ℝ`, the `j`-th iterated derivative of the function
`y' ↦ fderiv ℝ ψ y' ζ` is bounded by `‖ζ‖` times the `(j+1)`-st iterated derivative of `ψ`.

This is the "peel off the last argument" identity: the `j`-jet of the contraction
`y' ↦ fderiv ℝ ψ y' ζ` is the contraction of the `(j+1)`-jet of `ψ` in its last slot
(`Work.Diff.EXT.iteratedFDeriv_succ_snoc_apply`), and the operator norm of a multilinear
map dominates its value at any tuple (`ContinuousMultilinearMap.le_opNorm`).
-/

namespace Work.Diff.EXT.ConnCov

theorem norm_iteratedFDeriv_fderiv_apply_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : E → ℝ} {y ζ : E} {j : ℕ} (hψ : ContDiffAt ℝ (⊤ : ℕ∞) ψ y) :
    ‖iteratedFDeriv ℝ j (fun y' : E => fderiv ℝ ψ y' ζ) y‖
      ≤ ‖ζ‖ * ‖iteratedFDeriv ℝ (j + 1) ψ y‖ := by
  -- a smooth function is `C^{j+1}`, hence its derivative is `C^j`
  have hψ' : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) ψ y := hψ.of_le (by simp)
  have hf : ContDiffAt ℝ ((j : ℕ) : WithTop ℕ∞) (fderiv ℝ ψ) y :=
    hψ'.fderiv_right (hmn := le_rfl)
  refine ContinuousMultilinearMap.opNorm_le_bound
    (M := ‖ζ‖ * ‖iteratedFDeriv ℝ (j + 1) ψ y‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun v => ?_)
  -- peel off the last argument of the `(j+1)`-st derivative
  have hkey : (iteratedFDeriv ℝ j (fun y' : E => fderiv ℝ ψ y' ζ) y) v
      = (iteratedFDeriv ℝ (j + 1) ψ y) (Fin.snoc (α := fun _ : Fin (j + 1) => E) v ζ) :=
    (iteratedFDeriv_succ_snoc_apply (V := E) (W := ℝ) (G := ψ) (q := y) (k := j)
      hf le_rfl v ζ).symm
  rw [hkey]
  refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
  have hprod : ∏ i : Fin (j + 1),
      ‖(Fin.snoc (α := fun _ : Fin (j + 1) => E) v ζ) i‖ = (∏ i : Fin j, ‖v i‖) * ‖ζ‖ := by
    rw [Fin.prod_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hprod]
  exact le_of_eq (by ring)

end Work.Diff.EXT.ConnCov
