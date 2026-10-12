import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.L1Tails.DefsC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails.conjSlice

/-- `fderiv ℝ` commutes with complex conjugation on a slice: for the smooth kernel `H`,
`Σ_j ‖∂_{w_j}(w' ↦ conj (H w' y)) w‖² = Σ_j ‖∂_{w_j}(w' ↦ H w' y) w‖²`.  Route: `starRingEnd ℂ` is
the continuous `ℝ`-linear map `Complex.conjCLE`, so
`fderiv ℝ (fun w' => conj (H w' y)) w = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (fun w' => H w' y) w)`
by `HasFDerivAt.comp`, and it is an isometry (`Complex.conjCLE.norm_map`). -/
theorem sum_norm_fderiv_conjSlice
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (y w : EuclideanSpace ℝ (Fin 3)) :
    (∑ j : Fin 3, ‖fderiv ℝ (fun w' => (starRingEnd ℂ) (H w' y)) w
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ∑ j : Fin 3, ‖fderiv ℝ (fun w' => H w' y) w
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  have _hH := hH
  -- `starRingEnd ℂ` is (definitionally) the continuous `ℝ`-linear equivalence `Complex.conjCLE`.
  have hcomp : (fun w' => (starRingEnd ℂ) (H w' y))
      = (⇑(Complex.conjCLE : ℂ ≃L[ℝ] ℂ)) ∘ (fun w' => H w' y) := by
    funext w'
    exact (Complex.conjCLE_apply (H w' y)).symm
  -- `ContinuousLinearEquiv.comp_fderiv` needs no differentiability hypothesis: it holds because
  -- `Complex.conjCLE` is a *bijective* continuous linear map, so `fderiv` of the composite is the
  -- composite of the `fderiv`s even where the inner map is not differentiable (both sides are `0`).
  rw [hcomp, ContinuousLinearEquiv.comp_fderiv]
  -- `Complex.conjCLE` preserves the norm, hence each summand, hence the sum.
  simp

end Work.BoseBoxFock.L1Tails.conjSlice
