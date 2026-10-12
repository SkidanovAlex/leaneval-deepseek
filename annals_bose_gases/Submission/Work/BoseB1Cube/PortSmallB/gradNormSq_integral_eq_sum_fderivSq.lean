import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Resolve.sum_integral_inner_sq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The squared gradient norm as a sum of coordinate derivatives

For an *arbitrary* function `u : ℝ³ → ℝ` (no regularity, no integrability),

    ∫_z ‖∇u z‖² = ∫_z Σ_k (∂_{e_k} u z)² ,

where `e_k = kcStdBasis k` is the standard coordinate basis of `ℝ³`.

The two sides have *pointwise* equal integrands: `‖∇u z‖² = Σ_k ⟪∇u z, e_k⟫²` is
Parseval for the orthonormal coordinate basis (`sum_inner_kcStdBasis_sq_local`), and
`⟪∇u z, e_k⟫ = fderiv ℝ u z e_k` is `inner_gradient_left` (the defining property of
`gradient`, valid for every `u` — including points where `u` is not differentiable,
where both sides are `0`).  Hence the integral identity is `integral_congr_ae`.

No hypothesis on `u` is needed, and none is carried.
-/

namespace Work.BoseB1Cube.PortSmallB

/-- **Pointwise form**: `‖∇u z‖² = Σ_k (∂_{e_k} u z)²`, with no hypothesis on `u`. -/
lemma gradNormSq_eq_sum_fderivSq (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (z : EuclideanSpace ℝ (Fin 3)) :
    ‖gradient u z‖ ^ 2
      = ∑ k : Fin 3, (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  rw [← Work.SmallBoxBridge.Resolve.sum_inner_kcStdBasis_sq_local (gradient u z)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [inner_gradient_left]

theorem gradNormSq_integral_eq_sum_fderivSq (u : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ z : EuclideanSpace ℝ (Fin 3), ‖gradient u z‖ ^ 2)
      = ∫ z : EuclideanSpace ℝ (Fin 3),
          ∑ k : Fin 3, (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact gradNormSq_eq_sum_fderivSq u z

end Work.BoseB1Cube.PortSmallB
