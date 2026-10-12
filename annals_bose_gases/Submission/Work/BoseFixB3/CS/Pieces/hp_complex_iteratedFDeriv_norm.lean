import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

/-!
# `hp_complex_iteratedFDeriv_norm`

The 40-th iterated (Fréchet) derivative of a real-valued smooth function,
regarded as a `ℂ`-valued function, evaluated on 40 copies of the unit vector
`kcStdBasis k`, is bounded by the operator norm of the real 40-th derivative.

The two ingredients are:

* `ContinuousLinearMap.iteratedFDeriv_comp_left` applied to the linear isometry
  `Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ`, which identifies the complexified iterated
  derivative with `ofRealLI ∘ (iteratedFDeriv ℝ 40 u x)` (nothing is lost, since
  `ofRealLI` preserves norms);
* `‖kcStdBasis k‖ = 1` together with `ContinuousMultilinearMap.le_opNorm_mul_prod_of_le`.
-/

theorem hp_complex_iteratedFDeriv_norm (u : EuclideanSpace ℝ (Fin 3) → ℝ) (k : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3)) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ‖(iteratedFDeriv ℝ 40 (fun y : EuclideanSpace ℝ (Fin 3) => (u y : ℂ)) x)
        (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)‖
      ≤ ‖iteratedFDeriv ℝ 40 u x‖ := by
  have hv : ‖Submission.BoseGases.kcStdBasis k‖ = 1 := by
    rw [Submission.BoseGases.kcStdBasis]
    simp
  -- the complexified iterated derivative is the `ℝ`-linear isometry `ofRealLI`
  -- applied to the real iterated derivative
  have key : iteratedFDeriv ℝ 40 (fun y : EuclideanSpace ℝ (Fin 3) => (u y : ℂ)) x
      = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ).toContinuousLinearMap.compContinuousMultilinearMap
          (iteratedFDeriv ℝ 40 u x) := by
    have hfun : (fun y : EuclideanSpace ℝ (Fin 3) => (u y : ℂ))
        = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ).toContinuousLinearMap ∘ u := by
      funext y; simp [Complex.ofRealLI_apply]
    rw [hfun]
    refine ContinuousLinearMap.iteratedFDeriv_comp_left _ hu.contDiffAt ?_
    exact WithTop.coe_le_coe.mpr le_top
  rw [key]
  rw [show ((Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ).toContinuousLinearMap.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 40 u x)) (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)
      = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ)
          ((iteratedFDeriv ℝ 40 u x) (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k))
      from rfl]
  rw [LinearIsometry.norm_map]
  calc ‖(iteratedFDeriv ℝ 40 u x) (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)‖
      ≤ ‖iteratedFDeriv ℝ 40 u x‖ * ∏ _ : Fin 40, (1 : ℝ) :=
        ContinuousMultilinearMap.le_opNorm_mul_prod_of_le _ (fun _ => by rw [hv])
    _ = ‖iteratedFDeriv ℝ 40 u x‖ := by simp

end Work.BoseFixB3.CS.Pieces
