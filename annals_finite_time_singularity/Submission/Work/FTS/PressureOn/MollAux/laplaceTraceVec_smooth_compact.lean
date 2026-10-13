import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Auxiliary.laplaceTraceVec_identity
import Submission.Work.FTS.PressureOn.Auxiliary.div_laplaceTraceVec
import Submission.Work.FTS.PressureOn.Auxiliary.gradient_smooth_norm
import Submission.Work.FTS.PressureOn.Green.integrable_gaussScale_mul_laplaceTraceVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

theorem laplaceTraceVec_smooth_compact (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ n : ℕ, ContDiff ℝ n W) :
    (∀ n : ℕ, ContDiff ℝ n (Work.FTS.PressureOn.laplaceTraceVec W)) ∧
      (HasCompactSupport W → HasCompactSupport (Work.FTS.PressureOn.laplaceTraceVec W)) := by
  constructor
  · -- Smoothness: each coordinate of `laplaceTraceVec W` is `∂ᵢ∂ᵢ W · eᵢ`, the derivative of the
    -- `C^∞` slice `fun w => fderiv ℝ W w (e i)`, applied to the constant `e i`.
    intro m
    unfold Work.FTS.PressureOn.laplaceTraceVec
    refine ContDiff.sum fun i _ => ?_
    have h1 : ContDiff ℝ (m + 1)
        (fun w : EuclideanSpace ℝ (Fin 3) =>
          fderiv ℝ W w (FiniteTimeSingularity.e i)) :=
      ((hW (m + 2)).fderiv_right (m := m + 1)
        (by exact_mod_cast (show (m : ℕ) + 1 + 1 ≤ m + 2 by omega))).clm_apply contDiff_const
    have h3 : ContDiff ℝ m
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
            fderiv ℝ W w (FiniteTimeSingularity.e i)) p.1) p.2) :=
      h1.contDiff_fderiv_apply (m := m)
        (by exact_mod_cast (show (m : ℕ) + 1 ≤ m + 1 by omega))
    exact h3.comp (contDiff_id.prodMk contDiff_const)
  · -- Compact support: the support of the Laplacian trace is contained in `tsupport W`.
    intro hWc
    exact HasCompactSupport.of_support_subset_isCompact hWc.isCompact
      (Work.FTS.PressureOn.Green.support_laplaceTraceVec_subset W)

end Work.FTS.PressureOn.MollAux
