import Mathlib
import Submission.Work.NN.Core.Defs

namespace Work.NN.Core

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

/-- A coordinate projection does not increase the operator norm; used to bound the differential of
the standard coordinate functions by `‖tupleDeriv T‖`. -/
lemma proj_comp_norm_le {n : ℕ} (L : E n →L[ℝ] (Fin n → ℂ)) (j : Fin n) :
    ‖(ContinuousLinearMap.proj j).comp L‖ ≤ ‖L‖ := by
  calc ‖(ContinuousLinearMap.proj j).comp L‖
      ≤ ‖(ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℝ] ℂ)‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖L‖ := by
        gcongr
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro x
        simpa using norm_le_pi_norm x j
    _ = ‖L‖ := one_mul _

end Work.NN.Core
