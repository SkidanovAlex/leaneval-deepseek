import Mathlib
import Submission.Work.NN.Core.Defs

namespace Work.NN.Core

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

lemma norm_I_div_two : ‖(Complex.I / 2 : ℂ)‖ = 1/2 := by
  rw [norm_div, Complex.norm_I]; norm_num

/-- The perturbation `L_A u = (i/2)·du ∘ A` of the `∂̄`-operator is bounded by half the size of
the differential of `u` times the size of the perturbation `A` of the complex structure. -/
lemma dbarPert_norm_le {n : ℕ} (A : E n → E n →L[ℝ] E n) (u : E n → ℂ) (y : E n) :
    ‖dbarPert A u y‖ ≤ (1/2 : ℝ) * ‖fderiv ℝ u y‖ * ‖A y‖ := by
  rw [dbarPert, norm_smul, norm_I_div_two]
  calc (1/2) * ‖(fderiv ℝ u y).comp (A y)‖
      ≤ (1/2) * (‖fderiv ℝ u y‖ * ‖A y‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = (1/2) * ‖fderiv ℝ u y‖ * ‖A y‖ := by ring

end Work.NN.Core
