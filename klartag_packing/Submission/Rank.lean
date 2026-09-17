import Mathlib
import Submission.MatSpace
import Submission.MatBridge
import Submission.DriftStep

/-!
# The expected square norm of a projected Gaussian is the rank of the projection

For a submodule `F` of the matrix space `MatV d` (a Euclidean space), the orthogonal projection
`F.starProjection` applied to a standard Gaussian `ξ` satisfies

    E ‖F.starProjection ξ‖² = dim F .

This is the "trace = rank" identity for orthogonal projections, and it is what turns the
`k`-th drift increment `‖π_k ξ_k‖²` of the exploration process of `Submission/PLAN_V7.md` into
the dimension `N_k` of the constraint space.
-/

namespace Submission.Rank

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.MatBridge
open Submission.DriftStep

noncomputable section

variable {d : ℕ}

/-- The square norm on `MatV d` is the sum of squares of the coordinates. -/
lemma norm_sq_eq_sum_sq (x : MatV d) :
    ‖x‖ ^ 2 = ∑ p : Fin d × Fin d, x p ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **Parseval for the orthogonal projection.**  The square norm of the projection of `ξ` onto
`F` is the sum of the squares of the coefficients of `ξ` in an orthonormal basis of `F`. -/
lemma norm_sq_starProjection_eq_sum_sq_coeff (F : Submodule ℝ (MatV d)) (ξ : MatV d) :
    ‖F.starProjection ξ‖ ^ 2 = ∑ i, coeff F ξ i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [Submodule.inner_starProjection_left_eq_right F ξ (F.starProjection ξ),
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem F ξ)]
  rw [starProjection_eq_sum, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, real_inner_comm (↑((stdOrthonormalBasis ℝ ↥F) i)) ξ, ← sq]
  rfl

/-- **The expected square norm of a projected standard Gaussian is the rank.** -/
theorem integral_norm_sq_starProjection (F : Submodule ℝ (MatV d)) :
    (∫ ξ : MatV d, ‖F.starProjection ξ‖ ^ 2 ∂(ProbabilityTheory.stdGaussian (MatV d)))
      = (Module.finrank ℝ ↥F : ℝ) := by
  have hpt : ∀ ξ : MatV d, ‖F.starProjection ξ‖ ^ 2
      = ∑ i : Fin (Module.finrank ℝ ↥F), coeff F ξ i * coeff F ξ i := by
    intro ξ
    rw [norm_sq_starProjection_eq_sum_sq_coeff F ξ]
    exact Finset.sum_congr rfl fun i _ => (sq _)
  simp only [hpt]
  rw [MeasureTheory.integral_finsetSum (μ := ProbabilityTheory.stdGaussian (MatV d))
    (ι := Fin (Module.finrank ℝ ↥F)) (s := Finset.univ)
    (f := fun i ξ => coeff F ξ i * coeff F ξ i)
    (fun i _ => coeff_mul_coeff_integrable F i i)]
  rw [Finset.sum_congr rfl (fun i _ => integral_coeff_mul_coeff F i i)]
  simp

end

end Submission.Rank
