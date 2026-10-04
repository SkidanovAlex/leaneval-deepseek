import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep1.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open scoped BigOperators

/-- The weight `1 + Σᵢ vᵢ²` is the *square* of the Euclidean norm of the vector `(1, v)`, and
`Σᵢ (vᵢ - wᵢ)²` is the square of the Euclidean norm of `(1,v) - (1,w) = (0, v - w)`.  Hence the
reverse triangle inequality (in `EuclideanSpace ℝ (Option ι)`) gives the estimate below.

This is the analytic content of `sqrt_wt_sub_le`: `√(wt ·)` is a norm, so it is `1`-Lipschitz with
respect to the `ℓ²` metric on frequencies. -/
lemma abs_sqrt_one_add_sum_sq_sub_le {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    |Real.sqrt (1 + ∑ i, v i ^ 2) - Real.sqrt (1 + ∑ i, w i ^ 2)|
      ≤ Real.sqrt (∑ i, (v i - w i) ^ 2) := by
  have h1 : ‖((WithLp.equiv 2 (Option ι → ℝ)).symm (fun j => j.elim 1 (fun i => v i)) :
      EuclideanSpace ℝ (Option ι))‖ = Real.sqrt (1 + ∑ i, v i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    rw [Fintype.sum_option]
    simp [Real.norm_eq_abs, sq_abs]
  have h2 : ‖((WithLp.equiv 2 (Option ι → ℝ)).symm (fun j => j.elim 1 (fun i => w i)) :
      EuclideanSpace ℝ (Option ι))‖ = Real.sqrt (1 + ∑ i, w i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    rw [Fintype.sum_option]
    simp [Real.norm_eq_abs, sq_abs]
  have h3 : ‖((WithLp.equiv 2 (Option ι → ℝ)).symm (fun j => j.elim 1 (fun i => v i)) :
      EuclideanSpace ℝ (Option ι))
      - ((WithLp.equiv 2 (Option ι → ℝ)).symm (fun j => j.elim 1 (fun i => w i)) :
      EuclideanSpace ℝ (Option ι))‖ = Real.sqrt (∑ i, (v i - w i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    rw [Fintype.sum_option]
    simp [Real.norm_eq_abs, sq_abs]
  rw [← h1, ← h2, ← h3]
  exact abs_norm_sub_norm_le _ _

theorem sqrt_wt_sub_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m n : ι → ℤ) :
    |Real.sqrt (Work.Diff.STE.wt m) - Real.sqrt (Work.Diff.STE.wt n)|
      ≤ Real.sqrt (∑ i, (((m i - n i : ℤ)) : ℝ) ^ 2) := by
  have h := abs_sqrt_one_add_sum_sq_sub_le (fun i => ((m i : ℤ) : ℝ)) (fun i => ((n i : ℤ) : ℝ))
  simpa only [Work.Diff.STE.wt, Int.cast_sub] using h

end Work.Diff.STE.B3
