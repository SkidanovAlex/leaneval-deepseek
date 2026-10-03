import Mathlib
import Submission.Work.Analysis.ExponentialSums.model721_bundle

namespace Work.KMTAreas.A7

open scoped BigOperators

/-- The elementary finite-set lattice bound: for every finite `u ⊆ ℤ`, the shifted reciprocal-square
sum is at most `2 + π/a`.  This is the finite content of the `ℤ`-lattice Cauchy-kernel estimate
(`Commons.Analysis.ExponentialSums.finset_sum_inv_one_add_sq_step_le`), with the two sides put in the
shape used below. -/
private lemma finset_one_div_one_add_sq_mul_le (a : ℝ) (ha : 0 < a) (x : ℝ) (u : Finset ℤ) :
    ∑ j ∈ u, 1 / (1 + (a * ((j : ℝ) - x)) ^ 2) ≤ 2 + Real.pi / a := by
  calc ∑ j ∈ u, 1 / (1 + (a * ((j : ℝ) - x)) ^ 2)
      = ∑ j ∈ u, (1 + (a * (x - (j : ℝ))) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [one_div]
        congr 1
        ring
    _ ≤ 2 * (1 + Real.pi / (2 * a)) :=
        Commons.Analysis.ExponentialSums.finset_sum_inv_one_add_sq_step_le ha x u
    _ = 2 + Real.pi / a := by
        field_simp

theorem tsum_one_div_one_add_sq_mul_le (s : ℝ) (hs : 0 < s) (x : ℝ) :
    Summable (fun j : ℤ => 1 / (1 + (s * ((j : ℝ) - x)) ^ 2)) ∧
      ∑' j : ℤ, 1 / (1 + (s * ((j : ℝ) - x)) ^ 2) ≤ 2 + Real.pi / s := by
  have hfin : ∀ u : Finset ℤ,
      ∑ j ∈ u, 1 / (1 + (s * ((j : ℝ) - x)) ^ 2) ≤ 2 + Real.pi / s :=
    fun u => finset_one_div_one_add_sq_mul_le s hs x u
  exact ⟨summable_of_sum_le (fun j => by positivity) hfin,
    Real.tsum_le_of_sum_le (fun j => by positivity) hfin⟩

end Work.KMTAreas.A7
