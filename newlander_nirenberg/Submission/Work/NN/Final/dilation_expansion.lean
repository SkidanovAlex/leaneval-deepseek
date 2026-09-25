import Mathlib

namespace Work.NN.Final

open Finset

/-- Expansion of a continuous multilinear map along the perturbation
`a j ↦ a j + c j • e j`: the sum over subsets `s` of the coefficients
`∏ j ∈ s, c j` times `M` evaluated on the function that is `e` on `s` and `a` off `s`. -/
theorem dilation_expansion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ContinuousMultilinearMap ℝ (fun _ : ι => E) F) (a e : ι → E) (c : ι → ℝ) :
    M (fun j => a j + c j • e j) = ∑ s : Finset ι, (∏ j ∈ s, c j) • M (s.piecewise e a) := by
  rw [show (fun j => a j + c j • e j) = (fun j => c j • e j) + a from by
    ext j; simp [add_comm]]
  rw [ContinuousMultilinearMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← ContinuousMultilinearMap.map_piecewise_smul M c (s.piecewise e a) s]
  congr 1
  ext j
  by_cases hj : j ∈ s <;> simp [Finset.piecewise, hj]

end Work.NN.Final
