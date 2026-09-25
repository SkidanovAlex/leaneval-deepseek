import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.InnerProductSpace

theorem norm_sum_sq_of_orthogonal {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (s : Finset ι) (v : ι → E)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner 𝕜 (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, v i‖ ^ 2
        = RCLike.re (inner 𝕜 (∑ i ∈ s, v i) (∑ i ∈ s, v i)) := by
            rw [inner_self_eq_norm_sq]
    _ = ∑ i ∈ s, RCLike.re (inner 𝕜 (v i) (∑ j ∈ s, v j)) := by
            rw [sum_inner, map_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, RCLike.re (inner 𝕜 (v i) (v j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [inner_sum, map_sum]
    _ = ∑ i ∈ s, RCLike.re (inner 𝕜 (v i) (v i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          refine Finset.sum_eq_single_of_mem i hi (fun j hj hji => ?_)
          rw [h i hi j hj hji.symm, map_zero]
    _ = ∑ i ∈ s, ‖v i‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [inner_self_eq_norm_sq]

end Commons.Analysis.InnerProductSpace