import Mathlib.Analysis.InnerProductSpace.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.InnerProduct

theorem norm_sum_sq_of_pairwise_orthogonal {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type*} [Fintype ι]
    (v : ι → E) (h : ∀ i j, i ≠ j → inner 𝕜 (v i) (v j) = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have hnorm : ‖∑ i, v i‖ ^ 2 = RCLike.re (inner 𝕜 (∑ i, v i) (∑ i, v i)) :=
    norm_sq_eq_re_inner _
  rw [hnorm]
  have hinner : inner 𝕜 (∑ i, v i) (∑ i, v i) = ∑ i, inner 𝕜 (v i) (v i) := by
    rw [sum_inner]
    simp only [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · intro j _ hj; exact h i j hj.symm
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hinner, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (norm_sq_eq_re_inner (v i)).symm

end Commons.Analysis.InnerProduct