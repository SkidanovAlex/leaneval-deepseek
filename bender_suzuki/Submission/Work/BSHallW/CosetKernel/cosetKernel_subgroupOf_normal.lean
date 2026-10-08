import Mathlib
import Submission.Work.Grun.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSHallW.CosetKernel

/-- Hall's `K(x)` is normal in `P`.  Concretely, if `u ∈ K(x)` and `p ∈ P`, then for every
`y ∈ P` the conjugate `p u p⁻¹` satisfies
`(y x)⁻¹ (p u p⁻¹) (y x) = ((p⁻¹ y) x)⁻¹ u ((p⁻¹ y) x) ∈ H`, using `y x = p · (p⁻¹ y · x)`. -/
theorem cosetKernel_subgroupOf_normal {G : Type*} [Group G] (H P : Subgroup G) (x : G) :
    ((Work.Grun.cosetKernel H P x).subgroupOf P).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  rw [Work.Grun.mem_cosetKernel] at hn ⊢
  refine ⟨?_, ?_⟩
  · exact P.mul_mem (P.mul_mem g.2 hn.1) (P.inv_mem g.2)
  · intro y hy
    have hq : (g : G)⁻¹ * y ∈ P := P.mul_mem (P.inv_mem g.2) hy
    have key := hn.2 ((g : G)⁻¹ * y) hq
    convert key using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

end Work.BSHallW.CosetKernel
