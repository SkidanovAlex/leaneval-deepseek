import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.conj_mem_iff_mem_of_orderTwo
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.mem_map_conj_iff
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.orderOf_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

/-- If `M` meets each of its conjugates `Mᵍ` (`g ∉ M`) in a subgroup of odd order,
then the set of elements conjugating a fixed involution `t` into `M` is a coset of
`M`: if `x⁻¹ t x ∈ M` and `z⁻¹ t z ∈ M`, then `x⁻¹ z ∈ M`.

Proof: `a := x⁻¹ t x` lies in `M` and has order two (conjugation preserves the
order).  Moreover `a = (x⁻¹ z) · (z⁻¹ t z) · (x⁻¹ z)⁻¹`, so `a` lies in the
conjugate `M^(x⁻¹ z)`.  Since `M` contains the involution `a` and `M^(x⁻¹ z)` too,
`conj_mem_iff_mem_of_orderTwo` yields `x⁻¹ z ∈ M`. -/
theorem inv_mul_mem_of_conj_mem_of_orderTwo {G : Type*} [Group G] (M : Subgroup G)
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {t x z : G} (ht : orderOf t = 2)
    (hx : x⁻¹ * t * x ∈ M) (hz : z⁻¹ * t * z ∈ M) : x⁻¹ * z ∈ M := by
  have ha2 : orderOf (x⁻¹ * t * x) = 2 := by
    calc orderOf (x⁻¹ * t * x) = orderOf t := by simpa using orderOf_conj x⁻¹ t
      _ = 2 := ht
  exact (conj_mem_iff_mem_of_orderTwo M hOdd hx ha2 (g := x⁻¹ * z)).mp
    (Subgroup.mem_map.mpr ⟨z⁻¹ * t * z, hz, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩)

end Commons.GroupTheory.StronglyEmbedded
