import Mathlib

namespace Work.ORLocInd.FKSKernel

theorem quotientKerSubgroupEquivMap {A B : Type*} [Group A] [Group B]
    (f : A →* B) (K : Subgroup A) :
    Nonempty (K ⧸ (MonoidHom.ker f).subgroupOf K ≃* Subgroup.map f K) := by
  -- Apply Noether's first isomorphism theorem to the restriction `f.domRestrict K : K →* B`,
  -- whose kernel is `(ker f).subgroupOf K` and whose range is `Subgroup.map f K`.
  refine ⟨(QuotientGroup.quotientKerEquivRange (f.domRestrict K)).trans
    (MulEquiv.subgroupCongr ?_)⟩
  rw [MonoidHom.domRestrict_range]

end Work.ORLocInd.FKSKernel
