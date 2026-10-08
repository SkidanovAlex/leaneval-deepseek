import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.involution_mem_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem exists_conj_mem_of_orderOf_eq_two {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) (hMne : M ≠ ⊤) (hMeven : Even (Nat.card M))
    (hModd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {t : G} (ht : orderOf t = 2) :
    ∃ g : G, t ∈ M.map (MulAut.conj g).toMonoidHom := by
  exact involution_mem_conj M hMeven hModd ht

end Commons.GroupTheory.StronglyEmbedded
