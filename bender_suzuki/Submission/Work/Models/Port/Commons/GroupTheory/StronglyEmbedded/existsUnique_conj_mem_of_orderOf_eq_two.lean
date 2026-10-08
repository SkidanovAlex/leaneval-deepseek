import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.isBenderAction_coset
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.involution_mem_conj
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.eq_of_mem_map_conj_of_orderTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem existsUnique_conj_mem_of_orderOf_eq_two {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) (hMne : M ≠ ⊤) (hMeven : Even (Nat.card M))
    (hModd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {t : G} (ht : orderOf t = 2) :
    ∃! H : Subgroup G, (∃ g : G, H = M.map (MulAut.conj g).toMonoidHom) ∧ t ∈ H := by
  obtain ⟨x, hx⟩ := involution_mem_conj M hMeven hModd ht
  refine ⟨M.map (MulAut.conj x).toMonoidHom, ⟨⟨x, rfl⟩, hx⟩, ?_⟩
  rintro H ⟨⟨g, rfl⟩, hg⟩
  exact eq_of_mem_map_conj_of_orderTwo M hModd ht hg hx

end Commons.GroupTheory.StronglyEmbedded
