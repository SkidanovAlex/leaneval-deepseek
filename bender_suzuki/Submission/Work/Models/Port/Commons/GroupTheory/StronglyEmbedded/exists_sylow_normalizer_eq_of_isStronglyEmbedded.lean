import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.sylow2_le
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.normalizer_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem exists_sylow_normalizer_eq_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) (hMne : M ≠ ⊤) (hMeven : Even (Nat.card M))
    (hModd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (hmax : ∀ T : Sylow 2 G, IsCoatom (Subgroup.normalizer ((T : Subgroup G) : Set G))) :
    ∃ T : Sylow 2 G, M = Subgroup.normalizer ((T : Subgroup G) : Set G) := by
  obtain ⟨P, hP⟩ := sylow2_le M hMne hMeven hModd
  refine ⟨P, ?_⟩
  have hNle : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M :=
    normalizer_le M hMeven hModd P hP
  rcases lt_or_eq_of_le hNle with hlt | heq
  · exact absurd ((hmax P).lt_iff.mp hlt) hMne
  · exact heq.symm

end Commons.GroupTheory.StronglyEmbedded
