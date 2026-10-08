import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.exists_sylow_normalizer_eq_of_isStronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

/-- Two proper subgroups of a finite group `G` which are "strongly embedded" (even order,
meeting each of their conjugates by an outer element in an odd-order subgroup) are conjugate,
provided the normalizer of every Sylow 2-subgroup of `G` is a maximal proper subgroup.

Indeed, the coatom hypothesis pins each such `M` down to the normalizer `N_G(P)` of a
Sylow 2-subgroup `P ≤ M` of `G`; two Sylow 2-subgroups are conjugate, and normalizers
of conjugate subgroups are conjugate. -/
theorem exists_conj_eq_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G]
    (M M' : Subgroup G)
    (hMne : M ≠ ⊤) (hMeven : Even (Nat.card M))
    (hModd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (hM'ne : M' ≠ ⊤) (hM'even : Even (Nat.card M'))
    (hM'odd : ∀ g : G, g ∉ M' →
      Odd (Nat.card ((M' ⊓ M'.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (hmax : ∀ T : Sylow 2 G, IsCoatom (Subgroup.normalizer ((T : Subgroup G) : Set G))) :
    ∃ g : G, M' = M.map (MulAut.conj g).toMonoidHom := by
  classical
  -- The coatom hypothesis forces `M` (resp. `M'`) to be the normalizer of a Sylow
  -- 2-subgroup of `G` contained in it.
  obtain ⟨P, hP⟩ :=
    exists_sylow_normalizer_eq_of_isStronglyEmbedded M hMne hMeven hModd hmax
  obtain ⟨P', hP'⟩ :=
    exists_sylow_normalizer_eq_of_isStronglyEmbedded M' hM'ne hM'even hM'odd hmax
  -- Sylow's second theorem: `P` and `P'` are conjugate.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  refine ⟨g, ?_⟩
  -- `P'` is the image of `P` under conjugation by `g`.
  have hsub : (P' : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    have hcoe := congrArg (fun s : Sylow 2 G => (s : Subgroup G)) hg
    rw [← hcoe]
    rfl
  -- Normalizers of conjugate subgroups are conjugate.
  rw [hP', hP, hsub, Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj]

end Commons.GroupTheory.StronglyEmbedded
