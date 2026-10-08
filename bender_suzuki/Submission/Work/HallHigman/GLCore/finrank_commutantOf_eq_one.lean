import Mathlib
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.GLCore.exists_scalar_of_commute_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- **L7 of the GL-core design** (Schur's lemma, Step 4c of the proof of Hall--Higman B, see
`NOTES_LEAD_ft_hallhigman.md` §2.2): over an algebraically closed field, the endomorphism ring of
an irreducible representation is one dimensional (the scalars). -/
lemma finrank_commutantOf_eq_one {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] {E : Type*} [Group E]
    (σ : E →* Module.End K V) (h : Work.HallHigman.IsIrreducibleFor (Set.range σ)) :
    Module.finrank K (Work.HallHigman.commutantOf σ) = 1 := by
  have hV : Nontrivial V := h.1
  -- Every element of the commutant is a scalar (Schur's lemma, L6).
  have hscalar : ∀ Y ∈ Work.HallHigman.commutantOf σ,
      ∃ c : K, Y = c • (1 : Module.End K V) := by
    intro Y hY
    obtain ⟨c, hc⟩ := Work.HallHigman.GLCore.exists_scalar_of_commute_irreducible
      (Set.range σ) h Y (fun s hs => by
        obtain ⟨e, rfl⟩ := hs
        exact (Work.HallHigman.mem_commutantOf_iff.mp hY e).symm)
    exact ⟨c, by rw [hc, Algebra.algebraMap_eq_smul_one]⟩
  -- Hence the commutant is exactly the line spanned by the identity.
  have hsub : Work.HallHigman.commutantOf σ = K ∙ (1 : Module.End K V) := by
    refine le_antisymm ?_ ?_
    · intro Y hY
      obtain ⟨c, hc⟩ := hscalar Y hY
      rw [hc]
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Work.HallHigman.one_mem_commutantOf σ
  rw [hsub, finrank_span_singleton (one_ne_zero : (1 : Module.End K V) ≠ 0)]

end Work.HallHigman.GLCore
