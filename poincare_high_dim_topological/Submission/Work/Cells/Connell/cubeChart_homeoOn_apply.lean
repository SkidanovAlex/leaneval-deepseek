import Mathlib
import Submission.Work.PL.Defs

namespace Work.Cells.Connell

set_option linter.unusedVariables false

/-- Restricting a cube chart `c` to an open subset `U` of the open unit cube gives a
homeomorphism `↥U ≃ₜ ↥(c.toFun '' U)` which is *the* map induced by `c.toFun`, i.e. the image of
`x ∈ U` is `c.toFun x`.  (Openness of `U` is not needed: any subset of the open cube restricts to an
embedding, hence to a homeomorphism onto its image.) -/
theorem cubeChart_homeoOn_apply {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {U : Set (PL.E n)} (hUo : IsOpen U)
    (hU : U ⊆ PL.openCube (n := n) 1) :
    ∃ e : ↥U ≃ₜ ↥(c.toFun '' U), ∀ x : ↥U, (e x : M) = c.toFun x := by
  -- The restricted chart `c.toFun` on the open cube is an embedding; compose it with the
  -- inclusion `↥U ↪ openCube 1`.
  have hφ : Topology.IsEmbedding
      ((PL.openCube (n := n) 1).domRestrict c.toFun ∘ Set.inclusion hU) :=
    c.emb.toIsEmbedding.comp (Topology.IsEmbedding.inclusion hU)
  -- Its range is exactly the image of `U` under `c.toFun`.
  have hrange : Set.range ((PL.openCube (n := n) 1).domRestrict c.toFun ∘ Set.inclusion hU)
      = c.toFun '' U := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  -- An embedding is a homeomorphism onto its range.
  refine ⟨hφ.toHomeomorph.trans (Homeomorph.setCongr hrange), ?_⟩
  intro x
  simp [Topology.IsEmbedding.toHomeomorph, Homeomorph.setCongr, Set.domRestrict]

end Work.Cells.Connell
