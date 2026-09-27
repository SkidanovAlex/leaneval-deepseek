import Mathlib
import Submission.Work.PL.Defs

namespace Work.Cells.Connell

set_option linter.unusedVariables false

/-- Restricting a cube chart to an open subset of the open unit cube gives a homeomorphism onto
its image.  (Openness of `U` is not needed: any subset of the open cube restricts to an embedding,
hence to a homeomorphism onto its image.) -/
theorem cubeChart_homeoOn {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M)
    {U : Set (PL.E n)} (hUo : IsOpen U) (hU : U ⊆ PL.openCube (n := n) 1) :
    Nonempty (↥U ≃ₜ ↥(c.toFun '' U)) := by
  -- The restricted chart `c.toFun` on the open cube is an embedding.
  have hφ : Topology.IsEmbedding
      ((PL.openCube (n := n) 1).domRestrict c.toFun ∘ Set.inclusion hU) :=
    c.emb.toIsEmbedding.comp (Topology.IsEmbedding.inclusion hU)
  -- Its range is exactly the image of `U`.
  have hrange : Set.range ((PL.openCube (n := n) 1).domRestrict c.toFun ∘ Set.inclusion hU)
      = c.toFun '' U := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  exact ⟨hφ.toHomeomorph.trans (Homeomorph.setCongr hrange)⟩

end Work.Cells.Connell
