import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.LI

/-- A finitely generated, nontrivial, locally indicable group is indicable.

This is the `H = ⊤` case of the definition of local indicability: a finitely generated nontrivial
group is itself a nontrivial finitely generated subgroup, so it admits a surjection onto the
infinite cyclic group `Multiplicative ℤ`.  The surjection is transported back along the canonical
isomorphism `↥(⊤ : Subgroup H) ≃* H`. -/
theorem indicable_of_locallyIndicable_fg {H : Type*} [Group H] [Group.FG H]
    (h : Group.LocallyIndicable H) (hne : Nontrivial H) : Group.Indicable H := by
  obtain ⟨f, hf⟩ := h ⊤ (by rw [← Group.fg_iff_subgroup_fg]; infer_instance) (by
    rw [← Subgroup.nontrivial_iff_ne_bot]; infer_instance)
  let e : H ≃* (⊤ : Subgroup H) := (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).symm
  exact ⟨f.comp e, hf.comp e.surjective⟩

end Work.ORLocInd.LI
