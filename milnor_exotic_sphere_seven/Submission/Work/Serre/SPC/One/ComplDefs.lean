import Mathlib
import Submission.Work.Serre.SPC.One.OneCellGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The complement of the centres of the attached `1`-cells

Helper facts about `W = (oneCellCentresOne Y ι f)ᶜ`, the space obtained from `Z` by deleting the
centres of the attached intervals: it is open, it contains the old part `Y'`, and every point of it
lies either in `Y'` or in the interior of exactly one of the attached cells.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}

theorem isClosed_oneCellCentresOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) : IsClosed (oneCellCentresOne Y ι f) := by
  rw [← cellUnionOne_centreSet f]
  exact isClosed_cellUnionOne f (fun x hx => by
      show ‖((x : cellD1) : ℝ)‖ < 1
      exact lt_of_le_of_lt hx zero_lt_one)
    (isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const)

theorem isOpen_compl_centres (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) : IsOpen ((oneCellCentresOne Y ι f)ᶜ) :=
  (isClosed_oneCellCentresOne Y ι f).isOpen_compl

@[simp] theorem mem_compl_centres {z : attachOneCells Y ι f} :
    z ∈ (oneCellCentresOne Y ι f)ᶜ ↔ ∀ i : ι, oneCellCentreOne Y ι f i ≠ z := by
  simp only [Set.mem_compl_iff, mem_oneCellCentresOne, not_exists]

theorem oldPart_subset_compl_centres :
    oneCellOldPart Y ι f ⊆ (oneCellCentresOne Y ι f)ᶜ :=
  fun z hz => by
    rw [mem_compl_centres]
    intro i hi
    exact oneCellCentreOne_not_mem_oldPart f i (hi ▸ hz)

/-- **The partition of `W`**: every point of the complement of the centres lies either in the old
part or in exactly one open cell. -/
theorem mem_oldPart_or_exists_cell {z : attachOneCells Y ι f}
    (hz : z ∈ (oneCellCentresOne Y ι f)ᶜ) :
    z ∈ oneCellOldPart Y ι f ∨ ∃ i : ι, z ∈ cellInteriorOne Y ι f i := by
  by_cases h : z ∈ oneCellOldPart Y ι f
  · exact Or.inl h
  · refine Or.inr ?_
    have h2 : z ∈ cellInnerUnionOne Y ι f := by
      simpa [oneCellOldPart_eq_compl f] using h
    rw [cellInnerUnionOne, cellUnionOne] at h2
    exact Set.mem_iUnion.mp h2

/-- A point of the complement of the centres which is not in the old part lies in the interior of a
unique cell. -/
theorem existsUnique_cellInteriorOne {z : attachOneCells Y ι f}
    (hz : z ∈ (oneCellCentresOne Y ι f)ᶜ) (hzo : z ∉ oneCellOldPart Y ι f) :
    ∃! i : ι, z ∈ cellInteriorOne Y ι f i := by
  obtain h | ⟨i, hi⟩ := mem_oldPart_or_exists_cell (f := f) hz
  · exact absurd h hzo
  · refine ⟨i, hi, fun j hj => ?_⟩
    by_contra hne
    exact Set.disjoint_left.mp
      (disjoint_cellInteriorOne (Y := Y) (f := f) (i := i) (j := j) (Ne.symm hne)) hi hj

/-- A point of the complement of the centres which is not in the old part determines its cell
index. -/
noncomputable def cellIndexOf {z : ↥((oneCellCentresOne Y ι f)ᶜ)}
    (hzo : (z : attachOneCells Y ι f) ∉ oneCellOldPart Y ι f) : ι :=
  Classical.choose (existsUnique_cellInteriorOne (f := f) z.2 hzo)

theorem cellIndexOf_mem {z : ↥((oneCellCentresOne Y ι f)ᶜ)}
    (hzo : (z : attachOneCells Y ι f) ∉ oneCellOldPart Y ι f) :
    (z : attachOneCells Y ι f) ∈ cellInteriorOne Y ι f (cellIndexOf (f := f) hzo) :=
  (Classical.choose_spec (existsUnique_cellInteriorOne (f := f) z.2 hzo)).1

end

end Work.Serre.SPC.One
