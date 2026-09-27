import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Cells.Connell.Defs
import Submission.Work.Cells.Connell.cubeChart_isOpen_image_openCube

namespace Work.Cells.Connell

open Set Metric

set_option linter.unusedVariables false

/-- A finite union of compact sets with empty interior in `ℝⁿ` (a `ThinFamily`) is nowhere dense,
so its image under a cube chart — an open embedding of the open unit cube — still has empty
interior.  Hence, given any nonempty open set `Aᶜ` in `M`, some point of `Aᶜ` lies outside the
image of `L` under the chart `cC`.

This is Connell's "count the cells" observation: an open nonempty set can never be covered by
the image of a finite union of nowhere dense "thin" pieces. -/
theorem exists_notMem_image_of_thinFamily {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    (ψ : PL.CubeChart n M) (A : Set M) (hA : IsClosed A) (hAne : (Aᶜ).Nonempty)
    (hψA : ∀ z ∈ PL.openCube (n := n) 1, ψ.toFun z ∈ Aᶜ)
    (cC : PL.CubeChart n M) {ι : Type} [Finite ι] (F : ι → Set (PL.E n)) (hF : ThinFamily F)
    {L : Set (PL.E n)} (hL : L ⊆ ⋃ i, F i) :
    ∃ p ∈ Aᶜ, p ∉ cC.toFun '' L := by
  -- Each `F i` is compact, hence closed, with empty interior, hence nowhere dense.
  have hFnd : ∀ i, IsNowhereDense (F i) :=
    fun i => ((hF i).1.isClosed).isNowhereDense_iff.mpr (hF i).2.2
  -- `L` is contained in the finite union of the `F i`, so `L` is nowhere dense.
  have hndL : IsNowhereDense L := (IsNowhereDense.iUnion hFnd).mono hL
  have hIntClL : interior (closure L) = ∅ := hndL
  have hIntL : interior L = ∅ :=
    eq_empty_of_subset_empty (hIntClL ▸ interior_mono subset_closure)
  -- The image of `L` under the chart `cC` has empty interior in `M`.
  have himg : interior (cC.toFun '' L) = ∅ := by
    let U : Set (PL.E n) := PL.openCube (n := n) 1
    have hUopen : IsOpen U := isOpen_openCube n 1
    have hLU : L ⊆ U := by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hL hx)
      exact (hF i).2.1 hi
    let L' : Set ↥U := Subtype.val ⁻¹' L
    have hL'val : Subtype.val '' L' = L := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hLU hx⟩, hx, rfl⟩
    -- `L'` is nowhere dense in the open subspace `↥U`.
    have hL'nd : IsNowhereDense L' := by
      rw [IsNowhereDense]
      have hcl : closure L' = Subtype.val ⁻¹' closure L := by
        rw [hUopen.isOpenEmbedding_subtypeVal.isEmbedding.closure_eq_preimage_closure_image L',
          hL'val]
      rw [hcl, ← hUopen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
            continuous_subtype_val (closure L), hIntClL, preimage_empty]
    -- Push it forward through the open embedding `U.domRestrict cC.toFun`.
    have hndImg : IsNowhereDense ((U.domRestrict cC.toFun) '' L') :=
      cC.emb.isInducing.isNowhereDense_image hL'nd
    have heq : (U.domRestrict cC.toFun) '' L' = cC.toFun '' L := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x.1, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hLU hx⟩, hx, rfl⟩
    rw [heq] at hndImg
    exact eq_empty_of_subset_empty (hndImg ▸ interior_mono subset_closure)
  -- `Aᶜ` is open and nonempty, so it cannot be contained in a set with empty interior.
  by_contra hcon
  push Not at hcon
  have hsub : Aᶜ ⊆ cC.toFun '' L := fun x hx => hcon x hx
  have hle : Aᶜ ⊆ interior (cC.toFun '' L) := interior_maximal hsub hA.isOpen_compl
  rw [himg] at hle
  obtain ⟨p, hp⟩ := hAne
  exact (notMem_empty p) (hle hp)

end Work.Cells.Connell
