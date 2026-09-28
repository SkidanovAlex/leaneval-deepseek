import Mathlib
import Submission.Work.RatHurewicz.AttachPush.CellInterior

/-!
# Auxiliary point-set facts for the push-off of a map off the cell centres

The map `X → attachCells n Y ι f` avoiding all cell centres is homotoped into `range attachIncl`
by pushing each cell radially from its centre.  This module collects the point-set facts about the
set of centres and about the saturated open set on which the push is defined.
-/

set_option maxHeartbeats 800000

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellSphere n, Y)}

/-- A point of the model cell of norm `< 1` is in the open model cell. -/
theorem mem_cellInner_of_norm_lt {x : cellDisk n} (h : ‖(x : CellVec n)‖ < 1) : x ∈ cellInner n := h

/-- **`cellMap i x` is never a cell centre when `x` is not the centre of the model cell.** -/
theorem cellMap_ne_cellOrigin {i : ι} {x : cellDisk n} (hx : (x : CellVec n) ≠ 0) (j : ι) :
    cellMap n Y ι f i x ≠ cellOrigin n Y ι f j := by
  intro h
  by_cases hnorm : ‖(x : CellVec n)‖ < 1
  · by_cases hij : i = j
    · subst hij
      have h' : Relation.EqvGen (attachRel n Y ι f) (Sum.inr ⟨i, x⟩)
          (Sum.inr ⟨i, cellDiskCentre n⟩) :=
        Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f)) h
      have h2 := eq_of_eqvGen_inr_cellInner (x := cellDiskCentre n)
        (by simp [cellInner, cellDiskCentre]) h'
      have h3 : x = cellDiskCentre n :=
        congrArg (fun p : Σ _ : ι, cellDisk n => p.2) (Sum.inr.inj h2)
      exact hx (by rw [h3]; rfl)
    · have hmem : cellMap n Y ι f i x ∈ cellInterior n Y ι f j := by
        rw [h]
        exact cellOrigin_mem_cellInterior n Y ι f j
      exact Set.disjoint_left.mp (disjoint_cellInterior (f := f) i j hij)
        (cellMap_mem_cellInterior_of_norm_lt (i := i) hnorm) hmem
  · have hxle : ‖(x : CellVec n)‖ ≤ 1 := by
      have h1 := Metric.mem_closedBall.mp x.2
      simpa [dist_eq_norm] using h1
    have hx1 : ‖(x : CellVec n)‖ = 1 := le_antisymm hxle (not_lt.mp hnorm)
    have hA : cellMap n Y ι f i x ∈ Set.range (attachIncl n Y ι f) := by
      let z : cellSphere n := ⟨x, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx1⟩
      have hxz : cellSphereToDisk n z = x := Subtype.ext rfl
      rw [← hxz, ← attachIncl_attachRel n Y ι f i z]
      exact ⟨f i z, rfl⟩
    rw [h] at hA
    exact cellOrigin_notMem_range_attachIncl (f := f) j hA

/-- **The set of cell centres is closed.** -/
theorem isClosed_cellCentres (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) : IsClosed (cellCentres n Y ι f) := by
  classical
  have hpre : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)) :
        (Y ⊕ (Σ _ : ι, cellDisk n)) → attachCells n Y ι f) ⁻¹' (cellCentres n Y ι f) =
      {a | ∃ i : ι, a = Sum.inr ⟨i, cellDiskCentre n⟩} := by
    ext a
    constructor
    · rintro ⟨i, hi⟩
      have hgen : Relation.EqvGen (attachRel n Y ι f) a (Sum.inr ⟨i, cellDiskCentre n⟩) :=
        Relation.EqvGen.symm _ _ (Quotient.exact
          (s := Relation.EqvGen.setoid (attachRel n Y ι f)) hi)
      exact ⟨i, eq_of_eqvGen_inr_cellInner (x := cellDiskCentre n)
        (by simp [cellInner, cellDiskCentre]) hgen⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  refine ((isQuotientMap_quotient_mk'
    (s := Relation.EqvGen.setoid (attachRel n Y ι f))).isCoinducing.isClosed_preimage
      (s := cellCentres n Y ι f)).mp ?_
  rw [hpre, ← isOpen_compl_iff, isOpen_sum_iff]
  constructor
  · have h1 : Sum.inl ⁻¹' {a : Y ⊕ (Σ _ : ι, cellDisk n) |
        ∃ i : ι, a = Sum.inr ⟨i, cellDiskCentre n⟩}ᶜ = Set.univ := by
      ext y
      simp
    rw [h1]
    exact isOpen_univ
  · rw [isOpen_sigma_iff]
    intro j
    have h1 : Sigma.mk j ⁻¹' (Sum.inr ⁻¹'
        {a : Y ⊕ (Σ _ : ι, cellDisk n) | ∃ i : ι, a = Sum.inr ⟨i, cellDiskCentre n⟩}ᶜ) =
        {cellDiskCentre n}ᶜ := by
      ext x
      constructor
      · intro hx hx0
        exact hx ⟨j, by rw [hx0]⟩
      · intro hx ⟨i, hi⟩
        have h2 : (⟨j, x⟩ : Σ _ : ι, cellDisk n) = ⟨i, cellDiskCentre n⟩ := Sum.inr.inj hi
        exact hx (congrArg (fun p : Σ _ : ι, cellDisk n => p.2) h2)
    rw [h1]
    exact isClosed_singleton.isOpen_compl

/-- The **saturated open set** on which the radial push is defined: the preimage of the complement
of the cell centres. -/
def pushDomain (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y)) :
    Set (Y ⊕ (Σ _ : ι, cellDisk n)) :=
  (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))) ⁻¹' (cellCentres n Y ι f)ᶜ

theorem isOpen_pushDomain : IsOpen (pushDomain n Y ι f) :=
  (isClosed_cellCentres n Y ι f).isOpen_compl.preimage (continuous_quotient_mk')

/-- A point of the push domain in the `i`-th summand has non-zero disc coordinate. -/
theorem ne_zero_of_mem_pushDomain {i : ι} {x : cellDisk n}
    (h : (Sum.inr ⟨i, x⟩ : Y ⊕ (Σ _ : ι, cellDisk n)) ∈ pushDomain n Y ι f) :
    (x : CellVec n) ≠ 0 := by
  intro h0
  have hQ : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
      (Sum.inr ⟨i, x⟩) : attachCells n Y ι f) ∈ cellCentres n Y ι f := by
    refine ⟨i, ?_⟩
    show cellOrigin n Y ι f i = Quotient.mk'' (Sum.inr ⟨i, x⟩)
    have hxeq : x = cellDiskCentre n := Subtype.ext h0
    rw [hxeq]
    rfl
  exact h hQ

end

end Work.RatHurewicz
