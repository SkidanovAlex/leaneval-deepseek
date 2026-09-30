import Mathlib
import Submission.Work.Serre.AttachCompress.Partition

/-!
# The cell chart: the interior of a cell is an open copy of the open model cell

The characteristic map `cellMap n Y ι f i` is injective on the open model cell `cellInner n` (its
points have singleton classes, `cls_of_inner`), its image `cellInterior n Y ι f i` is open in
`attachCells n Y ι f`, and the inverse of the resulting bijection is continuous: every open subset
of the model cell has (saturated) open image in the quotient.
-/

open scoped Topology unitInterval

namespace Work.Serre.AttachCompress

open Work.RatHurewicz Work.RatHurewicz.AttachRange

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-- The characteristic map of a cell is injective on the open model cell. -/
theorem cellMap_injOn_inner (f : ι → C(cellSphere n, Y)) (i : ι) :
    Set.InjOn (cellMap n Y ι f i) (cellInner n) := by
  intro x hx y hy hxy
  have hrel : Relation.EqvGen (attachRel n Y ι f) (Sum.inr ⟨i, x⟩) (Sum.inr ⟨i, y⟩) :=
    Quotient.exact (show (Quotient.mk'' (Sum.inr ⟨i, x⟩) : attachCells n Y ι f) =
      (Quotient.mk'' (Sum.inr ⟨i, y⟩) : attachCells n Y ι f) from hxy)
  exact (cls_inner_inj f hx hy (eqvGen_le_cls n Y ι f hrel)).2

/-- The `i`-th cell interior is open: its preimage in `Y ⊕ (Σ i, D)` is the open set of interior
points of the `i`-th model cell. -/
theorem isOpen_cellInterior (f : ι → C(cellSphere n, Y)) (i : ι) :
    IsOpen (cellInterior n Y ι f i) := by
  have hq : Topology.IsCoinducing (Quotient.mk'' :
      (Y ⊕ (Σ _ : ι, cellDisk n)) → attachCells n Y ι f) :=
    (isQuotientMap_quotient_mk' (X := Y ⊕ (Σ _ : ι, cellDisk n))
      (s := Relation.EqvGen.setoid (attachRel n Y ι f))).isCoinducing
  refine hq.isOpen_preimage.1 ?_
  have hpre : (Quotient.mk'' ⁻¹' cellInterior n Y ι f i : Set (Y ⊕ (Σ _ : ι, cellDisk n))) =
      {a | ∃ x : cellDisk n, a = Sum.inr ⟨i, x⟩ ∧ x ∈ cellInner n} := by
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx, hxq⟩ := ha
      have hrel : Relation.EqvGen (attachRel n Y ι f) (Sum.inr ⟨i, x⟩) a :=
        Quotient.exact (show (Quotient.mk'' (Sum.inr ⟨i, x⟩) : attachCells n Y ι f) =
          Quotient.mk'' a from hxq)
      rcases eqvGen_le_cls n Y ι f hrel with h | ⟨y, h1, h2⟩
      · exact ⟨x, h.symm, hx⟩
      · rcases h1 with h1 | ⟨i', z, h1, -⟩
        · exact absurd h1 Sum.inr_ne_inl
        · exfalso
          have h3 : x = cellSphereToDisk n z := congrArg Sigma.snd (Sum.inr.inj h1)
          have h4 : ‖(x : CellVec n)‖ = 1 := by rw [h3]; exact norm_cellSphereToDisk n z
          exact absurd h4 (ne_of_lt hx)
    · rintro ⟨x, rfl, hx⟩
      exact ⟨x, hx, rfl⟩
  rw [hpre]
  rw [isOpen_sum_iff]
  constructor
  · have h0 : Sum.inl ⁻¹' {a : Y ⊕ (Σ _ : ι, cellDisk n) |
        ∃ x : cellDisk n, a = Sum.inr ⟨i, x⟩ ∧ x ∈ cellInner n} = ∅ := by
      ext y; simp
    rw [h0]; exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro j
    by_cases hji : j = i
    · rw [hji]
      have h1 : (fun x : cellDisk n => (Sum.inr ⟨i, x⟩ : Y ⊕ (Σ _ : ι, cellDisk n))) ⁻¹'
          {a : Y ⊕ (Σ _ : ι, cellDisk n) | ∃ x : cellDisk n, a = Sum.inr ⟨i, x⟩ ∧
            x ∈ cellInner n} = cellInner n := by
        ext x
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · rintro ⟨x', hx'eq, hxinner⟩
          have hxx : x' = x := congrArg Sigma.snd (Sum.inr.inj hx'eq.symm)
          rwa [← hxx]
        · intro hx; exact ⟨x, rfl, hx⟩
      have : Sigma.mk i ⁻¹' Sum.inr ⁻¹' {a : Y ⊕ (Σ _ : ι, cellDisk n) |
          ∃ x : cellDisk n, a = Sum.inr ⟨i, x⟩ ∧ x ∈ cellInner n} = cellInner n := by
        rw [Set.preimage_preimage]; exact h1
      rw [this]
      exact isOpen_lt continuous_subtype_val.norm continuous_const
    · have h1 : (fun x : cellDisk n => (Sum.inr ⟨j, x⟩ : Y ⊕ (Σ _ : ι, cellDisk n))) ⁻¹'
          {a : Y ⊕ (Σ _ : ι, cellDisk n) | ∃ x : cellDisk n, a = Sum.inr ⟨i, x⟩ ∧
            x ∈ cellInner n} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨x', hx'eq, -⟩
        exact hji (congrArg Sigma.fst (Sum.inr.inj hx'eq))
      have : Sigma.mk j ⁻¹' Sum.inr ⁻¹' {a : Y ⊕ (Σ _ : ι, cellDisk n) |
          ∃ x : cellDisk n, a = Sum.inr ⟨i, x⟩ ∧ x ∈ cellInner n} = ∅ := by
        rw [Set.preimage_preimage]; exact h1
      rw [this]; exact isOpen_empty

/-- **The image of an open subset of the model cell is open in the attached space.** -/
theorem isOpen_image_of_open_inner (f : ι → C(cellSphere n, Y)) (i : ι) {W : Set (cellDisk n)}
    (hW : IsOpen W) (hWsub : W ⊆ cellInner n) :
    IsOpen (cellMap n Y ι f i '' W) := by
  have hq : Topology.IsCoinducing (Quotient.mk'' :
      (Y ⊕ (Σ _ : ι, cellDisk n)) → attachCells n Y ι f) :=
    (isQuotientMap_quotient_mk' (X := Y ⊕ (Σ _ : ι, cellDisk n))
      (s := Relation.EqvGen.setoid (attachRel n Y ι f))).isCoinducing
  refine hq.isOpen_preimage.1 ?_
  have hpre : (Quotient.mk'' ⁻¹' (cellMap n Y ι f i '' W) : Set (Y ⊕ (Σ _ : ι, cellDisk n))) =
      {a | ∃ x : cellDisk n, x ∈ W ∧ a = Sum.inr ⟨i, x⟩} := by
    ext a
    constructor
    · rintro ⟨x, hxW, hxa⟩
      have hrel : Relation.EqvGen (attachRel n Y ι f) (Sum.inr ⟨i, x⟩) a :=
        Quotient.exact (show (Quotient.mk'' (Sum.inr ⟨i, x⟩) : attachCells n Y ι f) =
          Quotient.mk'' a from hxa)
      rcases eqvGen_le_cls n Y ι f hrel with h | ⟨y, h1, h2⟩
      · exact ⟨x, hxW, h.symm⟩
      · rcases h1 with h1 | ⟨i', z, h1, -⟩
        · exact absurd h1 Sum.inr_ne_inl
        · exfalso
          have h3 : x = cellSphereToDisk n z := congrArg Sigma.snd (Sum.inr.inj h1)
          have h4 : ‖(x : CellVec n)‖ = 1 := by rw [h3]; exact norm_cellSphereToDisk n z
          exact absurd h4 (ne_of_lt (hWsub hxW))
    · rintro ⟨x, hxW, rfl⟩
      exact ⟨x, hxW, rfl⟩
  rw [hpre]
  rw [isOpen_sum_iff]
  constructor
  · have h0 : Sum.inl ⁻¹' {a : Y ⊕ (Σ _ : ι, cellDisk n) |
        ∃ x : cellDisk n, x ∈ W ∧ a = Sum.inr ⟨i, x⟩} = ∅ := by
      ext y; simp
    rw [h0]; exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro j
    by_cases hji : j = i
    · rw [hji]
      have h1 : (fun x : cellDisk n => (Sum.inr ⟨i, x⟩ : Y ⊕ (Σ _ : ι, cellDisk n))) ⁻¹'
          {a : Y ⊕ (Σ _ : ι, cellDisk n) | ∃ x : cellDisk n, x ∈ W ∧
            a = Sum.inr ⟨i, x⟩} = W := by
        ext x
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · rintro ⟨x', hx'W, hx'eq⟩
          have hxx : x' = x := congrArg Sigma.snd (Sum.inr.inj hx'eq.symm)
          rwa [← hxx]
        · intro hx; exact ⟨x, hx, rfl⟩
      have : Sigma.mk i ⁻¹' Sum.inr ⁻¹' {a : Y ⊕ (Σ _ : ι, cellDisk n) |
          ∃ x : cellDisk n, x ∈ W ∧ a = Sum.inr ⟨i, x⟩} = W := by
        rw [Set.preimage_preimage]; exact h1
      rw [this]; exact hW
    · have h1 : (fun x : cellDisk n => (Sum.inr ⟨j, x⟩ : Y ⊕ (Σ _ : ι, cellDisk n))) ⁻¹'
          {a : Y ⊕ (Σ _ : ι, cellDisk n) | ∃ x : cellDisk n, x ∈ W ∧
            a = Sum.inr ⟨i, x⟩} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨x', -, hx'eq⟩
        exact hji (congrArg Sigma.fst (Sum.inr.inj hx'eq))
      have : Sigma.mk j ⁻¹' Sum.inr ⁻¹' {a : Y ⊕ (Σ _ : ι, cellDisk n) |
          ∃ x : cellDisk n, x ∈ W ∧ a = Sum.inr ⟨i, x⟩} = ∅ := by
        rw [Set.preimage_preimage]; exact h1
      rw [this]; exact isOpen_empty

/-- **The cell chart**: `cellInterior n Y ι f i` is an open copy of the open model cell, via the
characteristic map. -/
theorem cellChart (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (i : ι) :
    IsOpen (cellInterior n Y ι f i) ∧
      ∃ S : C(↥(cellInterior n Y ι f i), ↥(cellInner n)),
        ∀ y : ↥(cellInterior n Y ι f i),
          cellMap n Y ι f i ((S y : ↥(cellInner n)) : cellDisk n) = (y : attachCells n Y ι f) := by
  classical
  have hcar : IsOpen (cellInner n) :=
    isOpen_lt continuous_subtype_val.norm continuous_const
  have hex : ∀ y : ↥(cellInterior n Y ι f i), ∃ x : ↥(cellInner n),
      cellMap n Y ι f i (x : cellDisk n) = (y : attachCells n Y ι f) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hx⟩, hxy⟩
  refine ⟨isOpen_cellInterior f i, ⟨⟨fun y => Classical.choose (hex y), ?_⟩,
    fun y => Classical.choose_spec (hex y)⟩⟩
  rw [continuous_def]
  intro W hW
  have hkey : ∀ y : ↥(cellInterior n Y ι f i),
      Classical.choose (hex y) ∈ W ↔
        ∃ x : ↥(cellInner n), x ∈ W ∧
          cellMap n Y ι f i (x : cellDisk n) = (y : attachCells n Y ι f) := by
    intro y
    constructor
    · intro hy
      exact ⟨Classical.choose (hex y), hy, Classical.choose_spec (hex y)⟩
    · rintro ⟨x, hxW, hxy⟩
      have h1 : x = Classical.choose (hex y) :=
        Subtype.ext (cellMap_injOn_inner f i x.2 (Classical.choose (hex y)).2
          (by rw [hxy, Classical.choose_spec (hex y)]))
      rwa [← h1]
  have hset : (fun y : ↥(cellInterior n Y ι f i) => Classical.choose (hex y)) ⁻¹' W =
      Subtype.val ⁻¹' (cellMap n Y ι f i '' (Subtype.val '' W)) := by
    ext y
    rw [Set.mem_preimage, Set.mem_preimage]
    constructor
    · intro hy
      obtain ⟨x, hxW, hxy⟩ := (hkey y).mp hy
      exact ⟨x, ⟨x, hxW, rfl⟩, hxy⟩
    · rintro ⟨x, ⟨x', hx'W, rfl⟩, hxy⟩
      exact (hkey y).mpr ⟨x', hx'W, hxy⟩
  rw [hset]
  have hImg : IsOpen (cellMap n Y ι f i '' (Subtype.val '' W)) :=
    isOpen_image_of_open_inner f i (hcar.isOpenMap_subtype_val W hW) (by
      rintro x ⟨x', -, rfl⟩
      exact x'.2)
  exact isOpen_induced (f := Subtype.val) hImg

end Work.Serre.AttachCompress
