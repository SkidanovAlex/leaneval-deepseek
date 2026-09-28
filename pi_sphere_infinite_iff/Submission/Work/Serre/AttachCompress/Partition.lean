import Mathlib
import Submission.Work.RatHurewicz.AttachPush.Defs
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj

/-!
# The cell partition of `Y ∪ (n+2)-cells`

The space `attachCells n Y ι f` is the disjoint union of the range of `attachIncl` and the open
cell interiors `cellInterior i`: interior points of the model cell have singleton classes in the
gluing relation (only *boundary* points are glued to `Y`).  Consequences:

* `cellInterior i` meets no other cell interior and is disjoint from the range;
* every centre `cellOrigin i` lies in `cellInterior i` and hence outside the range.
-/

open scoped Topology unitInterval

namespace Work.Serre.AttachCompress

open Work.RatHurewicz Work.RatHurewicz.AttachRange

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-- **Interior points of a cell have singleton classes**: the gluing relation only identifies
boundary points of the cells with points of `Y`. -/
theorem cls_of_inner (f : ι → C(cellSphere n, Y)) {i : ι} {x : cellDisk n}
    (hx : x ∈ cellInner n) (b : Y ⊕ (Σ _ : ι, cellDisk n)) :
    Cls n Y ι f (Sum.inr ⟨i, x⟩) b ↔ b = Sum.inr ⟨i, x⟩ := by
  constructor
  · intro h
    rcases h with h | ⟨y, h1, h2⟩
    · exact h.symm
    · rcases h1 with h1 | ⟨i', z, h1, -⟩
      · exact absurd h1 Sum.inr_ne_inl
      · exfalso
        have h2 : x = cellSphereToDisk n z := congrArg Sigma.snd (Sum.inr.inj h1)
        have h3 : ‖(x : CellVec n)‖ = 1 := by rw [h2]; exact norm_cellSphereToDisk n z
        exact absurd h3 (ne_of_lt hx)
  · intro h; subst h; exact cls_refl n Y ι f _

/-- Two related interior points of the cells are equal (and lie in the same cell). -/
theorem cls_inner_inj (f : ι → C(cellSphere n, Y)) {i j : ι} {x y : cellDisk n}
    (hx : x ∈ cellInner n) (hy : y ∈ cellInner n)
    (h : Cls n Y ι f (Sum.inr ⟨i, x⟩) (Sum.inr ⟨j, y⟩)) : i = j ∧ x = y := by
  have h1 : (Sum.inr ⟨j, y⟩ : Y ⊕ (Σ _ : ι, cellDisk n)) = Sum.inr ⟨i, x⟩ :=
    (cls_of_inner f hx _).mp h
  have h2 := Sum.inr.inj h1
  exact ⟨(congrArg Sigma.fst h2).symm, (congrArg Sigma.snd h2).symm⟩

/-- A point of the disjoint union has its image in the union of the open cells exactly when it is an
interior point of one of the cells. -/
theorem mk_mem_iUnion_cellInterior_iff (f : ι → C(cellSphere n, Y))
    (a : Y ⊕ (Σ _ : ι, cellDisk n)) :
    (Quotient.mk'' a : attachCells n Y ι f) ∈ (⋃ i, cellInterior n Y ι f i) ↔
      ∃ (i : ι) (x : cellDisk n), a = Sum.inr ⟨i, x⟩ ∧ x ∈ cellInner n := by
  constructor
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨i, hi⟩
    obtain ⟨x, hx, hxq⟩ := hi
    have hrel : Relation.EqvGen (attachRel n Y ι f) a (Sum.inr ⟨i, x⟩) :=
      Quotient.exact (show (Quotient.mk'' a : attachCells n Y ι f) =
        Quotient.mk'' (Sum.inr ⟨i, x⟩) from hxq.symm)
    rcases eqvGen_le_cls n Y ι f hrel with h | ⟨y, h1, h2⟩
    · exact ⟨i, x, h, hx⟩
    · rcases h2 with h2 | ⟨i', z, h2, -⟩
      · exact absurd h2 Sum.inr_ne_inl
      · exfalso
        have h3 : x = cellSphereToDisk n z := congrArg Sigma.snd (Sum.inr.inj h2)
        have h4 : ‖(x : CellVec n)‖ = 1 := by rw [h3]; exact norm_cellSphereToDisk n z
        exact absurd h4 (ne_of_lt hx)
  · rintro ⟨i, x, rfl, hx⟩
    exact Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩

/-- **The cell partition of `attachCells n Y ι f`**: the range of `attachIncl` is the complement of
the union of the open cell interiors, which are pairwise disjoint, and no centre lies in the
range. -/
theorem cellPartition (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) :
    Set.range (attachIncl n Y ι f) = (⋃ i, cellInterior n Y ι f i)ᶜ ∧
      Pairwise (fun i j => Disjoint (cellInterior n Y ι f i) (cellInterior n Y ι f j)) ∧
      (∀ i, cellOrigin n Y ι f i ∉ Set.range (attachIncl n Y ι f)) := by
  have key := mk_mem_iUnion_cellInterior_iff (n := n) (Y := Y) (ι := ι) f
  have h1 : Set.range (attachIncl n Y ι f) = (⋃ i, cellInterior n Y ι f i)ᶜ := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      intro hmem
      obtain ⟨i, x, hx, hinner⟩ := key (Sum.inl y) |>.mp hmem
      exact Sum.inl_ne_inr hx
    · intro hz
      obtain ⟨a, rfl⟩ := Quotient.exists_rep z
      rcases a with y | ⟨i, x⟩
      · exact ⟨y, rfl⟩
      · by_cases hx : x ∈ cellInner n
        · exact absurd (key (Sum.inr ⟨i, x⟩) |>.mpr ⟨i, x, rfl, hx⟩) hz
        · have hnorm : ‖(x : CellVec n)‖ = 1 := by
            have hle : ‖(x : CellVec n)‖ ≤ 1 := by
              have h := Metric.mem_closedBall.mp x.2
              simpa [dist_eq_norm] using h
            have hge : 1 ≤ ‖(x : CellVec n)‖ := le_of_not_gt hx
            exact le_antisymm hle hge
          have hsp : dist (x : CellVec n) 0 = 1 := by
            rw [dist_eq_norm, sub_zero]; exact hnorm
          refine ⟨f i ⟨(x : CellVec n), hsp⟩, ?_⟩
          have hc : cellSphereToDisk n ⟨(x : CellVec n), hsp⟩ = x := Subtype.ext rfl
          show attachIncl n Y ι f (f i ⟨(x : CellVec n), hsp⟩) = _
          rw [attachIncl_attachRel n Y ι f i ⟨(x : CellVec n), hsp⟩, hc]
          rfl
  refine ⟨h1, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    obtain ⟨x, hx, hxz⟩ := hzi
    obtain ⟨y, hy, hyz⟩ := hzj
    have hxz' : (Quotient.mk'' (Sum.inr ⟨i, x⟩) : attachCells n Y ι f) = z := hxz
    have hyz' : (Quotient.mk'' (Sum.inr ⟨j, y⟩) : attachCells n Y ι f) = z := hyz
    have hrel : Relation.EqvGen (attachRel n Y ι f) (Sum.inr ⟨i, x⟩) (Sum.inr ⟨j, y⟩) :=
      Quotient.exact (show (Quotient.mk'' (Sum.inr ⟨i, x⟩) : attachCells n Y ι f) =
        (Quotient.mk'' (Sum.inr ⟨j, y⟩) : attachCells n Y ι f) from by rw [hxz', hyz'])
    exact hij (cls_inner_inj f hx hy (eqvGen_le_cls n Y ι f hrel)).1
  · intro i hmem
    have h1' := h1
    rw [Set.mem_range] at hmem
    obtain ⟨y, hy⟩ := hmem
    have : cellOrigin n Y ι f i ∈ (⋃ i, cellInterior n Y ι f i)ᶜ := by
      rw [← h1']; exact ⟨y, hy⟩
    exact this (Set.mem_iUnion.mpr ⟨i, cellOrigin_mem_cellInterior n Y ι f i⟩)

end Work.Serre.AttachCompress
