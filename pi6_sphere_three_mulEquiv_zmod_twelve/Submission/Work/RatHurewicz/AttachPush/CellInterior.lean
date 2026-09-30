import Mathlib
import Submission.Work.RatHurewicz.AttachPush.Defs
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj

/-!
# The interior of an attached cell as an open copy of the open model cell

Point-set facts about `attachCells n Y ι f` used by the general-position and push-off steps:

* an interior point `(i, x)` with `‖x‖ < 1` has a *singleton* class in the gluing relation, so it is
  never identified with a point of `Y` or with a point of another cell;
* consequently `cellMap i` is injective on the open model cell, maps it onto the open set
  `cellInterior i`, and has a continuous inverse there (`cellInterior_section`);
* the cell interiors are pairwise disjoint.
-/

set_option maxHeartbeats 800000

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellSphere n, Y)}

theorem isOpen_cellInner (n : ℕ) : IsOpen (cellInner n) := by
  have h : cellInner n = Subtype.val ⁻¹' Metric.ball (0 : CellVec n) 1 := by
    ext x
    simp only [Set.mem_preimage, cellInner, Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm,
      sub_zero]
  rw [h]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

/-- An interior point of the `i`-th summand has a *singleton* class in the gluing relation. -/
theorem eq_of_eqvGen_inr_cellInner {i : ι} {x : cellDisk n} (hx : x ∈ cellInner n)
    {a : Y ⊕ (Σ _ : ι, cellDisk n)}
    (h : Relation.EqvGen (attachRel n Y ι f) a (Sum.inr ⟨i, x⟩)) : a = Sum.inr ⟨i, x⟩ := by
  rcases AttachRange.eqvGen_le_cls n Y ι f h with heq | ⟨y, -, h2⟩
  · exact heq
  · exfalso
    rcases h2 with h2 | ⟨i', z, h2, -⟩
    · exact Sum.inr_ne_inl h2
    · have hsig : (⟨i, x⟩ : Σ _ : ι, cellDisk n) = ⟨i', cellSphereToDisk n z⟩ := Sum.inr.inj h2
      have hxx : x = cellSphereToDisk n z :=
        congrArg (fun p : Σ _ : ι, cellDisk n => p.2) hsig
      have h1 : ‖(x : CellVec n)‖ < 1 := hx
      have h2' : ‖(x : CellVec n)‖ = 1 := by rw [hxx]; exact norm_cellSphereToDisk n z
      linarith

/-- A point of `Y` is never identified with an interior point of a cell. -/
theorem not_eqvGen_inl_inr_cellInner {i : ι} {x : cellDisk n} (hx : x ∈ cellInner n) (y : Y) :
    ¬ Relation.EqvGen (attachRel n Y ι f) (Sum.inl y) (Sum.inr ⟨i, x⟩) :=
  fun h => Sum.inl_ne_inr (eq_of_eqvGen_inr_cellInner hx h)

/-- The part of the `i`-th summand lying over `U ⊆ cellInner`. -/
def sigmaOver (i : ι) (U : Set (cellDisk n)) : Set (Y ⊕ (Σ _ : ι, cellDisk n)) :=
  {a | ∃ x ∈ U, a = Sum.inr ⟨i, x⟩}

theorem isOpen_sigmaOver {i : ι} {U : Set (cellDisk n)} (hU : IsOpen U) :
    IsOpen (sigmaOver (Y := Y) (ι := ι) i U) := by
  rw [isOpen_sum_iff]
  refine ⟨?_, ?_⟩
  · have hnil : Sum.inl ⁻¹' sigmaOver (Y := Y) (ι := ι) i U = ∅ := by
      ext y
      simp only [Set.mem_preimage, sigmaOver, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, -, h⟩
      exact absurd h Sum.inl_ne_inr
    rw [hnil]; exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro j
    by_cases hji : j = i
    · subst j
      have hset : Sigma.mk i ⁻¹' (Sum.inr ⁻¹' sigmaOver (Y := Y) (ι := ι) i U) = U := by
        ext x
        constructor
        · rintro ⟨x', hx'U, h⟩
          have h1 : (⟨i, x⟩ : Σ _ : ι, cellDisk n) = ⟨i, x'⟩ := Sum.inr.inj h
          have h2 : x = x' := congrArg (fun p : Σ _ : ι, cellDisk n => p.2) h1
          rwa [h2]
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [hset]; exact hU
    · have hnil : Sigma.mk j ⁻¹' (Sum.inr ⁻¹' sigmaOver (Y := Y) (ι := ι) i U) = ∅ := by
        ext x
        simp only [Set.mem_preimage, sigmaOver, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨x', -, h⟩
        have h1 : (⟨j, x⟩ : Σ _ : ι, cellDisk n) = ⟨i, x'⟩ := Sum.inr.inj h
        exact hji (congrArg (fun p : Σ _ : ι, cellDisk n => p.1) h1)
      rw [hnil]; exact isOpen_empty

/-- The saturated preimage of the image of `U ⊆ cellInner` under `cellMap i`: it is exactly the part
of the `i`-th summand lying over `U`. -/
theorem preimage_cellMap_image {i : ι} {U : Set (cellDisk n)} (hU : U ⊆ cellInner n) :
    ((Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)) :
        (Y ⊕ (Σ _ : ι, cellDisk n)) → attachCells n Y ι f) ⁻¹'
        {z : attachCells n Y ι f | ∃ x ∈ U, cellMap n Y ι f i x = z}) = sigmaOver i U := by
  ext a
  constructor
  · rintro ⟨x, hxU, hx⟩
    have hgen : Relation.EqvGen (attachRel n Y ι f) a (Sum.inr ⟨i, x⟩) :=
      Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f)) hx.symm
    exact ⟨x, hxU, eq_of_eqvGen_inr_cellInner (hU hxU) hgen⟩
  · rintro ⟨x, hxU, rfl⟩
    exact ⟨x, hxU, rfl⟩

/-- **The image of a relatively open part of the open model cell is open in the attachment**. -/
theorem isOpen_cellMap_image {i : ι} {U : Set (cellDisk n)} (hU : IsOpen U)
    (hUsub : U ⊆ cellInner n) :
    IsOpen {z : attachCells n Y ι f | ∃ x ∈ U, cellMap n Y ι f i x = z} := by
  have hq := (isQuotientMap_quotient_mk'
    (s := Relation.EqvGen.setoid (attachRel n Y ι f))).isCoinducing
  refine (hq.isOpen_preimage
    (s := {z : attachCells n Y ι f | ∃ x ∈ U, cellMap n Y ι f i x = z})).mp ?_
  rw [preimage_cellMap_image (i := i) (U := U) hUsub]
  exact isOpen_sigmaOver hU

/-- The interior of an attached cell is open. -/
theorem isOpen_cellInterior (i : ι) : IsOpen (cellInterior n Y ι f i) :=
  isOpen_cellMap_image (isOpen_cellInner n) (subset_refl _)

/-- `cellMap i` is injective on the open model cell. -/
theorem cellMap_injective_cellInner (i : ι) :
    Function.Injective fun x : ↥(cellInner n) => cellMap n Y ι f i (x : cellDisk n) := by
  intro x x' h
  have h' : Relation.EqvGen (attachRel n Y ι f) (Sum.inr ⟨i, (x : cellDisk n)⟩)
      (Sum.inr ⟨i, (x' : cellDisk n)⟩) :=
    Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f)) h
  have h2 := eq_of_eqvGen_inr_cellInner (x := (x' : cellDisk n)) x'.2 h'
  exact Subtype.ext (congrArg (fun p : Σ _ : ι, cellDisk n => p.2) (Sum.inr.inj h2))

/-- Two cell interiors are disjoint. -/
theorem disjoint_cellInterior (i j : ι) (hij : i ≠ j) :
    Disjoint (cellInterior n Y ι f i) (cellInterior n Y ι f j) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
  have hgen : Relation.EqvGen (attachRel n Y ι f) (Sum.inr ⟨i, x⟩) (Sum.inr ⟨j, x'⟩) :=
    Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f)) hxx'.symm
  have h2 := eq_of_eqvGen_inr_cellInner (x := x') hx' hgen
  exact hij (congrArg (fun p : Σ _ : ι, cellDisk n => p.1) (Sum.inr.inj h2))

/-- A point of the model cell of norm `< 1` maps into the interior of the cell. -/
theorem cellMap_mem_cellInterior_of_norm_lt {i : ι} {x : cellDisk n}
    (hx : ‖(x : CellVec n)‖ < 1) : cellMap n Y ι f i x ∈ cellInterior n Y ι f i :=
  ⟨x, hx, rfl⟩

/-- **The characteristic map is a homeomorphism from the open model cell onto the interior of the
attached cell**: a continuous section of `cellMap i` over `cellInterior i`. -/
theorem cellInterior_section (i : ι) :
    ∃ S : C(↥(cellInterior n Y ι f i), ↥(cellInner n)),
      ∀ y : ↥(cellInterior n Y ι f i),
        cellMap n Y ι f i ((S y : ↥(cellInner n)) : cellDisk n) = (y : attachCells n Y ι f) := by
  classical
  obtain ⟨Sf, hSf⟩ : ∃ Sf : ↥(cellInterior n Y ι f i) → ↥(cellInner n),
      ∀ y : ↥(cellInterior n Y ι f i),
        cellMap n Y ι f i ((Sf y : ↥(cellInner n)) : cellDisk n) = (y : attachCells n Y ι f) := by
    choose g hg using fun y : ↥(cellInterior n Y ι f i) => y.2
    exact ⟨fun y => ⟨g y, (hg y).1⟩, fun y => (hg y).2⟩
  refine ⟨⟨Sf, ?_⟩, hSf⟩
  rw [continuous_def]
  intro V hV
  obtain ⟨V₀, hV₀, hV₀eq⟩ := isOpen_induced_iff.mp hV
  have hWin : IsOpen (V₀ ∩ cellInner n) := hV₀.inter (isOpen_cellInner n)
  have hWeq : Subtype.val ⁻¹' (V₀ ∩ cellInner n) = V := by
    rw [← hV₀eq]
    ext z
    constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, z.2⟩
  rw [← hWeq]
  have hset : Sf ⁻¹' (Subtype.val ⁻¹' (V₀ ∩ cellInner n)) =
      (Subtype.val : ↥(cellInterior n Y ι f i) → attachCells n Y ι f) ⁻¹'
        {z : attachCells n Y ι f | ∃ x ∈ V₀ ∩ cellInner n, cellMap n Y ι f i x = z} := by
    ext y
    constructor
    · intro hy
      exact ⟨(Sf y : ↥(cellInner n)), ⟨hy.1, (Sf y).2⟩, hSf y⟩
    · rintro ⟨x, hx, hxy⟩
      have h1 : (⟨x, hx.2⟩ : ↥(cellInner n)) = Sf y := by
        refine cellMap_injective_cellInner (f := f) i ?_
        change cellMap n Y ι f i x = cellMap n Y ι f i ((Sf y : ↥(cellInner n)) : cellDisk n)
        rw [hxy, hSf y]
      show ((Sf y : ↥(cellInner n)) : cellDisk n) ∈ V₀ ∩ cellInner n
      rw [← h1]
      exact ⟨hx.1, hx.2⟩
  rw [hset]
  exact (isOpen_cellMap_image (i := i) hWin (Set.inter_subset_right)).preimage
    continuous_subtype_val


/-- **The range of `attachIncl` is the complement of the cell interiors.** -/
theorem range_attachIncl_eq_compl_iUnion_cellInterior :
    Set.range (attachIncl n Y ι f) = (⋃ i, cellInterior n Y ι f i)ᶜ := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro i
    rintro ⟨x, hx, hxy⟩
    have hgen : Relation.EqvGen (attachRel n Y ι f) (Sum.inl y) (Sum.inr ⟨i, x⟩) :=
      Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f)) hxy.symm
    exact not_eqvGen_inl_inr_cellInner hx y hgen
  · intro hz
    revert hz
    refine Quotient.inductionOn z ?_
    intro a hz
    cases a with
    | inl y => exact ⟨y, rfl⟩
    | inr p =>
      obtain ⟨i, x⟩ := p
      have hxle : ‖(x : CellVec n)‖ ≤ 1 := by
        have h := Metric.mem_closedBall.mp x.2
        simpa [dist_eq_norm] using h
      have hxge : 1 ≤ ‖(x : CellVec n)‖ := by
        by_contra hlt
        push_neg at hlt
        exact hz (Set.mem_iUnion.mpr ⟨i, ⟨x, hlt, rfl⟩⟩)
      have hx1 : ‖(x : CellVec n)‖ = 1 := le_antisymm hxle hxge
      let z' : cellSphere n := ⟨x, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx1⟩
      refine ⟨f i z', ?_⟩
      rw [attachIncl_attachRel n Y ι f i z']
      congr 1

/-- The range of `attachIncl` is closed (it is the complement of the open union of cell
interiors). -/
theorem isClosed_range_attachIncl : IsClosed (Set.range (attachIncl n Y ι f)) := by
  rw [range_attachIncl_eq_compl_iUnion_cellInterior]
  exact (isOpen_iUnion fun i => isOpen_cellInterior (n := n) (Y := Y) (ι := ι) (f := f) i).isClosed_compl

/-- The centre of a cell is never in the range of `attachIncl`. -/
theorem cellOrigin_notMem_range_attachIncl (i : ι) :
    cellOrigin n Y ι f i ∉ Set.range (attachIncl n Y ι f) := by
  rw [range_attachIncl_eq_compl_iUnion_cellInterior, Set.mem_compl_iff]
  intro h
  exact h (Set.mem_iUnion.mpr ⟨i, cellOrigin_mem_cellInterior n Y ι f i⟩)

end

end Work.RatHurewicz
