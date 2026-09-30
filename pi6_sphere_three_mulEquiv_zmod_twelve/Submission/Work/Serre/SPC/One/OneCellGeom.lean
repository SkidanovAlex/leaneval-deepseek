import Mathlib
import Submission.Work.Serre.SPC.One.Defs
import Submission.Work.StemsB.RelChainsR

set_option synthInstance.maxHeartbeats 400000


/-!
# The geometry of the `1`-cell attachment

`Z = attachOneCells Y ι f` is `Y` with the intervals `D¹` attached along `f : ι → C(S⁰, Y)`.
This file proves the geometric facts used by the neighbourhood argument of the `1`-cell step:

* interior points of a cell have singleton classes in the gluing relation (`clsOne_of_inner`);
* consequently the open cells are pairwise disjoint, the characteristic map is injective on the
  open model interval, and no interior point lies in the old part (`oneCellGeometry`);
* the image of an open (resp. closed) subset of the open model interval is open (resp. closed);
* the open cell is an open copy of the open model interval (`exists_chart`);
* the centres form a closed subset.

The proofs follow the templates of the general `(n+2)`-cell case
(`Submission/Work/Serre/AttachCompress/{Partition,Chart}.lean` and
`Submission/Work/AttachPush/isClosed_cellMap_image_closedBall.lean`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC.One

open Work.Serre.SPC

noncomputable section

/-! ## The intended equivalence relation -/

/-- The partition of `Y ⊕ (Σ i, D¹)` whose classes are the singletons of the interior points of the
cells and the sets `{inl y} ∪ {inr (i,z) : boundary z, f i z = y}`. -/
def ClsOne (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    (a b : Y ⊕ (Σ _ : ι, cellD1)) : Prop :=
  a = b ∨ ∃ y : Y,
    (a = Sum.inl y ∨ ∃ (i : ι) (z : cellS0),
      a = Sum.inr ⟨i, cellS0ToD1 z⟩ ∧ f i z = y) ∧
    (b = Sum.inl y ∨ ∃ (i : ι) (z : cellS0),
      b = Sum.inr ⟨i, cellS0ToD1 z⟩ ∧ f i z = y)

variable {Y : Type} [TopologicalSpace Y] {ι : Type} (f : ι → C(cellS0, Y))

theorem clsOne_rel (a b : Y ⊕ (Σ _ : ι, cellD1)) (h : oneCellRel Y ι f a b) :
    ClsOne Y ι f a b := by
  rcases h with ⟨i, z, rfl, rfl⟩
  exact Or.inr ⟨f i z, Or.inl rfl, Or.inr ⟨i, z, rfl, rfl⟩⟩

theorem clsOne_refl (a : Y ⊕ (Σ _ : ι, cellD1)) : ClsOne Y ι f a a := Or.inl rfl

theorem clsOne_symm {a b : Y ⊕ (Σ _ : ι, cellD1)} (h : ClsOne Y ι f a b) :
    ClsOne Y ι f b a := by
  rcases h with h | ⟨y, h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨y, h2, h1⟩

theorem clsOne_trans {a b c : Y ⊕ (Σ _ : ι, cellD1)}
    (hab : ClsOne Y ι f a b) (hbc : ClsOne Y ι f b c) : ClsOne Y ι f a c := by
  rcases hab with h | ⟨y, h1, h2⟩
  · subst h; exact hbc
  rcases hbc with h' | ⟨y', h3, h4⟩
  · subst h'; exact Or.inr ⟨y, h1, h2⟩
  have hyy' : y = y' := by
    cases h2 with
    | inl h2inl =>
      cases h3 with
      | inl h3inl => exact Sum.inl.inj (h2inl.symm.trans h3inl)
      | inr h3inr =>
        obtain ⟨i', z', hz', -⟩ := h3inr
        exact absurd (Eq.trans (Eq.symm h2inl) hz') Sum.inl_ne_inr
    | inr h2inr =>
      obtain ⟨i, z, hz, hfz⟩ := h2inr
      cases h3 with
      | inl h3inl => exact absurd (Eq.trans (Eq.symm h3inl) hz) Sum.inl_ne_inr
      | inr h3inr =>
        obtain ⟨i', z', hz', hfz'⟩ := h3inr
        have hiz : (⟨i, cellS0ToD1 z⟩ : Σ _ : ι, cellD1) =
            ⟨i', cellS0ToD1 z'⟩ := Sum.inr.inj (hz.symm.trans hz')
        have hi : i = i' := congrArg (fun p : Σ _ : ι, cellD1 => p.1) hiz
        have hzz : z = z' :=
          cellS0ToD1_injective (congrArg (fun p : Σ _ : ι, cellD1 => p.2) hiz)
        subst hi; subst hzz
        rw [← hfz, hfz']
  subst hyy'
  exact Or.inr ⟨y, h1, h4⟩

/-- The generated equivalence relation is contained in `ClsOne`. -/
theorem eqvGen_le_clsOne {a b : Y ⊕ (Σ _ : ι, cellD1)}
    (h : Relation.EqvGen (oneCellRel Y ι f) a b) : ClsOne Y ι f a b := by
  induction h with
  | rel x x' hxx' => exact clsOne_rel f x x' hxx'
  | refl x => exact clsOne_refl f x
  | symm x x' _ ih => exact clsOne_symm f ih
  | trans x x' x'' _ _ ih1 ih2 => exact clsOne_trans f ih1 ih2

/-! ## Interior points have singleton classes -/

/-- **Points of the open model interval have singleton classes.** -/
theorem clsOne_of_inner {i : ι} {x : cellD1} (hx : x ∈ cellInnerOne)
    (b : Y ⊕ (Σ _ : ι, cellD1)) :
    ClsOne Y ι f (Sum.inr ⟨i, x⟩) b ↔ b = Sum.inr ⟨i, x⟩ := by
  constructor
  · intro h
    rcases h with h | ⟨y, h1, h2⟩
    · exact h.symm
    · rcases h1 with h1 | ⟨i', z, h1, -⟩
      · exact absurd h1 Sum.inr_ne_inl
      · exfalso
        have h3 : x = cellS0ToD1 z := congrArg Sigma.snd (Sum.inr.inj h1)
        have h4 : ‖(x : ℝ)‖ = 1 := by rw [h3]; exact norm_cellS0ToD1 z
        exact absurd h4 (ne_of_lt hx)
  · intro h; subst h; exact clsOne_refl f _

/-- Two related points of the open model intervals are equal and lie in the same cell. -/
theorem clsOne_inner_inj {i j : ι} {x y : cellD1} (hx : x ∈ cellInnerOne)
    (_hy : y ∈ cellInnerOne) (h : ClsOne Y ι f (Sum.inr ⟨i, x⟩) (Sum.inr ⟨j, y⟩)) :
    i = j ∧ x = y := by
  have h1 : (Sum.inr ⟨j, y⟩ : Y ⊕ (Σ _ : ι, cellD1)) = Sum.inr ⟨i, x⟩ :=
    (clsOne_of_inner f hx _).mp h
  have h2 := Sum.inr.inj h1
  exact ⟨(congrArg Sigma.fst h2).symm, (congrArg Sigma.snd h2).symm⟩

/-- The characteristic map of a cell is injective on the open model interval. -/
theorem oneCellMap_injOn_inner (i : ι) : Set.InjOn (oneCellMap Y ι f i) cellInnerOne := by
  intro x hx y hy hxy
  have hrel : Relation.EqvGen (oneCellRel Y ι f) (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellD1))
      (Sum.inr (⟨i, y⟩ : Σ _ : ι, cellD1)) :=
    Quotient.exact (show (Quotient.mk'' (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellD1)) :
        attachOneCells Y ι f) =
      (Quotient.mk'' (Sum.inr (⟨i, y⟩ : Σ _ : ι, cellD1))) from hxy)
  exact (clsOne_inner_inj f hx hy (eqvGen_le_clsOne f hrel)).2

/-! ## The partition of `Z` -/

/-- **A point of the disjoint union lies in the union of the open cells exactly when it is an
interior point of one of the cells.** -/
theorem mk_mem_cellInnerUnionOne_iff (a : Y ⊕ (Σ _ : ι, cellD1)) :
    (Quotient.mk'' a : attachOneCells Y ι f) ∈ cellInnerUnionOne Y ι f ↔
      ∃ (i : ι) (x : cellD1), x ∈ cellInnerOne ∧ a = Sum.inr ⟨i, x⟩ := by
  constructor
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨i, hi⟩
    obtain ⟨x, hx, hxq⟩ := hi
    have hrel : Relation.EqvGen (oneCellRel Y ι f) a (Sum.inr ⟨i, x⟩) :=
      Quotient.exact (show (Quotient.mk'' a : attachOneCells Y ι f) =
        Quotient.mk'' (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellD1)) from hxq.symm)
    rcases eqvGen_le_clsOne f hrel with h | ⟨y, h1, h2⟩
    · exact ⟨i, x, hx, h⟩
    · rcases h2 with h2 | ⟨i', z, h2, -⟩
      · exact absurd h2 Sum.inr_ne_inl
      · exfalso
        have h3 : x = cellS0ToD1 z := congrArg Sigma.snd (Sum.inr.inj h2)
        have h4 : ‖(x : ℝ)‖ = 1 := by rw [h3]; exact norm_cellS0ToD1 z
        exact absurd h4 (ne_of_lt hx)
  · rintro ⟨i, x, hx, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩

/-- **The partition of `Z`**: the old part is the complement of the union of the open cells. -/
theorem oneCellOldPart_eq_compl : oneCellOldPart Y ι f = (cellInnerUnionOne Y ι f)ᶜ := by
  have key := mk_mem_cellInnerUnionOne_iff (Y := Y) (ι := ι) f
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    intro hmem
    obtain ⟨i, x, hx, ha⟩ := key (Sum.inl y) |>.mp hmem
    exact Sum.inl_ne_inr ha
  · intro hz
    obtain ⟨a, rfl⟩ := Quotient.exists_rep z
    rcases a with y | ⟨i, x⟩
    · exact ⟨y, rfl⟩
    · by_cases hx : x ∈ cellInnerOne
      · exact absurd (key (Sum.inr ⟨i, x⟩) |>.mpr ⟨i, x, hx, rfl⟩) hz
      · have hle : ‖(x : ℝ)‖ ≤ 1 := by
          have h := Metric.mem_closedBall.mp x.2
          simpa [dist_eq_norm] using h
        have hge : 1 ≤ ‖(x : ℝ)‖ := le_of_not_gt hx
        have hnorm : ‖(x : ℝ)‖ = 1 := le_antisymm hle hge
        have hsp : dist (x : ℝ) 0 = 1 := by rw [dist_eq_norm, sub_zero]; exact hnorm
        refine ⟨f i ⟨(x : ℝ), hsp⟩, ?_⟩
        have hc : cellS0ToD1 ⟨(x : ℝ), hsp⟩ = x := Subtype.ext rfl
        show oneIncl Y ι f (f i ⟨(x : ℝ), hsp⟩) = _
        rw [oneIncl_oneCellRel Y ι f i ⟨(x : ℝ), hsp⟩, hc]
        rfl

/-- The open cells are pairwise disjoint. -/
theorem disjoint_cellInteriorOne {i j : ι} (hij : i ≠ j) :
    Disjoint (cellInteriorOne Y ι f i) (cellInteriorOne Y ι f j) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hrel : Relation.EqvGen (oneCellRel Y ι f) (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellD1))
      (Sum.inr (⟨j, y⟩ : Σ _ : ι, cellD1)) :=
    Quotient.exact (show ((oneCellMap Y ι f i x : attachOneCells Y ι f)) =
      (oneCellMap Y ι f j y) from by rw [hxz, hyz])
  exact hij (clsOne_inner_inj f hx hy (eqvGen_le_clsOne f hrel)).1

/-- The centre of a cell lies in its open cell. -/
theorem oneCellCentreOne_mem_cellInteriorOne (i : ι) :
    oneCellCentreOne Y ι f i ∈ cellInteriorOne Y ι f i :=
  ⟨cellD1Centre, by simp [cellD1Centre, cellInnerOne], rfl⟩

/-- The centre of a cell does not lie in the old part. -/
theorem oneCellCentreOne_not_mem_oldPart (i : ι) :
    oneCellCentreOne Y ι f i ∉ oneCellOldPart Y ι f := by
  intro h
  rw [oneCellOldPart_eq_compl] at h
  exact h (Set.mem_iUnion.mpr ⟨i, oneCellCentreOne_mem_cellInteriorOne f i⟩)

/-! ## Openness and closedness of the images -/

/-- The saturated preimage of the union of the images of `U ⊆ cellInnerOne`. -/
theorem preimage_cellUnionOne {U : Set cellD1} (hU : U ⊆ cellInnerOne) :
    (Quotient.mk'' ⁻¹' cellUnionOne Y ι f U : Set (Y ⊕ (Σ _ : ι, cellD1))) =
      {a | ∃ (i : ι) (x : cellD1), x ∈ U ∧ a = Sum.inr ⟨i, x⟩} := by
  ext a
  constructor
  · intro ha
    simp only [Set.mem_preimage, mem_cellUnionOne] at ha
    obtain ⟨i, x, hx, hxa⟩ := ha
    have hrel : Relation.EqvGen (oneCellRel Y ι f) (Sum.inr ⟨i, x⟩) a :=
      Quotient.exact (show (Quotient.mk'' (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellD1)) :
        attachOneCells Y ι f) = Quotient.mk'' a from hxa)
    rcases eqvGen_le_clsOne f hrel with h | ⟨y, h1, h2⟩
    · exact ⟨i, x, hx, h.symm⟩
    · rcases h1 with h1 | ⟨i', z, h1, -⟩
      · exact absurd h1 Sum.inr_ne_inl
      · exfalso
        have h3 : x = cellS0ToD1 z := congrArg Sigma.snd (Sum.inr.inj h1)
        have h4 : ‖(x : ℝ)‖ = 1 := by rw [h3]; exact norm_cellS0ToD1 z
        exact absurd h4 (ne_of_lt (hU hx))
  · rintro ⟨i, x, hx, rfl⟩
    exact mem_cellUnionOne.mpr ⟨i, x, hx, rfl⟩

theorem isOpen_preimage_cellUnionOne {U : Set cellD1} (hU : U ⊆ cellInnerOne)
    (hUo : IsOpen U) :
    IsOpen ((Quotient.mk'' ⁻¹' cellUnionOne Y ι f U : Set (Y ⊕ (Σ _ : ι, cellD1)))) := by
  rw [preimage_cellUnionOne f hU, isOpen_sum_iff]
  constructor
  · have h0 : Sum.inl ⁻¹' {a : Y ⊕ (Σ _ : ι, cellD1) |
        ∃ (i : ι) (x : cellD1), x ∈ U ∧ a = Sum.inr ⟨i, x⟩} = ∅ := by
      ext y; simp
    rw [h0]; exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro j
    have h1 : Sigma.mk j ⁻¹' (Sum.inr ⁻¹' {a : Y ⊕ (Σ _ : ι, cellD1) |
        ∃ (i : ι) (x : cellD1), x ∈ U ∧ a = Sum.inr ⟨i, x⟩}) = U := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨i, x', hx', h⟩
        have h2 : (⟨j, x⟩ : Σ _ : ι, cellD1) = ⟨i, x'⟩ := Sum.inr.inj h
        have h3 : x = x' := congrArg Sigma.snd h2
        rwa [h3]
      · intro hx; exact ⟨j, x, hx, rfl⟩
    rw [h1]; exact hUo

theorem isClosed_preimage_cellUnionOne {U : Set cellD1} (hU : U ⊆ cellInnerOne)
    (hUc : IsClosed U) :
    IsClosed ((Quotient.mk'' ⁻¹' cellUnionOne Y ι f U : Set (Y ⊕ (Σ _ : ι, cellD1)))) := by
  rw [preimage_cellUnionOne f hU, isClosed_sum_iff]
  constructor
  · have h0 : Sum.inl ⁻¹' {a : Y ⊕ (Σ _ : ι, cellD1) |
        ∃ (i : ι) (x : cellD1), x ∈ U ∧ a = Sum.inr ⟨i, x⟩} = ∅ := by
      ext y; simp
    rw [h0]; exact isClosed_empty
  · rw [isClosed_sigma_iff]
    intro j
    have h1 : Sigma.mk j ⁻¹' (Sum.inr ⁻¹' {a : Y ⊕ (Σ _ : ι, cellD1) |
        ∃ (i : ι) (x : cellD1), x ∈ U ∧ a = Sum.inr ⟨i, x⟩}) = U := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨i, x', hx', h⟩
        have h2 : (⟨j, x⟩ : Σ _ : ι, cellD1) = ⟨i, x'⟩ := Sum.inr.inj h
        have h3 : x = x' := congrArg Sigma.snd h2
        rwa [h3]
      · intro hx; exact ⟨j, x, hx, rfl⟩
    rw [h1]; exact hUc

/-- **The image of an open subset of the open model interval is open.** -/
theorem isOpen_cellUnionOne {U : Set cellD1} (hU : U ⊆ cellInnerOne) (hUo : IsOpen U) :
    IsOpen (cellUnionOne Y ι f U) := by
  have hq : Topology.IsCoinducing (Quotient.mk'' :
      (Y ⊕ (Σ _ : ι, cellD1)) → attachOneCells Y ι f) :=
    (isQuotientMap_quotient_mk' (X := Y ⊕ (Σ _ : ι, cellD1))
      (s := Relation.EqvGen.setoid (oneCellRel Y ι f))).isCoinducing
  exact hq.isOpen_preimage.1 (isOpen_preimage_cellUnionOne f hU hUo)

/-- **The image of a closed subset of the open model interval is closed.** -/
theorem isClosed_cellUnionOne {U : Set cellD1} (hU : U ⊆ cellInnerOne) (hUc : IsClosed U) :
    IsClosed (cellUnionOne Y ι f U) := by
  have hq : Topology.IsCoinducing (Quotient.mk'' :
      (Y ⊕ (Σ _ : ι, cellD1)) → attachOneCells Y ι f) :=
    (isQuotientMap_quotient_mk' (X := Y ⊕ (Σ _ : ι, cellD1))
      (s := Relation.EqvGen.setoid (oneCellRel Y ι f))).isCoinducing
  exact hq.isClosed_preimage.1 (isClosed_preimage_cellUnionOne f hU hUc)

/-! ## The cell chart -/

theorem isOpen_cellImage_set (i : ι) {U : Set cellD1} (hU : IsOpen U) :
    IsOpen ({a : Y ⊕ (Σ _ : ι, cellD1) | ∃ x ∈ U, a = Sum.inr ⟨i, x⟩}) := by
  rw [isOpen_sum_iff]
  constructor
  · have hnil : Sum.inl ⁻¹'
        {a : Y ⊕ (Σ _ : ι, cellD1) | ∃ x ∈ U, a = Sum.inr ⟨i, x⟩} = ∅ := by
      ext y; simp
    rw [hnil]; exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro j
    by_cases hji : j = i
    · subst hji
      have h1 : (fun x : cellD1 => (Sum.inr (⟨j, x⟩ : Σ _ : ι, cellD1))) ⁻¹'
          {a : Y ⊕ (Σ _ : ι, cellD1) | ∃ x ∈ U, a = Sum.inr ⟨j, x⟩} = U := by
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨x', hx'U, h⟩
          have h2 : (⟨j, x⟩ : Σ _ : ι, cellD1) = ⟨j, x'⟩ := Sum.inr.inj h
          have h3 : x = x' := congrArg (fun p : Σ _ : ι, cellD1 => p.2) h2
          rwa [h3]
        · intro hx; exact ⟨x, hx, rfl⟩
      have h2 : Sigma.mk j ⁻¹' (Sum.inr ⁻¹'
          {a : Y ⊕ (Σ _ : ι, cellD1) | ∃ x ∈ U, a = Sum.inr ⟨j, x⟩}) = U := by
        rw [Set.preimage_preimage]; exact h1
      rw [h2]; exact hU
    · have h1 : (fun x : cellD1 => (Sum.inr (⟨j, x⟩ : Σ _ : ι, cellD1))) ⁻¹'
          {a : Y ⊕ (Σ _ : ι, cellD1) | ∃ x ∈ U, a = Sum.inr ⟨i, x⟩} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨x', -, h⟩
        have h2 : (⟨j, x⟩ : Σ _ : ι, cellD1) = ⟨i, x'⟩ := Sum.inr.inj h
        exact hji (congrArg (fun p : Σ _ : ι, cellD1 => p.1) h2)
      have h2 : Sigma.mk j ⁻¹' (Sum.inr ⁻¹'
          {a : Y ⊕ (Σ _ : ι, cellD1) | ∃ x ∈ U, a = Sum.inr ⟨i, x⟩}) = ∅ := by
        rw [Set.preimage_preimage]; exact h1
      rw [h2]; exact isOpen_empty

/-- The single-cell form of the saturated preimage. -/
theorem preimage_cellImage (i : ι) {U : Set cellD1} (hU : U ⊆ cellInnerOne) :
    (Quotient.mk'' ⁻¹'
        {z : attachOneCells Y ι f | ∃ x ∈ U, oneCellMap Y ι f i x = z}
      : Set (Y ⊕ (Σ _ : ι, cellD1))) = {a | ∃ x ∈ U, a = Sum.inr ⟨i, x⟩} := by
  ext a
  constructor
  · rintro ⟨x, hx, hxa⟩
    have hrel : Relation.EqvGen (oneCellRel Y ι f) (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellD1))
        a :=
      Quotient.exact (show (Quotient.mk'' (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellD1)) :
        attachOneCells Y ι f) = Quotient.mk'' a from hxa)
    exact ⟨x, hx, (clsOne_of_inner f (hU hx) a).mp (eqvGen_le_clsOne f hrel)⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem isOpen_cellImage (i : ι) {U : Set cellD1} (hU : U ⊆ cellInnerOne) (hUo : IsOpen U) :
    IsOpen {z : attachOneCells Y ι f | ∃ x ∈ U, oneCellMap Y ι f i x = z} := by
  have hq : Topology.IsCoinducing (Quotient.mk'' :
      (Y ⊕ (Σ _ : ι, cellD1)) → attachOneCells Y ι f) :=
    (isQuotientMap_quotient_mk' (X := Y ⊕ (Σ _ : ι, cellD1))
      (s := Relation.EqvGen.setoid (oneCellRel Y ι f))).isCoinducing
  refine hq.isOpen_preimage.1 ?_
  rw [preimage_cellImage f i hU]
  exact isOpen_cellImage_set i hUo

/-- **The open cell is an open copy of the open model interval**, via the characteristic map. -/
theorem exists_chart (i : ι) :
    ∃ S : C(↥(cellInteriorOne Y ι f i), ↥cellInnerOne),
      (∀ x : ↥(cellInteriorOne Y ι f i),
        oneCellMap Y ι f i (S x) = (x : attachOneCells Y ι f)) ∧
      (∀ x : ↥cellInnerOne, S ⟨oneCellMap Y ι f i x, ⟨x, x.2, rfl⟩⟩ = x) := by
  classical
  have hex : ∀ y : ↥(cellInteriorOne Y ι f i),
      ∃ x : ↥cellInnerOne, oneCellMap Y ι f i x = (y : attachOneCells Y ι f) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hx⟩, hxy⟩
  refine ⟨⟨fun y => Classical.choose (hex y), ?_⟩, fun y => Classical.choose_spec (hex y),
    fun x => ?_⟩
  · rw [continuous_def]
    intro W hW
    have hKey : ∀ y : ↥(cellInteriorOne Y ι f i),
        Classical.choose (hex y) ∈ W ↔
          ∃ x : ↥cellInnerOne, x ∈ W ∧ oneCellMap Y ι f i x = (y : attachOneCells Y ι f) := by
      intro y
      constructor
      · intro hy
        exact ⟨Classical.choose (hex y), hy, Classical.choose_spec (hex y)⟩
      · rintro ⟨x, hxW, hxy⟩
        have h1 : x = Classical.choose (hex y) :=
          Subtype.ext (oneCellMap_injOn_inner f i x.2 (Classical.choose (hex y)).2
            (by rw [hxy, Classical.choose_spec (hex y)]))
        rwa [← h1]
    have hset : (fun y : ↥(cellInteriorOne Y ι f i) => Classical.choose (hex y)) ⁻¹' W =
        Subtype.val ⁻¹' (⋃ j, oneCellMap Y ι f j '' (Subtype.val '' W)) := by
      ext y
      rw [Set.mem_preimage, Set.mem_preimage]
      constructor
      · intro hy
        obtain ⟨x, hxW, hxy⟩ := (hKey y).mp hy
        exact Set.mem_iUnion.mpr ⟨i, x, ⟨x, hxW, rfl⟩, hxy⟩
      · intro hy
        obtain ⟨j, x, ⟨x', hx'W, hx'eq⟩, hxy⟩ := Set.mem_iUnion.mp hy
        have hxi : x = (x' : cellD1) := hx'eq.symm
        subst hxi
        have hji : j = i := by
          by_contra hne
          have hd : Disjoint (cellInteriorOne Y ι f j) (cellInteriorOne Y ι f i) :=
            disjoint_cellInteriorOne f hne
          have h1 : (y : attachOneCells Y ι f) ∈ cellInteriorOne Y ι f j := ⟨x', x'.2, hxy⟩
          have h2 : (y : attachOneCells Y ι f) ∈ cellInteriorOne Y ι f i := y.2
          exact (Set.disjoint_left.mp hd) h1 h2
        subst hji
        exact (hKey y).mpr ⟨x', hx'W, hxy⟩
    rw [hset]
    have hInner : IsOpen cellInnerOne :=
      isOpen_lt continuous_subtype_val.norm continuous_const
    have hImg : IsOpen (⋃ j, oneCellMap Y ι f j '' (Subtype.val '' W)) :=
      isOpen_cellUnionOne f (by rintro z ⟨x', -, rfl⟩; exact x'.2)
        (hInner.isOpenMap_subtype_val W hW)
    exact isOpen_induced (f := Subtype.val) hImg
  · refine Subtype.ext ?_
    exact oneCellMap_injOn_inner f i (Classical.choose (hex _)).2 x.2
      (Classical.choose_spec (hex ⟨oneCellMap Y ι f i x, ⟨x, x.2, rfl⟩⟩))

/-! ## The centres -/

theorem cellUnionOne_centreSet :
    cellUnionOne Y ι f {x : cellD1 | ‖(x : ℝ)‖ ≤ 0} = oneCellCentresOne Y ι f := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, x, hx, hxz⟩ := mem_cellUnionOne.mp hz
    have hx0 : ‖(x : ℝ)‖ = 0 := le_antisymm hx (norm_nonneg _)
    have hx' : x = cellD1Centre := by
      refine Subtype.ext ?_
      simpa [cellD1Centre] using norm_eq_zero.mp hx0
    exact ⟨i, by rw [oneCellCentreOne, ← hx']; exact hxz⟩
  · rintro ⟨i, hi⟩
    refine mem_cellUnionOne.mpr ⟨i, cellD1Centre, ?_, ?_⟩
    · show ‖((cellD1Centre : cellD1) : ℝ)‖ ≤ 0
      simp [cellD1Centre]
    · show oneCellMap Y ι f i cellD1Centre = z
      rw [← hi]; rfl

/-! ## The geometry bundle -/

/-- **The geometry of the `1`-cell attachment**: the partition of `Z` into the old part and the open
cells, the disjointness and injectivity of the latter, the openness and closedness of the images of
subsets of the open model interval, the cell chart, and the closedness of the centres. -/
theorem oneCellGeometry (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) :
    (oneCellOldPart Y ι f = (cellInnerUnionOne Y ι f)ᶜ) ∧
    (∀ i j : ι, i ≠ j → Disjoint (cellInteriorOne Y ι f i)
      (cellInteriorOne Y ι f j)) ∧
    (∀ i : ι, Set.InjOn (oneCellMap Y ι f i) cellInnerOne) ∧
    (∀ i : ι, oneCellCentreOne Y ι f i ∈ cellInteriorOne Y ι f i ∧
      oneCellCentreOne Y ι f i ∉ oneCellOldPart Y ι f) ∧
    (∀ U : Set cellD1, U ⊆ cellInnerOne → IsOpen U →
      IsOpen (cellUnionOne Y ι f U)) ∧
    (∀ U : Set cellD1, U ⊆ cellInnerOne → IsClosed U →
      IsClosed (cellUnionOne Y ι f U)) ∧
    (∀ i : ι, ∃ S : C(↥(cellInteriorOne Y ι f i), ↥cellInnerOne),
      (∀ x : ↥(cellInteriorOne Y ι f i),
        oneCellMap Y ι f i (S x) = (x : attachOneCells Y ι f)) ∧
      (∀ x : ↥cellInnerOne, S ⟨oneCellMap Y ι f i x, ⟨x, x.2, rfl⟩⟩ = x)) ∧
    IsClosed (oneCellCentresOne Y ι f) := by
  refine ⟨oneCellOldPart_eq_compl f, fun i j hij => disjoint_cellInteriorOne f hij,
    fun i => oneCellMap_injOn_inner f i,
    fun i => ⟨oneCellCentreOne_mem_cellInteriorOne f i,
      oneCellCentreOne_not_mem_oldPart f i⟩,
    fun U hU hUo => isOpen_cellUnionOne f hU hUo,
    fun U hU hUc => isClosed_cellUnionOne f hU hUc,
    fun i => exists_chart f i, ?_⟩
  rw [← cellUnionOne_centreSet f]
  exact isClosed_cellUnionOne f (fun x hx => by
      show ‖((x : cellD1) : ℝ)‖ < 1
      exact lt_of_le_of_lt hx zero_lt_one)
    (isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const)

end

end Work.Serre.SPC.One
