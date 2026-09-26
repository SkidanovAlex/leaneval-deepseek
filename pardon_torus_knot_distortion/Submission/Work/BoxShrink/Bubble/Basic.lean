import Submission.Work.BoxShrink.Bubble.Defs

/-!
# The elementary geometry of the double bubble for the box/plane configuration

The easy but indispensable facts about the vocabulary of `Work.BoxShrink.Bubble.Defs`:

* the exterior of the box is the complement of the region inside the sphere, and the slab is open
  in `ℝ³`;
* the exterior collar is contained in the exterior of the box and in the slab, and is monotone in
  the half-width `δ`;
* the pinched region is the union of the region inside the sphere and the exterior collar, and the
  union of the two half-regions together with the neck (`neck = pinchedRegion ∖ (upper ∪ lower)`);
* the region inside the sphere is `pinchedRegion ∖ exteriorCollar`, and removing the exterior
  collar from the pinched region returns the region inside the sphere;
* `upperRegion ∪ lowerRegion ⊆ boxRegion ⊆ pinchedRegion`.

Nothing here uses any hypothesis: these are the set-theoretic identities which make the three-point
sweep of `Work.BoxShrink.Bubble.bubbleSweep_of_outsidePiece` work.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The exterior of the box, the slab, and the collar -/

/-- The region inside the box and the exterior of the box partition the surface. -/
theorem boxRegion_union_outsideRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Work.BoxShrink.Core.boxRegion P s c σ ∪ outsideRegion P s c σ = P.carrier := by
  ext y
  simp only [Set.mem_union, Work.BoxShrink.Core.mem_boxRegion, mem_outsideRegion]
  tauto

/-- The region inside the box and the exterior of the box are disjoint. -/
theorem disjoint_boxRegion_outsideRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Disjoint (Work.BoxShrink.Core.boxRegion P s c σ) (outsideRegion P s c σ) := by
  rw [Set.disjoint_left]
  rintro y ⟨-, hy⟩ ⟨-, hy'⟩
  exact hy' hy

/-- The slab is open in `ℝ³`. -/
theorem isOpen_slab (c : R3) (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    IsOpen (slab c σ u δ) :=
  isOpen_lt (continuous_abs.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).sub continuous_const))
    continuous_const

/-- The trace of the slab on the surface is open in the surface. -/
theorem isOpenInCarrier_carrier_inter_slab (P : Work.CoreTopology.ParamTorus) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier P (P.carrier ∩ slab c σ u δ) :=
  Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := P) (isOpen_slab c σ u δ)

theorem exteriorCollar_subset_outsideRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    exteriorCollar P s c σ u δ ⊆ outsideRegion P s c σ :=
  Set.inter_subset_left

theorem exteriorCollar_subset_slab (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    exteriorCollar P s c σ u δ ⊆ slab c σ u δ :=
  Set.inter_subset_right

theorem exteriorCollar_subset_carrier (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    exteriorCollar P s c σ u δ ⊆ P.carrier :=
  fun _ h => h.1.1

/-- The exterior collar shrinks with the half-width. -/
theorem exteriorCollar_mono (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) {δ δ' : ℝ} (h : δ ≤ δ') :
    exteriorCollar P s c σ u δ ⊆ exteriorCollar P s c σ u δ' := by
  rintro y ⟨hy, hys⟩
  exact ⟨hy, lt_of_lt_of_le hys h⟩

/-! ## The pinched region and the neck -/

theorem boxRegion_subset_pinchedRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    Work.BoxShrink.Core.boxRegion P s c σ ⊆ pinchedRegion P s c σ u δ :=
  Set.subset_union_left

theorem exteriorCollar_subset_pinchedRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    exteriorCollar P s c σ u δ ⊆ pinchedRegion P s c σ u δ :=
  Set.subset_union_right

theorem sliceRegion_subset_neck (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ neck P s c σ u δ :=
  Set.subset_union_left

theorem exteriorCollar_subset_neck (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    exteriorCollar P s c σ u δ ⊆ neck P s c σ u δ :=
  Set.subset_union_right

/-- The two half-regions lie inside the pinched region. -/
theorem upper_union_lower_subset_pinchedRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u ⊆
      pinchedRegion P s c σ u δ :=
  fun y hy => boxRegion_subset_pinchedRegion P s c σ u δ
    ((Work.BoxShrink.Core.boxRegion_eq_union P s c σ u) ▸ Or.inl hy)

/-- **The pinched region is the two halves together with the neck.** -/
theorem pinchedRegion_eq_union_neck (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    pinchedRegion P s c σ u δ =
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ∪ neck P s c σ u δ := by
  rw [pinchedRegion, neck, Work.BoxShrink.Core.boxRegion_eq_union]
  ext y
  simp only [Set.mem_union]
  tauto

/-- The exterior collar avoids the two half-regions (it lies outside the box). -/
theorem disjoint_exteriorCollar_upper_union_lower (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    Disjoint (exteriorCollar P s c σ u δ)
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  rw [Set.disjoint_left]
  rintro y hy (hy' | hy')
  · exact hy.1.2 hy'.1.2
  · exact hy.1.2 hy'.1.2

/-- The slice avoids the two half-regions (it lies in the cutting plane). -/
theorem disjoint_sliceRegion_upper_union_lower (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Disjoint (Work.BoxShrink.Core.sliceRegion P s c σ u)
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  rw [Set.disjoint_left]
  rintro y hy (hy' | hy')
  · rw [Work.BoxShrink.Core.mem_sliceRegion] at hy
    rw [Work.BoxShrink.Core.mem_upperRegion] at hy'
    exact absurd hy'.2.2 (by rw [hy.2.2]; exact lt_irrefl _)
  · rw [Work.BoxShrink.Core.mem_sliceRegion] at hy
    rw [Work.BoxShrink.Core.mem_lowerRegion] at hy'
    exact absurd hy'.2.2 (by rw [hy.2.2]; exact lt_irrefl _)

/-- **The neck is the pinched region with the two half-regions removed.** -/
theorem neck_eq_pinchedRegion_diff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    neck P s c σ u δ = pinchedRegion P s c σ u δ \
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  rw [pinchedRegion_eq_union_neck]
  ext y
  constructor
  · intro hy
    refine ⟨Or.inr hy, ?_⟩
    rcases hy with hy | hy
    · exact fun hc => (Set.disjoint_left.mp
        (disjoint_sliceRegion_upper_union_lower P s c σ u) hy) hc
    · exact fun hc => (Set.disjoint_left.mp
        (disjoint_exteriorCollar_upper_union_lower P s c σ u δ) hy) hc
  · rintro ⟨hy, hyc⟩
    rcases hy with h | h
    · exact absurd h hyc
    · exact h

/-- **Removing the exterior collar from the pinched region returns the region inside the box.** -/
theorem pinchedRegion_diff_exteriorCollar (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    pinchedRegion P s c σ u δ \ exteriorCollar P s c σ u δ =
      Work.BoxShrink.Core.boxRegion P s c σ := by
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    rcases hy with h | h
    · exact h
    · exact absurd h hyc
  · intro hy
    exact ⟨Or.inl hy, fun hyc => (disjoint_boxRegion_outsideRegion P s c σ).le_bot
      ⟨hy, exteriorCollar_subset_outsideRegion P s c σ u δ hyc⟩⟩

/-- The pinched region is the union of the region inside the box with the exterior collar. -/
theorem pinchedRegion_eq_boxRegion_union (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    pinchedRegion P s c σ u δ =
      Work.BoxShrink.Core.boxRegion P s c σ ∪ exteriorCollar P s c σ u δ := rfl

end

end Work.BoxShrink.Bubble
