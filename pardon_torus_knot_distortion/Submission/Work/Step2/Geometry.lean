import Submission.Work.Step2.Defs

/-!
# The explicit geometry of the box double bubble

All the point-set facts about the vocabulary of `Defs.lean`, with no geometric input whatsoever:

* the box sphere is the union of the two caps and the gluing circle (`sphereSet_eq_union`), and the
  closed caps are the caps together with the gluing circle (`closedUpperCap_eq_union`);
* the two halves of the double bubble are exactly the boundaries of the two half-boxes
  (`halfAbove_eq_frontier_upperBody`), they cover the footprint (`footprint_eq_union`) and the traced
  regions of the double bubble are the two half-*regions* of the crux
  (`upperRegion_eq_carrier_upperBody`, `lowerRegion_eq_carrier_lowerBody`) — so "the region of the
  surface inside the half `H₁` of the double bubble" is literally `Work.BoxShrink.Core.upperRegion`;
* the box minus the cutting plane is the disjoint union of the two half-boxes
  (`PBox_sdiff_cutPlane`), whence `halves = boxRegion \ sliceRegion`;
* the explicit pinching family `pinchRegion` has the two endpoints the reduction needs
  (`pinchRegion_zero`, `pinchRegion_one`), is open in the surface throughout, is contained in the box
  region, shrinks monotonically, and changes by the explicit neck pieces
  (`pinchRegion_eq_union_neckPiece`), which are open in the surface exactly when the surface misses
  the critical level of the pinch (`isOpenInCarrier_neckPiece_of_forall_ne`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Step2

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Membership -/

@[simp] theorem mem_upperCap {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ upperCap s c σ u ↔ Submission.boxNorm c σ y = s ∧ c (σ 2) + u < y (σ 2) := Iff.rfl

@[simp] theorem mem_lowerCap {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ lowerCap s c σ u ↔ Submission.boxNorm c σ y = s ∧ y (σ 2) < c (σ 2) + u := Iff.rfl

@[simp] theorem mem_boundaryCircle {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ boundaryCircle s c σ u ↔ Submission.boxNorm c σ y = s ∧ y (σ 2) = c (σ 2) + u := Iff.rfl

@[simp] theorem mem_closedUpperCap {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ closedUpperCap s c σ u ↔ Submission.boxNorm c σ y = s ∧ c (σ 2) + u ≤ y (σ 2) := Iff.rfl

@[simp] theorem mem_closedLowerCap {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ closedLowerCap s c σ u ↔ Submission.boxNorm c σ y = s ∧ y (σ 2) ≤ c (σ 2) + u := Iff.rfl

@[simp] theorem mem_halfAbove {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ halfAbove s c σ u ↔
      (Submission.boxNorm c σ y = s ∧ c (σ 2) + u ≤ y (σ 2)) ∨
        (y ∈ Submission.PBox s c σ ∧ y (σ 2) = c (σ 2) + u) := Iff.rfl

@[simp] theorem mem_halfBelow {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ halfBelow s c σ u ↔
      (Submission.boxNorm c σ y = s ∧ y (σ 2) ≤ c (σ 2) + u) ∨
        (y ∈ Submission.PBox s c σ ∧ y (σ 2) = c (σ 2) + u) := Iff.rfl

@[simp] theorem mem_footprint {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ footprint s c σ u ↔
      Submission.boxNorm c σ y = s ∨
        (y ∈ Submission.PBox s c σ ∧ y (σ 2) = c (σ 2) + u) := Iff.rfl

@[simp] theorem mem_upperBody {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ upperBody s c σ u ↔ y ∈ Submission.PBox s c σ ∧ c (σ 2) + u < y (σ 2) := Iff.rfl

@[simp] theorem mem_lowerBody {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ lowerBody s c σ u ↔ y ∈ Submission.PBox s c σ ∧ y (σ 2) < c (σ 2) + u := Iff.rfl

@[simp] theorem mem_slab {c : R3} {σ : Equiv.Perm (Fin 3)} {u w : ℝ} {y : R3} :
    y ∈ slab c σ u w ↔ |y (σ 2) - (c (σ 2) + u)| < w := Iff.rfl

@[simp] theorem mem_band {c : R3} {σ : Equiv.Perm (Fin 3)} {u w w' : ℝ} {y : R3} :
    y ∈ band c σ u w w' ↔
      w < |y (σ 2) - (c (σ 2) + u)| ∧ |y (σ 2) - (c (σ 2) + u)| < w' := Iff.rfl

@[simp] theorem mem_closedBand {c : R3} {σ : Equiv.Perm (Fin 3)} {u w w' : ℝ} {y : R3} :
    y ∈ closedBand c σ u w w' ↔
      w < |y (σ 2) - (c (σ 2) + u)| ∧ |y (σ 2) - (c (σ 2) + u)| ≤ w' := Iff.rfl

/-! ## The decomposition of the box sphere -/

theorem upperCap_subset_sphereSet (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    upperCap s c σ u ⊆ Work.BoxShrink.Core.sphereSet c σ s := inter_subset_left

theorem lowerCap_subset_sphereSet (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    lowerCap s c σ u ⊆ Work.BoxShrink.Core.sphereSet c σ s := inter_subset_left

theorem cutDisc_subset_footprint (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.cutDisc s c σ u ⊆ footprint s c σ u := subset_union_right

theorem sphereSet_subset_footprint (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sphereSet c σ s ⊆ footprint s c σ u := subset_union_left

/-- **The box sphere splits into the two caps and the gluing circle.** -/
theorem sphereSet_eq_union (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sphereSet c σ s =
      upperCap s c σ u ∪ lowerCap s c σ u ∪ boundaryCircle s c σ u := by
  ext y
  simp only [mem_upperCap, mem_lowerCap, mem_boundaryCircle, Set.mem_union]
  constructor
  · intro h
    rcases lt_trichotomy (y (σ 2)) (c (σ 2) + u) with hlt | heq | hgt
    · exact Or.inl (Or.inr ⟨h, hlt⟩)
    · exact Or.inr ⟨h, heq⟩
    · exact Or.inl (Or.inl ⟨h, hgt⟩)
  · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h

/-- **The closed upper cap is the upper cap together with the gluing circle.** -/
theorem closedUpperCap_eq_union (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closedUpperCap s c σ u = upperCap s c σ u ∪ boundaryCircle s c σ u := by
  ext y
  simp only [mem_closedUpperCap, mem_upperCap, mem_boundaryCircle, Set.mem_union]
  constructor
  · rintro ⟨h, hle⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, heq.symm⟩
  · rintro (⟨h, hlt⟩ | ⟨h, heq⟩)
    · exact ⟨h, le_of_lt hlt⟩
    · exact ⟨h, le_of_eq heq.symm⟩

/-- **The closed upper and lower caps cover the sphere.** -/
theorem closedUpperCap_union_closedLowerCap (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closedUpperCap s c σ u ∪ closedLowerCap s c σ u = Work.BoxShrink.Core.sphereSet c σ s := by
  ext y
  simp only [mem_closedUpperCap, mem_closedLowerCap, Set.mem_union]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases le_total (y (σ 2)) (c (σ 2) + u) with hle | hle
    · exact Or.inr ⟨h, hle⟩
    · exact Or.inl ⟨h, hle⟩

/-- **The two halves of the double bubble cover the footprint.** -/
theorem footprint_eq_union (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    footprint s c σ u = halfAbove s c σ u ∪ halfBelow s c σ u := by
  rw [footprint, halfAbove, halfBelow, ← closedUpperCap_union_closedLowerCap]
  ext y
  simp only [Set.mem_union]
  tauto

/-! ## The two half-boxes and the two half-regions -/

theorem upperRegion_eq_carrier_upperBody (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.upperRegion P s c σ u = P.carrier ∩ upperBody s c σ u := by
  ext y
  simp only [upperBody, Work.BoxShrink.Core.mem_upperRegion, Set.mem_inter_iff]
  tauto

theorem lowerRegion_eq_carrier_lowerBody (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.lowerRegion P s c σ u = P.carrier ∩ lowerBody s c σ u := by
  ext y
  simp only [lowerBody, Work.BoxShrink.Core.mem_lowerRegion, Set.mem_inter_iff]
  tauto

theorem upperBody_subset_PBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    upperBody s c σ u ⊆ Submission.PBox s c σ := inter_subset_left

theorem lowerBody_subset_PBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    lowerBody s c σ u ⊆ Submission.PBox s c σ := inter_subset_left

theorem disjoint_upperBody_lowerBody (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Disjoint (upperBody s c σ u) (lowerBody s c σ u) :=
  (Work.BoxShrink.Core.disjoint_upperHalf_lowerHalf c σ u).mono inter_subset_right
    inter_subset_right

/-- **The box minus the cutting plane is the disjoint union of the two half-boxes.** -/
theorem PBox_sdiff_cutPlane (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Submission.PBox s c σ \ Work.BoxShrink.Core.cutPlane c σ u =
      upperBody s c σ u ∪ lowerBody s c σ u := by
  ext y
  simp only [Set.mem_sdiff, Set.mem_union, mem_upperBody, mem_lowerBody,
    Work.BoxShrink.Core.mem_cutPlane]
  constructor
  · rintro ⟨hbox, hne⟩
    rcases lt_trichotomy (y (σ 2)) (c (σ 2) + u) with h | h | h
    · exact Or.inr ⟨hbox, h⟩
    · exact absurd h hne
    · exact Or.inl ⟨hbox, h⟩
  · rintro (⟨hbox, h⟩ | ⟨hbox, h⟩)
    · exact ⟨hbox, ne_of_gt h⟩
    · exact ⟨hbox, ne_of_lt h⟩

/-- **The two half-regions are the region inside the box minus the slice.** -/
theorem halves_eq_boxRegion_sdiff_sliceRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.PinchCounted.PinchSweep.halves P s c σ u =
      Work.BoxShrink.Core.boxRegion P s c σ \ Work.BoxShrink.Core.sliceRegion P s c σ u := by
  ext y
  constructor
  · intro hy
    rw [Work.PinchCounted.PinchSweep.halves, Set.mem_union] at hy
    rcases hy with hu | hl
    · rw [Work.BoxShrink.Core.mem_upperRegion] at hu
      exact ⟨⟨hu.1, hu.2.1⟩, fun h => ne_of_gt hu.2.2
        ((Work.BoxShrink.Core.mem_sliceRegion (P := P) (s := s) (c := c) (σ := σ) (u := u)).mp h).2.2⟩
    · rw [Work.BoxShrink.Core.mem_lowerRegion] at hl
      exact ⟨⟨hl.1, hl.2.1⟩, fun h => ne_of_lt hl.2.2
        ((Work.BoxShrink.Core.mem_sliceRegion (P := P) (s := s) (c := c) (σ := σ) (u := u)).mp h).2.2⟩
  · rintro ⟨⟨hyc, hyb⟩, hne⟩
    rcases lt_trichotomy (y (σ 2)) (c (σ 2) + u) with h | h | h
    · exact Or.inr ⟨⟨hyc, hyb⟩, h⟩
    · exact absurd ((Work.BoxShrink.Core.mem_sliceRegion (P := P) (s := s) (c := c) (σ := σ) (u := u)).mpr ⟨hyc, hyb, h⟩) hne
    · exact Or.inl ⟨⟨hyc, hyb⟩, h⟩

/-- The two half-regions are the trace of the box minus the cutting plane. -/
theorem halves_eq_carrier_sdiff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.PinchCounted.PinchSweep.halves P s c σ u =
      P.carrier ∩ (Submission.PBox s c σ \ Work.BoxShrink.Core.cutPlane c σ u) := by
  rw [halves_eq_boxRegion_sdiff_sliceRegion]
  ext y
  simp only [Work.BoxShrink.Core.boxRegion, Work.BoxShrink.Core.sliceRegion, Set.mem_sdiff,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hyc, hyb⟩, hne⟩
    exact ⟨hyc, hyb, fun h => hne ⟨⟨hyc, hyb⟩, h⟩⟩
  · rintro ⟨hyc, hyb, hne⟩
    exact ⟨⟨hyc, hyb⟩, fun h => hne h.2⟩

/-! ## The explicit pinching family -/

theorem isOpen_pinchSolid (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (t : ℝ) :
    IsOpen (pinchSolid s c σ u t) := by
  have hcont : Continuous fun y : R3 => |y (σ 2) - (c (σ 2) + u)| :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).sub continuous_const).abs
  exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
    (isOpen_lt continuous_const hcont)

theorem isOpenInCarrier_pinchRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (t : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier P (pinchRegion P s c σ u t) :=
  Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := P) (isOpen_pinchSolid s c σ u t)

theorem pinchSolid_zero (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    pinchSolid s c σ u 0 = Submission.PBox s c σ := by
  ext y
  simp only [pinchSolid, Set.mem_inter_iff, Set.mem_setOf_eq, zero_sub]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have := abs_nonneg (y (σ 2) - (c (σ 2) + u))
    linarith

theorem pinchSolid_one (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    pinchSolid s c σ u 1 =
      Submission.PBox s c σ \ Work.BoxShrink.Core.cutPlane c σ u := by
  rw [pinchSolid]
  ext y
  simp only [sub_self, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_sdiff,
    Work.BoxShrink.Core.mem_cutPlane]
  constructor
  · rintro ⟨hbox, hpos⟩
    refine ⟨hbox, fun hz => ?_⟩
    rw [hz] at hpos
    simp at hpos
  · rintro ⟨hbox, hne⟩
    exact ⟨hbox, abs_pos.mpr (sub_ne_zero.mpr hne)⟩

/-- **The pinching family starts at the region inside the box.** -/
@[simp] theorem pinchRegion_zero (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    pinchRegion P s c σ u 0 = Work.BoxShrink.Core.boxRegion P s c σ := by
  rw [pinchRegion, pinchSolid_zero]
  rfl

/-- **The pinching family ends at the two half-regions.** -/
@[simp] theorem pinchRegion_one (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    pinchRegion P s c σ u 1 = Work.PinchCounted.PinchSweep.halves P s c σ u := by
  rw [pinchRegion, pinchSolid_one, halves_eq_carrier_sdiff]

theorem pinchRegion_subset_boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (t : ℝ) :
    pinchRegion P s c σ u t ⊆ Work.BoxShrink.Core.boxRegion P s c σ :=
  fun _ hy => ⟨hy.1, hy.2.1⟩

/-- **The region of the pinch shrinks monotonically** with the parameter. -/
theorem pinchRegion_mono (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) {t r : ℝ} (h : t ≤ r) :
    pinchRegion P s c σ u r ⊆ pinchRegion P s c σ u t :=
  fun _ hy => ⟨hy.1, hy.2.1, lt_of_le_of_lt (by linarith : t - 1 ≤ r - 1) hy.2.2⟩

theorem pinchSolid_antitone {t r : ℝ} (h : t ≤ r) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : pinchSolid s c σ u r ⊆ pinchSolid s c σ u t :=
  fun _ hy => ⟨hy.1, lt_of_le_of_lt (by linarith : t - 1 ≤ r - 1) hy.2⟩

/-- **The pinching family is constant before the pinch.**  For every parameter `t < 1` nothing is
removed from the box, and the region is the region inside the box. -/
theorem pinchRegion_eq_boxRegion_of_lt_one (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) {t : ℝ} (ht : t < 1) :
    pinchRegion P s c σ u t = Work.BoxShrink.Core.boxRegion P s c σ := by
  rw [pinchRegion]
  congr 1
  ext y
  simp only [pinchSolid, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have := abs_nonneg (y (σ 2) - (c (σ 2) + u))
    linarith

/-- **After the pinch the region is contained in the two half-regions.**  For `t ≥ 1` the removed
slab already contains the cutting plane, so nothing of the slice survives. -/
theorem pinchRegion_subset_halves_of_one_le (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    pinchRegion P s c σ u t ⊆ Work.PinchCounted.PinchSweep.halves P s c σ u := by
  intro y hy
  rw [halves_eq_carrier_sdiff]
  refine ⟨hy.1, hy.2.1, ?_⟩
  intro hz
  have hz' : y (σ 2) = c (σ 2) + u := (Work.BoxShrink.Core.mem_cutPlane).mp hz
  have h2 := hy.2.2
  simp only [Set.mem_setOf_eq] at h2
  rw [hz', sub_self, abs_zero] at h2
  linarith

/-- **The explicit decomposition of the change of the pinching region.**  The region of the pinch at
the parameter `t` is the region at the later parameter `r ≥ t` together with the neck piece: the
piece of the surface through which the `2`-surgery passes between the two parameters. -/
theorem pinchRegion_eq_union_neckPiece (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) {t r : ℝ} (h : t ≤ r) :
    pinchRegion P s c σ u t =
      pinchRegion P s c σ u r ∪ neckPiece P s c σ u t r := by
  have hsub : pinchRegion P s c σ u r ⊆ pinchRegion P s c σ u t :=
    pinchRegion_mono P s c σ u h
  have hdiff : pinchRegion P s c σ u t \ pinchRegion P s c σ u r = neckPiece P s c σ u t r := by
    rw [neckPiece, pinchRegion, pinchRegion]
    ext y
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [← hdiff, Set.union_comm, Set.sdiff_union_of_subset hsub]

/-- **The neck piece is the trace of the closed band between the two slabs.** -/
theorem neckPiece_eq_carrier_closedBand (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (t r : ℝ) :
    neckPiece P s c σ u t r =
      P.carrier ∩ (Submission.PBox s c σ ∩ closedBand c σ u (t - 1) (r - 1)) := by
  ext y
  simp only [neckPiece, Set.mem_inter_iff, Set.mem_sdiff, pinchSolid, Set.mem_setOf_eq,
    mem_closedBand]
  constructor
  · rintro ⟨hyc, ⟨hyb, hlt⟩, hnr⟩
    refine ⟨hyc, hyb, hlt, ?_⟩
    by_contra hcon
    exact hnr ⟨hyb, not_le.mp hcon⟩
  · rintro ⟨hyc, hyb, hlt, hle⟩
    exact ⟨hyc, ⟨hyb, hlt⟩, fun h => absurd h.2 (not_lt.mpr hle)⟩

/-- **The neck piece is the trace of the open band as soon as the surface misses the critical level
`{|y (σ 2) - (c (σ 2) + u)| = r - 1}` of the pinch.**  This is exactly the general-position
condition on the cutting plane which the local model of the `2`-surgery needs — and it is *not*
available at every level, see the README. -/
theorem neckPiece_eq_carrier_band_of_forall_ne (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (t r : ℝ)
    (hgen : ∀ y : R3, y ∈ P.carrier → y ∈ Submission.PBox s c σ →
      |y (σ 2) - (c (σ 2) + u)| ≠ r - 1) :
    neckPiece P s c σ u t r =
      P.carrier ∩ (Submission.PBox s c σ ∩ band c σ u (t - 1) (r - 1)) := by
  rw [neckPiece_eq_carrier_closedBand]
  ext y
  simp only [Set.mem_inter_iff, mem_closedBand, mem_band]
  constructor
  · rintro ⟨hyc, hyb, hlt, hle⟩
    exact ⟨hyc, hyb, hlt, lt_of_le_of_ne hle (hgen y hyc hyb)⟩
  · rintro ⟨hyc, hyb, hlt, hlt'⟩
    exact ⟨hyc, hyb, hlt, le_of_lt hlt'⟩

/-- The neck piece is open in the surface as soon as the surface misses the critical level. -/
theorem isOpenInCarrier_neckPiece_of_forall_ne (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (t r : ℝ)
    (hgen : ∀ y : R3, y ∈ P.carrier → y ∈ Submission.PBox s c σ →
      |y (σ 2) - (c (σ 2) + u)| ≠ r - 1) :
    Work.SurgeryInvariance.IsOpenInCarrier P (neckPiece P s c σ u t r) := by
  rw [neckPiece_eq_carrier_band_of_forall_ne P s c σ u t r hgen]
  refine Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := P) ?_
  have hcont : Continuous fun y : R3 => |y (σ 2) - (c (σ 2) + u)| :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).sub continuous_const).abs
  exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
    (hcont.isOpen_preimage _ isOpen_Ioo)

theorem neckPiece_subset_PBox (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (t r : ℝ) :
    neckPiece P s c σ u t r ⊆ Submission.PBox s c σ := by
  intro y hy
  simp only [neckPiece, pinchSolid, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq] at hy
  exact hy.2.1.1

theorem neckPiece_subset_boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (t r : ℝ) :
    neckPiece P s c σ u t r ⊆ Work.BoxShrink.Core.boxRegion P s c σ :=
  fun _ hy => ⟨hy.1, neckPiece_subset_PBox P s c σ u t r hy⟩

/-- **The total change of the pinching family is exactly the slice.**  This is the *obstruction* to
reading the pinching family as a family of local moves of the library's kind: the slice is closed in
the surface, but not open in it, while every local model of a `2`-surgery
(`Work.SurgeryInvariance.SurgeryStepZero`, `Work.PinchCounted.CountedStep`) requires the changed
piece to be open in the surface. -/
theorem neckPiece_zero_one (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    neckPiece P s c σ u 0 1 = Work.BoxShrink.Core.sliceRegion P s c σ u := by
  rw [neckPiece, pinchSolid_zero, pinchSolid_one]
  ext y
  constructor
  · rintro ⟨hyc, hyb, hne⟩
    exact (Work.BoxShrink.Core.mem_sliceRegion (P := P) (s := s) (c := c) (σ := σ) (u := u)).mpr
      ⟨hyc, hyb, by
        by_contra hc
        exact hne ⟨hyb, hc⟩⟩
  · rintro hy
    obtain ⟨hyc, hyb, hcut⟩ := (Work.BoxShrink.Core.mem_sliceRegion (P := P) (s := s) (c := c) (σ := σ) (u := u)).mp hy
    exact ⟨hyc, hyb, fun h => h.2 hcut⟩

end

end Work.Step2
