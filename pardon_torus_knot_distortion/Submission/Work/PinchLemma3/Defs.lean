import Submission.Work.BoxShrink.Pinch.All
import Submission.Work.BoxShrink.PinchOff.All

/-!
# `Work.PinchLemma3` — the walls of the slice: vocabulary

This module sets up the vocabulary of the chapter:

* `height` — the affine plane coordinate `y (σ 2) - (c (σ 2) + u)` of the cutting plane;
* `closedUpper`, `closedLower` — the two **closed** halves `boxRegion ∩ {0 ≤ height}` and
  `boxRegion ∩ {height ≤ 0}`, which carry the boundary of the box (this is the distinction that the
  parent chapter's trap about the *closed* slice turns on: the closed half is its open half
  together with the slice, and the slice is a closed subset of the box region whose complement is
  open);
* `halfRegions` — the two **open** halves `upperRegion ∪ lowerRegion`, the union the pinch consumes;
* `closedBoxRegion` — the trace of the closed box on the surface `P.carrier ∩ {boxNorm ≤ s}`, where
  the walls of the slice live;
* `outerRegion` — the **caps** of the box, `P.carrier ∖ boxRegion`.

Proved here (the API the rest of the chapter and any caller needs): the closed halves cover the
region inside the box and meet exactly in the slice; each closed half is its open half together with
the slice; the caps and the region inside the box partition the surface and are disjoint; the slice
lies in the trace of the cutting plane and is exactly the part of that trace inside the box.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchLemma3

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The height, the caps and the two closed halves -/

/-- **The height (plane coordinate) function** of the cutting plane `{y | y (σ 2) = c (σ 2) + u}`:
the affine function whose zero set is the cutting plane and whose sign tells the sides apart. -/
def height (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (y : R3) : ℝ := y (σ 2) - (c (σ 2) + u)

@[simp] theorem height_apply (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (y : R3) :
    height c σ u y = y (σ 2) - (c (σ 2) + u) := rfl

theorem height_lt_zero_iff {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    height c σ u y < 0 ↔ y (σ 2) < c (σ 2) + u := by
  simp [height]

theorem height_gt_zero_iff {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    0 < height c σ u y ↔ c (σ 2) + u < y (σ 2) := by
  simp [height]

theorem height_eq_zero_iff {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    height c σ u y = 0 ↔ y (σ 2) = c (σ 2) + u := by
  simp only [height, sub_eq_zero]

/-- **The closed upper half-region**: the part of the region inside the box on the upper side of
the cutting plane. -/
def closedUpper (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.boxRegion P s c σ ∩ {y : R3 | 0 ≤ height c σ u y}

/-- **The closed lower half-region**. -/
def closedLower (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.boxRegion P s c σ ∩ {y : R3 | height c σ u y ≤ 0}

/-- **The caps of the box**: the pieces of the surface outside the box. -/
def outerRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  {y : R3 | y ∈ P.carrier ∧ ¬ (y ∈ Submission.PBox s c σ)}

/-- **The closed box region**: the trace of the closed box on the surface.  This is the closure of
`boxRegion` in the carrier, and it is the region in which the *walls* of the slice live: the slice
itself is contained in the open box region, but its components run up to the boundary of the box. -/
def closedBoxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  P.carrier ∩ {y : R3 | Submission.boxNorm c σ y ≤ s}

@[simp] theorem mem_closedBoxRegion {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3} :
    y ∈ closedBoxRegion P s c σ ↔ y ∈ P.carrier ∧ Submission.boxNorm c σ y ≤ s := Iff.rfl

/-- The region inside the box is contained in the closed box region. -/
theorem boxRegion_subset_closedBoxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Work.BoxShrink.Core.boxRegion P s c σ ⊆ closedBoxRegion P s c σ :=
  fun y hy => ⟨hy.1,
    le_of_lt ((Submission.mem_PBox_iff s c σ y).mp hy.2)⟩

/-- The two half-regions together, in the form the pinch consumes them. -/
def halfRegions (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u

@[simp] theorem mem_closedUpper {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ closedUpper P s c σ u ↔
      y ∈ Work.BoxShrink.Core.boxRegion P s c σ ∧ 0 ≤ height c σ u y := by
  simp only [closedUpper, Set.mem_inter_iff, Set.mem_ofPred_eq]

@[simp] theorem mem_closedLower {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ closedLower P s c σ u ↔
      y ∈ Work.BoxShrink.Core.boxRegion P s c σ ∧ height c σ u y ≤ 0 := by
  simp only [closedLower, Set.mem_inter_iff, Set.mem_ofPred_eq]

@[simp] theorem mem_outerRegion {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3} :
    y ∈ outerRegion P s c σ ↔ y ∈ P.carrier ∧ ¬ (y ∈ Submission.PBox s c σ) := Iff.rfl

@[simp] theorem mem_halfRegions {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ halfRegions P s c σ u ↔
      y ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∨
        y ∈ Work.BoxShrink.Core.lowerRegion P s c σ u := Iff.rfl

/-! ## The elementary API -/

/-- The closed halves cover the region inside the box. -/
theorem boxRegion_eq_closedUpper_union_closedLower (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.boxRegion P s c σ = closedUpper P s c σ u ∪ closedLower P s c σ u := by
  ext y
  constructor
  · intro hy
    rcases le_total 0 (height c σ u y) with h | h
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩
  · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy

/-- The closed upper half is the upper region together with the slice. -/
theorem closedUpper_eq_union (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closedUpper P s c σ u =
      Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.sliceRegion P s c σ u := by
  ext y
  simp only [Set.mem_union, mem_closedUpper, Work.BoxShrink.Core.mem_upperRegion,
    Work.BoxShrink.Core.mem_sliceRegion, height]
  constructor
  · rintro ⟨⟨hyc, hyb⟩, h⟩
    rcases lt_or_eq_of_le h with h' | h'
    · exact Or.inl ⟨hyc, hyb, by linarith⟩
    · exact Or.inr ⟨hyc, hyb, by linarith⟩
  · rintro (⟨hyc, hyb, h⟩ | ⟨hyc, hyb, h⟩)
    · exact ⟨⟨hyc, hyb⟩, by linarith⟩
    · exact ⟨⟨hyc, hyb⟩, by linarith⟩

/-- The closed lower half is the lower region together with the slice. -/
theorem closedLower_eq_union (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closedLower P s c σ u =
      Work.BoxShrink.Core.lowerRegion P s c σ u ∪ Work.BoxShrink.Core.sliceRegion P s c σ u := by
  ext y
  simp only [Set.mem_union, mem_closedLower, Work.BoxShrink.Core.mem_lowerRegion,
    Work.BoxShrink.Core.mem_sliceRegion, height]
  constructor
  · rintro ⟨⟨hyc, hyb⟩, h⟩
    rcases lt_or_eq_of_le h with h' | h'
    · exact Or.inl ⟨hyc, hyb, by linarith⟩
    · exact Or.inr ⟨hyc, hyb, by linarith⟩
  · rintro (⟨hyc, hyb, h⟩ | ⟨hyc, hyb, h⟩)
    · exact ⟨⟨hyc, hyb⟩, by linarith⟩
    · exact ⟨⟨hyc, hyb⟩, by linarith⟩

/-- The two closed halves meet in the slice. -/
theorem closedUpper_inter_closedLower (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closedUpper P s c σ u ∩ closedLower P s c σ u = Work.BoxShrink.Core.sliceRegion P s c σ u := by
  ext y
  rw [Set.mem_inter_iff, mem_closedUpper, mem_closedLower,
    Work.BoxShrink.Core.mem_sliceRegion]
  constructor
  · rintro ⟨⟨hy, h1⟩, ⟨-, h2⟩⟩
    have h0 : height c σ u y = 0 := le_antisymm h2 h1
    exact ⟨hy.1, hy.2, (height_eq_zero_iff (c := c) (σ := σ) (u := u) (y := y)).mp h0⟩
  · rintro ⟨hyc, hyb, hz⟩
    have h0 : height c σ u y = 0 :=
      (height_eq_zero_iff (c := c) (σ := σ) (u := u) (y := y)).mpr hz
    exact ⟨⟨⟨hyc, hyb⟩, le_of_eq h0.symm⟩, ⟨hyc, hyb⟩, le_of_eq h0⟩

theorem closedUpper_subset_boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closedUpper P s c σ u ⊆ Work.BoxShrink.Core.boxRegion P s c σ :=
  fun _ h => (mem_closedUpper (P := P)).mp h |>.1

theorem closedLower_subset_boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closedLower P s c σ u ⊆ Work.BoxShrink.Core.boxRegion P s c σ :=
  fun _ h => (mem_closedLower (P := P)).mp h |>.1

theorem upperRegion_subset_closedUpper (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.upperRegion P s c σ u ⊆ closedUpper P s c σ u := by
  rw [closedUpper_eq_union]; exact subset_union_left

theorem lowerRegion_subset_closedLower (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ closedLower P s c σ u := by
  rw [closedLower_eq_union]; exact subset_union_left

theorem sliceRegion_subset_closedUpper (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ closedUpper P s c σ u := by
  rw [closedUpper_eq_union]; exact subset_union_right

theorem sliceRegion_subset_closedLower (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ closedLower P s c σ u := by
  rw [closedLower_eq_union]; exact subset_union_right

theorem halfRegions_subset_boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    halfRegions P s c σ u ⊆ Work.BoxShrink.Core.boxRegion P s c σ :=
  Work.BoxShrink.Bubble.upper_union_lower_subset_boxRegion P s c σ u

/-- The region inside the box and the caps partition the surface. -/
theorem boxRegion_union_outerRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Work.BoxShrink.Core.boxRegion P s c σ ∪ outerRegion P s c σ = P.carrier := by
  ext y
  rw [Set.mem_union, mem_outerRegion]
  constructor
  · rintro (h | ⟨h1, -⟩)
    · exact h.1
    · exact h1
  · intro hy
    by_cases h : y ∈ Submission.PBox s c σ
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩

theorem disjoint_boxRegion_outerRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Disjoint (Work.BoxShrink.Core.boxRegion P s c σ) (outerRegion P s c σ) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  exact ((mem_outerRegion (P := P)).mp hy').2 hy.2

/-- The slice lies in the trace of the cutting plane. -/
theorem sliceRegion_subset_planeTrace (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ Work.BoxShrink.Pinch.planeTrace P c σ u :=
  fun _ hy => ⟨((Work.BoxShrink.Core.mem_sliceRegion (P := P)).mp hy).1,
    ((Work.BoxShrink.Core.mem_sliceRegion (P := P)).mp hy).2.2⟩

/-- The slice is the part of the trace of the cutting plane inside the box. -/
theorem sliceRegion_eq_planeTrace_inter_boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sliceRegion P s c σ u =
      Work.BoxShrink.Pinch.planeTrace P c σ u ∩ Work.BoxShrink.Core.boxRegion P s c σ := by
  ext y
  rw [Set.mem_inter_iff, Work.BoxShrink.Core.mem_sliceRegion, Work.BoxShrink.Pinch.mem_planeTrace,
    Work.BoxShrink.Core.mem_boxRegion]
  tauto

end

end Work.PinchLemma3
