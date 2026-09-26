import Submission.Work.PinchFamily.Defs

/-!
# The pinching family from a collar

This module builds the family of `Work.PinchCounted.CountedPinch` out of a **collar**
`Work.PinchFamily.IsPinchCollar` whose winding span vanishes: the piece of the surface through which
Pardon's pinching sphere passes.

The family has three pieces, and it is exactly the discrete form of Pardon's pinch read through the
collar decomposition of the box region:

| parameter | region | what happened |
|---|---|---|
| `t < 1/2` | `boxRegion = (boxRegion ∖ Z) ∪ Z` | the pinching sphere has not yet eaten into the box region |
| `1/2 ≤ t < 3/4` | `boxRegion ∖ Z` | the collar `Z` (which contains the slice trace) is removed in the `2`-surgery |
| `t ≥ 3/4` | `halves = (boxRegion ∖ Z) ∪ (halves ∩ Z)` | the collar is pushed into the two half-regions, where it contributes nothing |

Both steps are `Work.SurgeryInvariance.SurgeryStepZero`s, hence `CountedStep`s: the changed piece is
`Z` (whose winding span vanishes) in the first step and `halves ∩ Z` (a subset of `Z`) in the
second.  No loop of the surface can be pinned to a piece of vanishing winding span, so the winding
span — and with it Pardon's invariant — is transported across the pinch.

This is the *geometric* form of Pardon's Step 2: the substance is the existence of the collar
`Z ⊇ sliceRegion` of vanishing span inside the box region, i.e.
`Work.PinchFamily.SpanCollarBody`.  (In the cruder form of `Family.lean` the whole content is
compressed into the push-off; here it is visible as the piece through which the pinch passes, which
is Pardon's own description.)
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchFamily

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The three-piece family -/

/-- **The pinching family of a collar** `Z`: the region inside the box before the pinch, the box
region with the collar removed in the middle of the pinch, and the two half-regions at the end. -/
def collarRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (Z : Set R3) : ℝ → Set R3 :=
  fun t => if t < 1 / 2 then box P s c σ
    else if t < 3 / 4 then box P s c σ \ Z else halves P s c σ u

theorem collarRegion_of_lt {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    {t : ℝ} (ht : t < 1 / 2) : collarRegion P s c σ u Z t = box P s c σ := by
  rw [collarRegion, if_pos ht]

theorem collarRegion_of_mem {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    {t : ℝ} (h₁ : ¬ t < 1 / 2) (h₂ : t < 3 / 4) :
    collarRegion P s c σ u Z t = box P s c σ \ Z := by
  rw [collarRegion, if_neg h₁, if_pos h₂]

theorem collarRegion_of_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    {t : ℝ} (h₁ : ¬ t < 1 / 2) (h₂ : ¬ t < 3 / 4) :
    collarRegion P s c σ u Z t = halves P s c σ u := by
  rw [collarRegion, if_neg h₁, if_neg h₂]

/-- **The family starts at the region inside the box.** -/
@[simp] theorem collarRegion_zero {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {Z : Set R3} : collarRegion P s c σ u Z 0 = box P s c σ :=
  collarRegion_of_lt (by norm_num)

/-- **The family ends at the two half-regions.** -/
@[simp] theorem collarRegion_one {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {Z : Set R3} : collarRegion P s c σ u Z 1 = halves P s c σ u :=
  collarRegion_of_le (by norm_num) (by norm_num)

/-- The family takes one of the three values of the collar decomposition. -/
theorem collarRegion_cases {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (t : ℝ) : collarRegion P s c σ u Z t = box P s c σ ∨
      collarRegion P s c σ u Z t = box P s c σ \ Z ∨
      collarRegion P s c σ u Z t = halves P s c σ u := by
  by_cases h₁ : t < 1 / 2
  · exact Or.inl (collarRegion_of_lt h₁)
  · by_cases h₂ : t < 3 / 4
    · exact Or.inr (Or.inl (collarRegion_of_mem h₁ h₂))
    · exact Or.inr (Or.inr (collarRegion_of_le h₁ h₂))

/-! ## The two steps of the collar decomposition -/

/-- **The two half-regions are the complement of the collar together with the part of the collar
lying in them.** -/
theorem halves_eq_sdiff_union {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z) :
    halves P s c σ u = (box P s c σ \ Z) ∪ (halves P s c σ u ∩ Z) := by
  apply le_antisymm
  · intro y hy
    have hybox : y ∈ box P s c σ :=
      Set.union_subset (Work.BoxShrink.Core.upperRegion_subset P s c σ u)
        (Work.BoxShrink.Core.lowerRegion_subset P s c σ u) hy
    by_cases hyZ : y ∈ Z
    · exact Set.mem_union_right _ ⟨hy, hyZ⟩
    · exact Set.mem_union_left _ ⟨hybox, hyZ⟩
  · exact Set.union_subset (hZ.sdiff_subset_halves) Set.inter_subset_left

theorem disjoint_sdiff_inter {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z) :
    Disjoint (box P s c σ \ Z) (halves P s c σ u ∩ Z) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hxZ⟩ ⟨-, hxZ'⟩
  exact hxZ hxZ'

/-- **The first step of the pinch: the collar is removed** (in the geometric local model, without
the `CountedStep` wrapper). -/
theorem surgeryStepZero_box_sdiff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.SurgeryInvariance.SurgeryStepZero P (box P s c σ) (box P s c σ \ Z) :=
  ⟨Z, hspan, Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ, hZ.open_sdiff,
    hZ.isOpen, Or.inl ⟨hZ.box_eq_union, hZ.disjoint_sdiff⟩⟩

/-- **The second step of the pinch: the collar is pushed into the two half-regions** (in the
geometric local model, without the `CountedStep` wrapper). -/
theorem surgeryStepZero_sdiff_halves {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {Z : Set R3} (hZ : IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.SurgeryInvariance.SurgeryStepZero P (box P s c σ \ Z) (halves P s c σ u) :=
  ⟨halves P s c σ u ∩ Z,
    le_antisymm ((Work.SurgeryInvariance.WindingSpan_mono P Set.inter_subset_right).trans_eq hspan)
      bot_le,
    hZ.open_sdiff, Work.PinchCounted.PinchSweep.isOpenInCarrier_halves P s c σ u,
    Work.SurgeryInvariance.isOpenInCarrier_inter (P := P)
      (Work.PinchCounted.PinchSweep.isOpenInCarrier_halves P s c σ u) hZ.isOpen,
    Or.inr ⟨halves_eq_sdiff_union (P := P) hZ, disjoint_sdiff_inter (P := P) hZ⟩⟩

/-- **The first step of the pinch: the collar is removed.** -/
theorem countedStep_box_sdiff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (β : Work.CoreTopology.ClosedCurve P) :
    Work.PinchCounted.CountedStep P β (box P s c σ) (box P s c σ \ Z) :=
  Work.PinchCounted.CountedStep.of_stepZero (surgeryStepZero_box_sdiff hZ hspan)

/-- **The second step of the pinch: the collar is pushed into the two half-regions.** -/
theorem countedStep_sdiff_halves {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (β : Work.CoreTopology.ClosedCurve P) :
    Work.PinchCounted.CountedStep P β (box P s c σ \ Z) (halves P s c σ u) :=
  Work.PinchCounted.CountedStep.of_stepZero (surgeryStepZero_sdiff_halves hZ hspan)

end

end Work.PinchFamily
