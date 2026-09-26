import Submission.Work.PinchCounted.Span
import Submission.Work.BoxShrink.PinchOff.Laminar

/-!
# Instances of the residual: non-vacuity

The residual `Work.PinchCounted.CountedPinchSweep` is an *existence* statement.  This module proves
that its geometric core `Work.PinchCounted.PinchSweep` is inhabited in every configuration in which
the pinch is *trivial*:

* `pinchSweepOfRegionEquivalent` — the general trivial case: if the loop content of the two half
  regions is the same as that of the box region (`Work.SurgeryInvariance.RegionEquivalent`), the
  pinch is the two-region family (box region before the pinching parameter, the two halves after it)
  with a trivial piece `Z = ∅`.  This is Pardon's pinch in the situation where no loop is lost;
* `pinchSweepOfHalvesEqBoxRegion` — if the box region already *is* the union of the two halves;
* `pinchSweepOfOpenSlice` — if the slice is open in the surface and carries no essential loop, the
  constant family with `Z = sliceRegion` is Pardon's pinch.

Consequently Pardon's Lemma 3 conclusion holds in all those configurations without any appeal to
the counting (`bubbleHalf_of_pinchSweep`), and the configurations covered by the sibling chapter's
`safe` cases (the slice covered by a finite laminar family of discs inside the box,
`Work.BoxShrink.PinchOff.bubbleHalf_of_sliceDiscCovering`) are covered as well.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The two-region family -/

/-- **The two-region family of the pinch**: the region inside the box before the pinching parameter
`1`, and the two half-regions after it. -/
def pinchRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (t : ℝ) : Set R3 :=
  if t < 1 then Work.BoxShrink.Core.boxRegion P s c σ else PinchSweep.halves P s c σ u

variable {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

theorem pinchRegion_of_lt {t : ℝ} (ht : t < 1) :
    pinchRegion P s c σ u t = Work.BoxShrink.Core.boxRegion P s c σ := if_pos ht

theorem pinchRegion_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    pinchRegion P s c σ u t = PinchSweep.halves P s c σ u :=
  if_neg (not_lt.mpr ht)

@[simp] theorem pinchRegion_zero :
    pinchRegion P s c σ u 0 = Work.BoxShrink.Core.boxRegion P s c σ :=
  pinchRegion_of_lt zero_lt_one

@[simp] theorem pinchRegion_one :
    pinchRegion P s c σ u 1 = PinchSweep.halves P s c σ u :=
  pinchRegion_of_one_le le_rfl

/-- **The two-region family is a `SweepLoops`** with the single exceptional parameter `1`, provided
the two regions are related by `RegionEquivalent` (this is the pinching step: no loop is
lost). -/
def pinchSweepLoops (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (h : Work.SurgeryInvariance.RegionEquivalent P (PinchSweep.halves P s c σ u)
      (Work.BoxShrink.Core.boxRegion P s c σ)) :
    Work.SurgeryInvariance.SweepLoops P where
  region := pinchRegion P s c σ u
  exc := ({1} : Finset ℝ)
  regular := by
    intro t ht
    have ht1 : t ≠ 1 := fun hh => ht (by rw [hh]; simp)
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · refine ⟨(1 - t) / 2, by linarith, ?_, ?_⟩
      · intro s hs hs1
        rw [Finset.mem_singleton] at hs1
        rw [hs1] at hs
        rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - t)] at hs
        linarith
      · intro s hs
        have hs1 : s < 1 := by
          rw [abs_lt] at hs
          linarith [hs.2]
        rw [pinchRegion_of_lt hlt, pinchRegion_of_lt hs1]
        exact ⟨fun γ hγ => ⟨γ, hγ, rfl⟩, fun γ hγ => ⟨γ, hγ, rfl⟩⟩
    · refine ⟨(t - 1) / 2, by linarith, ?_, ?_⟩
      · intro s hs hs1
        rw [Finset.mem_singleton] at hs1
        rw [hs1] at hs
        rw [abs_of_neg (by linarith : (1 : ℝ) - t < 0)] at hs
        linarith
      · intro s hs
        have hs1 : 1 ≤ s := by
          rw [abs_lt] at hs
          linarith [hs.1]
        rw [pinchRegion_of_one_le (le_of_lt hgt), pinchRegion_of_one_le hs1]
        exact ⟨fun γ hγ => ⟨γ, hγ, rfl⟩, fun γ hγ => ⟨γ, hγ, rfl⟩⟩
  surgery := by
    intro t ht
    have ht1 : t = 1 := Finset.mem_singleton.mp ht
    subst ht1
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro s _
    by_cases hs1 : s < 1
    · rw [pinchRegion_one, pinchRegion_of_lt hs1]
      exact Or.inr h
    · rw [pinchRegion_one, pinchRegion_of_one_le (le_of_not_gt hs1)]
      exact Or.inr ⟨fun γ hγ => ⟨γ, hγ, rfl⟩, fun γ hγ => ⟨γ, hγ, rfl⟩⟩

theorem pinchSweepLoops_zero (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (h : Work.SurgeryInvariance.RegionEquivalent P (PinchSweep.halves P s c σ u)
      (Work.BoxShrink.Core.boxRegion P s c σ)) :
    (pinchSweepLoops P s c σ u h).region 0 = Work.BoxShrink.Core.boxRegion P s c σ :=
  pinchRegion_zero

theorem pinchSweepLoops_one (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (h : Work.SurgeryInvariance.RegionEquivalent P (PinchSweep.halves P s c σ u)
      (Work.BoxShrink.Core.boxRegion P s c σ)) :
    (pinchSweepLoops P s c σ u h).region 1 = PinchSweep.halves P s c σ u :=
  pinchRegion_one

/-! ## The instances -/

/-- **The trivial pinch**: if the loop content of the two half-regions is the same as that of the
region inside the box, then the two-region family is Pardon's pinch with the trivial piece
`Z = ∅`. -/
def pinchSweepOfRegionEquivalent {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.SurgeryInvariance.RegionEquivalent P (PinchSweep.halves P s c σ u)
      (Work.BoxShrink.Core.boxRegion P s c σ)) : PinchSweep P s c σ u where
  sweep := pinchSweepLoops P s c σ u h
  zero := pinchRegion_zero
  Z := ∅
  Z_open := Work.BoxShrink.Pinch.isOpenInCarrier_empty P
  Z_span := Work.BoxShrink.Pinch.windingSpan_empty P
  Z_disj := by simp
  one := by
    simpa using pinchSweepLoops_one P s c σ u h

/-- **The trivial pinch is non-vacuous**: it exists whenever the loop content of the box region is
carried by the two half-regions. -/
theorem nonempty_pinchSweep_of_regionEquivalent {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.SurgeryInvariance.RegionEquivalent P (PinchSweep.halves P s c σ u)
      (Work.BoxShrink.Core.boxRegion P s c σ)) : Nonempty (PinchSweep P s c σ u) :=
  ⟨pinchSweepOfRegionEquivalent h⟩

/-- **The constant family with a zero-span piece**: if the box region is the union of the two
half-regions and an open piece of vanishing span disjoint from them, then the constant family is
Pardon's pinch. -/
def pinchSweepOfBoxRegion_eq {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {Z : Set R3} (hZopen : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hZspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (hZdisj : Disjoint (PinchSweep.halves P s c σ u) Z)
    (heq : Work.BoxShrink.Core.boxRegion P s c σ = PinchSweep.halves P s c σ u ∪ Z) :
    PinchSweep P s c σ u where
  sweep :=
    { region := fun _ => Work.BoxShrink.Core.boxRegion P s c σ
      exc := ∅
      regular := by
        intro t _
        exact ⟨1, one_pos, by simp, fun s _ => ⟨fun γ hγ => ⟨γ, hγ, rfl⟩, fun γ hγ => ⟨γ, hγ, rfl⟩⟩⟩
      surgery := by intro t ht; simp at ht }
  zero := rfl
  Z := Z
  Z_open := hZopen
  Z_span := hZspan
  Z_disj := hZdisj
  one := heq

/-- **If the box region already is the union of the two half-regions** (no pinch at all: for
instance when the cutting plane misses the surface inside the box) then the residual holds. -/
def pinchSweepOfHalvesEqBoxRegion {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : PinchSweep.halves P s c σ u = Work.BoxShrink.Core.boxRegion P s c σ) :
    PinchSweep P s c σ u :=
  pinchSweepOfBoxRegion_eq (P := P) (Z := ∅) (Work.BoxShrink.Pinch.isOpenInCarrier_empty P)
    (Work.BoxShrink.Pinch.windingSpan_empty P) (by simp) (by rw [h, Set.union_empty])

/-- **If the slice is open in the surface and carries no essential loop**, then the constant family
with `Z = sliceRegion` is Pardon's pinch (the slice is pushed off, no loop is lost). -/
def pinchSweepOfOpenSlice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P (Work.BoxShrink.Core.sliceRegion P s c σ u))
    (hZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u)) :
    PinchSweep P s c σ u :=
  pinchSweepOfBoxRegion_eq (P := P) hopen
    ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff P _).mpr hZ)
    (by
      rw [Set.disjoint_left]
      intro x hx hx'
      obtain ⟨-, -, hxa⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hx'
      rcases hx with hx | hx
      · have := (Work.BoxShrink.Core.mem_upperRegion.mp hx).2.2; linarith
      · have := (Work.BoxShrink.Core.mem_lowerRegion.mp hx).2.2; linarith)
    (Work.BoxShrink.Core.boxRegion_eq_union P s c σ u)

/-- **Pardon's Lemma 3 conclusion in the trivial cases**, without any counting input: whenever the
loop content of the box region is carried by the two half-regions, or the box region is already the
union of the halves, or the slice is open and inessential, the conclusion holds. -/
theorem bubbleHalf_of_regionEquivalent {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.SurgeryInvariance.RegionEquivalent P (PinchSweep.halves P s c σ u)
      (Work.BoxShrink.Core.boxRegion P s c σ)) : Work.BoxShrink.Bubble.BubbleHalf P s c σ u :=
  bubbleHalf_of_pinchSweep (pinchSweepOfRegionEquivalent h)

end

end Work.PinchCounted
