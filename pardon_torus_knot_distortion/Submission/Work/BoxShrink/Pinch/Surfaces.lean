import Submission.Work.BoxShrink.Pinch.Regions
import Submission.Work.SurgeryInvariance.SphereSweep
import Submission.Work.BoxShrink.Bubble.Defs

/-!
# The collar of the slice, and Pardon's Lemma 2.3 from a spatial sweep

The **collar** of the slice is `collar P s c σ u δ = boxRegion ∩ {|y (σ 2) - (c (σ 2) + u)| < δ}`:
the part of the box region within the slab of half-width `δ` around the cutting plane.  It is open
in the surface, contains the slice, and together with the two half-regions it covers the box region;
its homotopy type is that of the slice, so under Pardon's hypothesis `hZ` it carries no essential
loop.

The main theorem of this module is `bubbleHalf_of_sweep`: **Pardon's Lemma 2.3** in the form of the
chapter.  A `Work.SurgeryInvariance.Sweep` is a one-parameter family of regions of the surface
together with finitely many `2`-surgeries; along it the winding span is constant
(`Work.SurgeryInvariance.Sweep.windingSpan_eq`), so Pardon's dichotomy at the *initial* region —
which the counting supplies at the original sphere `∂PBox s c σ` — forces the invariant at the final
region, the union of the two half-regions, to be nonzero, and one of the two halves then carries an
essential loop.  Neither the dichotomy nor the dimension bound is needed at any intermediate
parameter: the local models of the sweep give them outright.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The collar -/

/-- **The collar of the slice**: the part of the box region inside the slab of half-width `δ`
around the cutting plane. -/
def collar (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u δ : ℝ) : Set R3 :=
  Work.BoxShrink.Core.boxRegion P s c σ ∩
    {y : R3 | |y (σ 2) - (c (σ 2) + u)| < δ}

@[simp] theorem mem_collar {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u δ : ℝ} {y : R3} :
    y ∈ collar P s c σ u δ ↔ y ∈ Work.BoxShrink.Core.boxRegion P s c σ ∧
      |y (σ 2) - (c (σ 2) + u)| < δ := Iff.rfl

theorem collar_subset_boxRegion {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u δ : ℝ} :
    collar P s c σ u δ ⊆ Work.BoxShrink.Core.boxRegion P s c σ := inter_subset_left

theorem collar_mono {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u δ δ' : ℝ} (h : δ ≤ δ') :
    collar P s c σ u δ ⊆ collar P s c σ u δ' :=
  fun _ hy => ⟨hy.1, lt_of_lt_of_le hy.2 h⟩

theorem collar_subset_slab {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u δ : ℝ} :
    collar P s c σ u δ ⊆ Work.BoxShrink.Bubble.slab c σ u δ :=
  fun _ hy => hy.2

/-- The collar is open in the surface (it is the trace of an open slab). -/
theorem isOpenInCarrier_collar (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u δ : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier P (collar P s c σ u δ) := by
  have hcont : Continuous fun y : R3 => |y (σ 2) - (c (σ 2) + u)| := by
    simpa only [Work.BoxShrink.Bubble.planeCoord] using
      (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).continuous.abs
  have h1 : IsOpen {y : R3 | |y (σ 2) - (c (σ 2) + u)| < δ} :=
    isOpen_lt hcont continuous_const
  have h2 : Work.SurgeryInvariance.IsOpenInCarrier P
      {y : R3 | |y (σ 2) - (c (σ 2) + u)| < δ} := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier]
    exact h1.preimage continuous_subtype_val
  exact Work.SurgeryInvariance.isOpenInCarrier_inter P
    (Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ) h2

/-- The slice is contained in every collar. -/
theorem sliceRegion_subset_collar {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u δ : ℝ}
    (hδ : 0 < δ) :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ collar P s c σ u δ := by
  intro y hy
  obtain ⟨hyc, hyb, hyl⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hy
  refine ⟨⟨hyc, hyb⟩, ?_⟩
  show |y (σ 2) - (c (σ 2) + u)| < δ
  rw [hyl, sub_self, abs_zero]
  exact hδ

/-- **The two half-regions and the collar cover the box region.** -/
theorem upper_union_lower_union_collar {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u δ : ℝ}
    (hδ : 0 < δ) :
    Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u ∪
      collar P s c σ u δ = Work.BoxShrink.Core.boxRegion P s c σ := by
  ext y
  constructor
  · rintro ((hy | hy) | hy)
    · exact ⟨(Work.BoxShrink.Core.mem_upperRegion.mp hy).1,
        (Work.BoxShrink.Core.mem_upperRegion.mp hy).2.1⟩
    · exact ⟨(Work.BoxShrink.Core.mem_lowerRegion.mp hy).1,
        (Work.BoxShrink.Core.mem_lowerRegion.mp hy).2.1⟩
    · exact hy.1
  · intro hy
    have hyc : y ∈ P.carrier := hy.1
    have hyb : y ∈ Submission.PBox s c σ := hy.2
    rcases lt_trichotomy (y (σ 2)) (c (σ 2) + u) with h | h | h
    · exact Or.inl (Or.inr ((Work.BoxShrink.Core.mem_lowerRegion).mpr ⟨hyc, hyb, h⟩))
    · refine Or.inr ⟨⟨hyc, hyb⟩, ?_⟩
      show |y (σ 2) - (c (σ 2) + u)| < δ
      rw [h, sub_self, abs_zero]
      exact hδ
    · exact Or.inl (Or.inl ((Work.BoxShrink.Core.mem_upperRegion).mpr ⟨hyc, hyb, h⟩))

/-- **The collar exists**: some `δ > 0` makes the collar open in the surface, contains the slice,
and, together with the two half-regions, covers the box region. -/
theorem exists_collar {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    ∃ δ : ℝ, 0 < δ ∧
      Work.SurgeryInvariance.IsOpenInCarrier P (collar P s c σ u δ) ∧
      Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ collar P s c σ u δ ∧
      Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u ∪
        collar P s c σ u δ = Work.BoxShrink.Core.boxRegion P s c σ :=
  ⟨1, one_pos, isOpenInCarrier_collar s c σ u 1, sliceRegion_subset_collar one_pos,
    upper_union_lower_union_collar one_pos⟩

/-! ## Pardon's Lemma 2.3 from a sweep -/

/-- **Pardon's Lemma 2.3 (`spherefamily` + the double bubble) from a spatial sweep.**  If a
`Work.SurgeryInvariance.Sweep` starts at the region inside the box, ends at the union of the two
half-regions, and the invariant of the initial region satisfies Pardon's dichotomy, then an
essential loop of the box region survives to one of the two halves.

The local models of the sweep (an ambient isotopy away from the exceptional parameters, a single
`2`-surgery at them) give both the dichotomy and the dimension bound along the whole family, so the
only remaining input is the dichotomy at `region 0` — which the counting hypothesis of Pardon's
paper supplies at the original sphere. -/
theorem bubbleHalf_of_sweep {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (S : Work.SurgeryInvariance.Sweep P)
    (hzero : S.region 0 = Work.BoxShrink.Core.boxRegion P s c σ)
    (hone : S.region 1 = Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u)
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (S.region 0)) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u :=
  bubbleHalf_of_pinchRegions (PinchRegions.ofSweep S hzero hone hdich)

/-- **Pardon's Lemma 2.3 for a family of *spheres*.**  Same conclusion, from the sphere-level
description `Work.SurgeryInvariance.SphereSweep` of the family. -/
theorem bubbleHalf_of_sphereSweep {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (S : Work.SurgeryInvariance.SphereSweep P)
    (hzero : S.region 0 = Work.BoxShrink.Core.boxRegion P s c σ)
    (hone : S.region 1 = Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u)
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (S.region 0)) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u :=
  bubbleHalf_of_sweep S.toSweep hzero hone hdich

end

end Work.BoxShrink.Pinch
