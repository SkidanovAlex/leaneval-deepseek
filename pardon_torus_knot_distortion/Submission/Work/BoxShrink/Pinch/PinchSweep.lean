import Submission.Work.BoxShrink.Pinch.Level
import Submission.Work.BoxShrink.Pinch.Main
import Submission.Work.BoxShrink.Pinch.Final
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Topology.SphereSlicing.boxNorm_continuous

/-!
# The concrete pinch: the sweep of boxes, and the last two inputs

`Level.lean` isolates Pardon's pinch as a family `region t` of sublevel regions
`region ψ (level t) 0` of *nice, continuous* level functions whose level sets carry no essential
loop, together with Pardon's dimension bound of a single surgery.  This module **constructs that
family** for the box/plane configuration, so that the whole residual of the challenge becomes two
explicit statements about the box and the plane:

* `Work.BoxShrink.Pinch.BoxSliceNice` — **the box-sphere trace is in general position**: the level
  set of `boxNorm c σ - s` on the smooth surface is a compact finite disjoint union of simple
  closed curves.  Mathlib has neither Sard's theorem nor the classification of compact
  `1`-manifolds, so this is carried, exactly as the sibling chapter carries its
  `Work.Smooth.Morse.LocallyFiniteCriticalValues` and `CompactOneManifoldInput` — and, unlike
  Pardon's equation (1), it is *not* about the pinch at all;
* `Work.BoxShrink.Pinch.PinchStepInput` — **Pardon's dimension bound at the pinch**: the winding
  spans of `boxRegion` and of `upperRegion ∪ lowerRegion` have dimensions differing by at most one.
  This is Pardon's "doing any of the allowed surgeries can change this value by at most 1"
  (Lemma 2.3) applied to the single surgery of the pinch: the sphere `∂PBox` is pinched along the
  flat disc `cutDisc s c σ u`, and passing the pinch replaces the region inside the box by the two
  half-regions.

## The family

The pinching sphere's interior is the box with a slab around the cutting disc removed, so with
`B = boxNorm c σ` and `g = planeCoord c σ u` the level function

  `slabLevel t = max (B - s) (min t 1 - 1 - |g|)`

has sublevel `{slabLevel t < 0}`:

* `= {B < s}` for `t < 1` (the whole box), and
* `= {B < s, g ≠ 0}` for `t ≥ 1` (the box with the slice removed, i.e. the union of the two
  half-regions).

So `region t = F ∩ {slabLevel t < 0}` is exactly the family of Pardon's pinch in its *degenerate*
form: the whole sweep happens at `t = 1`, which is the pinching parameter, and all the local models
of the sweep are captured by the single dimension bound `PinchStepInput`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

variable {ψ : Submission.Diffeo}

/-! ## The sweep of boxes -/

/-- **The level function of the pinch**: the maximum of the (shifted) box norm and of
`(min t 1) - 1 - |planeCoord|`, whose sublevel is the box, resp. the box with the cutting slab
removed. -/
noncomputable def slabLevel (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u t : ℝ) : R3 → ℝ :=
  fun y => max (Submission.boxNorm c σ y - s)
    (min t 1 - 1 - |Work.BoxShrink.Bubble.planeCoord c σ u y|)

/-- **The region of the pinch**: `F ∩ {slabLevel t < 0}`. -/
noncomputable def sweepRegion (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u t : ℝ) : Set R3 :=
  Work.Smooth.Morse.region ψ (slabLevel s c σ u t) 0

theorem slabLevel_neg_iff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3}
    {t : ℝ} (ht : t < 1) :
    slabLevel s c σ u t y < 0 ↔ Submission.boxNorm c σ y < s := by
  have hb : min t 1 - 1 - |Work.BoxShrink.Bubble.planeCoord c σ u y| < 0 := by
    have h1 : min t 1 ≤ t := min_le_left _ _
    have h2 : (0 : ℝ) ≤ |Work.BoxShrink.Bubble.planeCoord c σ u y| := abs_nonneg _
    linarith
  constructor
  · intro h
    rw [slabLevel, max_lt_iff] at h
    linarith [h.1]
  · intro h
    rw [slabLevel, max_lt_iff]
    exact ⟨by linarith, hb⟩

theorem slabLevel_neg_iff_of_one_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {y : R3} {t : ℝ} (ht : 1 ≤ t) :
    slabLevel s c σ u t y < 0 ↔
      Submission.boxNorm c σ y < s ∧ Work.BoxShrink.Bubble.planeCoord c σ u y ≠ 0 := by
  have hmin : min t 1 = 1 := min_eq_right ht
  rw [slabLevel, hmin, max_lt_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    intro hc
    rw [hc, abs_zero, sub_zero] at h2
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    have : (0 : ℝ) < |Work.BoxShrink.Bubble.planeCoord c σ u y| := abs_pos.mpr h2
    linarith

theorem slabLevel_eq_zero_iff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3}
    {t : ℝ} (ht : t < 1) :
    slabLevel s c σ u t y = 0 ↔ Submission.boxNorm c σ y = s := by
  have hb : min t 1 - 1 - |Work.BoxShrink.Bubble.planeCoord c σ u y| < 0 := by
    have h1 : min t 1 ≤ t := min_le_left _ _
    have h2 : (0 : ℝ) ≤ |Work.BoxShrink.Bubble.planeCoord c σ u y| := abs_nonneg _
    linarith
  constructor
  · intro h
    rw [slabLevel, max_eq_iff] at h
    rcases h with h | h
    · linarith [h.1]
    · linarith [h.1]
  · intro h
    rw [slabLevel, max_eq_left]
    · linarith
    · linarith

/-- **At time `0` the region is the one inside the box.** -/
theorem sweepRegion_zero (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    sweepRegion ψ s c σ u 0 =
      Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ := by
  ext y
  rw [sweepRegion, Work.Smooth.Morse.mem_region, Work.BoxShrink.Core.mem_boxRegion,
    Submission.mem_PBox_iff]
  exact ⟨fun h => ⟨h.1, (slabLevel_neg_iff (by norm_num)).mp h.2⟩,
    fun h => ⟨h.1, (slabLevel_neg_iff (by norm_num)).mpr h.2⟩⟩

/-- **At time `1` the region is the union of the two half-regions.** -/
theorem sweepRegion_one (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    sweepRegion ψ s c σ u 1 =
      Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u := by
  ext y
  rw [sweepRegion, Work.Smooth.Morse.mem_region, Set.mem_union,
    Work.BoxShrink.Core.mem_upperRegion, Work.BoxShrink.Core.mem_lowerRegion,
    Submission.mem_PBox_iff]
  constructor
  · rintro ⟨hy, hlt⟩
    obtain ⟨hb, hpc⟩ := (slabLevel_neg_iff_of_one_le (le_refl 1)).mp hlt
    have hg : y (σ 2) - (c (σ 2) + u) ≠ 0 := by
      simpa [Work.BoxShrink.Bubble.planeCoord] using hpc
    rcases lt_trichotomy (y (σ 2)) (c (σ 2) + u) with h | h | h
    · exact Or.inr ⟨hy, hb, h⟩
    · exact absurd (by linarith : y (σ 2) - (c (σ 2) + u) = 0) hg
    · exact Or.inl ⟨hy, hb, h⟩
  · rintro (⟨hy, hb, h⟩ | ⟨hy, hb, h⟩)
    · refine ⟨hy, (slabLevel_neg_iff_of_one_le (le_refl 1)).mpr ⟨hb, ?_⟩⟩
      simp only [Work.BoxShrink.Bubble.planeCoord]
      intro hc
      linarith
    · refine ⟨hy, (slabLevel_neg_iff_of_one_le (le_refl 1)).mpr ⟨hb, ?_⟩⟩
      simp only [Work.BoxShrink.Bubble.planeCoord]
      intro hc
      linarith

/-- **The region is the box for `t < 1`.** -/
theorem sweepRegion_of_lt {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u t : ℝ} (ht : t < 1) :
    sweepRegion ψ s c σ u t =
      Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ := by
  ext y
  rw [sweepRegion, Work.Smooth.Morse.mem_region, Work.BoxShrink.Core.mem_boxRegion,
    Submission.mem_PBox_iff]
  exact ⟨fun h => ⟨h.1, (slabLevel_neg_iff ht).mp h.2⟩,
    fun h => ⟨h.1, (slabLevel_neg_iff ht).mpr h.2⟩⟩

/-- **The region is the union of the halves for `t ≥ 1`.** -/
theorem sweepRegion_of_one_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u t : ℝ}
    (ht : 1 ≤ t) :
    sweepRegion ψ s c σ u t =
      Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u := by
  have hmin : min t 1 = 1 := min_eq_right ht
  have hlev : slabLevel s c σ u t = slabLevel s c σ u 1 := by
    funext y; simp only [slabLevel, hmin, min_self]
  unfold sweepRegion
  rw [hlev]
  exact sweepRegion_one s c σ u

theorem slabLevel_continuous (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u t : ℝ) :
    Continuous (slabLevel s c σ u t) := by
  have h1 : Continuous fun y : R3 => Submission.boxNorm c σ y - s :=
    (Work.Topology.SphereSlicing.boxNorm_continuous c σ).sub continuous_const
  have h2 : Continuous fun y : R3 => min t 1 - 1 -
      |Work.BoxShrink.Bubble.planeCoord c σ u y| :=
    continuous_const.sub ((Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).continuous.abs)
  exact h1.max h2

/-- **The level set of the pinch at time `t < 1` is the trace of the box sphere.** -/
theorem levelSet_slabLevel_subset_sphereSet {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {t : ℝ} (ht : t < 1) :
    Work.Smooth.Morse.levelSet ψ (slabLevel s c σ u t) 0 ⊆ Work.BoxShrink.Core.sphereSet c σ s := by
  intro y hy
  rw [Work.Smooth.Morse.mem_levelSet] at hy
  rw [Work.BoxShrink.Core.mem_sphereSet]
  exact (slabLevel_eq_zero_iff ht).mp hy.2

/-! ## The level function of the box sphere, and the transfer of the general position -/

/-- **The level function of the box sphere**: `boxNorm c σ - s`.  Its level set is the box sphere
`∂PBox s c σ` and its sublevel region is `PBox s c σ`. -/
noncomputable def boxLevel (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : R3 → ℝ :=
  fun y => Submission.boxNorm c σ y - s

theorem boxLevel_continuous (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (boxLevel s c σ) :=
  (Work.Topology.SphereSlicing.boxNorm_continuous c σ).sub continuous_const

/-- The level-`0` set of the pinching level function is the box sphere (for `t < 1`, where the
second branch of the maximum is automatically negative). -/
theorem slabLevel_levelSet_eq {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u t : ℝ}
    (ht : t < 1) :
    Work.Smooth.Morse.levelSet ψ (slabLevel s c σ u t) 0 =
      Work.Smooth.Morse.levelSet ψ (boxLevel s c σ) 0 := by
  ext y
  rw [Work.Smooth.Morse.mem_levelSet, Work.Smooth.Morse.mem_levelSet]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, by simpa only [boxLevel, sub_eq_zero] using (slabLevel_eq_zero_iff ht).mp h⟩
  · rintro ⟨hy, h⟩
    exact ⟨hy, (slabLevel_eq_zero_iff ht).mpr (by simpa only [boxLevel, sub_eq_zero] using h)⟩

/-- The closed sublevel region of the pinching level function is that of the box sphere. -/
theorem slabLevel_closedRegion_eq {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u t : ℝ}
    (ht : t < 1) :
    Work.Smooth.Morse.closedRegion ψ (slabLevel s c σ u t) 0 =
      Work.Smooth.Morse.closedRegion ψ (boxLevel s c σ) 0 := by
  have hle : ∀ y : R3, slabLevel s c σ u t y ≤ 0 ↔ boxLevel s c σ y ≤ 0 := by
    intro y
    rw [slabLevel, max_le_iff, boxLevel]
    constructor
    · rintro ⟨h1, _⟩; linarith
    · intro h1
      refine ⟨by linarith, ?_⟩
      have h2 : min t 1 ≤ t := min_le_left _ _
      have h3 : (0 : ℝ) ≤ |Work.BoxShrink.Bubble.planeCoord c σ u y| := abs_nonneg _
      linarith
  ext y
  rw [Work.Smooth.Morse.mem_closedRegion, Work.Smooth.Morse.mem_closedRegion]
  exact ⟨fun h => ⟨h.1, (hle y).mp h.2⟩, fun h => ⟨h.1, (hle y).mpr h.2⟩⟩

/-- **The general position of the pinching level function follows from that of the box sphere.**
The two level sets coincide for `t < 1`, and so do the closed sublevel regions. -/
theorem niceLevel_slabLevel {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u t : ℝ} (ht : t < 1)
    (h : Work.Smooth.Morse.NiceLevel ψ (boxLevel s c σ) 0) :
    Work.Smooth.Morse.NiceLevel ψ (slabLevel s c σ u t) 0 where
  isCompact_levelSet := by rw [slabLevel_levelSet_eq (ψ := ψ) ht]; exact h.isCompact_levelSet
  circleUnion := by rw [slabLevel_levelSet_eq (ψ := ψ) ht]; exact h.circleUnion
  isCompact_closedRegion := by
    rw [slabLevel_closedRegion_eq (ψ := ψ) ht]; exact h.isCompact_closedRegion

/-- **The general position of the box-sphere trace** from the two inputs isolated by the smooth
chapter: the classification of compact `1`-manifolds (`CompactOneManifoldInput`) and the local
flatness of the box sphere trace (`IsLocalArc`).  The two compactness fields are free, since the
box norm is continuous and the surface is compact. -/
theorem boxSliceNice_of_localArc {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (harc : Work.Smooth.Morse.IsLocalArc ψ
      (Work.Smooth.Morse.levelSet ψ (boxLevel s c σ) 0)) :
    Work.Smooth.Morse.NiceLevel ψ (boxLevel s c σ) 0 where
  isCompact_levelSet :=
    Work.Smooth.Morse.Surface.isCompact_levelSet ψ (boxLevel_continuous s c σ) 0
  circleUnion := hclass _ (Work.Smooth.Morse.Surface.isCompact_levelSet ψ
    (boxLevel_continuous s c σ) 0) harc
  isCompact_closedRegion :=
    Work.Smooth.Morse.Surface.isCompact_closedRegion ψ (boxLevel_continuous s c σ) 0

/-! ## The level function of the double bubble -/

/-- **The level function of the double bubble**: `slabLevel s c σ u t` at the pinching parameter
`t = 1`, i.e. `max (boxNorm - s) (-|planeCoord|)`.  Its sublevel region is the union of the two
half-regions, so Pardon's equation (1) at this level function is exactly the dichotomy at the
*double bubble* — the `t = 1` case which `PinchLevels` deliberately does not require. -/
noncomputable def bbLevel (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : R3 → ℝ :=
  slabLevel s c σ u 1

theorem bbLevel_def (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    bbLevel s c σ u = slabLevel s c σ u 1 := rfl

theorem bbLevel_continuous (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Continuous (bbLevel s c σ u) := slabLevel_continuous s c σ u 1

/-- **The region inside the double bubble is the union of the two half-regions.** -/
theorem region_bbLevel (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.Smooth.Morse.region ψ (bbLevel s c σ u) 0 =
      Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u :=
  sweepRegion_one s c σ u

/-- **Pardon's equation (1) at the double bubble.**  If the level set of `bbLevel` is nice and
carries no essential loop — which is what Pardon's counting supplies at the pinching parameter,
since the trace of the two half-spheres meets `β` no more often than the trace of the box sphere
plus twice the trace of the cutting disc — then the union of the two half-regions satisfies the
dichotomy: its winding span is `⊥` or `⊤`. -/
theorem pardonDichotomy_region_bbLevel {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Equation1Input)
    (hnice : Work.Smooth.Morse.NiceLevel ψ (bbLevel s c σ u) 0)
    (hiness : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.Smooth.Morse.levelSet ψ (bbLevel s c σ u) 0)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.Smooth.Morse.region ψ (bbLevel s c σ u) 0) :=
  h ψ (bbLevel s c σ u) 0 (bbLevel_continuous s c σ u) hnice hiness

/-- **The dichotomy at the double bubble, in the form the pinch consumes it.** -/
theorem pardonDichotomy_upper_union_lower {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Equation1Input)
    (hnice : Work.Smooth.Morse.NiceLevel ψ (bbLevel s c σ u) 0)
    (hiness : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.Smooth.Morse.levelSet ψ (bbLevel s c σ u) 0)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) := by
  rw [← region_bbLevel s c σ u]
  exact pardonDichotomy_region_bbLevel (ψ := ψ) h hnice hiness

/-! ## The two residual inputs -/

/-- **The box-sphere trace is in general position.**  The level set of the box norm (equivalently,
of the pinching level function `slabLevel s c σ u t` for `t < 1`) on the smooth surface is a *nice
level*: compact, a finite disjoint union of simple closed curves of the surface, and with compact
closed sublevel region.

For a smooth embedded surface this is Sard's theorem (almost every `s` is a regular value of the box
norm on the surface) plus the classification of compact `1`-manifolds (a compact `1`-manifold
without boundary is a finite disjoint union of circles); Mathlib has neither, and the sibling
`smooth` chapter carries the same two statements as `Work.Smooth.Morse.LocallyFiniteCriticalValues`
and `Work.Smooth.Morse.CompactOneManifoldInput`.  It is reduced to them by
`boxSliceNice_of_localArc`, and `niceLevel_slabLevel` transfers it to the pinching level function.
Note that the statement is *not* about the pinch: it says only that the trace of a box sphere with
the surface is tame. -/
def BoxSliceNice : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
    Work.Smooth.Morse.NiceLevel ψ (boxLevel s c σ) 0

/-- **Pardon's dimension bound at the pinch.**  The pinch replaces the region inside the box by the
two half-regions; Pardon's Lemma 2.3 says that a single surgery changes
`dim_Q im (H₁ (F ∩ int S; ℚ) → H₁ (F; ℚ))` by at most one, and this is the statement for the
single surgery of the box/plane configuration, under the hypotheses of the pinch (both the sphere
trace and the slice trace carry no essential loop).

It is stated purely as a dimension inequality between the winding spans of two explicitly given
regions; it contains no conclusion about which half carries a loop. -/
def PinchStepInput : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) + 1 ∧
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) + 1

/-! ## The pinch from the box and the two inputs -/

/-- **Pardon's pinch exists for the box/plane configuration**, from the two inputs: the family of
level functions `slabLevel t`, its general position (`BoxSliceNice`), the inessentiality of the box
sphere trace (Pardon's counting, `hS`) and the dimension bound at the pinch (`PinchStepInput`).

The dichotomy of the family is *not* assumed: it comes from Pardon's equation (1) at each level
(`Equation1Input`), applied to the level function `slabLevel t` for `t < 1`, whose level set is
(part of) the box sphere trace. -/
noncomputable def pinchLevels_of_box {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hnice : BoxSliceNice) (hS : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s))
    (hZ : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u))
    (hstep : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) + 1 ∧
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) + 1) :
    PinchLevels ψ s c σ u where
  level := slabLevel s c σ u
  region := sweepRegion ψ s c σ u
  zero := sweepRegion_zero s c σ u
  one := sweepRegion_one s c σ u
  region_eq := fun _ _ => rfl
  nice := fun t ht => niceLevel_slabLevel (ψ := ψ) ht (hnice ψ s c σ)
  continuous := fun t _ => slabLevel_continuous s c σ u t
  trace_inessential := fun t ht =>
    fun hcon => hS ((Work.CoreTopology.ParamTorus.containsEssentialLoop_mono _)
      (levelSet_slabLevel_subset_sphereSet (ψ := ψ) ht) hcon)
  step := fun t => by
    have hA : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (sweepRegion ψ s c σ u 1) = Work.SurgeryInvariance.WindingSpan
        (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) := by
      rw [sweepRegion_of_one_le (le_refl 1)]
    rcases lt_trichotomy t 1 with ht | ht | ht
    · refine ⟨(1 - t) / 2, by linarith, fun r hr => ?_⟩
      have hr1 : r < 1 := by
        have := (abs_lt.mp hr).2; linarith
      rw [sweepRegion_of_lt hr1, sweepRegion_of_lt ht]
      exact ⟨Nat.le_succ _, Nat.le_succ _⟩
    · subst ht
      refine ⟨1, one_pos, fun r _ => ?_⟩
      rcases lt_or_ge r 1 with hr | hr
      · rw [sweepRegion_of_lt hr, sweepRegion_of_one_le (le_refl 1)]
        exact hstep
      · rw [sweepRegion_of_one_le hr, sweepRegion_of_one_le (le_refl 1)]
        exact ⟨Nat.le_succ _, Nat.le_succ _⟩
    · refine ⟨(t - 1) / 2, by linarith, fun r hr => ?_⟩
      have hr1 : 1 ≤ r := by
        have := (abs_lt.mp hr).1; linarith
      rw [sweepRegion_of_one_le hr1, sweepRegion_of_one_le (le_of_lt ht)]
      exact ⟨Nat.le_succ _, Nat.le_succ _⟩

/-- **Pardon's Lemma 3 from the two inputs and his equation (1).** -/
theorem smoothHalfS_of_eq1_boxStep (h1 : Equation1Input) (hnice : BoxSliceNice)
    (hstep : PinchStepInput) : SmoothHalfS :=
  smoothHalfS_of_pinchLevelsInput h1
    (fun ψ s c σ u hS hZ => ⟨pinchLevels_of_box hnice hS hZ (hstep ψ s c σ u hS hZ)⟩)

/-- **Pardon's theorem from the two explicit inputs of the pinch.** -/
theorem pardon_torus_knot_distortion_of_eq1_boxStep
    (h1 : Equation1Input) (hnice : BoxSliceNice) (hstep : PinchStepInput)
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hdisc (smoothHalfS_of_eq1_boxStep h1 hnice hstep)
    hclean hae

end

end Work.BoxShrink.Pinch
