import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_iff_realizedWindings
import Submission.Work.Smooth.Morse.Flow

/-!
# The push-off for the smooth tori, from the flow of the plane coordinate

`Work.Smooth.Morse.Flow.regularEquivalent_of_contDiff_two` (proved in the sibling chapter) says that
for a function `g` of class `C²` on the surface and a critical-value-free interval `[a,b]` the two
sublevel regions `F ∩ {g < a}` and `F ∩ {g < b}` are `RegionEquivalent`: the normalised gradient flow
of `g|_F` transports every loop of the larger region to a loop of the smaller one with the same
winding vector (the flow moves each point of the surface down to the level `a`).

This file applies that theorem to the **plane coordinate**
`planeCoord c σ u = y ↦ y (σ 2) - (c (σ 2) + u)`, whose sublevel regions are the traces of the
half-spaces bounded by the cutting plane.  The conclusion is the chapter's isolated input in the two
"plateau" configurations in which the flow *provably lands inside the box region*:

* `slicePushOff_of_belowPlateau`: if the region inside the box is a below-plateau of the plane
  coordinate (`boxRegion ⊆ {g < b}` and `{g < b} ∩ F ⊆ boxRegion`, for a `b > 0`), and `[a,b]` with
  `a < 0` is critical-value-free, then the flow transports every loop of the region into
  `F ∩ {g < a} ⊆ lowerRegion`: the push-off holds;
* `slicePushOff_of_abovePlateau`: the mirror statement, with `{g > b} ∩ F ⊆ boxRegion` and
  `boxRegion ⊆ {g > a}`, giving loops in `upperRegion`.

So the push-off holds whenever the box region is exactly a sublevel (resp. superlevel) plateau of
the plane coordinate over a critical-value-free interval containing `0`.  What a general
configuration is missing is exactly this "the destonaton of the flow stays in the box" (the flow of
the plane coordinate moves the loops off the plane but out of a bounded box) together with the
transversality of the level `0`; see `README.md` and `PLAN.md`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-- **The plane coordinate**: the signed `σ 2`-distance to the cutting plane
`{y | y (σ 2) = c (σ 2) + u}`.  Its level `0` is the cutting plane itself, and its negative sublevel
region is the trace of the lower half-space. -/
def planeCoord (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : R3 → ℝ :=
  fun y => y (σ 2) - (c (σ 2) + u)

@[simp] theorem planeCoord_apply (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (y : R3) :
    planeCoord c σ u y = y (σ 2) - (c (σ 2) + u) := rfl

/-- The plane coordinate is `C²` (it is linear). -/
theorem contDiff_planeCoord (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    ContDiff ℝ 2 (planeCoord c σ u) := by
  show ContDiff ℝ 2 (fun y : R3 => y (σ 2) - (c (σ 2) + u))
  exact ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) (σ 2) : R3 →L[ℝ] ℝ).contDiff).sub contDiff_const

/-- The negated plane coordinate is `C²`. -/
theorem contDiff_neg_planeCoord (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    ContDiff ℝ 2 (fun y : R3 => -planeCoord c σ u y) :=
  (contDiff_planeCoord c σ u).neg

/-! ## The two plateau statements -/

/-- **The push-off from a below-plateau.**  If `[a,b]` (with `a < 0 < b`) is critical-value-free
for the plane coordinate, everything of the surface below the level `b` lies in the region inside
the box, and the region inside the box lies below the level `b`, then the normalised gradient flow of
the plane coordinate transports the region's loops into the **lower** region
`F ∩ {g < a} ⊆ lowerRegion`: in particular the push-off holds. -/
theorem slicePushOff_of_belowPlateau {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u a b : ℝ}
    (hab : a ≤ b) (ha : a < 0) (hb : 0 < b)
    (hreg : ∀ t ∈ Set.Icc a b, Work.Smooth.Morse.IsRegularValue ψ (planeCoord c σ u) t)
    (hcont : ∀ x ∈ (Work.Smooth.Morse.torus ψ).carrier, planeCoord c σ u x < b →
      x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
    (hbox : ∀ x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ,
      planeCoord c σ u x < b) :
    SlicePushOff (Work.Smooth.Morse.torus ψ) s c σ u := by
  have hRE := Work.Smooth.Morse.regularEquivalent_of_contDiff_two ψ
    (contDiff_planeCoord c σ u) a b hab hreg
  have hEq := (Toolkit.regionEquivalent_iff_realizedWindings (Work.Smooth.Morse.torus ψ)
    (Work.Smooth.Morse.region ψ (planeCoord c σ u) a)
    (Work.Smooth.Morse.region ψ (planeCoord c σ u) b)).mp hRE
  intro k hk
  -- the loop lies below the level `b`, hence in `region ψ g b`
  have h1 : k ∈ RealizedWindings (Work.Smooth.Morse.torus ψ)
      (Work.Smooth.Morse.region ψ (planeCoord c σ u) b) :=
    RealizedWindings_mono
      (X := Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
      (Y := Work.Smooth.Morse.region ψ (planeCoord c σ u) b)
      (fun x hx => ⟨hx.1, hbox x hx⟩) hk
  rw [← hEq] at h1
  -- and the transported loop lies below the level `a < 0`, hence in the lower region
  refine RealizedWindings_mono (X := Work.Smooth.Morse.region ψ (planeCoord c σ u) a)
    (Y := Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
      Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) ?_ h1
  intro x hx
  have hxc : x ∈ (Work.Smooth.Morse.torus ψ).carrier := hx.1
  have hxbox : x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ :=
    hcont x hxc (lt_of_lt_of_le hx.2 hab)
  have hlt : x (σ 2) < c (σ 2) + u := by
    have h : x (σ 2) - (c (σ 2) + u) < a := hx.2
    linarith
  exact Set.subset_union_right
    ((Work.BoxShrink.Core.mem_lowerRegion (P := Work.Smooth.Morse.torus ψ)).mpr
      ⟨hxc, (Work.BoxShrink.Core.mem_boxRegion.mp hxbox).2, hlt⟩)

/-- **The push-off from an above-plateau** (the mirror statement): if `[a,b]` with `a < 0 < b` is
critical-value-free for the negated plane coordinate, everything of the surface *above* the level
`b` (`{g > b}`, i.e. `-g < -b`) lies in the region, and the region lies above the level `a`
(`-g < -a`), then the flow transports the region's loops into the **upper** region
`F ∩ {g > b} ⊆ upperRegion`. -/
theorem slicePushOff_of_abovePlateau {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u a b : ℝ}
    (hab : a ≤ b) (ha : a < 0) (hb : 0 < b)
    (hreg : ∀ t ∈ Set.Icc (-b) (-a),
      Work.Smooth.Morse.IsRegularValue ψ (fun y : R3 => -planeCoord c σ u y) t)
    (hcont : ∀ x ∈ (Work.Smooth.Morse.torus ψ).carrier, -planeCoord c σ u x < -b →
      x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
    (hbox : ∀ x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ,
      -planeCoord c σ u x < -a) :
    SlicePushOff (Work.Smooth.Morse.torus ψ) s c σ u := by
  have hRE := Work.Smooth.Morse.regularEquivalent_of_contDiff_two ψ
    (contDiff_neg_planeCoord c σ u) (-b) (-a) (neg_le_neg hab) hreg
  have hEq := (Toolkit.regionEquivalent_iff_realizedWindings (Work.Smooth.Morse.torus ψ)
    (Work.Smooth.Morse.region ψ (fun y : R3 => -planeCoord c σ u y) (-b))
    (Work.Smooth.Morse.region ψ (fun y : R3 => -planeCoord c σ u y) (-a))).mp hRE
  intro k hk
  have h1 : k ∈ RealizedWindings (Work.Smooth.Morse.torus ψ)
      (Work.Smooth.Morse.region ψ (fun y : R3 => -planeCoord c σ u y) (-a)) :=
    RealizedWindings_mono
      (X := Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
      (Y := Work.Smooth.Morse.region ψ (fun y : R3 => -planeCoord c σ u y) (-a))
      (fun x hx => ⟨hx.1, hbox x hx⟩) hk
  rw [← hEq] at h1
  refine RealizedWindings_mono
    (X := Work.Smooth.Morse.region ψ (fun y : R3 => -planeCoord c σ u y) (-b))
    (Y := Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
      Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) ?_ h1
  intro x hx
  have hxc : x ∈ (Work.Smooth.Morse.torus ψ).carrier := hx.1
  have hxbox : x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ :=
    hcont x hxc hx.2
  have hgt : c (σ 2) + u < x (σ 2) := by
    have h : b < x (σ 2) - (c (σ 2) + u) := by
      have h' : - (x (σ 2) - (c (σ 2) + u)) < -b := hx.2
      linarith
    linarith
  exact Set.subset_union_left
    ((Work.BoxShrink.Core.mem_upperRegion (P := Work.Smooth.Morse.torus ψ)).mpr
      ⟨hxc, (Work.BoxShrink.Core.mem_boxRegion.mp hxbox).2, hgt⟩)

/-! ## The field in the two plateau configurations -/

/-- **The field `bubble`, in the below-plateau configuration.** -/
noncomputable def bubbleSweep_of_belowPlateau {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u a b : ℝ}
    (hab : a ≤ b) (ha : a < 0) (hb : 0 < b)
    (hreg : ∀ t ∈ Set.Icc a b, Work.Smooth.Morse.IsRegularValue ψ (planeCoord c σ u) t)
    (hcont : ∀ x ∈ (Work.Smooth.Morse.torus ψ).carrier, planeCoord c σ u x < b →
      x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
    (hbox : ∀ x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ,
      planeCoord c σ u x < b) :
    Work.BoxShrink.Core.BubbleSweep (Work.Smooth.Morse.torus ψ) s c σ u :=
  bubble_of_slicePushOff (slicePushOff_of_belowPlateau (ψ := ψ) hab ha hb hreg hcont hbox)

/-- **The field `bubble`, in the above-plateau configuration.** -/
noncomputable def bubbleSweep_of_abovePlateau {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u a b : ℝ}
    (hab : a ≤ b) (ha : a < 0) (hb : 0 < b)
    (hreg : ∀ t ∈ Set.Icc (-b) (-a),
      Work.Smooth.Morse.IsRegularValue ψ (fun y : R3 => -planeCoord c σ u y) t)
    (hcont : ∀ x ∈ (Work.Smooth.Morse.torus ψ).carrier, -planeCoord c σ u x < -b →
      x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
    (hbox : ∀ x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ,
      -planeCoord c σ u x < -a) :
    Work.BoxShrink.Core.BubbleSweep (Work.Smooth.Morse.torus ψ) s c σ u :=
  bubble_of_slicePushOff (slicePushOff_of_abovePlateau (ψ := ψ) hab ha hb hreg hcont hbox)

end

end Work.BoxShrink.Bubble
