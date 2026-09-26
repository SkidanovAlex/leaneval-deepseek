import Submission.Work.BoxShrink.Pinch.Basic
import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.BoxShrink.crux

/-!
# The pinch: Pardon's pinching family, and the residual input

This module fixes the object the whole chapter is about.

## Pardon's pinch

Let `F = P.carrier` be the surface (in the application the smooth torus of the challenge), let
`PBox s c σ` be Pardon's box and let `D = cutDisc s c σ u = PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}`
be the flat disc cut out of the box by the cutting plane.  Pardon's Lemma `doublebubble`
(*On the distortion of knots on embedded surfaces*, §3) is proved by considering a **one-parameter
family of embedded spheres** `{S_t}`, `t ∈ [0,1]`, obtained "by starting with `S₀ = ∂PBox s c σ`
and performing a `2`-surgery along the disc `D`": pinching the boundary sphere of the box along
`D` until it becomes the two spheres bounding the two halves into which `D` divides the box.

The region `F ∩ int(S_t)` cut out of the surface starts at `boxRegion = F ∩ int(S₀)` and ends at
the two half-regions `upperRegion ∪ lowerRegion` (together, in the perturbed version
`doublebubble2`, with the trace of `D` itself, a piece of the surface through which the surgery
passes and which contributes nothing to the winding span: this is why the endpoint below carries an
arbitrary piece `Z` of vanishing winding span rather than only an embedded disc).

**The local models must be Pardon's, and not the stronger `Work.SurgeryInvariance.SweepLoops` or
`Work.SurgeryInvariance.Sweep` ones.**  The pinch *shrinks* the essential content of the region: at
the counterexample configuration of the sibling chapter the region inside the box has winding span
`⊤` (`Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top`) while the union of the two halves has
span `≤ ℚ·(0,1) ⊊ ⊤` (`Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`), so the span is *not*
constant along the pinch.  A family whose local models preserve the span exactly
(`RegionIsolated`, `SurgeryStepZero`, `SurgeryShape`, `SweepLoops`, `Sweep`, `LevelFamily`) can
therefore never reach the two halves from the box region: see
`Work.BoxShrink.Pinch.Warning`.  Pardon's own local models are the ones which allow the jump: away
from finitely many parameters the loops are transported, at an exceptional parameter the region
changes by a single `2`-surgery — i.e. by an open piece of winding span different from `⊤`
(`Work.BoxShrink.Bubble.SurgeryStepSmall`) — the *dimension* of the essential content changes by at
most one at each surgery, and Pardon's dichotomy (the possible values are `0` and `2g`, i.e.
`⊥` and `⊤`) then makes it constant along the family on `[0,1)`; the pinch itself, at `t = 1`, is a
separate inclusion, the endgame field below.

This is exactly the structure of the library's isolated input
`Work.BoxShrink.Bubble.PinchDatum`, with the endpoint generalised by the zero-span piece `Z` (the
perturbation of Pardon's `doublebubble2`).  So the chapter's residual input is precisely "Pardon's
pinch exists", and it is *implied* by the library's isolated input
(`pinchInputAll_of_pardonPinchInput`).

## What this module contains

* `PinchFamily P s c σ u` — Pardon's pinch for the box/plane configuration;
* `bubbleHalf_of_pinchFamily` — **the family produces Pardon's Lemma 3 conclusion**
  (`Work.BoxShrink.Bubble.BubbleHalf`): the persistence of the essential loop along the family on
  `[0,1)` (`Work.BoxShrink.Bubble.SweepLoopsSmall.containsEssentialLoop_of_lt_one`) followed by the
  endgame and the double-bubble step (`double_bubble_persistence_of_zero_span`);
* instances: `pinchFamilyOfPinchDatum` (from the library's isolated input), `pinchFamilyOfEmptyBox`
  (the box misses the surface), `pinchFamilyOfEmptySlice` and `pinchFamilyOfOpenSlice` (with Pardon's
  dichotomy at the initial sphere, which is what the counting supplies);
* `PinchInput` / `PinchInputAll` / `PinchInputHZAll` / `PinchInputSmoothAll` — the residual input in
  its various forms, with `pinchInputAll_of_pardonPinchInput` and
  `pinchInputSmoothAll_of_pardonPinchInput` connecting it to the library's own isolated input;
* `PinchInputCounting` — the input with the whole counting datum of the crux available, which is the
  form Pardon's paper produces;
* `SmoothHalfS` — Pardon's Lemma 3 conclusion under *both* of his endpoint hypotheses (strictly
  weaker than the field `Work.BoxShrink.Bubble.SmoothHalf` of `Work.BoxShrink.FinalInput`, and
  sufficient for the crux).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Pardon's pinch -/

/-- **Pardon's pinch of the box/plane configuration.**

The one-parameter family of spheres of Pardon's Lemma `doublebubble`, recorded through the regions
`F ∩ int(S_t)` that it cuts out of the surface:

* `sweep` — the family, with **Pardon's local models** (`Work.BoxShrink.Bubble.SweepLoopsSmall`:
  away from the finitely many exceptional parameters the loops of the region are transported with
  their winding vectors, at an exceptional parameter the region changes by a single `2`-surgery, i.e.
  by an open piece of winding span `≠ ⊤`, and Pardon's dichotomy `⊥`/`⊤` holds at every parameter
  before the pinch);
* `zero` — at time `0` the family is the boundary sphere of Pardon's box: `sweep.region 0 =
  boxRegion`;
* `Z` — the piece of the surface through which the pinch takes place (the trace of the flat disc
  `cutDisc s c σ u` in the perturbed double bubble of Pardon's `doublebubble2`), or `∅`: open in
  the surface, of vanishing winding span, disjoint from the two half-regions;
* `one` — at time `1` the family is the two half-regions together with that piece:
  `sweep.region 1 = (upperRegion ∪ lowerRegion) ∪ Z`;
* `endgame` — **the pinch itself**: some region strictly before the pinch already contains an
  essential loop only if the final region does (Pardon: "since `F ∩ int(S)` is an open surface, the
  property of it having a connected component of genus `g` is preserved under sufficiently small
  perturbations of `S`").  This is where the span is allowed to jump. -/
structure PinchFamily (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) where
  /-- the one-parameter family of spheres, with Pardon's local models and dichotomy -/
  sweep : Work.BoxShrink.Bubble.SweepLoopsSmall P
  /-- at time `0` the family is the boundary sphere of the box -/
  zero : sweep.region 0 = Work.BoxShrink.Core.boxRegion P s c σ
  /-- the piece of the surface through which the pinch takes place -/
  Z : Set R3
  /-- it is open in the surface -/
  Z_open : Work.SurgeryInvariance.IsOpenInCarrier P Z
  /-- it contributes nothing to the winding span -/
  Z_span : Work.SurgeryInvariance.WindingSpan P Z = ⊥
  /-- it is disjoint from the two half-regions -/
  Z_disj : Disjoint (Work.BoxShrink.Core.upperRegion P s c σ u ∪
    Work.BoxShrink.Core.lowerRegion P s c σ u) Z
  /-- at time `1` the family is the two half-regions together with that piece -/
  one : sweep.region 1 =
    (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) ∪ Z
  /-- **the endgame at the pinching parameter**: the essential loop of a region strictly before the
  pinch survives to the final region -/
  endgame : ∃ t : ℝ, t < 1 ∧ (P.ContainsEssentialLoop (sweep.region t) →
    P.ContainsEssentialLoop (sweep.region 1))

/-- **Pardon's Lemma 3 (`doublebubble`) from the pinch.**  An essential loop of the region inside
the box persists along the family up to every parameter before the pinch (constancy of the
vanishing of the winding span on `[0,1)`, using Pardon's local models and dichotomy), the endgame
carries it to time `1`, and there the region is the union of the two half-regions and the
zero-span piece `Z`, so one of the two half-regions carries it. -/
theorem bubbleHalf_of_pinchFamily {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : PinchFamily P s c σ u) : Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  have h0 : P.ContainsEssentialLoop (D.sweep.region 0) := by rw [D.zero]; exact hbox
  obtain ⟨t, ht, hend⟩ := D.endgame
  have ht' : P.ContainsEssentialLoop (D.sweep.region t) :=
    D.sweep.containsEssentialLoop_of_lt_one t ht h0
  have h1 : P.ContainsEssentialLoop (D.sweep.region 1) := hend ht'
  rw [D.one] at h1
  exact Work.SurgeryInvariance.double_bubble_persistence_of_zero_span
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)
    D.Z_open D.Z_disj D.Z_span rfl h1

/-! ## The empty piece -/

/-- The empty set is open in the surface. -/
theorem isOpenInCarrier_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.IsOpenInCarrier P (∅ : Set R3) := by
  rw [Work.SurgeryInvariance.IsOpenInCarrier]
  simp

/-- The empty set has vanishing winding span. -/
theorem windingSpan_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.WindingSpan P (∅ : Set R3) = ⊥ := by
  have hv : Work.SurgeryInvariance.windingVectors P (∅ : Set R3) = ∅ := by
    ext v
    simp [Work.SurgeryInvariance.windingVectors]
  rw [Work.SurgeryInvariance.WindingSpan, hv, Submodule.span_empty]

/-! ## Instances of the pinch -/

/-- **The library's isolated input gives the pinch**: `Work.BoxShrink.Bubble.PinchDatum` is exactly
Pardon's family with the *exact* double-bubble endpoint (`Z = ∅`), and its `pinch` field is the
endgame. -/
def pinchFamilyOfPinchDatum {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : Work.BoxShrink.Bubble.PinchDatum P s c σ u) : PinchFamily P s c σ u where
  sweep := D.sweep
  zero := D.zero
  Z := ∅
  Z_open := isOpenInCarrier_empty P
  Z_span := windingSpan_empty P
  Z_disj := by simp
  one := by
    rw [D.one, Set.union_empty]
  endgame := D.pinch

/-- **The degenerate pinch: the box misses the surface.**  Then the region inside the box and the
two half-regions are all empty, and the constant family (no surgery at all) is Pardon's pinch with
`Z = ∅`; Pardon's dichotomy holds because the winding span vanishes. -/
def pinchFamilyOfEmptyBox {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.boxRegion P s c σ = ∅) : PinchFamily P s c σ u where
  sweep :=
    { region := fun _ => Work.BoxShrink.Core.boxRegion P s c σ
      exc := ∅
      regular := fun t _ => ⟨1, one_pos, by simp, fun s _ =>
        Work.SurgeryInvariance.RegionEquivalent.refl (P := P) _⟩
      surgery := by intro t ht; simp at ht
      dichotomy := fun t _ => by
        show Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥ ∨
          Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊤
        rw [h]
        exact Or.inl (windingSpan_empty P) }
  zero := rfl
  Z := ∅
  Z_open := isOpenInCarrier_empty P
  Z_span := windingSpan_empty P
  Z_disj := by simp
  one := by
    change Work.BoxShrink.Core.boxRegion P s c σ =
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ∪ (∅ : Set R3)
    have hu : Work.BoxShrink.Core.upperRegion P s c σ u = ∅ :=
      Set.subset_empty_iff.mp ((Work.BoxShrink.Core.upperRegion_subset P s c σ u).trans h.le)
    have hl : Work.BoxShrink.Core.lowerRegion P s c σ u = ∅ :=
      Set.subset_empty_iff.mp ((Work.BoxShrink.Core.lowerRegion_subset P s c σ u).trans h.le)
    rw [h, hu, hl]
    simp
  endgame := ⟨0, by norm_num, fun h => h⟩

/-- **The pinch when the slice is empty**: the region inside the box is already the union of the two
half-regions, and the constant family is Pardon's pinch with `Z = ∅`.  Pardon's dichotomy at the
initial sphere is the extra input (it is what the counting supplies, see
`Work.BoxShrink.Bubble.pardonDichotomy_boxRegion_of_empty_sphereTrace` for the cases in which it is
a theorem). -/
def pinchFamilyOfEmptySlice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅)
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ)) :
    PinchFamily P s c σ u where
  sweep :=
    { region := fun _ => Work.BoxShrink.Core.boxRegion P s c σ
      exc := ∅
      regular := fun t _ => ⟨1, one_pos, by simp, fun s _ =>
        Work.SurgeryInvariance.RegionEquivalent.refl (P := P) _⟩
      surgery := by intro t ht; simp at ht
      dichotomy := fun t _ => hdich }
  zero := rfl
  Z := ∅
  Z_open := isOpenInCarrier_empty P
  Z_span := windingSpan_empty P
  Z_disj := by simp
  one := by
    change Work.BoxShrink.Core.boxRegion P s c σ =
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ∪ (∅ : Set R3)
    rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u, h]
  endgame := ⟨0, by norm_num, fun h => h⟩

/-- **The pinch when the slice is open in the surface**: the region never changes, and the slice
itself is the zero-span piece through which the pinch passes.  Again Pardon's dichotomy at the
initial sphere is an input. -/
def pinchFamilyOfOpenSlice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P (Work.BoxShrink.Core.sliceRegion P s c σ u))
    (hZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u))
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ)) :
    PinchFamily P s c σ u where
  sweep :=
    { region := fun _ => Work.BoxShrink.Core.boxRegion P s c σ
      exc := ∅
      regular := fun t _ => ⟨1, one_pos, by simp, fun s _ =>
        Work.SurgeryInvariance.RegionEquivalent.refl (P := P) _⟩
      surgery := by intro t ht; simp at ht
      dichotomy := fun t _ => hdich }
  zero := rfl
  Z := Work.BoxShrink.Core.sliceRegion P s c σ u
  Z_open := hopen
  Z_span := (Work.SurgeryInvariance.WindingSpan_eq_bot_iff P _).mpr hZ
  Z_disj := by
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨-, -, hxa⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hx'
    rcases hx with hx | hx
    · have := (Work.BoxShrink.Core.mem_upperRegion.mp hx).2.2; linarith
    · have := (Work.BoxShrink.Core.mem_lowerRegion.mp hx).2.2; linarith
  one := by
    change Work.BoxShrink.Core.boxRegion P s c σ =
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ∪ Work.BoxShrink.Core.sliceRegion P s c σ u
    rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u]
  endgame := ⟨0, by norm_num, fun h => h⟩

/-! ## The link with the library's own isolated input -/

/-- **The library's `PinchDatum` from a pinch with `Z = ∅`.**  This is the converse of
`pinchFamilyOfPinchDatum` (up to the endpoint `Z = ∅`). -/
def BubblePinchDatum_of_pinchFamily {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : PinchFamily P s c σ u) (hZ : D.Z = ∅) :
    Work.BoxShrink.Bubble.PinchDatum P s c σ u where
  sweep := D.sweep
  zero := D.zero
  one := by
    rw [D.one, hZ, Set.union_empty]
  pinch := D.endgame

/-- **Pardon's isolated input of the library gives the pinch input**: the pinch exists wherever
`Work.BoxShrink.Bubble.PardonPinchInput` says it does (with the sphere-trace hypothesis dropped, so
this is a strict weakening of the library's isolated input). -/
theorem pinchInputAll_of_pardonPinchInput (h : Work.BoxShrink.Bubble.PardonPinchInput) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Nonempty (PinchFamily P s c σ u) :=
  fun P s c σ u hS hZ => ⟨pinchFamilyOfPinchDatum (h P s c σ u hS hZ)⟩

/-! ## The residual input of the chapter -/

/-- **The residual input, for all parametrised tori**: Pardon's pinch exists in every
configuration whose sphere and slice traces carry no essential loop. -/
def PinchInputAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    Nonempty (PinchFamily P s c σ u)

/-- **The weakest form of the residual input**: Pardon's pinch exists in every configuration whose
*slice* carries no essential loop, for all parametrised tori.

**WARNING (see `BubbleHalfRefuted.lean` / `SphereTraceEssential.lean`).**  This input — like the `hZ`-only input
`PinchInput` below and the `hZ`-only interface `Work.BoxShrink.Bubble.SmoothHalf` — is **false**:
it implies `SmoothHalf` (`pinchInput_of_pinchInputHZAll` and `smoothHalf_of_pinchInput`), which is
refuted at the standard small box: `Work.BoxShrink.Pinch.BubbleHalfRefuted` proves
`¬ Work.BoxShrink.Bubble.BubbleHalf standard (3/2) 0 (swap 1 2) 0`, which is the conclusion these
inputs would produce, so they are false — and at that configuration the hypothesis `hS` also fails
(`Work.BoxShrink.Pinch.sphereSet_threeHalves_essential`), which is exactly why the interface with
both endpoint hypotheses is not refuted by it.  The hypothesis `hS` on the sphere trace is *not*
redundant.  Use the inputs carrying both endpoint hypotheses: `PinchInputAll`,
`PinchInputSmoothAll`, `PinchInputCounting` (and see `PinchNoJump` of `SliceSpanStep.lean` for the
sharpest form of the remaining one-sided bound). -/
def PinchInputHZAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    Nonempty (PinchFamily P s c σ u)

/-- **The residual input for the smooth tori of the challenge**, which is all the crux needs.

**WARNING.**  This `hZ`-only input is **false**: its conclusion would give
`Work.BoxShrink.Bubble.SmoothHalf`, hence `Work.BoxShrink.Bubble.BubbleHalf standard (3/2) 0
(swap 1 2) 0`, which `Work.BoxShrink.Pinch.BubbleHalfRefuted` refutes; use
`PinchInputSmoothAll` (which also assumes `hS`) instead.  See the warning at `PinchInputHZAll`. -/
def PinchInput : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Nonempty (PinchFamily (Work.Smooth.Morse.torus ψ) s c σ u)

/-- The weakest input gives the `hZ`-only input for the smooth tori. -/
theorem pinchInput_of_pinchInputHZAll (h : PinchInputHZAll) : PinchInput :=
  fun ψ s c σ u hZ => h (Work.Smooth.Morse.torus ψ) s c σ u hZ

/-- The weakest input gives the input used for the all-tori conclusions. -/
theorem pinchInputAll_of_pinchInputHZAll (h : PinchInputHZAll) : PinchInputAll :=
  fun P s c σ u _hS hZ => h P s c σ u hZ

/-- The same input for the smooth tori, with the hypothesis on the sphere trace available as well
(the form in which Pardon's construction is carried out). -/
def PinchInputSmoothAll : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Nonempty (PinchFamily (Work.Smooth.Morse.torus ψ) s c σ u)

theorem pinchInputSmoothAll_of_pinchInputAll (h : PinchInputAll) : PinchInputSmoothAll :=
  fun ψ s c σ u hS hZ => h (Work.Smooth.Morse.torus ψ) s c σ u hS hZ

theorem pinchInputSmoothAll_of_pinchInput (h : PinchInput) : PinchInputSmoothAll :=
  fun ψ s c σ u _ hZ => h ψ s c σ u hZ

theorem pinchInputSmoothAll_of_pardonPinchInput (h : Work.BoxShrink.Bubble.PardonPinchInput) :
    PinchInputSmoothAll :=
  fun ψ s c σ u hS hZ => ⟨pinchFamilyOfPinchDatum (h (Work.Smooth.Morse.torus ψ) s c σ u hS hZ)⟩

/-- **Pardon's Lemma 3 conclusion with both of Pardon's endpoint hypotheses**: the sphere trace and
the slice trace both carry no essential loop.  This is strictly weaker than
`Work.BoxShrink.Bubble.SmoothHalf` (which asks for the conclusion with the sphere-trace hypothesis
dropped), and it is all the crux consumes (`Work.BoxShrink.Pinch.cruxCore_of_smoothHalfS`), since
the crux derives the vanishing of the sphere trace from its counting hypotheses. -/
def SmoothHalfS : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Work.BoxShrink.Bubble.BubbleHalf (Work.Smooth.Morse.torus ψ) s c σ u

/-- The pinch with both endpoint hypotheses gives `SmoothHalfS`. -/
theorem smoothHalfS_of_pinchInputSmoothAll (h : PinchInputSmoothAll) : SmoothHalfS :=
  fun ψ s c σ u hS hZ => bubbleHalf_of_pinchFamily (h ψ s c σ u hS hZ).some

/-- **The corrected field, from the pinch.** -/
theorem pushOffHalf_of_pinchInputAll (h : PinchInputAll) : Work.BoxShrink.Bubble.PushOffHalf :=
  fun P s c σ u _hS hZ => bubbleHalf_of_pinchFamily (h P s c σ u _hS hZ).some

/-- **The restricted input of the challenge, from the pinch.**

**WARNING.**  The *conclusion* of this theorem is false
(`Work.BoxShrink.Pinch.BubbleHalfRefuted` refutes `BubbleHalf` at the standard small box), so its
hypothesis `PinchInput` is false too; the theorem is
recorded only to show that the `hZ`-only interface is *implied* by the `hZ`-only input.  Use
`smoothHalfS_of_pinchInputSmoothAll` (or `smoothHalfS_of_cutOffInputSmooth`) for the usable
statement. -/
theorem smoothHalf_of_pinchInput (h : PinchInput) : Work.BoxShrink.Bubble.SmoothHalf :=
  fun ψ s c σ u hZ => bubbleHalf_of_pinchFamily (h ψ s c σ u hZ).some

/-! ## The input in the form of Pardon's counting

Pardon constructs the family from the counting hypothesis applied to *every* intermediate sphere
of the pinch: `|S_t ∩ β| ≤ |S ∩ β| + 2|D ∩ β| < I(F,β)`, hence (Lemma `mustbeinessential`) every
curve of `S_t ∩ F` is inessential in `F`, and the pinching family exists.  This is strictly more
data than the hypothesis of `BubbleHalf`, so the input below is strictly weaker than `PinchInput`,
and it is the form the paper actually delivers. -/

/-- **The residual input with the counting of Pardon's proof available.**  Every bound of the crux
(`Work.BoxShrink.CruxCore`) is a hypothesis; what is asked for is Pardon's pinch at the
configuration. -/
def PinchInputCounting : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          Nonempty (PinchFamily (Work.Smooth.Morse.torus ψ) s c σ u)

/-- **Pardon's Lemma 3 with the counting of the crux available** — the honest residual input of the
chapter, at the level of the *conclusion*: for every configuration carrying the counting data of
`Work.BoxShrink.CruxCore` (the knot, the distortion bound, the smallness, the swept sphere in
general position, the two counts and the cut-and-paste input), an essential loop of the region inside
the box survives to one of the two half-regions.

Everything else about the crux is *proved* in the sibling chapters: the counting gives the
vanishing of the essential loops on the sphere trace
(`Work.BoxShrink.Core.not_containsEssentialLoop_sphereSet_of_slicing`) and on the slice
(`Work.BoxShrink.Core.not_containsEssentialLoop_sliceRegion`), hence the hypotheses `hS`, `hZ` of
Pardon's Lemma 3; what remains is the lemma itself, whose proof (Pardon's one-parameter family of
spheres) is discussed in `README.md` — its local models cannot be expressed by any of the loop-level
or spatial families of the library (`Work.BoxShrink.Pinch.Warning`), so the field of the corrected
interface has to be the conclusion. -/
def CountingHalf : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          Work.BoxShrink.Bubble.BubbleHalf (Work.Smooth.Morse.torus ψ) s c σ u

/-- **The input whose piece `Z` is empty**, i.e. Pardon's *exact* double bubble (the endpoint
`region 1 = upperRegion ∪ lowerRegion`, without the perturbation of `doublebubble2`): by
`BubblePinchDatum_of_pinchFamily` such a family *is* the library's `Work.BoxShrink.Bubble.PinchDatum`
up to `Z = ∅`. -/
def PinchInputPardon : Type :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    {D : PinchFamily P s c σ u // D.Z = ∅}

end

end Work.BoxShrink.Pinch
