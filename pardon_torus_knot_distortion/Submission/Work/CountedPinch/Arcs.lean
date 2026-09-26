import Submission.Work.CountedPinch.Routes
import Submission.Work.CountedPinch.not_containsEssentialLoop_of_arcs
import Submission.Work.CountedPinch.transversePlane_of_arcs
import Submission.Work.BoxShrink.PinchOff.OpenArcs
import Submission.Work.BoxShrink.PinchOff.SliceConnected
import Submission.Work.BoxShrink.PinchOff.KeyTameClosed

/-!
# The honest arcs route: the slice is a finite disjoint union of arcs closed at the ends

This module carries the second route of the chapter, the one that does *not* need the slice to be
compact.  At a counted configuration at which the closure of the slice is a finite disjoint union
of embedded arcs of the surface (`CountedSliceArcs`) and the cutting plane is transverse
(`CountedSliceCrossing`), we have, with **no counting argument for the slice**:

* the inessentiality of the slice (`no_essential_of_sliceArcsBody`): the image of a closed curve is
  connected, a connected set covered by finitely many pairwise disjoint compact sets lies in one of
  them, and a loop lying in an arc of the surface is inessential
  (`Work.Smooth.Plane.Slicing.not_isEssential_of_range_subset_arc`);
* the honest tameness `Work.BoxShrink.PinchOff.TameClosedSlice` (`tameClosedSlice_of_sliceArcsBody`),
  whose arcs are closed at the ends and may run to the box sphere.

On this route the counting is used only for the *sphere* trace: the general position of the box
sphere (`SlicedSphere`), the cut-and-paste (`CleansDiscs`) and the sphere count, all hypotheses of
the counted configuration, give `¬ ContainsEssentialLoop (SphereTrace s c σ)` by Pardon's Lemma 2
(`sphereTrace_inessential_of_counts`).  With that, and with the sibling chapter's general position
of the loops (`FiniteCrossing` and path connectedness of the slice) and its carried classical input
`BoxSliceNice`, the sibling's engine
`Work.BoxShrink.PinchOff.bubbleHalf_of_finiteCrossing_of_isPathConnected_slice` gives Pardon's
Lemma 3 in the counted form, `countingHalf_of_countedSliceArcs`.

`Arcs.lean` also records, machine-checked, *why* the arcs of the datum must be closed at the ends:
the naive version (`SliceCompactArcsBody`, the arcs lying in the slice) makes the slice compact
(`isCompact_slice_of_sliceCompactArcsBody`) and hence fails at every configuration whose slice is
not compact (`not_sliceCompactArcsBody_of_not_isCompact`) — the same finding as the sibling's
`Work.BoxShrink.PinchOff.not_sliceArcsOnly_of_not_isCompact`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.CountedPinch

noncomputable section

/-! ## The closure of the slice lies on the surface -/

theorem closure_slice_subset_carrier (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closure (slice (Work.Smooth.Morse.torus ψ) s c σ u) ⊆ (Work.Smooth.Morse.torus ψ).carrier :=
  closure_minimal (fun _ hx => (Work.BoxShrink.Core.mem_sliceRegion.mp hx).1)
    (Work.Smooth.Morse.Surface.isCompact_torus ψ).isClosed

/-! ## The inessentiality and the tameness of the slice, from the arc structure -/

/-- **The slice carries no essential loop, from the arc structure alone**: a loop of the surface
inside the slice lies inside its closure, hence (by connectedness, the arcs being finitely many
compact pairwise disjoint sets) inside a single arc, where
`Work.Smooth.Plane.Slicing.not_isEssential_of_range_subset_arc` makes it inessential. -/
theorem no_essential_of_sliceArcsBody {ψ : Submission.Diffeo}
    {β : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)}
    {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : SliceArcsBody (Work.Smooth.Morse.torus ψ) β s c σ u) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (slice (Work.Smooth.Morse.torus ψ) s c σ u) := by
  obtain ⟨n, a, hinj, hmem, hdisj, hcov⟩ := h
  have hcar := closure_slice_subset_carrier ψ s c σ u
  have hno := not_containsEssentialLoop_of_arcs (P := Work.Smooth.Morse.torus ψ)
    (D := closure (slice (Work.Smooth.Morse.torus ψ) s c σ u)) a hinj
    (fun j x => hcar (hmem j x)) hdisj (fun x hx _ => Set.mem_iUnion.mp (hcov hx))
  intro hcon
  obtain ⟨γ, hess, hγ⟩ := hcon
  exact hno ⟨γ, hess, fun t => subset_closure (hγ t)⟩

/-- **The honest tameness `TameClosedSlice` of the sibling chapter, from the arc structure.** -/
theorem tameClosedSlice_of_sliceArcsBody {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {β : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)}
    (h : SliceArcsBody (Work.Smooth.Morse.torus ψ) β s c σ u) :
    Work.BoxShrink.PinchOff.TameClosedSlice ψ s c σ u := by
  obtain ⟨n, a, _hinj, hmem, _hdisj, hcov⟩ := h
  exact ⟨Fin n, inferInstance, a, 0, Fin.elim0, hmem, (fun i => i.elim0), fun x hx =>
    Or.inl (Set.mem_iUnion.mp (hcov hx))⟩

/-! ## The naive datum is unusable: it forces the slice to be compact -/

/-- **The naive arcs datum forces the slice to be compact** (a finite union of compact images of the
interval contains an open set only if it is compact). -/
theorem isCompact_slice_of_sliceCompactArcsBody {P : Work.CoreTopology.ParamTorus}
    {β : Work.CoreTopology.ClosedCurve P} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : SliceCompactArcsBody P β s c σ u) : IsCompact (slice P s c σ u) := by
  obtain ⟨n, a, _hinj, hmem, hmemD, _hdisj, hcov⟩ := h
  have hunion : (⋃ j, Set.range (a j)) = slice P s c σ u := by
    refine Set.Subset.antisymm ?_ hcov
    intro x hx
    obtain ⟨j, x', hx'⟩ := Set.mem_iUnion.mp hx
    rw [← hx']
    exact Work.BoxShrink.Core.mem_sliceRegion.mpr
      ⟨hmem j x', (Work.BoxShrink.Core.mem_cutDisc.mp (hmemD j x')).1,
        (Work.BoxShrink.Core.mem_cutDisc.mp (hmemD j x')).2⟩
  rw [← hunion]
  exact isCompact_iUnion fun j => isCompact_range (a j).continuous

/-- **The naive arcs datum fails at every configuration whose slice is not compact** — for instance
at every configuration at which the trace of the cutting plane leaves the box through a point of the
box sphere, since the box is open and such a point is a limit point of the slice. -/
theorem not_sliceCompactArcsBody_of_not_isCompact {P : Work.CoreTopology.ParamTorus}
    {β : Work.CoreTopology.ClosedCurve P} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ¬ IsCompact (slice P s c σ u)) : ¬ SliceCompactArcsBody P β s c σ u :=
  fun hA => h (isCompact_slice_of_sliceCompactArcsBody hA)

/-! ## The naive datum is a special case of the honest one (at a compact slice) -/

/-- **Every instance of the naive datum is an instance of the honest one.**  The arcs of the naive
datum lie in the flat disc, hence on the slice; their union is compact, so the slice is compact and
therefore closed, so the arcs also cover its closure. -/
theorem sliceArcsBody_of_sliceCompactArcsBody {P : Work.CoreTopology.ParamTorus}
    {β : Work.CoreTopology.ClosedCurve P} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : SliceCompactArcsBody P β s c σ u) : SliceArcsBody P β s c σ u := by
  obtain ⟨n, a, hinj, hmem, hmemD, hdisj, hcov⟩ := h
  refine ⟨n, a, hinj, fun j x => ?_, hdisj, ?_⟩
  · refine subset_closure ?_
    exact (Work.BoxShrink.Core.mem_sliceRegion.mpr
      ⟨hmem j x, (Work.BoxShrink.Core.mem_cutDisc.mp (hmemD j x)).1,
        (Work.BoxShrink.Core.mem_cutDisc.mp (hmemD j x)).2⟩)
  · have hcl : IsClosed (slice P s c σ u) :=
      (isCompact_slice_of_sliceCompactArcsBody (β := β) ⟨n, a, hinj, hmem, hmemD, hdisj, hcov⟩).isClosed
    rw [hcl.closure_eq]
    exact hcov

/-! ## The arcs route to Pardon's Lemma 3 in the counted form -/

/-- **Pardon's Lemma 3 in the counted form, from the arc structure of the slice.**

The counting is used only for the *sphere* trace: the general position of the box sphere
(`SlicedSphere`), the cut-and-paste and the sphere count of the counted configuration give
`¬ ContainsEssentialLoop (SphereTrace s c σ)` (`Work.PinchCounted.sphereTrace_inessential_of_counts`).
The slice's inessentiality and its honest tameness come from the arc structure
(`no_essential_of_sliceArcsBody`, `tameClosedSlice_of_sliceArcsBody`), and the two global
general-position inputs — `Work.BoxShrink.Pinch.BoxSliceNice` and the crossing datum of the sibling
chapter (`FiniteCrossing` together with path connectedness of the slice at every transverse
configuration) — are those of the sibling's engine.

**Warning.**  The engine's second hypothesis is a *global* statement containing `FiniteCrossing`,
which is **false** at generic configurations (`Work.CountedPinch.not_finiteCrossing_std`: a
continuous loop can oscillate around the slice infinitely often).  This assembly is therefore
*vacuous*; use the `DropCase`-based route of the next section instead. -/
theorem bubbleHalf_of_sliceArcsBody
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hgp : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      IsPathConnected (Work.BoxShrink.PinchOff.Sigma ψ s c σ u) ∧
        Work.BoxShrink.PinchOff.FiniteCrossing ψ s c σ u)
    {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (β : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ))
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hA : SliceArcsBody (Work.Smooth.Morse.torus ψ) β s c σ u)
    (hS : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s)) :
    Work.BoxShrink.Bubble.BubbleHalf (Work.Smooth.Morse.torus ψ) s c σ u :=
  Work.BoxShrink.PinchOff.bubbleHalf_of_finiteCrossing_of_isPathConnected_slice hnice hgp
    ψ s c σ u hT (tameClosedSlice_of_sliceArcsBody hA) hS (no_essential_of_sliceArcsBody hA)

/-- **Pardon's Lemma 3 in the counted form, from the arc structure of the slice.**  At every
counted configuration the sphere trace is inessential by Pardon's Lemma 2 and the sphere count, and
the slice's inessentiality and tameness come from the arc structure; the sibling's engine concludes
Pardon's conclusion. -/
theorem countingHalf_of_countedSliceArcs
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hgp : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      IsPathConnected (Work.BoxShrink.PinchOff.Sigma ψ s c σ u) ∧
        Work.BoxShrink.PinchOff.FiniteCrossing ψ s c σ u)
    (hcross : CountedSliceCrossing) (hA : CountedSliceArcs) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    bubbleHalf_of_sliceArcsBody hnice hgp
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q))
      (hcross p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)
      (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)
      (Work.PinchCounted.sphereTrace_inessential_of_counts p q hp hq hc ψ K hd himg hsmall
        (lt_trans hr hrs) c σ hslice hcl hS)

/-- **The crux of the challenge from the arc structure of the slice.** -/
theorem cruxCore_of_countedSliceArcs
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hgp : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      IsPathConnected (Work.BoxShrink.PinchOff.Sigma ψ s c σ u) ∧
        Work.BoxShrink.PinchOff.FiniteCrossing ψ s c σ u)
    (hcross : CountedSliceCrossing) (hA : CountedSliceArcs) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_countedSliceArcs hnice hgp hcross hA)

/-- **Pardon's shrinking step from the arc structure of the slice** (with the remaining classical
input: the cut-and-paste). -/
theorem boxShrink_of_countedSliceArcs
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hgp : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      IsPathConnected (Work.BoxShrink.PinchOff.Sigma ψ s c σ u) ∧
        Work.BoxShrink.PinchOff.FiniteCrossing ψ s c σ u)
    (hcross : CountedSliceCrossing) (hA : CountedSliceArcs)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_countingHalf hpush
    (countingHalf_of_countedSliceArcs hnice hgp hcross hA)

/-- **Pardon's theorem from the arc structure of the slice** (with the remaining classical input:
the cut-and-paste `Work.Topology.Classical.PushThroughInnermost`). -/
theorem pardon_torus_knot_distortion_of_countedSliceArcs
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hgp : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      IsPathConnected (Work.BoxShrink.PinchOff.Sigma ψ s c σ u) ∧
        Work.BoxShrink.PinchOff.FiniteCrossing ψ s c σ u)
    (hcross : CountedSliceCrossing) (hA : CountedSliceArcs)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, countingHalf_of_countedSliceArcs hnice hgp hcross hA⟩

/-! ## The arcs route to Pardon's Lemma 3, on the sibling's residual

**Warning (do not use the theorems of this section).**  The theorems below are stated with the
sibling chapter's residual `Work.BoxShrink.PinchOff.DropCase`, and that residual is **refuted** in
the sibling chapter: `Work.BoxShrink.PinchOff.RefuteDrop.not_dropCase : ¬ DropCase` (and
`…not_keyTameClosed : ¬ KeyTameClosed`), at the explicit configuration `dropDiffeo, dropS, dropC,
dropCyc, dropU`, where all five hypotheses of `DropCase` hold and the box region has rank `2`.  So
the theorems of this section are *vacuous*.  They are kept for the record, as the vacuous shadow of
the live route which uses the **counted** restriction `Work.CountedPinch.CountedDrop` of the drop
datum (see the next section).

Contrast the *engine-based* assembly further below (`bubbleHalf_of_sliceArcsBody`,
`countingHalf_of_countedSliceArcs`), which invokes the sibling's
`Work.BoxShrink.PinchOff.bubbleHalf_of_finiteCrossing_of_isPathConnected_slice` and therefore needs
the *global* hypothesis `∀ ψ s c σ u, TransverseSlice → IsPathConnected (Sigma) ∧ FiniteCrossing`.
That hypothesis is **false** — `not_finiteCrossing_std` refutes `FiniteCrossing` at a concrete
configuration of the standard torus (a loop can oscillate infinitely often around the slice, since
`ClosedCurve` is only continuous) — so the engine-based assembly, and with it the sibling's
`…_of_finiteCrossing_of_isPathConnected_slice` reductions, are *vacuous*.  They are kept for the
record; the theorems below are the ones to use. -/

/-- **Pardon's conclusion at a single configuration, from the arc structure, on the sibling's
residual `DropCase`.** -/
theorem bubbleHalf_of_sliceArcsBody_dropCase
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hdrop : Work.BoxShrink.PinchOff.DropCase)
    {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (β : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ))
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hA : SliceArcsBody (Work.Smooth.Morse.torus ψ) β s c σ u)
    (hS : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s)) :
    Work.BoxShrink.Bubble.BubbleHalf (Work.Smooth.Morse.torus ψ) s c σ u :=
  Work.BoxShrink.PinchOff.bubbleHalf_of_keyTameClosed hnice
    (Work.BoxShrink.PinchOff.keyTameClosed_of_dropCase hdrop)
    ψ s c σ u hT (tameClosedSlice_of_sliceArcsBody hA) hS (no_essential_of_sliceArcsBody hA)

/-- **Pardon's Lemma 3 in the counted form, from the arc structure and the sibling's residual
`DropCase`.**  The sphere trace is inessential by Pardon's Lemma 2 and the sphere count of the
counted configuration; the arc structure gives the inessentiality of the slice and the honest
tameness; `DropCase` is the remaining pure pinch statement. -/
theorem countingHalf_of_countedSliceArcs_dropCase
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hdrop : Work.BoxShrink.PinchOff.DropCase)
    (hcross : CountedSliceCrossing) (hA : CountedSliceArcs) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    bubbleHalf_of_sliceArcsBody_dropCase hnice hdrop
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q))
      (hcross p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)
      (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)
      (Work.PinchCounted.sphereTrace_inessential_of_counts p q hp hq hc ψ K hd himg hsmall
        (lt_trans hr hrs) c σ hslice hcl hS)

/-- **The crux of the challenge from the arc structure and `DropCase`.** -/
theorem cruxCore_of_countedSliceArcs_dropCase
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hdrop : Work.BoxShrink.PinchOff.DropCase)
    (hcross : CountedSliceCrossing) (hA : CountedSliceArcs) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf
    (countingHalf_of_countedSliceArcs_dropCase hnice hdrop hcross hA)

/-- **Pardon's theorem from the arc structure and `DropCase`.** -/
theorem pardon_torus_knot_distortion_of_countedSliceArcs_dropCase
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hdrop : Work.BoxShrink.PinchOff.DropCase)
    (hcross : CountedSliceCrossing) (hA : CountedSliceArcs)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, countingHalf_of_countedSliceArcs_dropCase hnice hdrop hcross hA⟩

/-! ## The live arcs route: the *counted* drop case

The sibling chapter's residuals `DropCase`/`KeyTameClosed` are refuted in that chapter
(`Work.BoxShrink.PinchOff.RefuteDrop.not_dropCase`, `…not_keyTameClosed` — see the module docstring
of `Defs.lean`), so the `DropCase`-based assembly of the previous section is vacuous.  The
*counted restriction*
`Work.CountedPinch.CountedDrop` is not touched by that refutation (its configuration carries no
counting data), and it is the residual of the live arcs route:

```
CountedSliceArcs + CountedSliceCrossing + CountedDrop + BoxSliceNice
        ↓ tameClosedSlice_of_sliceArcsBody, no_essential_of_sliceArcsBody,
          sphereTrace_inessential_of_counts (the sphere count)
   TransverseSlice + TameClosedSlice + hZ + hS  ⟹  the counted drop datum applies
        ↓ bubbleHalf_of_dropBody (Pardon's dichotomy at the box region)
   BubbleHalf = CountingHalf ─→ CruxCore ─→ BoxShrinkStatement ─→ the challenge
``` -/

/-- **Pardon's conclusion at a single configuration, from the drop datum and the dichotomy.**  At a
configuration whose box sphere (`hS`) and slice (`hZ`) carry no essential loop and whose box region
is in general position (`hnice`, i.e. `Work.BoxShrink.Pinch.BoxSliceNice`), the drop datum — the
dimension bound in the case where the two halves are inessential — forces one of the two
half-regions to carry an essential loop as soon as the box region does.

This is the argument of `Work.BoxShrink.PinchOff.bubbleHalf_of_keyTameClosed`, with the *counted*
drop datum `DropBody` in place of the refuted `KeyTameClosed`. -/
theorem bubbleHalf_of_dropBody
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hdrop : DropBody ψ s c σ u)
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hTa : Work.BoxShrink.PinchOff.TameClosedSlice ψ s c σ u)
    (hS : ¬ (Work.BoxShrink.PinchOff.surface ψ).ContainsEssentialLoop
      (Work.BoxShrink.PinchOff.SphereTrace s c σ))
    (hZ : ¬ (Work.BoxShrink.PinchOff.surface ψ).ContainsEssentialLoop
      (Work.BoxShrink.PinchOff.Sigma ψ s c σ u)) :
    Work.BoxShrink.Bubble.BubbleHalf (Work.BoxShrink.PinchOff.surface ψ) s c σ u := by
  intro hbox
  by_contra hno
  have hdich := Work.BoxShrink.PinchOff.pardonDichotomy_boxRegion (ψ := ψ) (s := s) (c := c)
    (σ := σ) (hnice ψ s c σ) hS
  have htop : Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
      (Work.BoxShrink.PinchOff.Omega ψ s c σ) = ⊤ := by
    rcases hdich with hbot | htop
    · exact absurd hbox ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mp hbot)
    · exact htop
  have hfin2 : Module.finrank ℚ
      ↥(Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
        (Work.BoxShrink.PinchOff.Omega ψ s c σ)) = 2 := by
    rw [htop, finrank_top, Module.finrank_prod]
    simp
  have hhalvesBot : Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
      (Work.BoxShrink.PinchOff.Halves ψ s c σ u) = ⊥ := by
    rw [Work.BoxShrink.PinchOff.Halves, Work.SurgeryInvariance.Span.union_eq_sup
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion (Work.BoxShrink.PinchOff.surface ψ) s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion (Work.BoxShrink.PinchOff.surface ψ) s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion (Work.BoxShrink.PinchOff.surface ψ)
        s c σ u)]
    have hup : Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
        (Work.BoxShrink.Core.upperRegion (Work.BoxShrink.PinchOff.surface ψ) s c σ u) = ⊥ :=
      (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mpr (fun h => hno (Or.inl h))
    have hlo : Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
        (Work.BoxShrink.Core.lowerRegion (Work.BoxShrink.PinchOff.surface ψ) s c σ u) = ⊥ :=
      (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mpr (fun h => hno (Or.inr h))
    rw [hup, hlo, sup_bot_eq]
  have hle := hdrop hT hTa hS hZ hhalvesBot
  rw [hfin2] at hle
  omega

/-- **Pardon's Lemma 3 in the counted form, from the arc structure and the counted drop case.**  The
sphere trace is inessential by Pardon's Lemma 2 and the sphere count of the counted configuration,
the arc structure gives the inessentiality of the slice and the honest tameness, `BoxSliceNice` is the
sibling chapter's carried classical input, and `CountedDrop` is the remaining pure pinch statement at
the counted configurations. -/
theorem countingHalf_of_countedSliceArcs_countedDrop
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hdrop : CountedDrop)
    (hcross : CountedSliceCrossing) (hA : CountedSliceArcs) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    bubbleHalf_of_dropBody hnice
      (hdrop p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)
      (hcross p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)
      (tameClosedSlice_of_sliceArcsBody
        (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU))
      (Work.PinchCounted.sphereTrace_inessential_of_counts p q hp hq hc ψ K hd himg hsmall
        (lt_trans hr hrs) c σ hslice hcl hS)
      (no_essential_of_sliceArcsBody
        (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU))

/-- **The crux of the challenge from the arc structure and the counted drop case.** -/
theorem cruxCore_of_countedSliceArcs_countedDrop
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hdrop : CountedDrop)
    (hcross : CountedSliceCrossing) (hA : CountedSliceArcs) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf
    (countingHalf_of_countedSliceArcs_countedDrop hnice hdrop hcross hA)

/-- **Pardon's theorem from the arc structure and the counted drop case.** -/
theorem pardon_torus_knot_distortion_of_countedSliceArcs_countedDrop
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hdrop : CountedDrop)
    (hcross : CountedSliceCrossing) (hA : CountedSliceArcs)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, countingHalf_of_countedSliceArcs_countedDrop hnice hdrop hcross hA⟩

/-! ## The compact direction of the arcs discussion

For completeness, the same lemmas give the *compact* direction as well: if finitely many pairwise
disjoint arcs lying in the flat disc cover the slice, then the plane is transverse along the slice,
the tameness `TameSlice` of the workspace holds (`transversePlane_of_arcs`), the slice carries no
essential loop, and the capstone gives the push-off — with **no counting at all**.  This direction is
*not* the arcs route of §3.2 of the README (its hypothesis forces the slice to be compact,
`isCompact_slice_of_sliceCompactArcsBody`); it is recorded because it is the honest link between the
compact case of the plane route and the arc vocabulary. -/

/-- **Pardon's push-off from a finite arc cover of the slice lying in the flat disc, with no
counting.** -/
theorem regionPushOff_of_arcsData {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {n : ℕ}
    (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3))
    (hinj : ∀ j : Fin n, Function.Injective (a j))
    (hmem : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ (Work.Smooth.Morse.torus ψ).carrier)
    (hmemD : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval), a j x ∈ flatDisc s c σ u)
    (hdisj : Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j')))
    (hcov : slice (Work.Smooth.Morse.torus ψ) s c σ u ⊆ ⋃ j, Set.range (a j))
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :
    Work.PinchFamily.RegionPushOff (Work.Smooth.Morse.torus ψ) s c σ u := by
  have hcovD : ∀ x : R3, x ∈ flatDisc s c σ u → x ∈ (Work.Smooth.Morse.torus ψ).carrier →
      ∃ j : Fin n, x ∈ Set.range (a j) :=
    fun x hx hxc => Set.mem_iUnion.mp (hcov (Work.BoxShrink.Core.mem_sliceRegion.mpr
      ⟨hxc, (Work.BoxShrink.Core.mem_cutDisc.mp hx).1,
        (Work.BoxShrink.Core.mem_cutDisc.mp hx).2⟩))
  have hno : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (flatDisc s c σ u) :=
    not_containsEssentialLoop_of_arcs a hinj hmem hdisj hcovD
  refine Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice hT
    (transversePlane_of_arcs a hinj hmem hmemD hdisj hcovD) ?_
  intro hcon
  obtain ⟨γ, hess, hγ⟩ := hcon
  exact hno ⟨γ, hess, fun t => Work.BoxShrink.Core.mem_cutDisc.mpr
    ⟨(Work.BoxShrink.Core.mem_sliceRegion.mp (hγ t)).2.1,
      (Work.BoxShrink.Core.mem_sliceRegion.mp (hγ t)).2.2⟩⟩

end

end Work.CountedPinch
