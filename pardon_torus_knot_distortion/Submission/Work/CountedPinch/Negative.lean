import Submission.Work.CountedPinch.Instances
import Submission.Work.BoxShrink.PinchOff.NotTransverse
import Submission.Work.CountedPinch.not_finiteCrossing_std
import Submission.Work.CountedPinch.transverseSlice_std_four
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.Main
import Submission.Work.CountedPinch.tameSlice_standard_equator
import Submission.Work.CountedPinch.not_sliceArcsBody_of_isCompact

/-!
# The counting is not decoration: the residual is false without it

Every residual of this chapter is stated in the *counted* vocabulary — the hypotheses of the crux
(a knot of small distortion whose image is that of the standard `(p,q)` curve, a swept box with an
essential loop, the sphere and plane counts, the cut-and-paste and the general position of the box
sphere).  This module records, in the vocabulary of this chapter, that the hypotheses *cannot be
dropped*: the bodies of the residuals are **false** in general.

* `not_forall_transverseSlice` — the transversality of the cutting plane along the slice is false
  in general: at the tangent configuration of the standard torus (box centre `(1,0,0)`, the
  point at which the plane `{x = 1}` is tangent to the surface, radius `13/10`, `σ = (0 1 2)`)
  the derivative of the plane coordinate vanishes at a point of the slice inside the box
  (`Work.BoxShrink.PinchOff.tangent_not_transverseSlice`).  The workspace's valuation of that
  configuration — the box region carries an essential loop while *both* half-regions are
  inessential (`Work.BoxShrink.PinchOff.tangent_boxSpan_eq_top`,
  `Work.BoxShrink.PinchOff.tangent_halvesSpan_eq_bot`) — shows that the general position is
  exactly the missing hypothesis, and hence that Pardon's count is what has to supply it.
* `not_forall_regionPushOff` — the push-off itself is false at the standard configuration
  `s = 5/2`, `c = 0`, `σ = swap 1 2`, `u = 0` (`Work.PinchFamily.not_regionPushOff_cex`): the box
  region realises the longitude `{z = -1}` while the two halves realise only meridians.  So no
  residual stated without the counting can be *proved* — a reduction to such a statement would be
  worthless.
* `not_forall_sliceGoodBody`, `not_forall_slicePlaneBody` — consequently neither the body of
  `CountedSliceGood` nor that of `CountedSlicePlane` holds at every configuration.
* the two spellings of the residual of this chapter are *complementary*, and neither can be
  weakened to the other:
  * the plane datum contains the workspace's tameness predicate, which **forces the slice to be
    compact** (`isCompact_slice_of_tameSlice`), i.e. the trace does not leave the box — the case in
    which the slice is a finite disjoint union of circles of the surface
    (`Work.BoxShrink.PinchOff.sliceCirclesOnly_of_isCompact`, and the sibling chapter's
    `Work.BoxShrink.PinchOff.tracePerpRealisable_of_isCompact_slice` settles the residual there);
  * the arcs datum, by contrast, **fails at every compact non-empty transverse slice**
    (`Work.CountedPinch.not_sliceArcsBody_of_isCompact`): the arcs are injective images of the
    interval, whose endpoints force a boundary where the slice is locally Euclidean.  So
    `CountedSliceArcs` speaks only about the configurations whose trace leaves the box — the
    generic case, and the case of Pardon's finger move.
  * the *naive* arcs datum (arcs lying in the slice, `SliceCompactArcsBody`) is unusable in the
    other direction: it forces the slice to be compact
    (`isCompact_slice_of_sliceCompactArcsBody`) and hence is refuted at every non-compact slice
    (`not_sliceCompactArcsBody_of_not_isCompact`) — the same finding as the sibling chapter's
    `Work.BoxShrink.PinchOff.not_sliceArcsOnly_of_not_isCompact`.

Finally, the general position of the cutting plane cannot be obtained from the *level* alone: the
workspace proves (`Work.PlaneSlice.not_ae_transversePlane_pardonSlice`) that for the open box the
planar general position fails on a set of plane levels of *positive measure*, so an
almost-everywhere argument cannot replace the counting.  That theorem lives in the sibling
directory and is cited here rather than imported, to keep this chapter's dependency closure small.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.CountedPinch

noncomputable section

/-! ## The transversality is not free -/

/-- **The transversality of the cutting plane along the slice fails in general** (the tangent
configuration of the standard torus, `Work.BoxShrink.PinchOff.not_forall_transverseSlice`). -/
theorem not_forall_transverseSlice :
    ¬ (∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :=
  Work.BoxShrink.PinchOff.not_forall_transverseSlice

/-- **The body of `CountedSliceCrossing`, hence of `CountedSlicePlane` and of `CountedSliceGood`,
is false in general.** -/
theorem not_forall_slicePlaneBody :
    ¬ (∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧
          Work.Smooth.Plane.SlicedPlane (Work.Smooth.Morse.torus ψ)
            (Work.BoxShrink.Core.cutDisc s c σ u)) :=
  fun h => not_forall_transverseSlice fun ψ s c σ u => (h ψ s c σ u).1

/-- **The body of `CountedSliceGood` is false in general** (its first component is the
transversality of the cutting plane). -/
theorem not_forall_sliceGoodBody :
    ¬ (∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧
          Work.BoxShrink.Pinch.TameSlice ψ s c σ u ∧
            ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
              (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u)) :=
  fun h => not_forall_transverseSlice fun ψ s c σ u => (h ψ s c σ u).1

/-! ## The push-off is not free either -/

/-- **The push-off fails at an explicit configuration of the standard torus**: the standard torus,
`s = 5/2`, `c = 0`, `σ = swap 1 2`, `u = 0` (`Work.PinchFamily.not_regionPushOff_cex`).  Hence no
ordinary (`∀`-quantified, un-counted) transport statement can be true, and a reduction to one
would be worthless. -/
theorem not_forall_regionPushOff :
    ¬ (∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.PinchFamily.RegionPushOff P s c σ u) :=
  fun h => Work.PinchFamily.not_regionPushOff_cex
    (h Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0)

/-- The same failure in the vocabulary of the counted shell: the body of `PinchTransport` is not
universally true. -/
theorem not_forall_regionPushOff_on_standard :
    ¬ (∀ (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.PinchFamily.RegionPushOff Work.CoreTopology.standard s c σ u) :=
  fun h => Work.PinchFamily.not_regionPushOff_cex
    (h (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0)

/-! ## The crossing datum of the sibling chapter is false for continuous loops -/

/-- **`FiniteCrossing` fails in general.**  The loops of a box region are only *continuous*, so a
loop can oscillate around the slice infinitely often; `not_finiteCrossing_std` exhibits such a loop
at the standard torus in the box `PBox 4 0 (refl (Fin 3))` with the plane `{z = 1/2}`. -/
theorem not_forall_finiteCrossing :
    ¬ (∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.BoxShrink.PinchOff.FiniteCrossing ψ s c σ u) :=
  fun h => Work.CountedPinch.not_finiteCrossing_std (h _ _ _ _ _)

/-- **The engine hypothesis of the sibling chapter is unsatisfiable.**  At the configuration of
`not_finiteCrossing_std` the cutting plane is transverse (`transverseSlice_std_four`), so the global
statement

```lean
∀ ψ s c σ u, TransverseSlice ψ s c σ u → IsPathConnected (Sigma ψ s c σ u) ∧ FiniteCrossing ψ s c σ u
```

— the hypothesis of `Work.BoxShrink.PinchOff.dropCase_of_finiteCrossing_of_isPathConnected_slice`,
`…keyTameClosed_of_finiteCrossing_of_isPathConnected_slice` and
`…bubbleHalf_of_finiteCrossing_of_isPathConnected_slice`, and of the engine-based assembly of
`Arcs.lean` — is **false**.  Those reductions are therefore vacuous, and the honest content of the
sibling's area is its residual `Work.BoxShrink.PinchOff.DropCase` / `KeyTameClosed` itself. -/
theorem not_forall_transverse_finiteCrossing :
    ¬ (∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
          IsPathConnected (Work.BoxShrink.PinchOff.Sigma ψ s c σ u) ∧
            Work.BoxShrink.PinchOff.FiniteCrossing ψ s c σ u) :=
  fun h => Work.CountedPinch.not_finiteCrossing_std
    (h _ _ _ _ _ transverseSlice_std_four).2

/-! ## The honest arcs datum fails at a concrete compact slice -/

/-- **The arcs datum fails at the two-latitude-circle configuration**: `Work.BoxShrink.PinchOff.idDiffeo`,
the box `PBox 4 0 (refl (Fin 3))` (which contains the whole torus) and the plane `{z = 1/2}`, whose
slice is the two latitude circles `{v = π/6}`, `{v = 5π/6}`.  The plane is transverse there
(`transverseSlice_std_four`), the slice is compact and non-empty (its points are the points of the
inner latitude, `longitudeCurve_mem_cutDisc`), so `not_sliceArcsBody_of_isCompact` applies.  This is
the concrete form of the complementarity of the two routes of this chapter. -/
theorem not_sliceArcsBody_std_equator (β : Work.CoreTopology.ClosedCurve Work.CoreTopology.standard) :
    ¬ SliceArcsBody Work.CoreTopology.standard β 4 (0 : R3) (Equiv.refl (Fin 3)) (1 / 2) :=
  not_sliceArcsBody_of_isCompact (ψ := Work.BoxShrink.PinchOff.idDiffeo)
    transverseSlice_std_four
    (isCompact_slice_of_tameSlice tameSlice_standard_equator)
    ⟨(Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (5 * Real.pi / 6)).γ 0,
      Work.BoxShrink.Core.mem_sliceRegion.mpr
        ⟨(Work.CoreTopology.longitudeCurve Work.CoreTopology.standard
            (5 * Real.pi / 6)).mem 0,
          (Work.BoxShrink.Core.mem_cutDisc.mp
            (longitudeCurve_mem_cutDisc (5 * Real.pi / 6) 0
              Work.CountedPinch.sin_five_pi_div_six)).1,
          (Work.BoxShrink.Core.mem_cutDisc.mp
            (longitudeCurve_mem_cutDisc (5 * Real.pi / 6) 0
              Work.CountedPinch.sin_five_pi_div_six)).2⟩⟩

/-! ## The unrestricted drop datum of the sibling chapter is refuted

`Work.BoxShrink.PinchOff.RefuteDrop.not_dropCase` proves `¬ Work.BoxShrink.PinchOff.DropCase`
(and `¬ KeyTameClosed`) at the explicit configuration `dropDiffeo, dropS, dropC, dropCyc, dropU`,
where the box sphere, the slice and the two half-regions all carry no essential loop and the box
region has rank `2`.  So the sibling's named residual cannot be used as a hypothesis — exactly the
rule "do not reduce to a false statement" — and the counted chapter must use the **counted**
restriction.  This module re-exports the refutation in the vocabulary of this chapter, so that the
status of `Work.CountedPinch.CountedDrop` (the counted restriction, *not* touched by the refutation,
whose configuration carries no knot, distortion bound or counts) is recorded in the same place as
the other negative results. -/

/-- **The unrestricted drop case of the sibling chapter is false.** -/
theorem not_dropCase : ¬ Work.BoxShrink.PinchOff.DropCase :=
  Work.BoxShrink.PinchOff.RefuteDrop.not_dropCase

/-- **The sibling chapter's honest residual `KeyTameClosed` is false as well.** -/
theorem not_keyTameClosed : ¬ Work.BoxShrink.PinchOff.KeyTameClosed :=
  Work.BoxShrink.PinchOff.RefuteDrop.not_keyTameClosed

end

end Work.CountedPinch
