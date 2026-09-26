import Submission.Work.CountedPinch.Routes
import Submission.Work.CountedPinch.transverseSlice_std_four
import Submission.Work.CountedPinch.tameSlice_standard_equator
import Submission.Work.CountedPinch.innermostDiscInput_standard_equator

/-!
# Non-vacuity of the counted residual: configurations whose flat disc misses the surface

This module records the one class of configurations at which the residual `CountedSlicePlane` of
this chapter is *proved* (not assumed): those at which the flat disc `cutDisc s c σ u` cut out of
the box by the cutting plane misses the surface altogether.

There, both components of the residual hold with no geometry at all:

* the cutting plane is transverse along the slice *vacuously* — a tangency point of the plane with
  the surface inside the box would be a surface point of the flat disc;
* the flat disc is sliced by the surface with **no pieces at all**
  (`Work.Smooth.Plane.slicedPlane_of_disjoint`).

Everything else then follows from `Routes.lean`: `CountedSliceGood`, the push-off `PinchTransport`,
the local residual `CountedPinch`, Pardon's Lemma 3 in the counted form, the crux, and — through
the ledger — the challenge.

Note what this certificate does *not* claim: it does not exhibit the counted hypotheses themselves
(a knot of small distortion on the surface, a swept box with an essential loop and the two
intersection counts) at such a configuration — indeed no counted configuration can be exhibited
without proving the challenge itself.  It shows that the residual's body is *inhabited* and that
the chain of this chapter delivers Pardon's Lemma 3 there, exactly as the previous chapters'
non-vacuity certificates do.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.CountedPinch

noncomputable section

/-- **The residual holds when the flat disc misses the surface.**  If at every counted
configuration the flat disc `cutDisc s c σ u` carries no point of the surface, then
`CountedSlicePlane`: transversality is vacuous and the slicing datum of the disc is the empty one.

The hypothesis is deliberately stated in the `ψ`-visible counted shell, i.e. as a `∀`-statement
over the counted data with no reference to the counting itself. -/
theorem countedSlicePlane_of_disjoint
    (h : CountedD fun ψ _ _ _ s c σ u =>
      ∀ x : R3, x ∈ flatDisc s c σ u → x ∉ (Work.Smooth.Morse.torus ψ).carrier) :
    CountedSlicePlane :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let hdisj :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ⟨fun p hB hG => by
        have hmem : Work.BoxShrink.Pinch.par ψ p ∈ flatDisc s c σ u :=
          Work.BoxShrink.Core.mem_cutDisc.mpr
            ⟨(Submission.mem_PBox_iff s c σ _).mpr (by
                rw [← Work.BoxShrink.Pinch.boxB_apply]; exact hB),
              by
                have := hG
                rw [Work.BoxShrink.Pinch.planeG_apply,
                  Work.BoxShrink.Bubble.planeCoord_apply] at this
                linarith⟩
        exact absurd (Work.BoxShrink.Pinch.par_mem_carrier ψ p) (hdisj _ hmem),
      Work.Smooth.Plane.slicedPlane_of_disjoint
        (fun x hx => hdisj x hx)⟩

/-- **Pardon's push-off at every counted configuration whose flat disc misses the surface.** -/
theorem pinchTransport_of_disjoint
    (h : CountedD fun ψ _ _ _ s c σ u =>
      ∀ x : R3, x ∈ flatDisc s c σ u → x ∉ (Work.Smooth.Morse.torus ψ).carrier) :
    PinchTransport :=
  pinchTransport_of_countedSlicePlane (countedSlicePlane_of_disjoint h)

/-- **The local residual at every counted configuration whose flat disc misses the surface.** -/
theorem countedPinch_of_disjoint
    (h : CountedD fun ψ _ _ _ s c σ u =>
      ∀ x : R3, x ∈ flatDisc s c σ u → x ∉ (Work.Smooth.Morse.torus ψ).carrier) :
    CountedPinch :=
  countedPinch_of_countedSlicePlane (countedSlicePlane_of_disjoint h)

/-- **Pardon's Lemma 3 in the counted form, at every counted configuration whose flat disc misses
the surface.** -/
theorem countingHalf_of_disjoint
    (h : CountedD fun ψ _ _ _ s c σ u =>
      ∀ x : R3, x ∈ flatDisc s c σ u → x ∉ (Work.Smooth.Morse.torus ψ).carrier) :
    Work.BoxShrink.Pinch.CountingHalf :=
  countingHalf_of_countedSlicePlane (countedSlicePlane_of_disjoint h)

/-- **The arcs residual holds when the flat disc misses the surface** (the closure of the empty
slice is empty, so the datum holds with no arcs at all). -/
theorem countedSliceArcs_of_disjoint
    (h : CountedD fun ψ _ _ _ s c σ u =>
      ∀ x : R3, x ∈ flatDisc s c σ u → x ∉ (Work.Smooth.Morse.torus ψ).carrier) :
    CountedSliceArcs :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    have hdisj :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    have hempty : slice (Work.Smooth.Morse.torus ψ) s c σ u = ∅ := by
      ext x
      refine ⟨fun hx => ?_, by simp⟩
      obtain ⟨hxc, hxb, hxu⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hx
      exact (hdisj x (Work.BoxShrink.Core.mem_cutDisc.mpr ⟨hxb, hxu⟩)) hxc
    ⟨0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      by rw [hempty]; simp⟩

/-- **The transversality residual holds when the flat disc misses the surface** (vacuously). -/
theorem countedSliceCrossing_of_disjoint
    (h : CountedD fun ψ _ _ _ s c σ u =>
      ∀ x : R3, x ∈ flatDisc s c σ u → x ∉ (Work.Smooth.Morse.torus ψ).carrier) :
    CountedSliceCrossing :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let hdisj :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    fun p hB hG => by
      have hmem : Work.BoxShrink.Pinch.par ψ p ∈ flatDisc s c σ u :=
        Work.BoxShrink.Core.mem_cutDisc.mpr
          ⟨(Submission.mem_PBox_iff s c σ _).mpr (by
              rw [← Work.BoxShrink.Pinch.boxB_apply]; exact hB),
            by
              have := hG
              rw [Work.BoxShrink.Pinch.planeG_apply,
                Work.BoxShrink.Bubble.planeCoord_apply] at this
              linarith⟩
      exact absurd (Work.BoxShrink.Pinch.par_mem_carrier ψ p) (hdisj _ hmem)

/-! ## A non-degenerate configuration in which the arcs datum holds

The honest arcs datum is satisfied at a configuration whose slice is *non-empty* and leaves the open
box: `Work.CountedPinch.sliceArcsBody_standard_local` (in its own module) proves `SliceArcsBody` for
the standard torus, the small box `PBox (1/4) (3,0,0) (refl (Fin 3))` and the plane `{z = 0}`, where
the closure of the slice is a single arc of the outer equator.  Together with the empty-slice
certificates below this shows that the residuals of this chapter are not vacuous in either case.

## A non-degenerate configuration in which the plane datum holds

The two components of the body of `CountedSlicePlane` (except for the strongest, `SlicedPlane`) hold
at a concrete configuration of the standard torus whose slice is *non-empty*: the box
`PBox 4 0 (refl (Fin 3))`, which contains the whole torus, and the plane `{z = 1/2}`, whose trace is
the two latitude circles `{v = π/6}`, `{v = 5π/6}`.  There the plane is transverse
(`Work.CountedPinch.transverseSlice_std_four`) and the slice is tame
(`Work.CountedPinch.tameSlice_standard_equator`); the slice is compact — the case the plane route of
`Routes.lean` covers. -/

/-- **The transversality and tameness of the plane at a concrete non-degenerate configuration.** -/
theorem sliceCrossing_and_tame_std :
    Work.BoxShrink.Pinch.TransverseSlice Work.BoxShrink.PinchOff.idDiffeo 4
        (0 : R3) (Equiv.refl (Fin 3)) (1 / 2) ∧
      Work.BoxShrink.Pinch.TameSlice Work.BoxShrink.PinchOff.idDiffeo 4
        (0 : R3) (Equiv.refl (Fin 3)) (1 / 2) :=
  ⟨transverseSlice_std_four, tameSlice_standard_equator⟩

/-- **The whole body of `CountedPlaneInput` (its three components) at the concrete
non-degenerate configuration of `sliceCrossing_and_tame_std`**: the plane is transverse along the
slice, the slice is tame, and the flat disc is innermost-complete. -/
theorem planeInputBody_std :
    Work.BoxShrink.Pinch.TransverseSlice Work.BoxShrink.PinchOff.idDiffeo 4
        (0 : R3) (Equiv.refl (Fin 3)) (1 / 2) ∧
      Work.BoxShrink.Pinch.TameSlice Work.BoxShrink.PinchOff.idDiffeo 4
        (0 : R3) (Equiv.refl (Fin 3)) (1 / 2) ∧
      Work.InnermostDisk.InnermostDiscInput Work.CoreTopology.standard
        (Work.BoxShrink.Core.cutDisc 4 (WithLp.toLp 2 (![0, 0, 0] : Fin 3 → ℝ))
          (Equiv.refl (Fin 3)) (1 / 2)) :=
  ⟨transverseSlice_std_four, tameSlice_standard_equator, innermostDiscInput_standard_equator⟩

end

end Work.CountedPinch
