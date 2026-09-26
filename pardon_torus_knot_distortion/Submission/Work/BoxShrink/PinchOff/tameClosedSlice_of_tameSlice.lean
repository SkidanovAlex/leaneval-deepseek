import Mathlib
import Submission.Work.BoxShrink.PinchOff.PerpBox
import Submission.Work.BoxShrink.PinchOff.OpenArcs
import Submission.Work.BoxShrink.Pinch.Basic
import Submission.Work.BoxShrink.PinchOff.SliceCover

/-!
# The bridge from `TameSlice` to the honest tameness predicate `TameClosedSlice`

`Work.BoxShrink.Pinch.TameSlice ψ s c σ u` is a `Work.Smooth.Plane.TransversePlane` datum for the
flat disc `cutDisc s c σ u` cut out of the box by the plane; its pieces (arcs and circles of the
surface) are required to lie in the disc, hence in the slice `Σ = F ∩ PBox s c σ ∩ {G = 0}`.

The honest predicate `Work.BoxShrink.PinchOff.TameClosedSlice` asks for the same pieces, but only
that they lie in, and cover, the *closure* of the slice `Σ`.

The two are equivalent here because `TameSlice` **forces `Σ` to be compact**
(`Work.BoxShrink.PinchOff.isCompact_sliceRegion_of_tameSlice`): the slice is the finite union of
the images of the pieces of the datum, each of which is compact (the arcs are parametrised over the
compact interval `[0,1]`, the circles are compact ranges).  A compact subset of `ℝ³` is closed, so
`closure Σ = Σ`, and the pieces of the datum lie in the disc; restricted to the surface they lie in
`Σ = F ∩ cutDisc` and cover it.  Hence they are a witness for `TameClosedSlice`.

**This bridge is the reason a `TameSlice` configuration cannot exhibit the geometric case Pardon's
Lemma 3 is about** (arcs of the trace running to the box sphere, open at their ends); see the
discussion in `OpenArcs.lean` and `ResidualHolds.lean`.  It is recorded here because the box-local
residual `Work.BoxShrink.PinchOff.TracePerpSliceBox` (and hence `KeyTame`) consumes the honest
predicate, and the parent chapter's tameness hypothesis has to be discharged into it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **`TameSlice` gives the honest tameness predicate `TameClosedSlice`.**  The pieces of the
tameness datum for the flat disc lie in `Σ = F ∩ cutDisc` (they lie on the surface and in the disc)
and cover it, so they cover `closure Σ`; and since they make `Σ` a finite union of compact sets,
`Σ` is closed, so `closure Σ = Σ`. -/
theorem tameClosedSlice_of_tameSlice (ψ : Submission.Diffeo) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (h : Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    Work.BoxShrink.PinchOff.TameClosedSlice ψ s c σ u := by
  classical
  have hT : Work.BoxShrink.Pinch.TameSlice ψ s c σ u := h
  obtain ⟨ι, hι, c', κ, hκ, a, hsimple, hdisj, hmem, ha_inj, ha_mem, ha_surf, ha_disj, hac_disj,
    hcover⟩ := h
  have hcpt : IsCompact (Sigma ψ s c σ u) := isCompact_sliceRegion_of_tameSlice hT
  have hcl : closure (Sigma ψ s c σ u) = Sigma ψ s c σ u := hcpt.isClosed.closure_eq
  have hseq : Sigma ψ s c σ u =
      (surface ψ).carrier ∩ Work.BoxShrink.Core.cutDisc s c σ u :=
    Work.BoxShrink.Core.sliceRegion_eq_carrier_inter_cutDisc (surface ψ) s c σ u
  refine ⟨κ, hκ, a, Fintype.card ι, fun i => c' ((Fintype.equivFin ι).symm i), ?_, ?_, ?_⟩
  · intro j t
    rw [hcl, hseq]
    exact ⟨ha_surf j t, ha_mem j t⟩
  · intro i t
    rw [hcl, hseq]
    exact ⟨(c' ((Fintype.equivFin ι).symm i)).mem t,
      hmem ((Fintype.equivFin ι).symm i) t⟩
  · intro x hx
    rw [hcl, hseq] at hx
    obtain ⟨hxc, hxD⟩ := hx
    rcases hcover x hxD hxc with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact Or.inr ⟨Fintype.equivFin ι i, by simpa using hi⟩
    · exact Or.inl ⟨j, hj⟩

end

end Work.BoxShrink.PinchOff
