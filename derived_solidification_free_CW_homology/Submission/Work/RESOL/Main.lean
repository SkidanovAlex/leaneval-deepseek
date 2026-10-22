/-
AREA RESOL — functorial solid-cofibrant resolutions.

# Main results of the area

* `Work.RESOL.resolution_prop` (**the deliverable**)
  : `Submission.Blueprint.ResolutionProp`, assuming `AtomProp` (the analytic input, proved in
  AREA ATOM) and `ToolkitProp`.

The proof is assembled from three independent layers.

* **B4** `Work.RESOL.cofibrantClosure` (`RESOL/Closure.lean`): the class of solid-cofibrant
  complexes is closed under isomorphisms in `K(LightCondAb)`, shifts, mapping cones and small
  coproducts.  This is the structure `Work.RESOL.CofibrantClosure`.

* **B5** `Work.RESOL.solidCofibrant_of_boundedAbove_atomic`
  (`RESOL/solidCofibrant_of_boundedAbove_atomic.lean`): a complex of atoms which is bounded above
  is solid-cofibrant.

* **B6**, the functorial resolution, in three steps:
  * `Work.RESOL.hasAtomicCoverZero` (`RESOL/AtomicCoverZero.lean`) gives a functorial epimorphism
    onto every light condensed abelian group from a small sum of atoms, whose functor preserves
    zero morphisms (this is what makes the double complex of degreewise resolutions a double
    complex);
  * `Work.RESOL.hasBoundedResolutionZero` (`RESOL/hasBoundedResolutionZero.lean`) turns this into a
    functorial degreewise resolution `R` of bounded-above complexes by complexes of atoms, with
    `R B ⟶ B` a quasi-isomorphism and `R B` solid-cofibrant;
  * `Work.RESOL.hasFunctorialResolution_of_bounded`
    (`RESOL/hasFunctorialResolution_of_bounded.lean`) telescopes `R` applied to the two-sided
    brutal truncations of an arbitrary complex, producing the functorial solid-cofibrant
    resolution.

The second conjunct of `ResolutionProp` (K-projective complexes are solid-cofibrant) is
`Work.RESOL.solidCofibrant_of_isKProjective` in `RESOL/Basic.lean`.
-/
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.Instances
import Submission.Work.RESOL.Closure
import Submission.Work.RESOL.AtomicCoverZero
import Submission.Work.RESOL.solidCofibrant_of_boundedAbove_atomic
import Submission.Work.RESOL.hasBoundedResolutionZero
import Submission.Work.RESOL.hasFunctorialResolution_of_bounded

noncomputable section

namespace Work.RESOL

/-- **B5**, in the form used by the construction. -/
theorem boundedAbove_atomic_solidCofibrant (hA : Submission.Blueprint.AtomProp) :
    ∀ (K : Cpx), IsBoundedAbove K → HasAtomicTerms K →
      Submission.Blueprint.SolidCofibrant K :=
  fun K hbd hat => solidCofibrant_of_boundedAbove_atomic hA cofibrantClosure K hbd hat

/-- **B6 (assembled)**: `AtomProp` gives a functorial solid-cofibrant resolution of every cochain
complex: this is the first conjunct of `Submission.Blueprint.ResolutionProp`. -/
theorem hasFunctorialResolution (hA : Submission.Blueprint.AtomProp) :
    HasFunctorialResolution := by
  refine hasFunctorialResolution_of_bounded cofibrantClosure ?_
  obtain ⟨R, ε, h₁, h₂, h₃⟩ :=
    hasBoundedResolutionZero hasAtomicCoverZero cofibrantClosure
      (boundedAbove_atomic_solidCofibrant hA)
  exact ⟨R, ε, h₁, fun B hbd _ => h₂ B hbd, h₃⟩

/-- `resolution_prop` with the (unused) `ToolkitProp` hypothesis removed. -/
theorem resolution_prop_of_atomProp (hA : Submission.Blueprint.AtomProp) :
    Submission.Blueprint.ResolutionProp :=
  ⟨hasFunctorialResolution hA, fun K hK => @solidCofibrant_of_isKProjective K hK⟩

/-- **AREA RESOL.**  Functorial solid-cofibrant resolutions of unbounded complexes exist, and
K-projective complexes are solid-cofibrant.

The analytic input `AtomProp` (free light condensed abelian groups on light profinite sets are
solid-cofibrant) is assumed, as is `ToolkitProp`; nothing else is needed.  (The coproduct closure
of B4 is proved directly in area RESOL, so `ToolkitProp` is not used; it is accepted because the
blueprint allows assuming it.) -/
theorem resolution_prop (hA : Submission.Blueprint.AtomProp)
    (hT : Submission.Blueprint.ToolkitProp) :
    Submission.Blueprint.ResolutionProp :=
  resolution_prop_of_atomProp hA

end Work.RESOL
