import Mathlib
import Submission.Work.Thom.TransgressionSquare
import Submission.Work.Thom.Glue
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general
import Submission.Work.Thom.transgressionSquareAux

/-!
# The transgression square of the Mayer--Vietoris ladder

This is the target statement `Work.Thom.TransgressionSquare` of the Thom chapter: the
compatibility of the Thom map `x ↦ π^*(x) ⌣ τ` with the Mayer--Vietoris connecting maps of the
base `B` and of the Thom pair `(E, E∖0)`.

The mathematical content is split into two independently proved pieces (see
`Submission/Work/Thom/transgressionSquareAux.lean`):

* `Work.Thom.honestDelta_mixedCup` (file `Submission/Work/Thom/honestDelta_mixedCup.lean`):
  for a single space `X`, a pair `(X,A)` and a cover `U ∪ V = X`, cupping with a relative class
  `b ∈ H^n(X,A)` intertwines the connecting map of the absolute Mayer--Vietoris sequence of
  `(X,∅)` with that of the relative one of `(X,A)`;
* `Work.Thom.transgressionNatural` (file `Submission/Work/Thom/transgressionNatural.lean`):
  naturality of the absolute Mayer--Vietoris connecting map under a continuous map and the
  preimage cover.

Composing the second with the projection `π : E → B` of a real bundle and applying the first to
`(E, E∖0)` and the cover `(π⁻¹U, π⁻¹V)` gives the square, after identifying `Ttop`/`Tov` with
`thomMap`/`localThomMap` and `piTop`/`piOv` with the pullbacks along `π`.

The proof is contained in `Work.Thom.transgressionSquareAux`, whose statement is *verbatim* the
one required here; this file is the bridge that the task asks for.
-/

namespace Work.Thom

theorem transgressionSquare (B : Type) [TopologicalSpace B] (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ι : Type) (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) {U V : Set B}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (τ : Work.Thom.OpenThom Z n) :
    Work.Thom.TransgressionSquare Z n hU hV hcov τ :=
  transgressionSquareAux B F ι Z n hU hV hcov τ

end Work.Thom
