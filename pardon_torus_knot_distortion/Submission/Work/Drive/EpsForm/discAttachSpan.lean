import Mathlib
import Submission.Work.Drive.EpsForm.regionEquivalent_of_discAttach
import Submission.Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq

/-!
# Corollaries of the disc-attachment transport

`Work.Drive.EpsForm.regionEquivalent_of_discAttach` transports the loops of `A ∪ B` into `A` when
`B` is a piece of the surface contained in an embedded disc of the surface, open in the carrier, whose
"free boundary" `closure B \ B` lies in `A` and whose points of `closure B \ B` are pairwise joined
inside `A ∩ D.carrier`.  This file records the two forms its consumers want:

* `windingSpan_eq_of_discAttach` — the **span** form: `WindingSpan P (A ∪ B) = WindingSpan P A`.
  This is the `k = 1` disc-attachment span lemma of `EpsForm/COORD.md` ("between critical values the
  swept strips are discs attached along ONE arc, so the spans are equal"), and (via
  `regular_span_of_stripTransport`) it discharges the field `regular_span` of `SideSweepData` at a
  regular level, once the geometry has supplied a strip of that shape;
* `containsEssentialLoop_of_discAttach` — the **loop** form: an essential loop of `A ∪ B` yields one
  of `A`.  This is the form the endgames consume (`containsEssentialLoop_of_union_disc`-shaped
  arguments, and the peel of a clean slice).

Neither lemma asks for `A` to be open in the carrier: that is exactly the point of the transport
route (`EpsForm/NOTES_discAttach.md` §2), the `SurgeryStepZero` shape being unavailable.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The span form of the disc-attachment lemma.** -/
theorem windingSpan_eq_of_discAttach {A B : Set R3}
    {D : Work.SurgeryInvariance.DiscRegion P}
    (hB : B ⊆ D.carrier)
    (hBopen : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hcl : ∀ x : R3, x ∈ P.carrier → x ∈ closure B → x ∉ B → x ∈ A)
    (hconn : ∀ p : R3, p ∈ closure B → p ∉ B → ∀ q : R3, q ∈ closure B → q ∉ B →
      JoinedIn (A ∩ D.carrier) p q) :
    Work.SurgeryInvariance.WindingSpan P (A ∪ B) =
      Work.SurgeryInvariance.WindingSpan P A :=
  Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq
    (regionEquivalent_of_discAttach hB hBopen hcl hconn)

/-- **The loop form of the disc-attachment lemma**: an essential loop of `A ∪ B` gives one of `A`. -/
theorem containsEssentialLoop_of_discAttach {A B : Set R3}
    {D : Work.SurgeryInvariance.DiscRegion P}
    (hB : B ⊆ D.carrier)
    (hBopen : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hcl : ∀ x : R3, x ∈ P.carrier → x ∈ closure B → x ∉ B → x ∈ A)
    (hconn : ∀ p : R3, p ∈ closure B → p ∉ B → ∀ q : R3, q ∈ closure B → q ∉ B →
      JoinedIn (A ∩ D.carrier) p q)
    (h : P.ContainsEssentialLoop (A ∪ B)) :
    P.ContainsEssentialLoop A := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff P A]
  rw [← windingSpan_eq_of_discAttach hB hBopen hcl hconn]
  exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P (A ∪ B)).mpr h

end

end Work.Drive.EpsForm
