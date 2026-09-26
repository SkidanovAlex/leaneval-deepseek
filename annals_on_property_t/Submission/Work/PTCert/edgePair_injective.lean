import Mathlib
import Submission.Work.PTCert.QAdjOpDefs

namespace Work.PTCert

/-- `edgePair` reads off the two vertices of an edge as a pair of naturals; it is injective
because a `Fin`-valued component is recovered from its value. -/
theorem edgePair_injective (r : ℕ) :
    Function.Injective (Submission.PTCert.edgePair (r := r)) := by
  intro a b h
  simp only [Submission.PTCert.edgePair, Prod.mk.injEq] at h
  exact Subtype.ext (Prod.ext (Fin.ext h.1) (Fin.ext h.2))

end Work.PTCert
