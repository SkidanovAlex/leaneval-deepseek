import Mathlib
import Submission.Work.Tower.FrattiniLayer.Basic

namespace Work.Tower.FrattiniLayer

/-- Everywhere-unramifiedness is invariant under `F`-algebra isomorphisms of the top field:
if `L ≃ₐ[F] L'` and `L/F` is unramified at every finite prime, so is `L'/F`. -/
theorem isUnramifiedOver_of_algEquiv {F L L' : Type*} [Field F] [Field L] [Field L']
    [Algebra F L] [Algebra F L'] (φ : L ≃ₐ[F] L')
    (h : Work.Tower.FrattiniLayer.IsUnramifiedOver F L) :
    Work.Tower.FrattiniLayer.IsUnramifiedOver F L' := by
  rw [isUnramifiedOver_iff_formallyUnramified] at h ⊢
  exact (Algebra.FormallyUnramified.iff_of_equiv
    (NumberField.RingOfIntegers.mapAlgEquiv φ)).mp h

end Work.Tower.FrattiniLayer
