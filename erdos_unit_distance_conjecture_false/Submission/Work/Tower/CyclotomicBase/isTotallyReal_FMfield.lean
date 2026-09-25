import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.exists_mulEquiv_Mfield_gal
import Submission.Work.Tower.CyclotomicBase.finrank_Ffield_eq_three
import Submission.Work.Tower.CyclotomicCubic

set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Work.Tower.CyclotomicBase

/-- The field `F` of the construction (viewed as the intermediate field `FMfield` of `M`) is
totally real: it is `ℚ`-isomorphic to `Ffield`, which is a Galois extension of `ℚ` of degree `3`
(`finrank_Ffield_eq_three`, `isGalois_Ffield`), and a degree-`3` Galois extension of `ℚ` is
totally real (`Work.Tower.isTotallyReal_of_isGalois_finrank_three`); total realness transfers
along the `ℚ`-algebra isomorphism `restrictAlgEquiv : ↥Ffield ≃ₐ[ℚ] ↥FMfield`. -/
theorem isTotallyReal_FMfield {ℓ : ℕ} (hℓ : 0 < ℓ) (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] :
    NumberField.IsTotallyReal ↥(FMfield r hr hr3) := by
  have hfin : Module.finrank ℚ ↥(Ffield r hr hr3) = 3 :=
    finrank_Ffield_eq_three hℓ r hr hr3 hrinj
  haveI hg : IsGalois ℚ ↥(Ffield r hr hr3) := isGalois_Ffield r hr hr3
  haveI hreal : NumberField.IsTotallyReal ↥(Ffield r hr hr3) :=
    isTotallyReal_of_isGalois_finrank_three _ hfin
  exact NumberField.IsTotallyReal.ofRingEquiv
    (IntermediateField.restrictAlgEquiv (Ffield_le_Mfield r hr hr3)).toRingEquiv

end Work.Tower.CyclotomicBase
