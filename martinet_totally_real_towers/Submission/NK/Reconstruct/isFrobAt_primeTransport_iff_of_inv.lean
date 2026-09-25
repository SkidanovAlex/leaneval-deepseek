import Mathlib
import Submission.NK.Reconstruct.isFrobAt_primeTransport_iff_inv

/-!
# Frobenius elements and the correspondence of primes (forward direction, from the inverse)

This file proves `NK.Reconstruct.isFrobAt_primeTransport_iff_of_inv`, the forward companion of
`NK.Reconstruct.isFrobAt_primeTransport_iff_inv`: for a ring isomorphism `τ : ↥L₁ ≃+* ↥L₂` of
finite levels which is compatible with the base fields, an element `d` of `Gal(↥L₁/K₁)` is a
Frobenius element at a prime `P` of `𝓞 L₁` if and only if its conjugate `τ d τ⁻¹` is a Frobenius
element at the transported prime `primeTransport τ P`.

The proof is a formal consequence of the inverse direction: the two conjugations
`conjAlgEquiv τ h` and `conjAlgEquiv τ.symm h.symm` are mutually inverse
(`conjAlgEquiv_symm_conjAlgEquiv`), so it suffices to apply
`isFrobAt_primeTransport_iff_inv` to `conjAlgEquiv τ h d` and cancel the round trip.
-/

namespace NK.Reconstruct

/-- **The round trip of the conjugation across a level isomorphism.**  Conjugating an element of
`Gal(↥L₁/K₁)` by `τ` and then by `τ⁻¹` returns the original element. -/
lemma conjAlgEquiv_symm_conjAlgEquiv {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} [FiniteDimensional K₁ ↥L₁] [NumberField ↥L₁]
    [FiniteDimensional K₂ ↥L₂] [NumberField ↥L₂] {τ : ↥L₁ ≃+* ↥L₂}
    (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) (d : Gal(↥L₁/K₁)) :
    NK.Reconstruct.conjAlgEquiv τ.symm h.symm (NK.Reconstruct.conjAlgEquiv τ h d) = d := by
  ext x
  simp [NK.Reconstruct.conjAlgEquiv_apply]

theorem isFrobAt_primeTransport_iff_of_inv {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} [FiniteDimensional K₁ ↥L₁] [NumberField ↥L₁]
    [FiniteDimensional K₂ ↥L₂] [NumberField ↥L₂] {τ : ↥L₁ ≃+* ↥L₂}
    (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) (d : Gal(↥L₁/K₁))
    (P : NK.Chebotarev.PrimeIdeal ↥L₁) :
    NK.Chebotarev.IsFrobAt P d ↔
      NK.Chebotarev.IsFrobAt (NK.Reconstruct.primeTransport τ P)
        (NK.Reconstruct.conjAlgEquiv τ h d) := by
  rw [isFrobAt_primeTransport_iff_inv h (conjAlgEquiv τ h d) P]
  rw [conjAlgEquiv_symm_conjAlgEquiv]

end NK.Reconstruct
