import Mathlib
import Submission.NK.Reconstruct.Transport
import Submission.NK.Reconstruct.isFrobAt_primeTransport_iff
import Submission.NK.Reconstruct.restrictNormalHom_conjHomEquiv
import Submission.NK.Reconstruct.mapsBaseLevel_sigmaLevelEquiv

/-!
# The Frobenius correspondence for the conjugation isomorphism

`Submission.NeukirchUchida.conjHomEquiv hσ` is the isomorphism
`Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` given by conjugation `x ↦ σ⁻¹ (g (σ x))` with
`σ : K₂' ≃+* K₁'` mapping the embedded copy of `K₂` onto that of `K₁`.

Frobenius elements are manifestly preserved by a conjugation: conjugating a Frobenius at a prime
`P` by the level isomorphism transports it to a Frobenius at the corresponding prime.  This file
proves that, in the finite-level form recorded as `NK.Reconstruct.FrobeniusCorrespondence`, by
combining

* `NK.Reconstruct.isFrobAt_primeTransport_iff` (Frobenius elements are preserved by the
  transport of primes along a level isomorphism), with
* the computation `NK.Reconstruct.restrictNormalHom_conjHomEquiv_of_apply` of the restriction of
  the conjugation `↥L₂`-wise: on a finite level `L₂ ⊆ K₂'` and its image `L₁ = σ⁻¹(L₂) ⊆ K₁'`, the
  conjugation by `σ` is the conjugation by the level isomorphism `σ⁻¹ : ↥L₁ ≃+* ↥L₂`.

The arithmetic content is entirely inside `isFrobAt_primeTransport_iff`; what is added here is the
bookkeeping identifying an arbitrary level `L₁` which `τ` maps onto `L₂` compatibly with `σ` with
the level `sigmaLevel σ hσ L₂` of `Transport.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **A level isomorphism compatible with `σ` is a `MapsBaseLevel`.**

If `τ : ↥L₁ ≃+* ↥L₂` intertwines the two embeddings of the base fields with `σ.symm`, i.e.
`(τ x : K₂') = σ.symm (x : K₁')`, then `τ` carries the embedded copy of `K₁` into that of `K₂`
and back, because `σ` does (`Submission.NeukirchUchida.MapsBase`). -/
theorem mapsBaseLevel_of_apply_eq {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (τ : ↥L₁ ≃+* ↥L₂) (hτ : ∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁')) :
    MapsBaseLevel L₁ L₂ τ := by
  constructor
  · intro a
    obtain ⟨c, hc⟩ := Submission.NeukirchUchida.mapsBase_mem_symm (algebraMap K₁ K₁')
      (algebraMap K₂ K₂') hσ (x := algebraMap K₁ K₁' a) ⟨a, rfl⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    show (τ (algebraMap K₁ ↥L₁ a) : K₂') = algebraMap K₂ K₂' c
    simpa using (hτ (algebraMap K₁ ↥L₁ a)).trans hc.symm
  · intro b
    have h1 := hτ (τ.symm (algebraMap K₂ ↥L₂ b))
    rw [τ.apply_symm_apply] at h1
    have h2 : (τ.symm (algebraMap K₂ ↥L₂ b) : K₁') = σ (algebraMap K₂ K₂' b) := by
      have := congrArg σ h1
      simpa using this.symm
    obtain ⟨c, hc⟩ := Submission.NeukirchUchida.mapsBase_mem (algebraMap K₁ K₁')
      (algebraMap K₂ K₂') hσ (x := algebraMap K₂ K₂' b) ⟨b, rfl⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    show (τ.symm (algebraMap K₂ ↥L₂ b) : K₁') = algebraMap K₁ K₁' c
    rw [h2]
    exact hc.symm

/-- **The restriction of the conjugation by `σ` to a level**, for an arbitrary pair of levels
identified by `τ`.

Let `L₂ ⊆ K₂'` be a finite normal level of `K₂` and `L₁ ⊆ K₁'` a finite normal level of `K₁`,
and let `τ : ↥L₁ ≃+* ↥L₂` be compatible with `σ`, i.e. `(τ x : K₂') = σ.symm (x : K₁')`.  Then for
every `g : Gal(K₁'/K₁)` the restriction to `L₂` of the conjugation `σ⁻¹ g σ` is the conjugation
by `τ` of the restriction of `g` to `L₁`.

This generalises `NK.Reconstruct.restrictNormalHom_conjHomEquiv`, where `L₁` is the concrete
level `sigmaLevel σ hσ L₂` and `τ = sigmaLevelEquiv σ hσ L₂`. -/
theorem restrictNormalHom_conjHomEquiv_of_apply {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} [FiniteDimensional K₁ ↥L₁] [Normal K₁ ↥L₁]
    [NumberField ↥L₁] [FiniteDimensional K₂ ↥L₂] [Normal K₂ ↥L₂] [NumberField ↥L₂]
    (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (τ : ↥L₁ ≃+* ↥L₂) (hτ : ∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁'))
    (h : MapsBaseLevel L₁ L₂ τ) (g : Gal(K₁'/K₁)) :
    AlgEquiv.restrictNormalHom L₂ (Submission.NeukirchUchida.conjHomEquiv hσ g) =
      conjAlgEquiv τ h (AlgEquiv.restrictNormalHom L₁ g) := by
  ext y
  have hsymm : ((τ.symm y : ↥L₁) : K₁') = σ (y : K₂') := by
    have h1 := hτ (τ.symm y)
    rw [show τ (τ.symm y) = y from τ.apply_symm_apply y] at h1
    simpa using (congrArg (fun z => σ z) h1).symm
  simp only [AlgEquiv.restrictNormalHom_apply, conjAlgEquiv_apply]
  rw [show (Submission.NeukirchUchida.conjHomEquiv hσ) g = Submission.NeukirchUchida.conj hσ g
    from rfl, Submission.NeukirchUchida.conj_apply,
    hτ (((AlgEquiv.restrictNormalHom ↥L₁) g) (τ.symm y)),
    AlgEquiv.restrictNormalHom_apply, hsymm]

theorem frobeniusCorrespondence_conjHomEquiv {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    NK.Reconstruct.FrobeniusCorrespondence (Submission.NeukirchUchida.conjHomEquiv hσ) σ := by
  intro L₂ _ _ _ L₁ _ _ _ τ hτ p P hP hunram g hg
  have h : MapsBaseLevel L₁ L₂ τ := mapsBaseLevel_of_apply_eq σ hσ τ hτ
  have hkey : NK.Chebotarev.IsFrobAt (primeTransport τ P)
      (NK.Reconstruct.conjAlgEquiv τ h (AlgEquiv.restrictNormalHom L₁ g)) :=
    (isFrobAt_primeTransport_iff h (AlgEquiv.restrictNormalHom L₁ g) P).mp hg
  have heq : AlgEquiv.restrictNormalHom L₂ (Submission.NeukirchUchida.conjHomEquiv hσ g) =
      NK.Reconstruct.conjAlgEquiv τ h (AlgEquiv.restrictNormalHom L₁ g) :=
    restrictNormalHom_conjHomEquiv_of_apply σ hσ τ hτ h g
  simpa [heq] using hkey

end NK.Reconstruct
