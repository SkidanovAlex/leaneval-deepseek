import Mathlib
import Submission.NK.Reconstruct.Transport
import Submission.NK.ReconstructField.localDegree_primeTransport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.Reconstruct

open NumberField

/-! ## Auxiliary facts about the induced isomorphism of rings of integers

The proofs below transport the fibre of primes above a prime along the ring isomorphism
`𝓞 A ≃+* 𝓞 B` induced by a field isomorphism `e : A ≃+* B`.  They use the inverse books of
`ringOfIntegersEquiv`, namely that `ringOfIntegersEquiv e.symm` is an inverse of
`ringOfIntegersEquiv e`, both as a ring homomorphism and as a map on ideals.

Because `Ideal.map` applied to a `RingEquiv` and applied to its coercion to a `RingHom` are the
same function (`rfl`), the identities below are first put in the coerced form with `change`. -/

/-- **The induced isomorphism of rings of integers composed with the inverse is the identity.** -/
lemma ringOfIntegersEquiv_comp_symm {L₁ L₂ : Type*} [Field L₁] [Field L₂] (τ : L₁ ≃+* L₂) :
    ((NK.Reconstruct.ringOfIntegersEquiv τ : 𝓞 L₁ ≃+* 𝓞 L₂) : 𝓞 L₁ →+* 𝓞 L₂).comp
      ((NK.Reconstruct.ringOfIntegersEquiv τ.symm : 𝓞 L₂ ≃+* 𝓞 L₁) : 𝓞 L₂ →+* 𝓞 L₁) =
        RingHom.id (𝓞 L₂) := by
  ext x
  simp [NK.Reconstruct.ringOfIntegersEquiv_apply]

/-- **The inverse of the induced isomorphism of rings of integers composed with it is the
identity.** -/
lemma ringOfIntegersEquiv_symm_comp {L₁ L₂ : Type*} [Field L₁] [Field L₂] (τ : L₁ ≃+* L₂) :
    ((NK.Reconstruct.ringOfIntegersEquiv τ.symm : 𝓞 L₂ ≃+* 𝓞 L₁) : 𝓞 L₂ →+* 𝓞 L₁).comp
      ((NK.Reconstruct.ringOfIntegersEquiv τ : 𝓞 L₁ ≃+* 𝓞 L₂) : 𝓞 L₁ →+* 𝓞 L₂) =
        RingHom.id (𝓞 L₁) := by
  ext x
  simp [NK.Reconstruct.ringOfIntegersEquiv_apply]

/-- **`Ideal.map` along the induced isomorphism of rings of integers, followed by the inverse map,
is the identity.** -/
lemma map_map_apply_ringOfIntegersEquiv {L₁ L₂ : Type*} [Field L₁] [Field L₂]
    (e : L₁ ≃+* L₂) (I : Ideal (𝓞 L₁)) :
    Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e.symm)
      (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e) I) = I := by
  change Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv e.symm : 𝓞 L₂ →+* 𝓞 L₁))
    (Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv e : 𝓞 L₁ →+* 𝓞 L₂)) I) = I
  rw [Ideal.map_map, ringOfIntegersEquiv_symm_comp, Ideal.map_id]

/-- **The inverse map on ideals, followed by `Ideal.map` along the induced isomorphism of rings of
integers, is the identity.** -/
lemma map_ringOfIntegersEquiv_map_symm {L₁ L₂ : Type*} [Field L₁] [Field L₂]
    (e : L₁ ≃+* L₂) (J : Ideal (𝓞 L₂)) :
    Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e)
      (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e.symm) J) = J := by
  change Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv e : 𝓞 L₁ →+* 𝓞 L₂))
    (Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv e.symm : 𝓞 L₂ →+* 𝓞 L₁)) J) = J
  rw [Ideal.map_map, ringOfIntegersEquiv_comp_symm, Ideal.map_id]

/-- **Transport of the fibre of primes over a prime along an isomorphism of extensions.**

Let `A` and `B` be number fields, `C ⊆ A` and `D ⊆ B` subfields which are themselves number fields,
and let `e : A ≃+* B` and `τ : C ≃+* D` be compatible ring isomorphisms (i.e. `e` carries the image
of `C` into that of `D` through `τ`).  Then for a prime `Q` of `𝓞 C` the number of primes of `𝓞 A`
lying over `Q` equals the number of primes of `𝓞 B` lying over the transported prime
`primeTransport τ Q`: `e` induces a bijection between the two fibres. -/
theorem ncard_primesOver_map_ringEquiv {A B C D : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] [Field C] [NumberField C] [Field D] [NumberField D] [Algebra C A] [Algebra D B]
    (e : A ≃+* B) (τ : C ≃+* D) (h : ∀ x : C, e (algebraMap C A x) = algebraMap D B (τ x))
    (Q : NK.Chebotarev.PrimeIdeal C) :
    (Q.asIdeal.primesOver (NumberField.RingOfIntegers A)).ncard =
      ((NK.Reconstruct.primeTransport τ Q).asIdeal.primesOver
        (NumberField.RingOfIntegers B)).ncard := by
  -- compatibility of the inverse isomorphisms, at the level of the base fields
  have h' : ∀ y : D, e.symm (algebraMap D B y) = algebraMap C A (τ.symm y) := by
    intro y
    have hy := h (τ.symm y)
    rw [RingEquiv.apply_symm_apply] at hy
    rw [← hy, RingEquiv.symm_apply_apply]
  -- `e` induces the map `Ideal.map (ringOfIntegersEquiv e)` on ideals, which is a bijection
  -- between the two fibres
  refine Set.ncard_congr (fun I _ => Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e) I) ?_ ?_ ?_
  · -- the map sends the fibre over `Q` into the fibre over `primeTransport τ Q`
    intro I hI
    simp only [Ideal.primesOver, Set.mem_ofPred_eq] at hI ⊢
    haveI : I.IsPrime := hI.1
    refine ⟨Ideal.map_isPrime_of_equiv (NK.Reconstruct.ringOfIntegersEquiv e), ?_⟩
    rw [Ideal.liesOver_iff] at hI ⊢
    -- the contraction of the image is the image of the contraction
    rw [NK.ReconstructField.under_map_ringOfIntegersEquiv e τ h I, ← hI.2]
    rfl
  · -- the map is injective on the fibre
    intro I₁ I₂ _ _ heq
    have h2' := congrArg (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e.symm)) heq
    rw [map_map_apply_ringOfIntegersEquiv e I₁, map_map_apply_ringOfIntegersEquiv e I₂] at h2'
    exact h2'
  · -- the map is surjective onto the fibre over `primeTransport τ Q`
    intro J hJ
    refine ⟨Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e.symm) J, ?_, ?_⟩
    · simp only [Ideal.primesOver, Set.mem_ofPred_eq] at hJ ⊢
      haveI : J.IsPrime := hJ.1
      refine ⟨Ideal.map_isPrime_of_equiv (NK.Reconstruct.ringOfIntegersEquiv e.symm), ?_⟩
      rw [Ideal.liesOver_iff] at hJ ⊢
      rw [NK.ReconstructField.under_map_ringOfIntegersEquiv e.symm τ.symm h' J, ← hJ.2]
      rw [show (NK.Reconstruct.primeTransport τ Q).asIdeal =
          Ideal.map (NK.Reconstruct.ringOfIntegersEquiv τ) Q.asIdeal from rfl]
      rw [map_map_apply_ringOfIntegersEquiv τ Q.asIdeal]
    · exact map_ringOfIntegersEquiv_map_symm e J

end NK.Reconstruct
