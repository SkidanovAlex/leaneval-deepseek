import Mathlib
import Submission.NK.Reconstruct.Transport
import Submission.NK.LocalInputs.Defs
import Submission.NK.ReconstructField.localDegree_primeTransport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The number of primes above a prime is invariant under an isomorphism of number field
extensions

Let `A₁ → B₁` and `A₂ → B₂` be extensions of number fields and let `μ : B₁ ≃+* B₂` be a field
isomorphism compatible with a field isomorphism `μ₀ : A₁ ≃+* A₂` of the base fields,
`μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x)`.  Then `μ` induces ring isomorphisms of the
rings of integers and, for a prime `P` of `𝓞 A₁`, a bijection between the primes of `𝓞 B₁` lying
over `P` and the primes of `𝓞 B₂` lying over the transported prime
`NK.Reconstruct.primeTransport μ₀ P` — the prime `Ideal.map (ringOfIntegersEquiv μ₀) P.asIdeal`.
Consequently the two sets have the same number of elements.

The bijection is `Q ↦ Ideal.map (ringOfIntegersEquiv μ) Q`, and both directions are pure transport
along the ring equivalences: a prime `Q` lies over `P` if and only if its image lies over the image
of `P`, which is the content of `NK.ReconstructField.under_map_ringOfIntegersEquiv` (the trace of
the image is the image of the trace).  The argument is first proved in the abstract setting of an
arbitrary commutative square of rings, `ncard_primesOver_map_of_commute`, and then specialised.
-/

namespace NK.ReconstructField

/-- **The number of primes over an ideal is invariant under an isomorphism of the ambient rings
which is compatible with an isomorphism of the base rings.**

Let `R₁ → S₁`, `R₂ → S₂` be ring extensions, `φ : S₁ ≃+* S₂`, `φ₀ : R₁ ≃+* R₂` ring equivalences
commuting with the structure maps, `φ (algebraMap R₁ S₁ x) = algebraMap R₂ S₂ (φ₀ x)`.  Then `φ`
induces a bijection between the primes of `S₁` over an ideal `p` of `R₁` and the primes of `S₂`
over `Ideal.map φ₀ p`; hence the two sets have the same number of elements. -/
lemma ncard_primesOver_map_of_commute {R₁ R₂ S₁ S₂ : Type*} [CommRing R₁] [CommRing R₂]
    [CommRing S₁] [CommRing S₂] [Algebra R₁ S₁] [Algebra R₂ S₂]
    (φ : S₁ ≃+* S₂) (φ₀ : R₁ ≃+* R₂)
    (hφ : ∀ x : R₁, φ (algebraMap R₁ S₁ x) = algebraMap R₂ S₂ (φ₀ x))
    (p : Ideal R₁) :
    (p.primesOver S₁).ncard = ((Ideal.map φ₀ p).primesOver S₂).ncard := by
  have hφsymm : ∀ x : R₂, φ.symm (algebraMap R₂ S₂ x) = algebraMap R₁ S₁ (φ₀.symm x) := by
    intro x
    apply φ.injective
    rw [RingEquiv.apply_symm_apply, hφ, φ₀.apply_symm_apply]
  refine Set.ncard_congr (fun Q _ => Ideal.map (φ : S₁ →+* S₂) Q) ?_ ?_ ?_
  · -- the image of a prime over `p` is a prime over `Ideal.map φ₀ p`
    intro Q hQ
    obtain ⟨hQp, hQl⟩ := hQ
    refine ⟨Ideal.map_isPrime_of_equiv φ, ⟨?_⟩⟩
    have h1 : Ideal.comap (algebraMap R₂ S₂) (Ideal.map (φ : S₁ →+* S₂) Q) =
        Ideal.map (φ₀ : R₁ →+* R₂) p := by
      have hl := NK.ReconstructField.comap_map_eq_map_comap φ φ₀ (algebraMap R₁ S₁)
        (algebraMap R₂ S₂) hφ Q
      have hqu : Ideal.comap (algebraMap R₁ S₁) Q = p := by
        rw [show Ideal.comap (algebraMap R₁ S₁) Q = Q.under R₁ from rfl, ← hQl.over]
      rw [hqu] at hl
      exact hl
    exact h1.symm
  · -- injectivity
    intro Q Q' hQ hQ' hEq
    have h2 := congrArg (Ideal.map (φ.symm : S₂ →+* S₁)) hEq
    simpa using h2
  · -- surjectivity
    intro R hR
    refine ⟨Ideal.map (φ.symm : S₂ →+* S₁) R, ?_, ?_⟩
    · obtain ⟨hRp, hRl⟩ := hR
      refine ⟨Ideal.map_isPrime_of_equiv φ.symm, ⟨?_⟩⟩
      have h1 : Ideal.comap (algebraMap R₁ S₁) (Ideal.map (φ.symm : S₂ →+* S₁) R) = p := by
        have hl := NK.ReconstructField.comap_map_eq_map_comap φ.symm φ₀.symm
          (algebraMap R₂ S₂) (algebraMap R₁ S₁) hφsymm R
        have hru : Ideal.comap (algebraMap R₂ S₂) R = Ideal.map (φ₀ : R₁ →+* R₂) p := by
          rw [show Ideal.comap (algebraMap R₂ S₂) R = R.under R₂ from rfl]
          exact hRl.over.symm
        rw [hru] at hl
        refine hl.trans ?_
        have h2 : Ideal.map (φ₀.symm : R₂ →+* R₁) (Ideal.map (φ₀ : R₁ →+* R₂) p) = p := by
          rw [Ideal.map_map]
          simp
        exact h2
      exact h1.symm
    · rw [Ideal.map_map]
      simp

/-- **The number of primes above a prime is invariant under an isomorphism of number field
extensions.**

Let `A₁ → B₁` and `A₂ → B₂` be extensions of number fields, and let `μ : B₁ ≃+* B₂` be a field
isomorphism compatible with a field isomorphism `μ₀ : A₁ ≃+* A₂` of the base fields.  Then for
every prime `P` of `𝓞 A₁` the number of primes of `𝓞 B₁` lying over `P` equals the number of
primes of `𝓞 B₂` lying over the transported prime `primeTransport μ₀ P`. -/
theorem ncard_primesOver_primeTransport {A₁ A₂ B₁ B₂ : Type*} [Field A₁] [NumberField A₁]
    [Field A₂] [NumberField A₂] [Field B₁] [NumberField B₁] [Field B₂] [NumberField B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂] (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (P : NK.Chebotarev.PrimeIdeal A₁) :
    (P.asIdeal.primesOver (NumberField.RingOfIntegers B₁)).ncard =
      ((NK.Reconstruct.primeTransport μ₀ P).asIdeal.primesOver
        (NumberField.RingOfIntegers B₂)).ncard := by
  rw [NK.ReconstructField.primeTransport_asIdeal μ₀ P]
  exact ncard_primesOver_map_of_commute (NK.Reconstruct.ringOfIntegersEquiv μ)
    (NK.Reconstruct.ringOfIntegersEquiv μ₀)
    (fun x => NK.ReconstructField.ringOfIntegersEquiv_algebraMap μ μ₀ hμ x) P.asIdeal

end NK.ReconstructField
