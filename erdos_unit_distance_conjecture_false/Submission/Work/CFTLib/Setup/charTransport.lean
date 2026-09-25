import Mathlib
import Submission.Work.CFTLib.ClassGroupTransport.exists_classGroup_mulEquiv
import Submission.Work.CFTLib.PrimeCorrespondence.exists_prime_map_eq

namespace Work.CFTLib.Setup

/-- Transport of a nontrivial `p`-torsion character of the ideal class group along an
`F`-algebra embedding `ψ : K →ₐ[F] AlgebraicClosure F` of number fields.  The embedding
identifies `K` with its image `ψ.fieldRange`, hence induces an isomorphism of class groups,
and this isomorphism is compatible with the `𝓞 F`-algebra structures, so the condition of
being trivial on primes above `T` is preserved. -/
theorem charTransport (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (p : ℕ) [Fact p.Prime] (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (ψ : K →ₐ[F] AlgebraicClosure F) [NumberField ↥(ψ.fieldRange)] (χ : ClassGroup (NumberField.RingOfIntegers K) →* Multiplicative (ZMod p)) (hχne : χ ≠ 1) (hχT : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), (∃ v ∈ T, w.asIdeal.LiesOver v.asIdeal) → χ (ClassGroup.mk0 ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩) = 1) : ∃ χ' : ClassGroup (NumberField.RingOfIntegers ↥(ψ.fieldRange)) →* Multiplicative (ZMod p), χ' ≠ 1 ∧ ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(ψ.fieldRange)), (∃ v ∈ T, w.asIdeal.LiesOver v.asIdeal) → χ' (ClassGroup.mk0 ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩) = 1 := by
  -- `ψ` is injective, and identifies `K` with its image
  have hInj : Function.Injective ψ := RingHom.injective ψ.toRingHom
  let eK : K ≃ₐ[F] ↥(ψ.fieldRange) := AlgEquiv.ofInjective ψ hInj
  -- the induced isomorphism of rings of integers
  let e : NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers ↥(ψ.fieldRange) :=
    (NumberField.RingOfIntegers.mapAlgEquiv eK).toRingEquiv
  -- compatibility with the structure maps of `F`
  have hcomm : ∀ x : NumberField.RingOfIntegers F,
      e (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) x) =
        algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers ↥(ψ.fieldRange)) x :=
    fun x => (NumberField.RingOfIntegers.mapAlgEquiv eK).commutes' x
  -- the induced isomorphism of class groups
  obtain ⟨φ, hφ⟩ := Work.CFTLib.ClassGroupTransport.exists_classGroup_mulEquiv e
  refine ⟨χ.comp φ.symm.toMonoidHom, ?_, ?_⟩
  · -- nontriviality transports
    intro h
    apply hχne
    ext a
    have h1 := congrArg (fun g : ClassGroup (NumberField.RingOfIntegers ↥(ψ.fieldRange)) →*
        Multiplicative (ZMod p) => g (φ a)) h
    simpa [MulEquiv.symm_apply_apply] using h1
  · -- the vanishing condition transports
    intro w hw
    obtain ⟨u, huT, hwu⟩ := hw
    -- pull `w` back to a prime of `𝓞 K` lying over the same `u ∈ T`
    obtain ⟨v, hv_over, hvw⟩ :=
      Work.CFTLib.PrimeCorrespondence.exists_prime_map_eq e hcomm u w hwu
    have hφv := hφ v w hvw
    have hχv : χ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) = 1 :=
      hχT v ⟨u, huT, hv_over⟩
    simp only [MonoidHom.comp_apply]
    rw [← hφv]
    simpa [MulEquiv.symm_apply_apply] using hχv

end Work.CFTLib.Setup
