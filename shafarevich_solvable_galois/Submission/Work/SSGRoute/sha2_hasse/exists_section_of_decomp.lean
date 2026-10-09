import Submission.Work.SSGRoute.sha2_hasse.Gateway
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField Pointwise

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute.sha2_hasse

variable {k : Type} [Field k] [NumberField k]

theorem stabilizer_ofFinite_eq_decompositionSubgroup
    (E : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 (Lf E))) :
    MulAction.stabilizer (Lf E ≃ₐ[k] Lf E) (NK.GlobalCFT.Place.ofFinite q)
      = Submission.NeukirchUchida.Local.decompositionSubgroup (K := k) q := by
  ext σ
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h1 : NK.GlobalCFT.Place.smulHeightOneSpectrum σ q = q := by
      have h2 := h
      rw [NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj] at h2
      exact h2
    have hring : (↑(NK.GlobalCFT.Place.ringOfIntegersEquiv σ) : 𝓞 (Lf E) →+* 𝓞 (Lf E)) =
        ↑((galRestrict (𝓞 k) k (Lf E) (𝓞 (Lf E))) σ) :=
      congrArg (fun e : 𝓞 (Lf E) ≃+* 𝓞 (Lf E) => (e : 𝓞 (Lf E) →+* 𝓞 (Lf E)))
        (NK.GlobalCFT.Galois.ringOfIntegersEquiv_eq_galRestrict σ)
    rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup]
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [Submission.NeukirchUchida.Local.placeSmul_asIdeal]
    calc Ideal.map (↑((galRestrict (𝓞 k) k (Lf E) (𝓞 (Lf E))) σ) : 𝓞 (Lf E) →+* 𝓞 (Lf E)) q.asIdeal
        = Ideal.map (↑(NK.GlobalCFT.Place.ringOfIntegersEquiv σ) : 𝓞 (Lf E) →+* 𝓞 (Lf E)) q.asIdeal := by
          rw [hring]
      _ = (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q).asIdeal := by
          rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
          rfl
      _ = q.asIdeal := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h1
  · intro h
    exact NK.GlobalCFT.Galois.smul_ofFinite_of_mem_decompositionSubgroup h

theorem exists_section_of_decomp
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring (AlgebraicClosure k))
    (hA : A.comap (algebraMap k (AlgebraicClosure k)) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p)
    (E : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    ∃ σ : ↥(MulAction.stabilizer (Lf E ≃ₐ[k] Lf E)
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.Local.placeOf p A hA
          (E : IntermediateField k (AlgebraicClosure k))))) →
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k),
      (∀ γ, σ γ ∈ SSGRoute.decomp k A) ∧
      (∀ γ, levelRes E (σ γ) = (γ : Lf E ≃ₐ[k] Lf E)) := by
  classical
  haveI : Normal k (E : IntermediateField k (AlgebraicClosure k)) := IsGalois.to_normal
  have hsub := stabilizer_ofFinite_eq_decompositionSubgroup (k := k) E
    (Submission.NeukirchUchida.Local.placeOf p A hA (E : IntermediateField k (AlgebraicClosure k)))
  have hsurj := Submission.NeukirchUchida.Local.decompositionRestrictHom_surjective p A hA
    (E : IntermediateField k (AlgebraicClosure k))
  let Φ : ↥(MulAction.stabilizer (Lf E ≃ₐ[k] Lf E)
      (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.Local.placeOf p A hA
        (E : IntermediateField k (AlgebraicClosure k))))) →
      ↥(Submission.NeukirchUchida.Local.decompositionSubgroup (K := k)
        (Submission.NeukirchUchida.Local.placeOf p A hA (E : IntermediateField k (AlgebraicClosure k)))) :=
    fun γ => ⟨(γ : Lf E ≃ₐ[k] Lf E), by
      rw [← hsub]
      exact γ.2⟩
  refine ⟨fun γ => (Classical.choose (hsurj (Φ γ))).1, ?_, ?_⟩
  · intro γ
    exact (Classical.choose (hsurj (Φ γ))).2
  · intro γ
    have hspec := Classical.choose_spec (hsurj (Φ γ))
    have hval := congrArg (fun x : ↥(Submission.NeukirchUchida.Local.decompositionSubgroup (K := k)
        (Submission.NeukirchUchida.Local.placeOf p A hA (E : IntermediateField k (AlgebraicClosure k)))) =>
      (x : Lf E ≃ₐ[k] Lf E)) hspec
    rw [Submission.NeukirchUchida.Local.decompositionRestrictHom_apply] at hval
    simpa [levelRes, Φ] using hval

end Work.SSGRoute.sha2_hasse
