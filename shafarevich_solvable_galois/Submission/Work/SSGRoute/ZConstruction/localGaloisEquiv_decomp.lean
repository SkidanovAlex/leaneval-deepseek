import Mathlib
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
import Submission.Work.SSGRoute.ZConstruction.lcHoms_natCard_congr

namespace Work.SSGRoute.ZConstruction

theorem localGaloisEquiv_decomp
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
      (e : ↥(SSGRoute.decomp (k := ↥K) A) ≃*
        (SeparableClosure (𝔭.adicCompletion ↥K) ≃ₐ[𝔭.adicCompletion ↥K]
          SeparableClosure (𝔭.adicCompletion ↥K))),
      IsHomeomorph (e : ↥(SSGRoute.decomp (k := ↥K) A) →
        (SeparableClosure (𝔭.adicCompletion ↥K) ≃ₐ[𝔭.adicCompletion ↥K]
          SeparableClosure (𝔭.adicCompletion ↥K))) := by
  classical
  -- `A` is a finite place of `Ω` over `↥K` as well
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro h
    apply hA
    rw [eq_top_iff]
    intro x _
    rw [ValuationSubring.mem_comap]
    have hx : algebraMap k ↥K x ∈ A.comap (algebraMap ↥K Ω) := by rw [h]; trivial
    rwa [ValuationSubring.mem_comap] at hx
  -- `Ω` is a separable closure of `↥K` (char. 0)
  haveI : IsSepClosure ↥K Ω := by
    have : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    exact IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- the prime of `↥K` below `A`, and the completion `κ = 𝔭.adicCompletion ↥K`
  let 𝔭 := Submission.NeukirchUchida.primeOf A hAK
  have h𝔭 := Submission.NeukirchUchida.primeOf_spec A hAK
  letI : Algebra (𝔭.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭).toAlgebra
  have halg : ∀ z : 𝔭.adicCompletion ↥K,
      (algebraMap (𝔭.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭 z := fun z => rfl
  have hW :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔭 A h𝔭
  haveI : IsSepClosure (𝔭.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion 𝔭 A h𝔭 halg
  refine ⟨𝔭, NK.Mine.localGaloisEquiv 𝔭 A h𝔭 halg hW, ?_⟩
  exact NK.Mine.isHomeomorph_trans (NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW)
    (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv 𝔭 A h𝔭 halg))
    (NK.Mine.isHomeomorph_adjoinLocalEquiv 𝔭 A h𝔭 halg hW)
    (NK.Mine.isHomeomorph_autCongr (NK.Mine.adjoinSepEquiv 𝔭 A h𝔭 halg))

end Work.SSGRoute.ZConstruction
