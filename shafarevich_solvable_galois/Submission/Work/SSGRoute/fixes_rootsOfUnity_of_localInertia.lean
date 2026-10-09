import Mathlib
import Submission.Work.SSGRoute.local_lifting_setup
import Submission.Work.SSGRoute.isInertia_of_mem_inertia

namespace Work.SSGRoute

set_option linter.style.haveILetI false

/-- **The local inertia subgroup fixes the prime-to-`p` roots of unity of `Ω`.**

Let `k` be a number field, `Ω` an algebraic closure of `k`, `A` a finite place of `Ω` over `k`,
`p` the residue characteristic of `A` and `𝔨 = k_𝔭` the local field of `A` (`𝔭` the prime of `k`
below `A`).  Let `σ` be an element of the decomposition group `D_A` of `A` whose image under the
identification `D_A ≃* Gal(𝔨̄/𝔨)` lies in the local inertia subgroup `I_𝔨`
(`NK.LocalAnabelian.inertiaSubgroup`, the fixing subgroup of the prime-to-`p` roots of unity of
`𝔨̄`).  Then `σ` fixes every root of unity of `Ω` of order prime to `p`.

The `TameData` hypothesis is only used to replace the opaque identification
`NK.FrobeniusBridge.localGaloisEquiv` by the explicit `NK.ResidueFrob.localGaloisEquivAdjoin`
(via `NK.LocalTame.inertiaOfDecomposition_iff_of_localIso`); for the explicit identification,
inertia membership unwinds to the statement that the restriction `σ̂|_M` of `σ` to
`M = 𝔨·Ω` fixes the prime-to-`p` roots of unity of `M`, and those are exactly the images of the
prime-to-`p` roots of unity of `Ω` under `NK.NeukirchUchida.coInAdjoin 𝔭 A`. -/
theorem fixes_rootsOfUnity_of_localInertia
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (p q : ℕ)
    (hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField ⟨A, hA⟩)
      (NK.FrobeniusBridge.localClosure ⟨A, hA⟩))
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k A)
    (h : NK.FrobeniusBridge.localGaloisEquiv ⟨A, hA⟩ ⟨σ, hσ⟩ ∈
      NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField ⟨A, hA⟩)
        (K' := NK.FrobeniusBridge.localClosure ⟨A, hA⟩) p) :
    ∀ (n : ℕ), ¬ p ∣ n → ∀ ζ : Ω, IsPrimitiveRoot ζ n → σ ζ = ζ := by
  -- the algebra structure making the place completion of `A` an extension of the local field
  letI : Algebra (NK.FrobeniusBridge.localField ⟨A, hA⟩) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion
      (Submission.NeukirchUchida.primeOf A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  let pp := Submission.NeukirchUchida.primeOf A hA
  let hp := Submission.NeukirchUchida.primeOf_spec A hA
  let halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion k pp,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion pp A hp z :=
    fun z => rfl
  let hW := NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
    pp A hp
  let σ' : ↥(NK.Mine.decompositionGroupOf k Ω A) := ⟨σ, hσ⟩
  -- switch from the opaque identification to the explicit one
  have h' : NK.ResidueFrob.localGaloisEquivAdjoin ⟨A, hA⟩ σ' ∈
      NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField ⟨A, hA⟩)
        (K' := NK.FrobeniusBridge.localClosure ⟨A, hA⟩) p := by
    have hiff := NK.LocalTame.inertiaOfDecomposition_iff_of_localIso
      (D := ↥(SSGRoute.decomp k A)) hT
      (NK.ResidueFrob.localGaloisEquivAdjoin ⟨A, hA⟩)
      (NK.FrobeniusBridge.localGaloisEquiv ⟨A, hA⟩) σ'
    exact hiff.mpr h
  have hun : NK.ResidueFrob.localGaloisEquivAdjoin ⟨A, hA⟩ σ' =
      NK.ResidueFrob.adjoinLocalIso pp A hp halg hW σ' := rfl
  rw [hun] at h'
  -- the explicit identification acts on `𝔨̄` by `ζ ↦ φ (σ̂|_M (φ⁻¹ ζ))`
  have hval2 : ∀ u : NK.FrobeniusBridge.localClosure ⟨A, hA⟩,
      ((NK.ResidueFrob.adjoinLocalIso pp A hp halg hW) σ') u =
        (NK.ResidueFrob.adjoinSepEquiv pp A hp halg)
          ((NK.NeukirchUchida.decompositionToAdjoin pp A hp halg σ')
            ((NK.ResidueFrob.adjoinSepEquiv pp A hp halg).symm u)) := by
    intro u
    simp only [NK.ResidueFrob.adjoinLocalIso, MulEquiv.trans_apply, AlgEquiv.autCongr_apply,
      AlgEquiv.trans_apply, NK.ResidueFrob.decompositionAdjoinEquiv_apply]
  intro n hn ζ hζ
  let φ : ↥(NK.NeukirchUchida.adjoinPlaceCompletion pp A) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion k pp]
      SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion k pp) :=
    NK.ResidueFrob.adjoinSepEquiv pp A hp halg
  have hw_prim : IsPrimitiveRoot (φ (NK.NeukirchUchida.coInAdjoin pp A ζ)) n :=
    (hζ.map_of_injective (NK.ResidueFrob.coInAdjoinHom_injective pp A)).map_of_injective
      φ.injective
  have hfix := (NK.LocalAnabelian.mem_inertiaSubgroup_iff p _).mp h' n hn _ hw_prim
  rw [hval2, AlgEquiv.symm_apply_apply] at hfix
  have key : (NK.NeukirchUchida.decompositionToAdjoin pp A hp halg σ')
      (NK.NeukirchUchida.coInAdjoin pp A ζ) = NK.NeukirchUchida.coInAdjoin pp A ζ :=
    φ.injective hfix
  have h2 : NK.NeukirchUchida.coInAdjoin pp A
        ((σ' : Ω ≃ₐ[k] Ω) ζ) = NK.NeukirchUchida.coInAdjoin pp A ζ := by
    rw [← NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin pp A hp halg σ' ζ]
    exact key
  exact NK.ResidueFrob.coInAdjoinHom_injective pp A h2

end Work.SSGRoute
