import Mathlib
import Submission.NK.BrauerHasse.All
import Submission.NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
import Submission.NK.NeukirchUchida.isHomeomorph_conjHomEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Mine

open scoped Pointwise

universe u

/-- **The key step: local Brauer input produces a place whose decomposition group is the image of
a given one.**

Let `K`, `L` be number fields with separable closures `K'`, `L'`, and `ϕ : Gal(K'/K) ≃* Gal(L'/L)` a
homeomorphism.  Suppose that for every finite prime `𝔭` of `K` the local Brauer data
(`LocalH2Input`, `Sha2Vanishing`, `LocalDecompositionCriterion`) for the `p`-adic field
`K_𝔭 = adicCompletion K 𝔭` is available at `L`.  Then for every place `A` of `K'` over a finite
prime of `K`, the image `ϕ(D_A)` of its decomposition group is the decomposition group of a place
`B` of `L'` over a finite prime of `L`.

The proof is Neukirch's characterisation of decomposition groups
(`NK.BrauerHasse.exists_decompositionGroup_of_localGalois`): `ϕ(D_A)` is closed (the image of the
closed subgroup `D_A` under the homeomorphism `ϕ`), self-normalising (the image of the
self-normalising subgroup `D_A`, `normalizer_decompositionGroup`), and isomorphic to the absolute
Galois group of the completion `K_𝔭` (`nonempty_mulEquiv_decompositionGroupOf_localGalois`). -/
private theorem exists_place_of_localData
    {K K' L L' : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field K'] [Field L'] [Algebra K K'] [Algebra L L']
    [IsSepClosure K K'] [IsSepClosure L L']
    (ϕ : Gal(K'/K) ≃* Gal(L'/L)) (he : IsHomeomorph ϕ)
    (h : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        ∃ p : ℕ, p.Prime ∧
          NK.BrauerHasse.LocalH2Input p L L'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)) ∧
          NK.BrauerHasse.Sha2Vanishing p L L'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)) ∧
          NK.BrauerHasse.LocalDecompositionCriterion p L L'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭))) :
    ∀ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ →
      ∃ B : ValuationSubring L', B.comap (algebraMap L L') ≠ ⊤ ∧
        (NK.Mine.decompositionGroupOf K K' A).map (ϕ : Gal(K'/K) →* Gal(L'/L)) =
          NK.Mine.decompositionGroupOf L L' B := by
  intro A hA
  obtain ⟨𝔭, h𝔭⟩ := NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := K) (K' := K') A hA
  obtain ⟨p, hp, hLoc, hHasse, hStep⟩ := h 𝔭
  let D : Subgroup Gal(K'/K) := NK.Mine.decompositionGroupOf K K' A
  -- `D` is the closed stabiliser of `A` in the Krull topology
  have hDclosed : IsClosed ((D : Set Gal(K'/K))) :=
    Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A
  -- its image under the homeomorphism `ϕ` is closed as well
  have hHclosed : IsClosed (((D.map (ϕ : Gal(K'/K) →* Gal(L'/L))) : Subgroup Gal(L'/L)) :
      Set Gal(L'/L)) := by
    rw [Subgroup.coe_map]
    exact (Homeomorph.isClosed_image (IsHomeomorph.homeomorph (⇑ϕ) he)).mpr hDclosed
  -- `D` is self-normalising (CoNF (12.1.4)), hence so is its image
  have hND : Subgroup.normalizer D = D :=
    Submission.NeukirchUchida.normalizer_decompositionGroup (K₁ := K) (K₁' := K') 𝔭 A h𝔭
  have hN : Subgroup.normalizer (D.map (ϕ : Gal(K'/K) →* Gal(L'/L))) =
      D.map (ϕ : Gal(K'/K) →* Gal(L'/L)) := by
    rw [← Subgroup.map_normalizer_eq_of_bijective D ϕ.bijective, hND]
  -- and the image is isomorphic to the absolute Galois group of the completion `K_𝔭`
  have hκ : Nonempty ((D.map (ϕ : Gal(K'/K) →* Gal(L'/L))) ≃* Gal(SeparableClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭) /
      IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)) := by
    obtain ⟨e⟩ := NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
      (K := K) (K' := K') 𝔭 A h𝔭
    exact ⟨(Subgroup.equivMapOfInjective D (ϕ : Gal(K'/K) →* Gal(L'/L)) ϕ.injective).symm.trans e⟩
  -- Neukirch's criterion produces the required place of `L'`
  obtain ⟨B, hB, hBstab⟩ := NK.BrauerHasse.exists_decompositionGroup_of_localGalois
    (K := L) (K' := L') (κ := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
    (κ' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭))
    p hp (D.map (ϕ : Gal(K'/K) →* Gal(L'/L))) hHclosed hN hκ hLoc hHasse hStep
  refine ⟨B, hB, ?_⟩
  have h1 : NK.Mine.decompositionGroupOf L L' B = D.map (ϕ : Gal(K'/K) →* Gal(L'/L)) := hBstab
  rw [h1]

theorem preservesDecompositionGroups_of_localGalois
    {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
        ∃ p : ℕ, p.Prime ∧
          NK.BrauerHasse.LocalH2Input p K₂ K₂'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)) ∧
          NK.BrauerHasse.Sha2Vanishing p K₂ K₂'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)) ∧
          NK.BrauerHasse.LocalDecompositionCriterion p K₂ K₂'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)))
    (h₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
        ∃ p : ℕ, p.Prime ∧
          NK.BrauerHasse.LocalH2Input p K₁ K₁'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)) ∧
          NK.BrauerHasse.Sha2Vanishing p K₁ K₁'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)) ∧
          NK.BrauerHasse.LocalDecompositionCriterion p K₁ K₁'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮))) :
    Submission.NeukirchUchida.PreservesDecompositionGroups ϕ := by
  constructor
  · intro A hA
    exact exists_place_of_localData (K := K₁) (K' := K₁') (L := K₂) (L' := K₂') ϕ he h₁ A hA
  · intro B hB
    obtain ⟨A, hA, hAB⟩ := exists_place_of_localData (K := K₂) (K' := K₂') (L := K₁) (L' := K₁')
      ϕ.symm (Submission.NeukirchUchida.isHomeomorph_symm ϕ he) h₂ B hB
    refine ⟨A, hA, ?_⟩
    show (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      NK.Mine.decompositionGroupOf K₂ K₂' B
    rw [← hAB, Subgroup.map_map]
    have hcomp : ((ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)).comp
        (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁))) = MonoidHom.id Gal(K₂'/K₂) := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]

end NK.Mine
