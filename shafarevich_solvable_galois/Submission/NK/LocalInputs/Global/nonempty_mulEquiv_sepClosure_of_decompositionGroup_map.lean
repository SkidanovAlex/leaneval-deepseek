import Mathlib
import Submission.NK.Mine.CompletionAPI
import Submission.NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalInputs.Global

open scoped Pointwise

/-- If an isomorphism `ϕ` of absolute Galois groups of number fields maps the decomposition group
of a place `A` (above the finite prime `𝔭`) onto the decomposition group of a place `B` (above
`𝔮`), then the absolute Galois groups of the corresponding local fields `K₁_𝔭` and `K₂_𝔮` are
isomorphic as abstract groups.

This is the "local correspondence" content of Neukirch–Schmidt–Wingberg XII (12.1.9): each
decomposition group is the absolute Galois group of the completion at the place below it
(`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`), and `ϕ` restricts to
an isomorphism between these two subgroups. -/
theorem nonempty_mulEquiv_sepClosure_of_decompositionGroup_map
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁') (B : ValuationSubring K₂')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭)
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔮)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      NK.Mine.decompositionGroupOf K₂ K₂' B) :
    Nonempty (Gal(SeparableClosure (𝔭.adicCompletion K₁)/𝔭.adicCompletion K₁) ≃*
      Gal(SeparableClosure (𝔮.adicCompletion K₂)/𝔮.adicCompletion K₂)) := by
  obtain ⟨e1⟩ := NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
    (K := K₁) (K' := K₁') 𝔭 A hA
  obtain ⟨e2⟩ := NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
    (K := K₂) (K' := K₂') 𝔮 B hB
  refine ⟨(e1.symm.trans ?_).trans e2⟩
  exact (Subgroup.equivMapOfInjective _ _ ϕ.injective).trans (MulEquiv.subgroupCongr hAB)

end NK.LocalInputs.Global
