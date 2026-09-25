import Mathlib
import Submission.NK.EndgameRepair.Endgame

namespace NK.EndgameRepair

universe u

theorem neukirch_uchida_of_decompositionGroups_corrected
    {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (residueChar : ∀ (A : NK.Reconstruct.FinitePlaceOf K₁ K₁') (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal) ℓ)
    (localDegree : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ)
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : NK.EndgameRepair.Fourf5InputGenDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  exact neukirch_uchida_of_localCorrespondence_corrected_derived ϕ he
    (Submission.NeukirchUchida.localCorrespondenceOf ϕ h residueChar localDegree)
    (hb (Submission.NeukirchUchida.localCorrespondenceOf ϕ h residueChar localDegree))
    ℓ h45 hc

end NK.EndgameRepair
