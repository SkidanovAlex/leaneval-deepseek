import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap
import Submission.NK.Reconstruct.agreesOnLevels_of_map_decompositionGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level correspondences agree, from the realization of the place correspondence

`NK.Reconstruct.AgreesOnLevels ϕ hϕ σ hσ` says that the level correspondence of `σ`
(`sigmaLevel`) and the level correspondence of `ϕ` (`levelMap`) agree.  Here it is derived from the
two inputs of the reconstruction that concern the *place system*: the local correspondence (a) and
the realization of its place map by `σ` — no Frobenius or Čebotarev input is needed.  The argument
is the one of `NK.Reconstruct.agreesOnLevels_of_map_decompositionGroup`: `ϕ` and the conjugation
by `σ` have the same image on every decomposition group (by (a) and the realization), and the
completely split primes determine a finite Galois level
(`NK.Reconstruct.eq_of_splitPrimes_eq`).
-/

namespace NK.Reconstruct

open scoped Pointwise

set_option linter.unusedVariables false

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- The inverse of the conjugation isomorphism is the conjugation by the inverse. -/
theorem conjHomEquiv_symm_eq {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    ((Submission.NeukirchUchida.conjHomEquiv hσ).symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) =
      (Submission.NeukirchUchida.conjHomEquiv
        (Submission.NeukirchUchida.mapsBase_symm_alg hσ) : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) := by
  ext g
  rfl

/-- **The level correspondences agree, from the realization of the place correspondence.** -/
theorem agreesOnLevels_of_realizesPlaceMap {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (a : LocalCorrespondence ϕ) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hreal : ∀ A : FinitePlaceOf K₁ K₁',
      (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    AgreesOnLevels ϕ hϕ σ hσ := by
  refine agreesOnLevels_of_map_decompositionGroup hϕ σ hσ (fun A hA => ?_)
  rw [a.map_decomp ⟨A, hA⟩, conjHomEquiv_symm_eq hσ]
  rw [map_conjHomEquiv_decompositionGroup (K₁ := K₂) (K₂ := K₁) (K₁' := K₂') (K₂' := K₁')
    (σ := σ.symm) (Submission.NeukirchUchida.mapsBase_symm_alg hσ) (a.placeMap ⟨A, hA⟩).1]
  rw [hreal ⟨A, hA⟩]

end NK.Reconstruct
