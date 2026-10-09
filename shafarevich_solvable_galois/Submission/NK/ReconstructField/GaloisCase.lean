import Submission.NK.ReconstructField.Main
import Submission.NK.ReconstructField.exists_ringEquiv_of_isGalois_of_splitsCompletely_iff
import Submission.NK.ReconstructField.splitsCompletely_rat_iff_of_localCorrespondence
import Submission.NK.ReconstructField.primeTransport_eq_primeMap_of_realizesPlaceCorrespondence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reconstruction when `K₁` and `K₂` are Galois over `ℚ`: the base field is determined

In this file the *base-field* half of the reconstruction input is **proved**, so that in the
Galois-over-`ℚ` case the main theorem
`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius` needs only the *place realization*
(no base-field isomorphism is assumed).

The argument is Bauer's theorem in its abstract form: for `K₁/ℚ`, `K₂/ℚ` Galois with the same
completely split primes, the fields are isomorphic
(`NK.ReconstructField.exists_ringEquiv_of_isGalois_of_splitsCompletely_iff`, whose proof embeds
both into `AlgebraicClosure ℚ` and applies the density argument).  The equality of the completely
split primes is a theorem about the local correspondence `(A)` alone
(`NK.ReconstructField.splitsCompletely_rat_iff_of_localCorrespondence`).

What remains in that case is exactly the place-system rigidity: that the place map of `ϕ` is one of
the `Gal(K₂'/K₂)`-many place maps induced by the lifts of the base-field isomorphism.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The base-field isomorphism in the Galois case**, obtained from the equality of the completely
split primes (Bauer, via `AlgebraicClosure ℚ`). -/
noncomputable def galoisBaseIso {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) [IsGalois ℚ K₁] [IsGalois ℚ K₂] :
    K₁ ≃+* K₂ :=
  Classical.choice (exists_ringEquiv_of_isGalois_of_splitsCompletely_iff
    (fun p => splitsCompletely_rat_iff_of_localCorrespondence a p))

/-- **The reconstruction for number fields Galois over `ℚ`.**  If `K₁/ℚ` and `K₂/ℚ` are Galois,
then the base-field isomorphism is determined by the local correspondence `(A)`, so the main theorem
needs only the realization of the place correspondence by one of the `Gal(K₂'/K₂)`-many lifts of it.

The hypothesis is exactly "(ii)" of the boundary analysis of the README §8; no base-field
isomorphism and no `σ` is assumed. -/
theorem exists_sigma_of_placeMap_and_frobenius_galois
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    [IsGalois ℚ K₁] [IsGalois ℚ K₂]
    (hreal : ∃ h : Gal(K₂'/K₂),
      RealizesPlaceCorrespondence a (liftTwist K₁ K₂ K₁' K₂' (galoisBaseIso a) h)) :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        NK.Reconstruct.FrobeniusCorrespondence ϕ σ :=
  exists_sigma_of_placeMap_and_frobenius ϕ he a b ⟨galoisBaseIso a, hreal⟩

/-- The same, with the Čebotarev input, in the form `Conjugates σ ϕ`. -/
theorem exists_sigma_of_placeMap_and_frobenius_galois_conjugates
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    [IsGalois ℚ K₁] [IsGalois ℚ K₂]
    (hreal : ∃ h : Gal(K₂'/K₂),
      RealizesPlaceCorrespondence a (liftTwist K₁ K₂ K₁' K₂' (galoisBaseIso a) h))
    (hc : NK.Reconstruct.ChebotarevInput K₁ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_placeMap_and_frobenius_conjugates ϕ he a b ⟨galoisBaseIso a, hreal⟩ hc

end NK.ReconstructField
