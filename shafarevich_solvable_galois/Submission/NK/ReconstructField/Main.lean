import Submission.NK.ReconstructField.Input
import Submission.NK.Reconstruct.Reconstruction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reconstruction: producing the field isomorphism `σ` (CoNF XII §12.2)

This is the main file of `Submission/Work/ReconstructField/`: from

* **(A)** the local correspondence `NK.Reconstruct.LocalCorrespondence ϕ` (CoNF (12.1.9),
  produced by `Submission/Work/BrauerHasse/` together with the local structure theory
  `Submission/Work/LocalInputs/`),
* **(B)** the local Frobenius correspondence `NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a`
  (Shimizu, arXiv:2009.10431, Lemma 2.1.5; produced by `Submission/Work/LocalTame/`), and
* **(C)** the reconstruction input `NK.ReconstructField.ReconstructionInput he a` — the weak
  Neukirch–Uchida statement in the σ-free form explained in `Input.lean` (a base-field isomorphism
  `τ : K₁ ≃+* K₂` together with the Galois twist aligning its lift with the two correspondences),

it produces the field isomorphism `σ : K₂' ≃+* K₁'` mapping the embedded `K₂` onto the embedded `K₁`
together with the *σ-based* Frobenius correspondence `NK.Reconstruct.FrobeniusCorrespondence ϕ σ`,
i.e. exactly the hypothesis of
`NK.Mine.exists_sigma_of_frobeniusCorrespondence` (which then yields `Conjugates σ ϕ`).

The passage from `(B)` and the realization of the place correspondence to the σ-based Frobenius
correspondence is `NK.Reconstruct.frobeniusCorrespondence_of_place`
(module `Submission/Work/Reconstruct/frobeniusCorrespondence_of_place.lean`); the only new
ingredient needed here is the (provably existing) lift of the base-field isomorphism `τ` to the
separable closures, `NK.ReconstructField.liftBase`/`liftTwist`.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The reconstruction of the field isomorphism of CoNF XII §12.2, from (A), (B) and the
σ-free reconstruction input (C).**

Given a homeomorphic isomorphism `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` of the absolute Galois groups of
number fields, the local correspondence `a` of CoNF (12.1.9), the local Frobenius correspondence `b`
of Shimizu's Lemma 2.1.5, and the reconstruction input `hC`, there is a field isomorphism
`σ : K₂' ≃+* K₁'` mapping the embedded copy of `K₂` onto the embedded copy of `K₁` for which `ϕ`
matches the arithmetic Frobenius elements at corresponding primes of corresponding finite levels,
`NK.Reconstruct.FrobeniusCorrespondence ϕ σ`. -/
theorem exists_sigma_of_placeMap_and_frobenius
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (hC : ReconstructionInput he a) :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        NK.Reconstruct.FrobeniusCorrespondence ϕ σ := by
  obtain ⟨τ, h, hreal⟩ := hC
  refine ⟨liftTwist K₁ K₂ K₁' K₂' τ h, liftTwist_mapsBase K₁ K₂ K₁' K₂' τ h, ?_⟩
  exact NK.Reconstruct.frobeniusCorrespondence_of_place he a (liftTwist K₁ K₂ K₁' K₂' τ h)
    (liftTwist_mapsBase K₁ K₂ K₁' K₂' τ h) hreal
    (NK.Reconstruct.agreesOnLevels_of_realizesPlaceMap he a (liftTwist K₁ K₂ K₁' K₂' τ h)
      (liftTwist_mapsBase K₁ K₂ K₁' K₂' τ h) hreal) b

/-- **The reconstruction, with the Čebotarev input**: `ϕ` is induced by a field isomorphism.

Combining the reconstruction `NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius` with
`NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence` (which passes from `MapsBase` together
with the σ-based Frobenius correspondence to `Conjugates σ ϕ`, using the Čebotarev input and the
uniqueness of the Frobenius element at an unramified prime) gives the whole existence half of
CoNF XII Theorem 12.2.1, conditional only on `(A)`, `(B)`, the reconstruction input `(C)` and the
Čebotarev input. -/
theorem exists_sigma_of_placeMap_and_frobenius_conjugates
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (hC : ReconstructionInput he a) (hc : NK.Reconstruct.ChebotarevInput K₁ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, hfrob⟩ := exists_sigma_of_placeMap_and_frobenius ϕ he a b hC
  exact NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence ϕ σ hσ hfrob hc

end NK.ReconstructField
