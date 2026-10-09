import Submission.NK.Reconstruct.PlaceRigidity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reconstruction from the weak half plus the rigidity of the place system

This file records the *honest* hypothesis list for the reconstruction input (d) of
`Submission.NeukirchUchida.exists_sigma_of_reconstruction`, in the σ-free vocabulary of
`NK.Reconstruct.LocalCorrespondence` / `NK.Reconstruct.FrobeniusCorrespondencePlace`:

  **(a)** the σ-free local correspondence `LocalCorrespondence ϕ` (CoNF (12.1.9)),
  **(W)** the *weak* half of Neukirch–Uchida: *some* `MapsBase` isomorphism
          `σ₀ : K₂' ≃+* K₁'` — equivalently some ring isomorphism `K₁ ≃+* K₂`
          (`Submission/Work/UchidaKummer/`, or Shimizu's §§4 route),
  **(R)** the rigidity of the place system `PlaceRigidity K₂ K₂'` (Jarden–Ritter): every
          automorphism of `Gal(K₂'/K₂)` preserving the family of decomposition groups of the places
          over the finite primes of `K₂` is inner.

⟹ `∃ σ : K₂' ≃+* K₁'`, `Conjugates σ ϕ`.

Note that the Frobenius correspondence (b) and the Čebotarev input (c) are **not** needed on this
route: they are what replaces the rigidity input in the *other* route of this area
(`NK.Reconstruct.exists_sigma_of_localCorrespondence_sigmaFree`, where the missing ingredient is
instead the field isomorphism `σ` itself, i.e. the pinning problem).  The two routes are therefore:

* (a) + (b) + (c) + [the realizing `σ`]   (`Reconstruction.lean`, `Assembly.lean`), or
* (a) + (W) + (R)                          (this file).

Both reduce the reconstruction to a single classical input; no abelianised/rank data is used by
either, and neither input is a repackaging of the *conclusion* `∃σ, Conjugates σ ϕ`: (W) is the weak
Neukirch–Uchida theorem and (R) is the Jarden–Ritter rigidity.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The reconstruction (input (d)) from the local correspondence, the weak half `K₁ ≅ K₂` and the
rigidity of the place system.** -/
theorem exists_sigma_of_weak_and_placeRigidity {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : LocalCorrespondence ϕ)
    (hweak : ∃ σ₀ : K₂' ≃+* K₁', Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁')
      (algebraMap K₂ K₂') σ₀)
    (hrig : PlaceRigidity K₂ K₂') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ₀, hσ₀⟩ := hweak
  exact exists_conjugates_of_placeRigidity a hσ₀ hrig

end NK.Reconstruct
