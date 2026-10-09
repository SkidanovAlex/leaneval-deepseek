import Mathlib
import Submission.NK.Reconstruct.Basic
import Submission.NK.Reconstruct.InnerTwist
import Submission.NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The place correspondence of `ϕ` is realized by every conjugating `σ`

This file proves `NK.Reconstruct.comap_placeMap_eq_of_conjugates`: if `a : LocalCorrespondence ϕ`
is the (group-theoretically defined) local correspondence of a conjugating isomorphism
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` of absolute Galois groups, and `σ : K₂' ≃+* K₁'` is a
base-field-mapping isomorphism with `Conjugates σ ϕ` — i.e. `ϕ g = σ⁻¹ ∘ g ∘ σ` for every `g` —
then `σ` realizes the *place* correspondence as well: for every place `A` of `K₁'` over a finite
prime of `K₁`,

`(a.placeMap A).1.comap σ.symm = A.1`.

The mathematical content is the comparison of two descriptions of the same decomposition group:
`a.map_decomp` gives `ϕ(D_A) = D_{a.placeMap A}`, while
`NK.Reconstruct.map_conjHomEquiv_decompositionGroup` gives `Φ_σ(D_A) = D_{A.comap σ}` for the
conjugation isomorphism `Φ_σ = conjHomEquiv hσ`.  Since `Conjugates σ ϕ` says exactly that
`ϕ = Φ_σ`, the two decomposition groups coincide; places over finite primes are determined by
their decomposition groups (rigidity, `decompositionGroup_injective`), so
`(a.placeMap A).1 = A.1.comap σ`; applying `comap_symm_comap_eq` finishes the proof.
-/

namespace NK.Reconstruct

theorem comap_placeMap_eq_of_conjugates {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (a : LocalCorrespondence ϕ) {σ : K₂' ≃+* K₁'}
    (h : Submission.NeukirchUchida.Conjugates σ ϕ) (A : FinitePlaceOf K₁ K₁') :
    (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1 := by
  obtain ⟨hσ, hconj⟩ := h
  -- `ϕ` *is* the conjugation isomorphism induced by `σ`
  have hhom : (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      (Submission.NeukirchUchida.conjHomEquiv hσ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := by
    ext g x
    change (ϕ g).toRingEquiv x = (Submission.NeukirchUchida.conj hσ g).toRingEquiv x
    rw [hconj g, Submission.NeukirchUchida.conj_toRingEquiv hσ g]
  -- the decomposition group of `a.placeMap A` is that of the place transported by `σ`
  have hD : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (a.placeMap A).1 =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (A.1.comap (σ : K₂' →+* K₁')) := by
    rw [← a.map_decomp A, hhom, ← map_conjHomEquiv_decompositionGroup hσ A.1]
  -- rigidity of places: a place over a finite prime is determined by its decomposition group
  have hBC : (a.placeMap A).1 = A.1.comap (σ : K₂' →+* K₁') :=
    Submission.NeukirchUchida.decompositionGroup_injective (K₁ := K₂) (K₁' := K₂')
      (a.placeMap A).2 (comap_sigma_comap_ne_top hσ A.2) hD
  rw [hBC]
  exact comap_symm_comap_eq σ A.1

end NK.Reconstruct
