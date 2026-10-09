import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer.Identification

/-- **The place correspondence is the one realized by `σ` when `σ` induces `ϕ`.**

If a field isomorphism `σ : K₂' ≃+* K₁'` mapping the embedded copy of `K₂` onto the embedded copy
of `K₁` satisfies the conjugation formula `ϕ g = σ⁻¹ ∘ g ∘ σ` (`Conjugates σ ϕ`), then *any* local
correspondence `a : LocalCorrespondence ϕ` is the place correspondence realized by `σ`: for every
place `A` of `K₁'` over a finite prime of `K₁`,

`(a.placeMap A).comap σ.symm = A`.

Indeed, `Conjugates σ ϕ` says that `ϕ` is the conjugation isomorphism attached to `σ`, so
`a.map_decomp` identifies the decomposition group of `a.placeMap A` with that of `A.comap σ`, and
places over finite primes are determined by their decomposition groups (rigidity of places);
transporting back along `σ.symm` gives the claim. -/
theorem comap_placeMap_eq_of_conjugates
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (a : NK.Reconstruct.LocalCorrespondence ϕ)
    {σ : K₂' ≃+* K₁'} (h : Submission.NeukirchUchida.Conjugates σ ϕ) :
    ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1 := by
  intro A
  -- `Conjugates σ ϕ` says that `ϕ` agrees with the conjugation isomorphism of `σ`.
  have hϕeq : ∀ g : Gal(K₁'/K₁), ϕ g = Submission.NeukirchUchida.conjHomEquiv h.1 g := by
    intro g
    have h1 : (ϕ g).toRingEquiv = (Submission.NeukirchUchida.conj h.1 g).toRingEquiv := by
      rw [h.2 g, Submission.NeukirchUchida.conj_toRingEquiv]
    have h2 : ∀ x : K₂', ϕ g x = Submission.NeukirchUchida.conj h.1 g x :=
      fun x => congrArg (fun e : K₂' ≃+* K₂' => e x) h1
    apply AlgEquiv.ext
    intro x
    exact h2 x
  have hhom : (↑ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      (↑(Submission.NeukirchUchida.conjHomEquiv h.1) : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) :=
    MonoidHom.ext (fun g => hϕeq g)
  -- hence the decomposition group of `a.placeMap A` is that of `A.comap σ`
  have hdec : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (a.placeMap A).1 =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (A.1.comap (σ : K₂' →+* K₁')) := by
    rw [← a.map_decomp A]
    rw [hhom, NK.Reconstruct.map_conjHomEquiv_decompositionGroup h.1 A.1]
  -- rigidity of places: places over finite primes are determined by their decomposition groups
  have hplace : (a.placeMap A).1 = A.1.comap (σ : K₂' →+* K₁') :=
    Submission.NeukirchUchida.decompositionGroup_injective (K₁ := K₂) (K₁' := K₂')
      (a.placeMap A).2 (NK.Reconstruct.comap_sigma_comap_ne_top h.1 A.2) hdec
  rw [hplace]
  exact NK.Reconstruct.comap_symm_comap_eq σ A.1

end NK.UchidaKummer.Identification
