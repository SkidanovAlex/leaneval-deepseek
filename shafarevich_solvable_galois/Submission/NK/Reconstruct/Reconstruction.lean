import Submission.NK.Reconstruct.Basic
import Submission.NK.Reconstruct.Transport
import Submission.NK.Reconstruct.finiteDimensional_sigmaLevel
import Submission.NK.Reconstruct.normal_sigmaLevel
import Submission.NK.Reconstruct.mapsBaseLevel_sigmaLevelEquiv
import Submission.NK.Reconstruct.isFrobAt_primeTransport_iff_inv
import Submission.NK.Reconstruct.restrictNormalHom_conjHomEquiv
import Submission.NK.Reconstruct.eq_of_restrictNormalHom_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reconstruction step of Neukirch–Uchida

This file proves the core theorem of the area:

`NK.Reconstruct.exists_sigma_of_goodLocalCorrespondence`

from the three named inputs of `Submission/Work/Reconstruct/Basic.lean` and
`Submission/Work/Reconstruct/Transport.lean`:

* **(a)** `NK.Reconstruct.GoodLocalCorrespondence ϕ` — the good local correspondence
  (CoNF (12.1.9), Shimizu Theorem 2.5) *realized* by a field isomorphism `σ : K₂' ≃+* K₁'` mapping
  the embedded `K₂` onto the embedded `K₁`;
* **(b)** `NK.Reconstruct.FrobeniusCorrespondence ϕ σ` — the Frobenius correspondence (Shimizu
  Lemma 2.1.5): `ϕ` matches arithmetic Frobenius elements at places corresponding under `σ`;
* **(c)** `NK.Reconstruct.ChebotarevInput K₁ K₁'` — the Čebotarev density theorem (every element
  of the Galois group of a finite Galois extension of number fields is a Frobenius element at some
  unramified prime).

The conclusion `Conjugates σ ϕ` says that `σ` maps the embedded `K₂` onto the embedded `K₁` and that
`ϕ g = σ⁻¹ g σ` for **every** `g : Gal(K₁'/K₁)`.

The proof is the endgame of Neukirch–Uchida: the Frobenius correspondence only describes `ϕ` on
Frobenius elements *at corresponding places*, but

* at every finite level `L₁/K₁` identified with `L₂/K₂` by `σ`, the Čebotarev input (c) produces,
  for each `d : Gal(L₁/K₁)`, an *unramified* prime `P` at which `d` is a Frobenius element;
* at such a prime the Frobenius element is *unique* (`NK.Chebotarev.IsFrobAt.eq_of_isFrobAt`),
  so (b) and the invariance of Frobenius elements under the isomorphism `τ` of levels
  (`NK.Reconstruct.isFrobAt_primeTransport_iff`) show that the restriction of `ϕ g` to `L₂` is
  the conjugate of the restriction of `g` to `L₁`;
* since this holds on every finite normal level `L₂/K₂`, and the restrictions to those levels
  determine an element of `Gal(K₂'/K₂)`
  (`NK.Reconstruct.eq_of_restrictNormalHom_eq`), `ϕ g = σ⁻¹ g σ` for all `g`.

This is the step that consumes the Čebotarev density theorem; nothing else is used beyond the two
named inputs (a) and (b).
-/

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The core of the reconstruction step, in its sharpest form.**  Let
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` be an isomorphism of absolute Galois groups of number fields and
`σ : K₂' ≃+* K₁'` a field isomorphism mapping the embedded `K₂` onto the embedded `K₁`.  Assume

* **(b)** the *Frobenius correspondence* `FrobeniusCorrespondence ϕ σ`: at every pair of finite
  levels identified by `σ`, `ϕ` maps the arithmetic Frobenius element at a prime `P` over an
  unramified prime to the Frobenius element at the corresponding prime (Shimizu's Lemma 2.1.5);
* **(c)** the Čebotarev density input `ChebotarevInput K₁ K₁'`.

Then `ϕ` *is* the conjugation by `σ`: `σ⁻¹ g σ = ϕ g` for every `g : Gal(K₁'/K₁)`.

The proof is the endgame of Neukirch–Uchida: at each finite level `L₂/K₂` (with image level
`L₁ = σ(L₂) ⊆ K₁'` and `τ = σ⁻¹| : L₁ ≃+* L₂`), (c) provides, for each automorphism `d` of `L₁`,
an *unramified* prime `P` at which `d` is a Frobenius element; (b) and the invariance of Frobenius
elements under `τ` (`isFrobAt_primeTransport_iff_inv`) then show that `τ⁻¹((ϕ g)|L₂)τ` and `g|L₁`
are both Frobenius elements at `P`, so they are *equal* by uniqueness of the Frobenius at an
unramified prime (`NK.Chebotarev.IsFrobAt.eq_of_isFrobAt`).  Since this holds on every finite
normal level `L₂/K₂`, and those levels determine an element of `Gal(K₂'/K₂)`
(`eq_of_restrictNormalHom_eq`), `ϕ g = σ⁻¹ g σ`.

In particular no topological (homeomorphism) hypothesis is needed, and no input other than a
candidate `σ` and (b) + (c) is used. -/
theorem exists_sigma_of_frobeniusCorrespondence (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (b : FrobeniusCorrespondence ϕ σ) (c : ChebotarevInput K₁ K₁') :
    ∃ σ' : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ' ϕ := by
  refine ⟨σ, hσ, ?_⟩
  -- The comparison at a single finite level of `K₂'`.
  have key : ∀ (g : Gal(K₁'/K₁)) (L₂ : IntermediateField K₂ K₂') [FiniteDimensional K₂ L₂]
      [Normal K₂ L₂] [NumberField ↥L₂],
      AlgEquiv.restrictNormalHom L₂ (ϕ g) =
        AlgEquiv.restrictNormalHom L₂
          (Submission.NeukirchUchida.conjHomEquiv hσ g) := by
    intro g L₂ _ _ _
    -- the level of `K₁'` corresponding to `L₂` under `σ`, with its instances
    let L₁ : IntermediateField K₁ K₁' := sigmaLevel σ hσ L₂
    haveI hL₁fd : FiniteDimensional K₁ L₁ :=
      finiteDimensional_sigmaLevel σ hσ L₂
    haveI hL₁n : Normal K₁ L₁ := normal_sigmaLevel σ hσ L₂
    haveI hL₁nf : NumberField ↥L₁ :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField L₁
    haveI hL₁gal : IsGalois K₁ ↥L₁ :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    -- the level isomorphism
    let τ : ↥L₁ ≃+* ↥L₂ := sigmaLevelEquiv σ hσ L₂
    have hτ : MapsBaseLevel L₁ L₂ τ := mapsBaseLevel_sigmaLevelEquiv σ hσ L₂
    have hσ' : ∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁') := fun x =>
      sigmaLevelEquiv_apply σ hσ L₂ x
    -- the Čebotarev input at this level
    obtain ⟨p, P, hP, he, hfrob⟩ := c L₁ (AlgEquiv.restrictNormalHom L₁ g)
    -- (b): `ϕ g` is a Frobenius element at the corresponding prime
    have h1 : NK.Chebotarev.IsFrobAt (primeTransport τ P)
        (AlgEquiv.restrictNormalHom L₂ (ϕ g)) := b L₂ L₁ τ hσ' p P hP he g hfrob
    -- the invariance of Frobenius elements under `τ`: the conjugated element is a Frobenius
    -- element at `P`
    have h2 : NK.Chebotarev.IsFrobAt P
        (conjAlgEquiv τ.symm hτ.symm (AlgEquiv.restrictNormalHom L₂ (ϕ g))) :=
      (isFrobAt_primeTransport_iff_inv hτ (AlgEquiv.restrictNormalHom L₂ (ϕ g)) P).mp h1
    -- uniqueness of the Frobenius at the unramified prime `P`
    have h3 : conjAlgEquiv τ.symm hτ.symm (AlgEquiv.restrictNormalHom L₂ (ϕ g)) =
        AlgEquiv.restrictNormalHom L₁ g :=
      NK.Chebotarev.IsFrobAt.eq_of_isFrobAt hP he h2 hfrob
    -- the restriction of the conjugation by `σ` on this level is the conjugation by `τ`
    have h4 : AlgEquiv.restrictNormalHom L₂
          (Submission.NeukirchUchida.conjHomEquiv hσ g) =
        conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom L₁ g) :=
      restrictNormalHom_conjHomEquiv σ hσ L₂ g
    rw [h4]
    have h5 : conjAlgEquiv τ hτ
        (conjAlgEquiv τ.symm hτ.symm (AlgEquiv.restrictNormalHom L₂ (ϕ g))) =
        conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom L₁ g) := by rw [h3]
    rwa [conjAlgEquiv_conjAlgEquiv_symm] at h5
  -- the restrictions determine the element of `Gal(K₂'/K₂)`
  have hgal : IsGalois K₂ K₂' := IsSepClosure.isGalois
  intro g
  have heq : ϕ = Submission.NeukirchUchida.conjHomEquiv hσ :=
    MulEquiv.ext fun g =>
      @eq_of_restrictNormalHom_eq K₂ K₂' _ _ _ _ hgal (ϕ g)
        (Submission.NeukirchUchida.conjHomEquiv hσ g) (key g)
  have h1 : (ϕ g : K₂' ≃+* K₂') =
      ((Submission.NeukirchUchida.conjHomEquiv hσ g : Gal(K₂'/K₂)) : K₂' ≃+* K₂') :=
    congrArg (fun e : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂) =>
      ((e g : Gal(K₂'/K₂)) : K₂' ≃+* K₂')) heq
  exact h1.trans (Submission.NeukirchUchida.conj_toRingEquiv hσ g)

/-- **The core of the reconstruction step** (the form asked for by the interface): with the good
local correspondence (a) realized by `σ` — so that `σ` is available — the Frobenius correspondence
(b) and the Čebotarev input (c) give that `σ` reconstructs `ϕ`.  This is
`NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence` applied to `a.sigma` and
`a.sigma_mapsBase`. -/
theorem exists_sigma_of_goodLocalCorrespondence (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (a : GoodLocalCorrespondence ϕ) (b : FrobeniusCorrespondence ϕ a.sigma)
    (c : ChebotarevInput K₁ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_frobeniusCorrespondence ϕ a.sigma a.sigma_mapsBase b c

/-- **The core of the reconstruction with the realizing field isomorphism isolated.**

This is `NK.Reconstruct.exists_sigma_of_goodLocalCorrespondence` with the field isomorphism `σ`
separated from the local correspondence: given

* `a : LocalCorrespondence ϕ` — the good local correspondence of CoNF (12.1.9) (input (a) without
  the realization),
* a field isomorphism `σ` mapping the embedded `K₂` onto the embedded `K₁` (`hσ`) and realizing
  the place correspondence (`hreal`) — this is the *reconstruction input* (d), which is exactly
  Neukirch's CoNF XII §12.2 / Shimizu §4 output and can be supplied in the form
  `Submission.NeukirchUchida.RealizesPlaceMap` via
  `NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap`,
* the Frobenius correspondence `b` (input (b)) and the Čebotarev input `c` (input (c)),

the only non-elementary ingredient beyond (a), (b), (c) is the realization `σ`. -/
theorem exists_sigma_of_localCorrespondence_realization (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (a : LocalCorrespondence ϕ) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hreal : ∀ A : FinitePlaceOf K₁ K₁', (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1)
    (b : FrobeniusCorrespondence ϕ σ) (c : ChebotarevInput K₁ K₁') :
    ∃ σ' : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ' ϕ :=
  exists_sigma_of_goodLocalCorrespondence ϕ
    ⟨a, σ, hσ, hreal⟩ b c

end NK.Reconstruct
