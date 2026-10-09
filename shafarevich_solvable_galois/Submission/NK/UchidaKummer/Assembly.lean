/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.UchidaKummer.Assembly`: the reconstruction `(d)` by Uchida's Kummer method

Reference: arXiv:2601.01251, §5 (*Full Neukirch–Uchida*) and §6 (*Weak Neukirch–Uchida*).

## What this file delivers

The main theorem `NK.UchidaKummer.exists_sigma_of_kummerRoute` produces, from

* **(A)** the place correspondence `a : NK.Reconstruct.LocalCorrespondence ϕ` of CoNF (12.1.9)
  (produced in this workspace by `Submission/Work/BrauerHasse/` and the local structure theory),
* **(K)** the differentiation lemma `IsDifferentiable K₁ K₁' ℓ` of §5, and
* **(W)** the weak Neukirch–Uchida theorem `IsWeakUchida ℓ` of §6,

the reconstruction: a ring isomorphism `σ : K₂' ≃+* K₁'` with `Conjugates σ ϕ`, i.e.
`ϕ g = σ ∘ g ∘ σ⁻¹` for every `g : Gal(K₁'/K₁)`, mapping the embedded `K₂` onto the embedded `K₁`.
The companion `exists_sigma_of_kummerRoute_realizesPlaceMap` produces additionally the place
realization `(a.placeMap A).1.comap σ.symm = A.1` for every finite place `A`, i.e. exactly the
input `(d)` of `Submission/NeukirchUchida/Endgame.lean`.

## The remaining named input

The only step not carried out here is `KummerIdentificationStep`, the *Kummer identification step*
of §5: the derivation of the prime identification `KummerPrimeIdentification hϕ a` (a `MapsBase`
isomorphism `σ`, agreeing with `ϕ` on finite levels and realizing the place correspondence `a`
outside a set of primes of Dirichlet density zero) from `(K)` and `(W)`.  Concretely, in the paper
this is

* the *differentiation* of the primes of a full-density set by the local degrees of a finite
  extension `L₁/K₁` built from Kummer radicals (`lem:ell prime differentiation`), which is where
  the local Kummer surjection `IsKummerSurjective` and the local dichotomy
  `IsKummerLocalDichotomy` enter (`exists_kummerField_localDeg_eq_of_surjective` is the base step,
  proved in `Differentiation/`);
* the *weak theorem* §6 applied to each finite Galois level `L₁/K₁` and to its `ϕ`-image
  `L₂/K₂`, which produces the candidate isomorphisms `L₁ ≅ L₂`;
* the *finiteness of the set of isomorphisms* `K₁ ≃+* K₂`, which upgrades "for every finite subset
  of the full-density set" to "for the whole set".

Everything after that step — the upgrade from the density-one prime identification to the
group-theoretic statement `Conjugates σ ϕ`, which uses a prime splitting completely in the level
and the freeness of the Galois action on the primes above it — is
`NK.UchidaKummer.Identification.conjugates_of_kummerPrimeIdentification`, proved in
`Identification/` from the unconditional results of `SplitPrimes.lean`.

-/

import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.SplitPrimes
import Submission.NK.UchidaKummer.Identification.conjugates_of_kummerPrimeIdentification
import Submission.NK.UchidaKummer.Identification.comap_placeMap_eq_of_conjugates
import Submission.NK.UchidaKummer.Identification.conjugates_of_comap_placeMap_eq
import Submission.NK.UchidaKummer.Kummer.machinery_of_isPrimitiveRoot
import Submission.NK.ReconstructField.Weak
import Submission.NK.Reconstruct.PlaceRigidity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer

open IsDedekindDomain

section Main

variable {K₁ K₂ K₁' K₂' : Type*} {ℓ : ℕ} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The Kummer identification step of §5** — the one named input of the Kummer route.

It says that the differentiation lemma of §5 together with the weak Neukirch–Uchida theorem of §6
produce the prime identification of §5 `lem:alpha identifies with sigma on primes`: a `MapsBase`
isomorphism `σ : K₂' ≃+* K₁'` which agrees with `ϕ` on finite Galois levels (`AgreesOnLevels`) and
realizes the place correspondence `a` at every place over a set of primes of Dirichlet density
zero.

It is a `Prop`-valued definition, so a caller may state theorems conditionally on it; the
mathematical content of the step is described in the module docstring. -/
def KummerIdentificationStep (ℓ : ℕ) {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop :=
  IsDifferentiable K₁ K₁' ℓ → IsWeakUchida ℓ → KummerPrimeIdentification hϕ a

/-- **The reconstruction by Uchida's Kummer method.**

From the place correspondence (A) of CoNF (12.1.9), the §5 differentiation lemma (K) and the §6
weak Neukirch–Uchida theorem (W) — the inputs of the Kummer route — one obtains a field
isomorphism `σ : K₂' ≃+* K₁'` mapping the embedded `K₂` onto the embedded `K₁` and inducing `ϕ` by
conjugation.

No Čebotarev density theorem, no Leopoldt/Iwasawa input and no `ℓ`-adic cyclotomic character
recovery is used: the passage from primes to group elements is made with a prime splitting
completely in the relevant finite level (`SplitPrimes.eq_of_forall_placeSmul_eq_of_splitsCompletely`)
and the Kummer differentiation lemma, exactly as in §5 of arXiv:2601.01251. -/
theorem exists_sigma_of_kummerRoute
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hstep : KummerIdentificationStep (K₁ := K₁) (K₂ := K₂) (K₁' := K₁') (K₂' := K₂') ℓ hϕ a)
    (hD : IsDifferentiable K₁ K₁' ℓ) (hW : IsWeakUchida ℓ) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  NK.UchidaKummer.Identification.conjugates_of_kummerPrimeIdentification ϕ hϕ a
    (hstep hD hW)

/-- **The reconstruction `(d)` of `Submission/NeukirchUchida/Endgame.lean` by the Kummer route.**

The same inputs as `exists_sigma_of_kummerRoute`, with the witness `σ` exhibited *together with*
the realization of the place correspondence `(a.placeMap A).1.comap σ.symm = A.1` for **every**
finite place `A` — i.e. exactly the input `d` consumed by
`Submission.NeukirchUchida.exists_sigma_of_reconstruction`. -/
theorem exists_sigma_of_kummerRoute_realizesPlaceMap
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hstep : KummerIdentificationStep (K₁ := K₁) (K₂ := K₂) (K₁' := K₁') (K₂' := K₂') ℓ hϕ a)
    (hD : IsDifferentiable K₁ K₁' ℓ) (hW : IsWeakUchida ℓ) :
    ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      (∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) ∧
      Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hconj⟩ := exists_sigma_of_kummerRoute ϕ hϕ a hstep hD hW
  exact ⟨σ, hconj.1,
    NK.UchidaKummer.Identification.comap_placeMap_eq_of_conjugates a hconj, hconj⟩

/-- **The reconstruction by the Kummer route, with the differentiation lemma discharged.**

Here the hypothesis `IsDifferentiable K₁ K₁' ℓ` is no longer assumed: by
`Kummer.machinery_of_isPrimitiveRoot` it follows from `μ_ℓ ⊆ K₁`, since all four components of
`HasKummerMachinery` are proved in this area (the local Kummer surjection from weak approximation
and the openness of the `ℓ`-power subgroups; the non-`ℓ`-th-power local unit; the local Kummer
dichotomy). -/
theorem exists_sigma_of_kummerRoute_of_isPrimitiveRoot
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hstep : KummerIdentificationStep (K₁ := K₁) (K₂ := K₂) (K₁' := K₁') (K₂' := K₂') ℓ hϕ a)
    (hW : IsWeakUchida ℓ) (hℓ : ℓ.Prime) (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_kummerRoute ϕ hϕ a hstep
    (isDifferentiable_of_exists_isPrimitiveRoot ℓ hℓ hμ) hW

/-- The `(d)`-form of `exists_sigma_of_kummerRoute_of_isPrimitiveRoot`. -/
theorem exists_sigma_of_kummerRoute_of_isPrimitiveRoot_realizesPlaceMap
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hstep : KummerIdentificationStep (K₁ := K₁) (K₂ := K₂) (K₁' := K₁') (K₂' := K₂') ℓ hϕ a)
    (hW : IsWeakUchida ℓ) (hℓ : ℓ.Prime) (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) :
    ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      (∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) ∧
      Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_kummerRoute_realizesPlaceMap ϕ hϕ a hstep
    (isDifferentiable_of_exists_isPrimitiveRoot ℓ hℓ hμ) hW

section SigmaFree

/-- **The weak Neukirch–Uchida statement from the §6 weak theorem.**  (`IsWeakUchida` is stated for
fields in one universe; this is the only place where that is used.) -/
theorem weakNeukirchUchidaIso_of_isWeakUchida {k₁ k₂ k₁' k₂' : Type} [Field k₁] [Field k₂]
    [Field k₁'] [Field k₂'] [NumberField k₁] [NumberField k₂] [Algebra k₁ k₁'] [Algebra k₂ k₂']
    [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂'] {ℓ : ℕ} (hW : IsWeakUchida ℓ)
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) :
    NK.ReconstructField.WeakNeukirchUchidaIso k₁ k₂ :=
  hW k₁ k₂ k₁' k₂' ⟨ϕ⟩

/-- **The reconstruction by the Kummer route, with σ-FREE inputs.**

This is the form in which the inputs of the area are honest: none of

* `a : NK.Reconstruct.LocalCorrespondence ϕ` — input (A) of CoNF (12.1.9);
* `NK.ReconstructField.WeakNeukirchUchidaIso K₁ K₂` — the *weak* Neukirch–Uchida theorem, i.e.
  `Nonempty (K₁ ≃+* K₂)`; this is what the whole Kummer machinery of this area is aimed at (§6);
* `NK.Reconstruct.PlaceRigidity K₂ K₂'` — the rigidity of the place system of `K₂'` over `K₂`
  (Jarden–Ritter);

mentions `ϕ`, the place map `a.placeMap`, or the isomorphism `σ` that is produced.  The passage from
these to `σ` is `NK.Reconstruct.exists_conjugates_of_placeRigidity` (via
`NK.ReconstructField.exists_conjugates_of_weak_and_placeRigidity`): the obstruction
`Φ_{σ₀} ∘ ϕ⁻¹` preserves the place system, hence is induced by a field automorphism `c` of `K₂'`
preserving `K₂` (place rigidity), and `σ := σ₀ ∘ c⁻¹` then satisfies `Conjugates σ ϕ`. -/
theorem exists_sigma_of_kummerRoute_of_weakIso_and_placeRigidity
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hW : NK.ReconstructField.WeakNeukirchUchidaIso K₁ K₂)
    (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  NK.ReconstructField.exists_conjugates_of_weak_and_placeRigidity a hW hR

/-- The `(d)` form of `exists_sigma_of_kummerRoute_of_weakIso_and_placeRigidity`: the witness
together with the realization of the whole place correspondence. -/
theorem exists_sigma_of_kummerRoute_of_weakIso_and_placeRigidity_realizesPlaceMap
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hW : NK.ReconstructField.WeakNeukirchUchidaIso K₁ K₂)
    (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') :
    ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      (∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) ∧
      Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hconj⟩ :=
    exists_sigma_of_kummerRoute_of_weakIso_and_placeRigidity ϕ hϕ a hW hR
  exact ⟨σ, hconj.1,
    NK.UchidaKummer.Identification.comap_placeMap_eq_of_conjugates a hconj, hconj⟩

end SigmaFree

/-- **The endgame of Neukirch–Uchida without the Frobenius correspondence.**

`Submission.NeukirchUchida.exists_sigma_of_reconstruction` obtains `Conjugates σ ϕ` from input `(d)`
*and* the σ-free Frobenius correspondence `(b)` of `Submission/Work/LocalTame/`.  In fact `(d)`
alone suffices: if a `MapsBase` isomorphism realizes the place correspondence of `a`, then
`ϕ = conjHomEquiv hσ` — because for each `g`, the element induced by `σ` and `ϕ g` act identically
on every finite place of `K₂'`, and the intersection of the stabilisers of all finite places is
trivial (`NK.UchidaKummer.Identification.conjugates_of_comap_placeMap_eq`).

So the whole remaining obligation of the development may be taken to be `(A)` and `(d)`: inputs
`(b)` and `(c)` are not needed. -/
theorem exists_sigma_of_reconstruction_without_frobenius
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, hreal⟩ := d
  exact ⟨σ, NK.UchidaKummer.Identification.conjugates_of_comap_placeMap_eq a hσ hreal⟩

end Main

end NK.UchidaKummer
