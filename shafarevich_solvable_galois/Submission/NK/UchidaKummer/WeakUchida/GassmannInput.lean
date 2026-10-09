/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Gassmann/Perlis arithmetic input, and the weak Neukirch–Uchida theorem from it

Reference: arXiv:2601.01251, §6 (*Weak Neukirch–Uchida*), proof of `thm:uchida isomorphism`.

The proof of the weak theorem in §6 has three ingredients:

* **the Kummer embedding problem** (`lem:embedding problem`), proved unconditionally in this area
  (`Submission.NK.UchidaKummer.Embedding.isKummerEmbeddingProblem`);
* **the arithmetic-equivalence step** (`cor:arith equiv` + Perlis, *Theorem 1*);
* **the group-algebra computation** turning Gassmann equivalence of the `I_{H_i}` into a conjugacy
  of the subgroups `H₁, H₂ ≤ Gal(L/ℚ)`, hence into an isomorphism `K₁ ≅ K₂` by Galois
  correspondence — proved in `Submission.NK.UchidaKummer.Gassmann.*`.

This file isolates the middle item as the single named `Prop` `GassmannWeakUchidaInput`, stated at
the level of the subgroups of a common Galois closure `L/ℚ`, and proves the weak theorem from it.
-/

import Submission.NK.UchidaKummer.Gassmann.FieldBridge
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Identification.comap_placeMap_eq_of_conjugates
import Submission.NK.ReconstructField.Weak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

attribute [local instance] Classical.propDecidable

namespace NK.UchidaKummer

universe u

/-- **The Gassmann/Perlis arithmetic input of §6.**

Let `K₁`, `K₂` be number fields containing `μ_ℓ` whose absolute Galois groups are isomorphic.
Then there are embeddings of `K₁` and `K₂` into a common number field `L` which is Galois over `ℚ`,
such that the fixing subgroups of the two images in `Gal(L/ℚ)` are Gassmann equivalent (in both
directions).

This is what remains of §6 after the Kummer embedding problem
(`IsKummerEmbeddingProblem`, proved in `Submission.NK.UchidaKummer.Embedding`) has been used: the
arithmetic equivalence proved by `cor:arith equiv`, together with Perlis' theorem that
arithmetically equivalent number fields have the same Galois closure, read through the
Gassmann correspondence between arithmetic equivalence and the equality of the `I_H`-submodules. -/
def GassmannWeakUchidaInput (ℓ : ℕ) : Prop :=
  ∀ (K₁ K₂ : Type u) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (K₁' : Type u) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type u) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂'],
    (∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) → (∃ ζ : K₂, IsPrimitiveRoot ζ ℓ) →
    Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) →
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra ℚ L) (_ : IsGalois ℚ L)
      (i : K₁ →ₐ[ℚ] L) (j : K₂ →ₐ[ℚ] L),
      IsGassmannEquivalent (ZMod ℓ) (i.fieldRange).fixingSubgroup (j.fieldRange).fixingSubgroup ∧
      IsGassmannEquivalent (ZMod ℓ) (j.fieldRange).fixingSubgroup (i.fieldRange).fixingSubgroup

/-- **The weak Neukirch–Uchida theorem from the Gassmann/Perlis input.**

Number fields `K₁`, `K₂` containing `μ_ℓ` with isomorphic absolute Galois groups are isomorphic.
This is §6 `thm:uchida isomorphism`, discharged down to the single arithmetic input
`GassmannWeakUchidaInput` and the group-algebra computation of `Gassmann/`. -/
theorem nonempty_ringEquiv_of_gassmannWeakUchidaInput {ℓ : ℕ} [Fact ℓ.Prime]
    (h : GassmannWeakUchidaInput.{u} ℓ)
    (K₁ K₂ : Type u) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (K₁' : Type u) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type u) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (hμ₁ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) (hμ₂ : ∃ ζ : K₂, IsPrimitiveRoot ζ ℓ)
    (hϕ : Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))) :
    Nonempty (K₁ ≃+* K₂) := by
  obtain ⟨L, hfL, hnfL, halgL, hgalL, i, j, hG₁, hG₂⟩ := h K₁ K₂ K₁' K₂' hμ₁ hμ₂ hϕ
  letI : Field L := hfL
  letI : NumberField L := hnfL
  letI : Algebra ℚ L := halgL
  letI : IsGalois ℚ L := hgalL
  exact nonempty_ringEquiv_of_gassmann_fieldRange i j hG₁ hG₂

/-- The weak Neukirch–Uchida statement in the vocabulary of the sibling area
(`NK.ReconstructField.WeakNeukirchUchidaIso` is `Nonempty (K₁ ≃+* K₂)`). -/
theorem weakNeukirchUchidaIso_of_gassmannWeakUchidaInput {ℓ : ℕ} [Fact ℓ.Prime]
    (h : GassmannWeakUchidaInput.{u} ℓ)
    (K₁ K₂ : Type u) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (K₁' : Type u) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type u) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (hμ₁ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) (hμ₂ : ∃ ζ : K₂, IsPrimitiveRoot ζ ℓ)
    (hϕ : Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))) :
    NK.ReconstructField.WeakNeukirchUchidaIso K₁ K₂ :=
  nonempty_ringEquiv_of_gassmannWeakUchidaInput h K₁ K₂ K₁' K₂' hμ₁ hμ₂ hϕ

section Main

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The reconstruction `(d)` from the Gassmann/Perlis input.**

Inputs: (A) the local correspondence `a = NK.Reconstruct.LocalCorrespondence ϕ`, the Gassmann
input `GassmannWeakUchidaInput ℓ` (with `ℓ` prime and `μ_ℓ ⊆ K₂`), and the rigidity of the place
system of `K₂'` over `K₂` (Jarden–Ritter).  Conclusion: a field isomorphism `σ : K₂' ≃+* K₁'`
inducing `ϕ` by conjugation.

No Čebotarev density statement and no Leopoldt/Iwasawa input occurs. -/
theorem exists_conjugates_of_gassmannWeakUchidaInput {ℓ : ℕ} [Fact ℓ.Prime]
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (h : GassmannWeakUchidaInput.{u} ℓ)
    (hμ₁ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) (hμ₂ : ∃ ζ : K₂, IsPrimitiveRoot ζ ℓ)
    (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  NK.ReconstructField.exists_conjugates_of_weak_and_placeRigidity a
    (weakNeukirchUchidaIso_of_gassmannWeakUchidaInput h K₁ K₂ K₁' K₂' hμ₁ hμ₂ ⟨ϕ⟩) hR

/-- **The reconstruction `(d)` in the form consumed by the endgame.**

The witness `σ`, its `MapsBase` property, and the realization of the whole place correspondence. -/
theorem exists_sigma_of_gassmannWeakUchidaInput_realizesPlaceMap {ℓ : ℕ} [Fact ℓ.Prime]
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (h : GassmannWeakUchidaInput.{u} ℓ)
    (hμ₁ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) (hμ₂ : ∃ ζ : K₂, IsPrimitiveRoot ζ ℓ)
    (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') :
    ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      (∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) ∧
      Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hconj⟩ :=
    exists_conjugates_of_gassmannWeakUchidaInput ϕ a h hμ₁ hμ₂ hR
  exact ⟨σ, hconj.1,
    NK.UchidaKummer.Identification.comap_placeMap_eq_of_conjugates a hconj, hconj⟩

end Main

end NK.UchidaKummer
