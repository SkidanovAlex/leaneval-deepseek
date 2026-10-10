import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.Reconstruct.agreesOnLevels_of_realizesPlaceMap
import Submission.NK.ReconstructField.Lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reconstruction input, in σ-free form

This file states the *reconstruction input* of Neukirch–Uchida — the last remaining input of the
existence half of CoNF XII Theorem 12.2.1, on top of the local correspondence `(A)` of (12.1.9) and
the local Frobenius correspondence `(B)` of Shimizu's Lemma 2.1.5 — **without asserting the
existence of a field isomorphism of the separable closures**.

The input is a condition on

* a **base-field isomorphism** `τ : K₁ ≃+* K₂` (the weak Neukirch–Uchida statement: the number
  fields are isomorphic compatibly with the correspondence of primes), and
* a **Galois twist** `h ∈ Gal(K₂'/K₂)` (the freedom in extending `τ` to the separable closures),

namely that the (uniquely determined, and here *provably existing* —
`NK.ReconstructField.liftBase`) lift of `τ` twisted by `h` realizes the place correspondence of
`ϕ` (`NK.ReconstructField.RealizesPlaceCorrespondence`).

Nothing else is needed.  In particular the realization of the *level* correspondence follows from
the realization of the *place* correspondence: it is
`NK.Reconstruct.agreesOnLevels_of_realizesPlaceMap` (which uses, as the one analytic ingredient,
the density of the completely split primes — Bauer's theorem,
`NK.Reconstruct.eq_of_splitPrimes_eq`) and the σ-based Frobenius correspondence then follows from
`(B)` by `NK.Reconstruct.frobeniusCorrespondence_of_place`.  See
`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius`.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The reconstruction input of Neukirch–Uchida, in σ-free form.**

There are a base-field isomorphism `τ : K₁ ≃+* K₂` and a Galois twist `h ∈ Gal(K₂'/K₂)` such that
the lift of `τ` twisted by `h` (a ring isomorphism `K₂' ≃+* K₁'`, constructed in
`NK.ReconstructField.liftTwist` from
`NK.ReconstructField.exists_ringEquiv_mapsBase_of_ringEquiv`) realizes the place correspondence
`a` of the local correspondence of `ϕ`, i.e. carries the place `a.placeMap A` of `K₂'` to the place
`A` of `K₁'` for every place `A` over a finite prime.

Classically (and equivalently — see `NK.ReconstructField.exists_twist_of_mapsBase`): the local
correspondence at the boundary is induced by a field isomorphism of the separable closures which
maps the base field onto the base field.  This is Neukirch, *Kennzeichnung der p-adischen und der
endlich algebraischen Zahlkörper*, Invent. Math. 6 (1969), Satz 2 / CoNF XII §12.2 / Shimizu,
arXiv:2009.10431, Theorems 4.0–4.3: the step in which the place system of a number field is shown
to determine the field. -/
def ReconstructionInput {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (_hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop :=
  ∃ (τ : K₁ ≃+* K₂) (h : Gal(K₂'/K₂)),
    RealizesPlaceCorrespondence a (liftTwist K₁ K₂ K₁' K₂' τ h)

/-- **The reconstruction input in the σ-based form**: the place correspondence is realized by a
MapsBase isomorphism of the separable closures.  The forward implication is immediate from the
σ-free form via `liftTwist` and `liftTwist_mapsBase`; the converse is
`NK.ReconstructField.exists_twist_of_mapsBase`. -/
def ReconstructionInputSigma {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (_hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop :=
  ∃ σ : K₂' ≃+* K₁',
    Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
      RealizesPlaceCorrespondence a σ

/-- The σ-free form implies the σ-based form. -/
theorem reconstructionInputSigma_of_reconstructionInput
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {hϕ : IsHomeomorph ϕ}
    {a : NK.Reconstruct.LocalCorrespondence ϕ} (h : ReconstructionInput hϕ a) :
    ReconstructionInputSigma hϕ a := by
  obtain ⟨τ, h, hreal⟩ := h
  exact ⟨liftTwist K₁ K₂ K₁' K₂' τ h, liftTwist_mapsBase K₁ K₂ K₁' K₂' τ h, hreal⟩

end NK.ReconstructField
