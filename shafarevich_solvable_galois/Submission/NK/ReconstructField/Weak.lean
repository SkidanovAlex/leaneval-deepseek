import Submission.NK.ReconstructField.GaloisCase
import Submission.NK.ReconstructField.exists_twist_of_mapsBase
import Submission.NK.ReconstructField.Rigidity
import Submission.NK.Reconstruct.frobeniusCorrespondence_conjHomEquiv
import Submission.NK.Reconstruct.PlaceRigidity
import Submission.NK.Reconstruct.comap_placeMap_eq_of_conjugates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reconstruction from the weak Neukirch–Uchida theorem and the rigidity of the place system

This file isolates the **weak Neukirch–Uchida statement** — the number fields `K₁`, `K₂` are
isomorphic — as a named input, and proves that, together with the rigidity of the place system
(`NK.Reconstruct.PlaceRigidity`, i.e. Jarden–Ritter), it produces the field isomorphism
`σ : K₂' ≃+* K₁'` of CoNF XII §12.2:

```lean
theorem NK.ReconstructField.exists_conjugates_of_weak_and_placeRigidity
    (a : LocalCorrespondence ϕ) (hW : WeakNeukirchUchidaIso K₁ K₂) (hR : PlaceRigidity K₂ K₂') :
    ∃ σ : K₂' ≃+* K₁', Conjugates σ ϕ
```

and hence the `MapsBase` isomorphism together with the Frobenius correspondence
(`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius_of_weak_and_rigidity`).

**The input list, and why it is honest.**  Neither `hW` nor `hR` mentions the group isomorphism
`ϕ`, the place correspondence `a`, or the field isomorphism `σ` that is to be produced:

* `WeakNeukirchUchidaIso K₁ K₂` is `Nonempty (K₁ ≃+* K₂)`: the *weak* Neukirch–Uchida theorem, a
  statement about the two number fields alone;
* `NK.Reconstruct.PlaceRigidity K₂ K₂'` is a statement about the pair `(K₂, K₂')` alone: every
  automorphism of `Gal(K₂'/K₂)` carrying the family of decomposition groups of the places over the
  finite primes to itself is induced by a *field* automorphism of `K₂'` preserving the embedded
  copy of `K₂` (Jarden–Ritter).  Note that this is *not* the statement that the realization exists
  for the given `ϕ`.

In the Galois-over-`ℚ` case, `hW` is a **theorem** of this chapter (`galoisBaseIso`,
`NK.ReconstructField.weakNeukirchUchidaIso_of_galois`, from Bauer via the completely split
primes), so there the reconstruction needs only the rigidity `hR`
(`NK.ReconstructField.exists_conjugates_of_placeRigidity_galois`).

The local Frobenius correspondence `(B)` of Shimizu's Lemma 2.1.5 is **not** used on this route: the
conclusion `Conjugates σ ϕ` is stronger and yields `FrobeniusCorrespondence ϕ σ` directly
(`NK.ReconstructField.frobeniusCorrespondence_of_conjugates`).
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open NK.Reconstruct

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The weak Neukirch–Uchida statement**: the two number fields are isomorphic. -/
def WeakNeukirchUchidaIso (K₁ K₂ : Type*) [Field K₁] [Field K₂] : Prop := Nonempty (K₁ ≃+* K₂)

/-- **The weak Neukirch–Uchida statement is equivalent to the existence of a base-field-mapping
isomorphism of the separable closures.**  The direction `⟹` extends a base-field isomorphism to the
separable closures (`NK.ReconstructField.exists_ringEquiv_mapsBase_of_ringEquiv`, here through the
chosen lift `NK.ReconstructField.liftBase`); the direction `⟸` restricts a `MapsBase` isomorphism
to the base fields. -/
theorem weakNeukirchUchidaIso_iff_exists_mapsBase :
    WeakNeukirchUchidaIso K₁ K₂ ↔
      ∃ σ : K₂' ≃+* K₁',
        Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ := by
  constructor
  · rintro ⟨τ⟩
    exact ⟨liftBase K₁ K₂ K₁' K₂' τ, liftBase_mapsBase K₁ K₂ K₁' K₂' τ⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨ρ, -⟩ := baseRingEquiv_of_mapsBase σ hσ
    exact ⟨ρ.symm⟩

/-- **The weak Neukirch–Uchida statement in the Galois-over-`ℚ` case** (Bauer): if `K₁` and `K₂` are
Galois over `ℚ`, the base-field isomorphism is produced by the equality of the completely split
primes, which is a consequence of the local correspondence alone
(`NK.ReconstructField.splitsCompletely_rat_iff_of_localCorrespondence`,
`NK.ReconstructField.exists_ringEquiv_of_isGalois_of_splitsCompletely_iff`). -/
theorem weakNeukirchUchidaIso_of_galois {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) [IsGalois ℚ K₁] [IsGalois ℚ K₂] :
    WeakNeukirchUchidaIso K₁ K₂ :=
  ⟨galoisBaseIso a⟩

/-- **`Conjugates` implies the Frobenius correspondence**: if `ϕ` is the conjugation by the
`MapsBase` isomorphism `σ`, then `ϕ` matches the arithmetic Frobenius elements at corresponding
primes (`NK.Reconstruct.FrobeniusCorrespondence ϕ σ`).  This is the converse of the endgame's
`NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence`, and it shows that the *σ-based* Frobenius
correspondence is a consequence of the reconstruction rather than an extra input. -/
theorem frobeniusCorrespondence_of_conjugates {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    {σ : K₂' ≃+* K₁'} (h : Submission.NeukirchUchida.Conjugates σ ϕ) :
    NK.Reconstruct.FrobeniusCorrespondence ϕ σ := by
  obtain ⟨hσ, hconj⟩ := h
  have hhom : ϕ = Submission.NeukirchUchida.conjHomEquiv hσ := by
    refine MulEquiv.ext fun g => ?_
    ext x
    change (ϕ g).toRingEquiv x = (Submission.NeukirchUchida.conj hσ g).toRingEquiv x
    rw [hconj g, Submission.NeukirchUchida.conj_toRingEquiv hσ g]
  rw [hhom]
  exact NK.Reconstruct.frobeniusCorrespondence_conjHomEquiv σ hσ

/-- **The reconstruction from the weak Neukirch–Uchida theorem and the rigidity of the place
system.**  Given the local correspondence `a` of `ϕ` (input (A)), the weak Neukirch–Uchida theorem
`hW` and the rigidity of the place system of `K₂'` (`hR`), there is a `MapsBase` isomorphism
`σ : K₂' ≃+* K₁'` inducing `ϕ`.

The proof is `NK.Reconstruct.exists_conjugates_of_placeRigidity`: the obstruction
`Φ_{σ₀} ∘ ϕ⁻¹` (for any base-field-mapping `σ₀`, produced by `hW`) preserves the place system by
`NK.Reconstruct.exists_decompositionGroup_map_eq` (a consequence of `a.map_decomp`), so `hR`
exhibits it as the conjugation by a field automorphism, which the twist absorbs. -/
theorem exists_conjugates_of_weak_and_placeRigidity {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (hW : WeakNeukirchUchidaIso K₁ K₂)
    (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨τ⟩ := hW
  obtain ⟨σ₀, hσ₀, -⟩ :=
    exists_ringEquiv_mapsBase_of_ringEquiv (K₁ := K₁) (K₂ := K₂) (K₁' := K₁') (K₂' := K₂') τ
  exact NK.Reconstruct.exists_conjugates_of_placeRigidity a hσ₀ hR

/-- **The reconstruction from (A) and the rigidity of the place system, in the Galois-over-`ℚ`
case**: here the weak Neukirch–Uchida theorem is a theorem of this chapter
(`weakNeukirchUchidaIso_of_galois`), so the *only* remaining input is the Jarden–Ritter rigidity. -/
theorem exists_conjugates_of_placeRigidity_galois {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) [IsGalois ℚ K₁] [IsGalois ℚ K₂]
    (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_conjugates_of_weak_and_placeRigidity a (weakNeukirchUchidaIso_of_galois a) hR

/-- **The reconstruction, in the form consumed by the endgame**: from the local correspondence
`(A)`, the weak Neukirch–Uchida theorem and the rigidity of the place system, a `MapsBase`
isomorphism of the separable closures together with the σ-based Frobenius correspondence. -/
theorem exists_sigma_of_placeMap_and_frobenius_of_weak_and_rigidity
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hW : WeakNeukirchUchidaIso K₁ K₂) (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        NK.Reconstruct.FrobeniusCorrespondence ϕ σ := by
  obtain ⟨σ, hconj⟩ := exists_conjugates_of_weak_and_placeRigidity a hW hR
  exact ⟨σ, hconj.1, frobeniusCorrespondence_of_conjugates hconj⟩

/-- The same in the Galois-over-`ℚ` case, where the weak half is not an input. -/
theorem exists_sigma_of_placeMap_and_frobenius_galois_of_rigidity
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    [IsGalois ℚ K₁] [IsGalois ℚ K₂] (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        NK.Reconstruct.FrobeniusCorrespondence ϕ σ := by
  obtain ⟨σ, hconj⟩ := exists_conjugates_of_placeRigidity_galois a hR
  exact ⟨σ, hconj.1, frobeniusCorrespondence_of_conjugates hconj⟩

/-- **The reconstruction input `(C)` of this chapter from the weak half and the rigidity.**  In
particular the input list of the main theorem feeds the interface
`Submission.NeukirchUchida.exists_sigma_of_reconstructionInput` of the endgame: `(A)` + `(B)` +
`hW` + `hR` is *at least as strong* as `(A)` + `(B)` + `(C)`. -/
theorem reconstructionInput_of_weak_and_placeRigidity
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (hW : WeakNeukirchUchidaIso K₁ K₂)
    (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') : ReconstructionInput he a := by
  obtain ⟨σ, hconj⟩ := exists_conjugates_of_weak_and_placeRigidity a hW hR
  have hreal : RealizesPlaceCorrespondence a σ := fun A =>
    NK.Reconstruct.comap_placeMap_eq_of_conjugates a hconj A
  obtain ⟨hσ, _⟩ := hconj
  obtain ⟨τ, h, hσeq⟩ := exists_twist_of_mapsBase σ hσ
  refine ⟨τ, h, fun A => ?_⟩
  rw [← hσeq]
  exact hreal A

end NK.ReconstructField
