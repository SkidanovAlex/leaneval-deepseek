import Submission.NK.ResidueFrob.Core
import Submission.NK.ResidueFrob.Main
import Submission.NK.TameData.Places
import Submission.NK.LocalStructure.Main

/-!
# The residue-field dictionary from the local structure theory at every place

This is the *usable* boundary of the chapter.  The dictionary
`NK.FrobeniusBridge.FrobDictionary K K'` is proved here from the local structure theory at the
places of `K'` — the reduced input catalogue of the sibling chapters `Submission/Work/LocalStructure/`
and `Submission/Work/TameData/`, plus Shimizu's `ℤ_ℓ²`-detection of the residue characteristic —
with **no** residue-cardinality or level-inertia hypothesis: those are theorems.

Two shapes of the boundary are offered, the second weaker than the first.

* `NK.ResidueFrob.TameDataInputs K K' A` — **the weakest**: the catalogue
  `NK.TameData.TameDataInput` (`Submission/Work/TameData/Definitions.lean`) at the completion
  `κ = K_𝔭`, i.e. the structure of the tame quotient (`TameInertiaInput`, NSW (7.5.7)/(7.5.11);
  Iwasawa), the splitting of the abelianised tame quotient (`TameAbelianisationInput`, Shimizu
  Lemma 2.1) and the Frobenius normalisation (`NK.LocalStructure.TameFrobeniusCore`, NSW
  (12.1.8)) — together with `NK.LocalTame.Zl2ResidueChar`.  Note that no residue field order is
  a parameter: it is `NK.LocalStructure.residueCard K 𝔭`.
* `NK.ResidueFrob.LocalStructureData K K' A` — the `𝔭`-adic form of the same catalogue
  (`NK.LocalStructure.TameCore`, `NK.TameData.TameAbelianisationInput`,
  `NK.LocalStructure.TameFrobeniusCore`, `NK.LocalTame.Zl2ResidueChar`), which is the
  hypothesis of the sibling place-level theorem `NK.TameData.tameDataAtPlaces_of_inputs`.  It
  implies `TameDataInputs` (`NK.ResidueFrob.tameDataInputs_of_localStructureData`).

What is discharged, and how.

* The residue-cardinality normalisation `ResidueCardMatches A q` is discharged *by construction*:
  `q` is taken to be `NK.LocalStructure.residueCard K 𝔭 = #(𝒪_κ/𝔪_κ)`, and
  `NK.LocalStructure.residueCard_eq_absNorm` identifies it with `𝔭.asIdeal.absNorm =
  Nat.card (𝓞K ⧸ 𝔭.asIdeal)` (`NK.ResidueFrob.residueCardMatches_residueCard`).
* The Frobenius existence input `NK.LocalAnabelian.ResidueCardInput` is the first conjunct of
  `NK.LocalStructure.TameFrobeniusCore.exists_frob`
  (`NK.ResidueFrob.residueCardInput_of_tameFrobeniusCore`).
* The level-inertia input is `NK.ResidueFrob.levelInertiaCovered_of_tameData`, inside this
  chapter (`Submission/Work/ResidueFrob/levelInertiaCovered_of_tameData.lean`).

`NK.LocalTame.Zl2ResidueChar` (Shimizu, arXiv:2009.10431 Lemma 2.1) is *not* part of
`Submission/Work/TameData/` either (see the remark in `NK.TameData.Places`), so it is displayed
as a field of both bundles.  It is used only to identify the `p` of *other* local data at the same
place with the `p` of the chosen `D` (`NK.ResidueFrob.tameData_eq`, which prevents a local
Frobenius lift from being read with an inconsistent residue characteristic); a caller who has it
from elsewhere can weaken the bundles in the obvious way.

## Main results

* `NK.ResidueFrob.frobDictionary_of_tameDataInputs` — **the dictionary**, from
  `TameDataInputs` at every place.
* `NK.ResidueFrob.tameDataAtPlaces_of_tameDataInputs` — the same inputs give
  `NK.FrobeniusBridge.TameDataAtPlaces`, i.e. the local structure theory at every place.
* `NK.ResidueFrob.frobeniusCorrespondencePlace_of_tameDataInputs` — the endgame instantiation:
  the hypotheses `hD₁`, `hD₂` **and** `hTame` of
  `NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_tameData_atPlaces` are discharged.
* `NK.ResidueFrob.exists_sigma_of_tameDataInputs` — the existence half of Neukirch–Uchida from
  the local structure theory at every place of the two fields.
* `NK.ResidueFrob.frobDictionary_of_localStructureData`,
  `NK.ResidueFrob.tameDataAtPlaces_of_localStructureData`,
  `NK.ResidueFrob.frobeniusCorrespondencePlace_of_localStructureData`,
  `NK.ResidueFrob.exists_sigma_of_localStructureData` — the same for the `𝔭`-adic bundle.
-/

namespace NK.ResidueFrob

open scoped Pointwise Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The `𝔭`-adic local structure inputs at a place of `K'`**: at the completion `κ = K_𝔭` of `K`
at the prime below `A`, the reduced input catalogue of `Submission/Work/LocalStructure/` — the
structure of the tame quotient (`NK.LocalStructure.TameCore`), the splitting of the abelianised
tame quotient (`NK.TameData.TameAbelianisationInput`, Shimizu Lemma 2.1) and the Frobenius
normalisation (`NK.LocalStructure.TameFrobeniusCore`, NSW (12.1.8)) — together with Shimizu's
`ℤ_ℓ²`-detection of the residue characteristic (`NK.LocalTame.Zl2ResidueChar`).

This is the hypothesis of the sibling place-level theorem
`NK.TameData.tameDataAtPlaces_of_inputs`; it implies `NK.ResidueFrob.TameDataInputs`.

The residue field order is *not* a parameter: it is `NK.LocalStructure.residueCard K 𝔭`, the
cardinality of the residue field of the completion. -/
def LocalStructureData (K : Type*) [Field K] [NumberField K]
    (K' : Type*) [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') : Prop :=
  ∃ p : ℕ,
    NK.LocalStructure.TameCore p K (NK.TameData.primeBelow A)
      (NK.FrobeniusBridge.localClosure A) ∧
    NK.TameData.TameAbelianisationInput p
      (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) ∧
    NK.LocalStructure.TameFrobeniusCore p
      (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) ∧
    NK.LocalTame.Zl2ResidueChar p (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A)

/-- **The weakest local structure inputs at a place of `K'`**: the catalogue
`NK.TameData.TameDataInput` of `Submission/Work/TameData/Definitions.lean` at the completion
`κ = K_𝔭`, together with Shimizu's `ℤ_ℓ²`-detection of the residue characteristic.

Nothing else about the completion is used; in particular the residue field order is *defined* to be
`NK.LocalStructure.residueCard K 𝔭`. -/
def TameDataInputs (K : Type*) [Field K] [NumberField K]
    (K' : Type*) [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') : Prop :=
  ∃ p : ℕ,
    NK.TameData.TameDataInput p
      (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) ∧
    NK.LocalTame.Zl2ResidueChar p (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A)

/-- **The `𝔭`-adic reduced catalogue implies the general one** (the only difference being the
`CharP` field of `NK.LocalStructure.TameCore`, which is replaced by the abstract
`TameAbelianisationInput.q_eq`). -/
theorem tameDataInputs_of_localStructureData (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    (h : LocalStructureData K K' A) : TameDataInputs K K' A := by
  obtain ⟨p, hT, hA, hF, hZ⟩ := h
  exact ⟨p, ⟨NK.TameData.TameInertiaInput.ofTameCore (NK.TameData.primeBelow A) hT, hA, hF⟩, hZ⟩

/-- **The residue-cardinality normalisation is automatic** when `q` is taken to be the residue
cardinality of the completion: `NK.LocalStructure.residueCard K 𝔭 = 𝔭.asIdeal.absNorm =
Nat.card (𝓞K ⧸ 𝔭.asIdeal)`. -/
theorem residueCardMatches_residueCard (A : NK.FrobeniusBridge.FinitePlaceOf K K') :
    ResidueCardMatches A
      (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A)) := by
  rw [ResidueCardMatches, NK.LocalStructure.residueCard_eq_absNorm]
  exact (Ideal.absNorm_apply _).trans (Submodule.cardQuot_apply _)

/-- **The Frobenius existence input from the Frobenius normalisation core**: the element of
`NK.LocalStructure.TameFrobeniusCore.exists_frob` is a `NK.LocalAnabelian.ResidueCardInput`
for the local field, so the normalisation of the canonical Frobenius is *not* an input beyond the
local structure theory.  (`ResidueCardInput` carries data — the Frobenius element — so this is a
definition and not a theorem.) -/
noncomputable def residueCardInput_of_tameFrobeniusCore (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    {p : ℕ}
    (h : NK.LocalStructure.TameFrobeniusCore p
      (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A)) :
    NK.LocalAnabelian.ResidueCardInput p
      (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) :=
  ⟨h.hp, h.exists_frob.choose, h.exists_frob.choose_spec.1.1, h.exists_frob.choose_spec.1.2⟩

/-- **The weakest local structure inputs give the inputs of the dictionary at that place.** -/
noncomputable def placeLevelInputs_of_tameDataInputs (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    (h : TameDataInputs K K' A) : PlaceLevelInputs A :=
  ⟨⟨h.choose, NK.LocalStructure.residueCard K (NK.TameData.primeBelow A),
      NK.TameData.TameDataInput.toTameData h.choose_spec.1, h.choose_spec.2⟩,
    residueCardMatches_residueCard A,
    residueCardInput_of_tameFrobeniusCore A h.choose_spec.1.frobenius⟩

/-- **The local structure inputs at a place give the inputs of the dictionary at that place.** -/
noncomputable def placeLevelInputs_of_localStructureData (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    (h : LocalStructureData K K' A) : PlaceLevelInputs A :=
  placeLevelInputs_of_tameDataInputs A (tameDataInputs_of_localStructureData A h)

/-- **The local–global residue-field dictionary at every place**, from the local structure theory
at every place (weakest form).  This is the unconditional form of input (b) of the Neukirch–Uchida
endgame, relative to the local structure theory. -/
theorem frobDictionary_of_tameDataInputs
    (h : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', TameDataInputs K K' A) :
    NK.FrobeniusBridge.FrobDictionary K K' :=
  frobDictionary_of_placeLevelInputs fun A => placeLevelInputs_of_tameDataInputs A (h A)

/-- **The local structure theory at every place** (`NK.FrobeniusBridge.TameDataAtPlaces`), from
the reduced input catalogue at every place.  This is the shape consumed by
`NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_tameData_atPlaces`, and it is the
conjunction of `NK.TameData.TameDataInput.toTameData` with the identification
`NK.TameData.primeBelow A = Submission.NeukirchUchida.primeOf A.1 A.2`. -/
theorem tameDataAtPlaces_of_tameDataInputs
    (h : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', TameDataInputs K K' A) :
    NK.FrobeniusBridge.TameDataAtPlaces K K' := by
  intro A
  obtain ⟨p, hI, hZ⟩ := h A
  exact ⟨p, _, NK.TameData.TameDataInput.toTameData hI, hZ⟩

/-- **The dictionary from the `𝔭`-adic reduced catalogue at every place.** -/
theorem frobDictionary_of_localStructureData
    (h : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', LocalStructureData K K' A) :
    NK.FrobeniusBridge.FrobDictionary K K' :=
  frobDictionary_of_tameDataInputs fun A => tameDataInputs_of_localStructureData A (h A)

/-- **The local structure theory at every place, from the `𝔭`-adic reduced catalogue.** -/
theorem tameDataAtPlaces_of_localStructureData
    (h : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', LocalStructureData K K' A) :
    NK.FrobeniusBridge.TameDataAtPlaces K K' :=
  tameDataAtPlaces_of_tameDataInputs fun A => tameDataInputs_of_localStructureData A (h A)

section Endgame

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The instantiation in the endgame's vocabulary**: the hypotheses `hD₁`, `hD₂` (the local–global
dictionary at the places of the two fields) *and* `hTame` of
`NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_tameData_atPlaces` are **discharged** by the
local structure theory at the places of the two fields, so the finite-level, σ-free Frobenius
correspondence — input (b) of the Neukirch–Uchida endgame — follows from the local structure
theory at the places of the two fields alone. -/
theorem frobeniusCorrespondencePlace_of_tameDataInputs
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁', TameDataInputs K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂', TameDataInputs K₂ K₂' B) :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a :=
  NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_tameData_atPlaces ϕ hϕ a
    (frobDictionary_of_tameDataInputs h₁) (frobDictionary_of_tameDataInputs h₂)
    (tameDataAtPlaces_of_tameDataInputs h₂)

/-- **The existence half of Neukirch–Uchida** from the local structure theory at every place of the
two fields: inputs (a) (the place correspondence), the local structure theory at the places of the
two fields, and the reconstruction (d) give `∃ σ, Conjugates σ ϕ`. -/
theorem exists_sigma_of_tameDataInputs (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁', TameDataInputs K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂', TameDataInputs K₂ K₂' B)
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  NK.FrobeniusBridge.exists_sigma_of_tameData_atPlaces ϕ hϕ a
    (frobDictionary_of_tameDataInputs h₁) (frobDictionary_of_tameDataInputs h₂)
    (tameDataAtPlaces_of_tameDataInputs h₂) d

/-- **The instantiation in the endgame's vocabulary, from the `𝔭`-adic reduced catalogue.** -/
theorem frobeniusCorrespondencePlace_of_localStructureData
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁', LocalStructureData K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂', LocalStructureData K₂ K₂' B) :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a :=
  frobeniusCorrespondencePlace_of_tameDataInputs ϕ hϕ a
    (fun A => tameDataInputs_of_localStructureData A (h₁ A))
    (fun B => tameDataInputs_of_localStructureData B (h₂ B))

/-- **The existence half of Neukirch–Uchida**, from the `𝔭`-adic reduced catalogue at every place
of the two fields. -/
theorem exists_sigma_of_localStructureData (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁', LocalStructureData K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂', LocalStructureData K₂ K₂' B)
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_tameDataInputs ϕ hϕ a
    (fun A => tameDataInputs_of_localStructureData A (h₁ A))
    (fun B => tameDataInputs_of_localStructureData B (h₂ B)) d

end Endgame

end NK.ResidueFrob
