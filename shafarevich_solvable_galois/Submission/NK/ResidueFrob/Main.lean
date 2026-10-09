import Submission.NK.ResidueFrob.Core
import Submission.NK.FrobeniusBridge.Endgame
import Submission.NK.FrobeniusBridge.Equivalence
import Submission.NK.ResidueFrob.inertia_of_levels_of_tameData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local–global residue-field dictionary: main results

* `frobDictionary_of_placeLevelInputs` — **the dictionary** `NK.FrobeniusBridge.FrobDictionary
  K K'` from the local inputs `NK.ResidueFrob.PlaceLevelInputs` at every place.  Both fields of
  `PlaceLevelInputs` beyond the local data `D` are discharged from the local structure theory in
  `Submission/Work/ResidueFrob/LocalStructureInputs.lean`
  (`frobDictionary_of_localStructureData`).
* `tameDataAtPlaces_of_frobDictionary` — **the boundary, unconditionally**: the dictionary implies
  the local structure theory at every place.  In particular the unconditional form of the
  dictionary is *equivalent* to the local structure theory (up to the two normalisation inputs
  displayed in `PlaceLevelInputs`); see `README.md`.
* `exists_residueCardInput_of_frobDictionary` — the dictionary *provides* the normalised Frobenius
  of the local field at every place.
* `frobeniusCorrespondencePlace_of_placeLevelInputs` — the endgame instantiation: the hypotheses
  `hD₁`, `hD₂` of `NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_tameData_atPlaces` are
  discharged by the dictionary, so the finite-level, σ-free Frobenius correspondence — input (b)
  of the Neukirch–Uchida endgame — follows from the local inputs at the places of the two fields
  and `TameDataAtPlaces` alone.
-/

namespace NK.ResidueFrob

open scoped Pointwise Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The local structure inputs chosen at the places of `K'`.** -/
noncomputable def chosenData (h : NK.FrobeniusBridge.TameDataAtPlaces K K')
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') : NK.FrobeniusBridge.PlaceLevelData A :=
  ⟨(h A).choose, (h A).choose_spec.choose, (h A).choose_spec.choose_spec.1,
    (h A).choose_spec.choose_spec.2⟩

/-- **The local–global residue-field dictionary at every place**, from the local structure theory
at every place plus, at every place, the residue-cardinality input and the normalised Frobenius
input.  (The level-inertia input of the older interface is a theorem of this chapter,
`NK.ResidueFrob.levelInertiaCovered_of_tameData`, and is no longer a hypothesis.) -/
theorem frobDictionary_of_tameDataAtPlaces (hT : NK.FrobeniusBridge.TameDataAtPlaces K K')
    (hq : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K',
      ResidueCardMatches A (chosenData hT A).q)
    (hF : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K',
      NK.LocalAnabelian.ResidueCardInput (chosenData hT A).p (chosenData hT A).q
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A)) :
    NK.FrobeniusBridge.FrobDictionary K K' :=
  frobDictionary_of_placeLevelInputs fun A => ⟨chosenData hT A, hq A, hF A⟩

/-- **The boundary, unconditionally**: the local–global residue-field dictionary at every place
implies the local structure theory at every place. -/
theorem tameDataAtPlaces_of_frobDictionary (h : NK.FrobeniusBridge.FrobDictionary K K') :
    NK.FrobeniusBridge.TameDataAtPlaces K K' := by
  intro A
  obtain ⟨g, hg⟩ := NK.FrobeniusBridge.PlaceLevelBridge.exists_localFrob (h A)
  obtain ⟨hgD, p, q, hT, hZ, hΓ⟩ := hg
  exact ⟨p, q, hT, hZ⟩

/-- **The dictionary provides the normalised Frobenius of the local field at every place.** -/
theorem exists_residueCardInput_of_frobDictionary (h : NK.FrobeniusBridge.FrobDictionary K K')
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') :
    ∃ p q : ℕ, Nonempty (NK.LocalAnabelian.ResidueCardInput p q
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A)) := by
  obtain ⟨g, hg⟩ := NK.FrobeniusBridge.PlaceLevelBridge.exists_localFrob (h A)
  obtain ⟨hgD, p, q, hT, hZ, hΓ⟩ := hg
  exact ⟨p, q, ⟨⟨hT.structure_input.hp, NK.FrobeniusBridge.localGaloisEquiv A ⟨g, hgD⟩,
    hΓ.1, hΓ.2⟩⟩⟩

/-- **The "all levels" inertia statement** (the statement of
`NK.FrobeniusBridge.InertiaLevelBridge`) in terms of the local data `D` at a place, with the
residue-cardinality input `hq`: an element of `D_A` acting trivially on the residue field of every
finite normal level lies in the local inertia subgroup `I_κ`.

This is the companion of the `inertia_surjective` field of the core: it is the direction
"local inertia ⊇ level inertia" at *all* levels, and it is the engine behind the (proved)
level-inertia theorem `NK.ResidueFrob.levelInertiaCovered_of_tameData`. -/
theorem inertia_of_levels_of_placeLevelData (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    (D : NK.FrobeniusBridge.PlaceLevelData A) (hq : ResidueCardMatches A D.q)
    (g : Gal(K'/K))
    (hgtriv : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
      NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L g)
    (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1) :
    NK.FrobeniusBridge.localGaloisEquiv A ⟨g, hg⟩ ∈
      NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A)
        (K' := NK.FrobeniusBridge.localClosure A) D.p :=
  inertia_of_levels_of_tameData A D.hT hq g hgtriv hg

section Endgame

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The instantiation in the endgame's vocabulary**: the hypotheses `hD₁`, `hD₂` of
`NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_tameData_atPlaces` are discharged by the
dictionary, so input (b) of the Neukirch–Uchida endgame follows from the local inputs at the
places of the two fields and `TameDataAtPlaces K₂ K₂'` alone. -/
theorem frobeniusCorrespondencePlace_of_placeLevelInputs
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁', PlaceLevelInputs A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂', PlaceLevelInputs B)
    (hTame : NK.FrobeniusBridge.TameDataAtPlaces K₂ K₂') :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a :=
  NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_tameData_atPlaces ϕ hϕ a
    (frobDictionary_of_placeLevelInputs h₁) (frobDictionary_of_placeLevelInputs h₂) hTame

/-- **The existence half of Neukirch–Uchida** with the dictionary discharged by the local inputs:
inputs (a), the local inputs at the places of the two fields, the local structure theory of `K₂`,
and the reconstruction (d) give `∃ σ, Conjugates σ ϕ`. -/
theorem exists_sigma_of_placeLevelInputs (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁', PlaceLevelInputs A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂', PlaceLevelInputs B)
    (hTame : NK.FrobeniusBridge.TameDataAtPlaces K₂ K₂')
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  NK.FrobeniusBridge.exists_sigma_of_tameData_atPlaces ϕ hϕ a
    (frobDictionary_of_placeLevelInputs h₁) (frobDictionary_of_placeLevelInputs h₂) hTame d

end Endgame

end NK.ResidueFrob
